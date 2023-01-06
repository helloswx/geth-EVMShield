// Copyright 2015 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package vm

import (
	"bytes"
	"io/ioutil"
	"log"
	"math/big"
	"os"

	"github.com/ethereum/go-ethereum/common"
	"github.com/holiman/uint256"

	//【*】
	"encoding/hex"
	"encoding/json"

	mapset "github.com/deckarep/golang-set"
	"github.com/ethereum/go-ethereum/crypto"
)

// ContractRef is a reference to the contract's backing object
type ContractRef interface {
	Address() common.Address
}

// AccountRef implements ContractRef.
//
// Account references are used during EVM initialisation and
// it's primary use is to fetch addresses. Removing this object
// proves difficult because of the cached jump destinations which
// are fetched from the parent contract (i.e. the caller), which
// is a ContractRef.
type AccountRef common.Address

// Address casts AccountRef to a Address
func (ar AccountRef) Address() common.Address { return (common.Address)(ar) }

//【*】变量名对应的绑定信息
type Variable struct {
	Slot      mapset.Set //所有slot
	StartSlot uint256.Int

	IfPackage     bool
	PackageSize   int
	OriginalValue uint256.Int //ssload时加载的值
	PackageStart  int

	IfDynamic       bool
	DynamicStart    uint256.Int //存储长度的初始slot
	IfDynamicUpdate bool

	IfMapping    bool
	MappingStart uint256.Int //（key，slot）中的slot，（key，hash）中的hash

	MappingValueType string //只记录最后一个的value的类型
	Deep             int    //mapping嵌套层数
	MapValue         []Variable
}

// Contract represents an ethereum contract in the state database. It contains
// the contract code, calling arguments. Contract implements ContractRef
type Contract struct {
	// CallerAddress is the result of the caller which initialised this
	// contract. However when the "call method" is delegated this value
	// needs to be initialised to that of the caller's caller.
	CallerAddress common.Address
	caller        ContractRef
	self          ContractRef

	jumpdests map[common.Hash]bitvec // Aggregated result of JUMPDEST analysis.
	analysis  bitvec                 // Locally cached result of JUMPDEST analysis

	Code     []byte
	CodeHash common.Hash
	CodeAddr *common.Address
	Input    []byte

	Gas   uint64
	value *big.Int

	//【*】函数名的绑定信息
	Functionname   string
	FunctionShield []Variable
	FunctionAllow  []Variable
}

// NewContract returns a new contract environment for the execution of EVM.
func NewContract(caller ContractRef, object ContractRef, value *big.Int, gas uint64) *Contract {
	c := &Contract{CallerAddress: caller.Address(), caller: caller, self: object}

	if parent, ok := caller.(*Contract); ok {
		// Reuse JUMPDEST analysis from parent context if available.
		c.jumpdests = parent.jumpdests
	} else {
		c.jumpdests = make(map[common.Hash]bitvec)
	}

	// Gas should be a pointer so it can safely be reduced through the run
	// This pointer will be off the state transition
	c.Gas = gas
	// ensures a value is set
	c.value = value

	return c
}

//【*】NewRule returns a new contract environment with the rule information for the execution of EVM.
// function 读取文件,json反序列化，添加到contract对象内
func (c *Contract) NewRule() *Contract {
	var Con Contract
	file, _ := os.Open("./rule.json")
	defer file.Close()
	decoder := json.NewDecoder(file)
	err := decoder.Decode(&Con)
	if err != nil {
		log.Println(err)
	}
	fn, _ := hex.DecodeString(Con.Functionname)

	if bytes.Equal(c.Input[0:4], fn) {
		c.Functionname = Con.Functionname
		c.FunctionShield = Con.FunctionShield
		for i := 0; i < len(c.FunctionShield); i++ {
			c.FunctionShield[i].InitSlot()
		}
		for i := 0; i < len(c.FunctionAllow); i++ {
			c.FunctionAllow[i].InitSlot()
		}
	}
	return c
}

func (v *Variable) InitSlot() *Variable {
	v.Slot = mapset.NewSet(v.StartSlot)
	if v.Deep != 0 {
		for i := 0; i < len(v.MapValue); i++ {
			v.MapValue[i].InitSlot()
		}
	}
	return v
}

func (c *Contract) Write() {

	data, err := json.MarshalIndent(c, "", "	")
	if err != nil {
		panic(err)
	}
	err = ioutil.WriteFile("rule.json", data, 0777)
	if err != nil {
		panic(err)
	}

}

//【*】屏蔽逻辑,SSTORE时调用
func (v *Variable) Shield(loc uint256.Int, val uint256.Int, interpreter *EVMInterpreter, scope *ScopeContext) bool {

	write := true
	//如果是打包情况下
	if v.IfPackage {

		//只有一个slot
		if v.Slot.Contains(loc) {
			//将不是val的位置改为 0
			//在SSLOAD时已将获取到的value的其他选定位置改为 0
			valueothers := val.Bytes32()
			valueoriginal := v.OriginalValue.Bytes32()
			for i := 0; i < v.PackageStart; i++ {

				valueothers[i] = 0
				v.OriginalValue[i] = 0
			}
			for i := v.PackageStart + v.PackageSize; i < len(valueothers); i++ {
				valueothers[i] = 0
				v.OriginalValue[i] = 0
			}
			res := bytes.Equal(valueothers[:], valueoriginal[:])
			if !res {

				write = false
				return write

			}

		}

		//mapping类型：遍历slot[]集合。如果是嵌套，递归
	} else if v.IfMapping {
		if v.Slot.Contains(loc) {
			write = false
			return write
		}
		if v.Deep != 0 {
			for _, mapv := range v.MapValue {
				write = mapv.Shield(loc, val, interpreter, scope)

			}
		}

		//不是打包情况下，直接遍历整个slot集合
	} else if v.IfDynamic {
		//在此之前先更新Dynamic的slot集合
		v.DynamicUpdate(interpreter, scope)

		if v.Slot.Contains(loc) {
			write = false
			return write
		}
	} else {
		if v.Slot.Contains(loc) {
			write = false
			return write
		}
	}
	return write
}

//【*】SHA3识别
// 本函数的功能在于
//给定slot，寻找是否为要标记的mapping 变量
//记录hash
func (v *Variable) IdentifyMap(slot uint256.Int, hash uint256.Int, interpreter *EVMInterpreter, scope *ScopeContext) *Variable {
	exist := false
	//只在mapping类型里找。
	if v.IfMapping {

		res := bytes.Equal(slot.Bytes(), v.MappingStart.Bytes())

		//在屏蔽列表中找到了
		//传进来的slot与记录的mapping slot 相等
		if res {

			//如果是嵌套mapping,查找hash是否已经被下一层 mapping 记录
			if v.Deep != 0 {
				//遍历已记录的下一层
				for i := 0; i < len(v.MapValue); i++ {
					if bytes.Equal(v.MapValue[i].MappingStart.Bytes(), hash.Bytes()) {
						exist = true
						// fmt.Println("DeepExit")
						break
					}
				}
				//如果不存在则添加
				if !exist {
					var deepvariable Variable
					deepvariable.Deep = v.Deep - 1
					deepvariable.MappingStart = hash
					deepvariable.IfMapping = true

					deepvariable.Slot = mapset.NewSet(hash)

					deepvariable.MappingValueType = v.MappingValueType
					v.MapValue = append(v.MapValue, deepvariable)
					return v
				}

			}

			//如果不是嵌套mapping,或者已经到最后一层：存储 mapping 的 Value 对应的 hash
			if v.Deep == 0 {
				v.Slot.Add(hash)
				if v.MappingValueType == "Dynamic" {
					v.DynamicStart = hash
					v.IfDynamic = true
					v.DynamicUpdate(interpreter, scope)
					//获取数组、string长度，计算所有slot
					//添加到 slot集合中
					//调用动态变量的情况下，更新列表的算法

				}
			}
			//这一层的start不对，递归去下一层找
		} else {
			count := v.Deep

			if count != 0 {
				count--
				for i := 0; i < len(v.MapValue); i++ {
					v.MapValue[i].IdentifyMap(slot, hash, interpreter, scope)
					// fmt.Println(v.MapValue[i])

				}
			}

		}
	}
	return v
}

//【*】 动态类型的对象成员更新
func (v *Variable) DynamicUpdate(interpreter *EVMInterpreter, scope *ScopeContext) *Variable {

	if v.IfDynamic {

		if interpreter.hasher == nil {
			interpreter.hasher = crypto.NewKeccakState()
		} else {
			interpreter.hasher.Reset()
		}
		interpreter.hasher.Write(v.DynamicStart.Bytes())
		interpreter.hasher.Read(interpreter.hasherBuf[:])

		evm := interpreter.evm
		if evm.Config.EnablePreimageRecording {
			evm.StateDB.AddPreimage(interpreter.hasherBuf, v.DynamicStart.Bytes())
		}

		hash := common.BytesToHash(interpreter.hasherBuf[:]).Bytes()

		v.GetDynamicSlot(hash, interpreter, scope)

	}
	return v
}

//【*】
func (v *Variable) GetDynamicSlot(first []byte, interpreter *EVMInterpreter, scope *ScopeContext) *Variable {
	var uintTemp uint256.Int
	uintTemp.SetBytes(first)
	val := interpreter.evm.StateDB.GetState(scope.Contract.Address(), common.BytesToHash(first)).Bytes()

	if val != nil {
		v.Slot.Add(uintTemp)
		uintTemp.Add(&uintTemp, uint256.NewInt(1))
		first = uintTemp.Bytes()

		return v.GetDynamicSlot(first, interpreter, scope)

	} else {
		return v
	}

}

//【*】FunctionAllow 正常运行时更新 mapping 、Dynamic
func (c *Contract) UpdateFuncAllow(interpreter *EVMInterpreter, scope *ScopeContext) *Contract {
	for i := 0; i < len(c.FunctionAllow); i++ {
		c.FunctionAllow[i].UpdatevariableAllow(interpreter, scope)
	}

	return c
}

//【*】
func (v *Variable) UpdatevariableAllow(interpreter *EVMInterpreter, scope *ScopeContext) *Variable {
	if v.IfDynamic {
		v.DynamicUpdate(interpreter, scope)
	}
	if v.Deep != 0 && v.MappingValueType == "Dynamic" {
		for i := 0; i < len(v.MapValue); i++ {
			v.MapValue[i].UpdatevariableAllow(interpreter, scope)

		}

	}

	return v
}

func (c *Contract) validJumpdest(dest *uint256.Int) bool {
	udest, overflow := dest.Uint64WithOverflow()
	// PC cannot go beyond len(code) and certainly can't be bigger than 63bits.
	// Don't bother checking for JUMPDEST in that case.
	if overflow || udest >= uint64(len(c.Code)) {
		return false
	}
	// Only JUMPDESTs allowed for destinations
	if OpCode(c.Code[udest]) != JUMPDEST {
		return false
	}
	return c.isCode(udest)
}

// isCode returns true if the provided PC location is an actual opcode, as
// opposed to a data-segment following a PUSHN operation.
func (c *Contract) isCode(udest uint64) bool {
	// Do we already have an analysis laying around?
	if c.analysis != nil {
		return c.analysis.codeSegment(udest)
	}
	// Do we have a contract hash already?
	// If we do have a hash, that means it's a 'regular' contract. For regular
	// contracts ( not temporary initcode), we store the analysis in a map
	if c.CodeHash != (common.Hash{}) {
		// Does parent context have the analysis?
		analysis, exist := c.jumpdests[c.CodeHash]
		if !exist {
			// Do the analysis and save in parent context
			// We do not need to store it in c.analysis
			analysis = codeBitmap(c.Code)
			c.jumpdests[c.CodeHash] = analysis
		}
		// Also stash it in current contract for faster access
		c.analysis = analysis
		return analysis.codeSegment(udest)
	}
	// We don't have the code hash, most likely a piece of initcode not already
	// in state trie. In that case, we do an analysis, and save it locally, so
	// we don't have to recalculate it for every JUMP instruction in the execution
	// However, we don't save it within the parent context
	if c.analysis == nil {
		c.analysis = codeBitmap(c.Code)
	}
	return c.analysis.codeSegment(udest)
}

// AsDelegate sets the contract to be a delegate call and returns the current
// contract (for chaining calls)
func (c *Contract) AsDelegate() *Contract {
	// NOTE: caller must, at all times be a contract. It should never happen
	// that caller is something other than a Contract.
	parent := c.caller.(*Contract)
	c.CallerAddress = parent.CallerAddress
	c.value = parent.value

	return c
}

// GetOp returns the n'th element in the contract's byte array
func (c *Contract) GetOp(n uint64) OpCode {
	if n < uint64(len(c.Code)) {
		return OpCode(c.Code[n])
	}

	return STOP
}

// Caller returns the caller of the contract.
//
// Caller will recursively call caller when the contract is a delegate
// call, including that of caller's caller.
func (c *Contract) Caller() common.Address {
	return c.CallerAddress
}

// UseGas attempts the use gas and subtracts it and returns true on success
func (c *Contract) UseGas(gas uint64) (ok bool) {
	if c.Gas < gas {
		return false
	}
	c.Gas -= gas
	return true
}

// Address returns the contracts address
func (c *Contract) Address() common.Address {
	return c.self.Address()
}

// Value returns the contract's value (sent to it from it's caller)
func (c *Contract) Value() *big.Int {
	return c.value
}

// SetCallCode sets the code of the contract and address of the backing data
// object
func (c *Contract) SetCallCode(addr *common.Address, hash common.Hash, code []byte) {
	c.Code = code
	c.CodeHash = hash
	c.CodeAddr = addr
}

// SetCodeOptionalHash can be used to provide code, but it's optional to provide hash.
// In case hash is not provided, the jumpdest analysis will not be saved to the parent context
func (c *Contract) SetCodeOptionalHash(addr *common.Address, codeAndHash *codeAndHash) {
	c.Code = codeAndHash.code
	c.CodeHash = codeAndHash.hash
	c.CodeAddr = addr
}
