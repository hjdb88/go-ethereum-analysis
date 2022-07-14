// Copyright 2014 The go-ethereum Authors
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
	"hash"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/log"
)

// Config are the configuration options for the Interpreter
type Config struct {
	Debug                   bool      // Enables debugging
	Tracer                  EVMLogger // Opcode logger
	NoBaseFee               bool      // Forces the EIP-1559 baseFee to 0 (needed for 0 price calls)
	EnablePreimageRecording bool      // Enables recording of SHA3/keccak preimages

	JumpTable *JumpTable // EVM instruction table, automatically populated if unset

	ExtraEips []int // Additional EIPS that are to be enabled
}

// ScopeContext contains the things that are per-call, such as stack and memory,
// but not transients like pc and gas
type ScopeContext struct {
	Memory   *Memory
	Stack    *Stack
	Contract *Contract
}

// keccakState wraps sha3.state. In addition to the usual hash methods, it also supports
// Read to get a variable amount of data from the hash state. Read is faster than Sum
// because it doesn't copy the internal state, but also modifies the internal state.
type keccakState interface {
	hash.Hash
	Read([]byte) (int, error)
}

// EVMInterpreter represents an EVM interpreter
type EVMInterpreter struct {
	evm *EVM
	cfg Config

	hasher    keccakState // Keccak256 hasher instance shared across opcodes
	hasherBuf common.Hash // Keccak256 hasher result array shared aross opcodes

	readOnly   bool   // Whether to throw on stateful modifications
	returnData []byte // Last CALL's return data for subsequent reuse
}

// NewEVMInterpreter returns a new instance of the Interpreter.
func NewEVMInterpreter(evm *EVM, cfg Config) *EVMInterpreter {
	// If jump table was not initialised we set the default one.
	if cfg.JumpTable == nil {
		switch {
		case evm.chainRules.IsMerge:
			cfg.JumpTable = &mergeInstructionSet
		case evm.chainRules.IsLondon:
			cfg.JumpTable = &londonInstructionSet
		case evm.chainRules.IsBerlin:
			cfg.JumpTable = &berlinInstructionSet
		case evm.chainRules.IsIstanbul:
			cfg.JumpTable = &istanbulInstructionSet
		case evm.chainRules.IsConstantinople:
			cfg.JumpTable = &constantinopleInstructionSet
		case evm.chainRules.IsByzantium:
			cfg.JumpTable = &byzantiumInstructionSet
		case evm.chainRules.IsEIP158:
			cfg.JumpTable = &spuriousDragonInstructionSet
		case evm.chainRules.IsEIP150:
			cfg.JumpTable = &tangerineWhistleInstructionSet
		case evm.chainRules.IsHomestead:
			cfg.JumpTable = &homesteadInstructionSet
		default:
			cfg.JumpTable = &frontierInstructionSet
		}
		for i, eip := range cfg.ExtraEips {
			copy := *cfg.JumpTable
			if err := EnableEIP(eip, &copy); err != nil {
				// Disable it, so caller can check if it's activated or not
				cfg.ExtraEips = append(cfg.ExtraEips[:i], cfg.ExtraEips[i+1:]...)
				log.Error("EIP activation failed", "eip", eip, "error", err)
			}
			cfg.JumpTable = &copy
		}
	}

	return &EVMInterpreter{
		evm: evm,
		cfg: cfg,
	}
}

// Run loops and evaluates the contract's code with the given input data and returns
// the return byte-slice and an error if one occurred.
//
// It's important to note that any errors returned by the interpreter should be
// considered a revert-and-consume-all-gas operation except for
// ErrExecutionReverted which means revert-and-keep-gas-left.
func (in *EVMInterpreter) Run(contract *Contract, input []byte, readOnly bool) (ret []byte, err error) {

	// Increment the call depth which is restricted to 1024
	in.evm.depth++
	defer func() { in.evm.depth-- }()

	// Make sure the readOnly is only set if we aren't in readOnly yet.
	// This also makes sure that the readOnly flag isn't removed for child calls.
	if readOnly && !in.readOnly {
		in.readOnly = true
		defer func() { in.readOnly = false }()
	}

	// Reset the previous call's return data. It's unimportant to preserve the old buffer
	// as every returning call will return new data anyway.
	in.returnData = nil

	// Don't bother with the execution if there's no code.
	if len(contract.Code) == 0 {
		return nil, nil
	}

	var (
		op          OpCode        // current opcode
		mem         = NewMemory() // bound memory
		stack       = newstack()  // local stack
		callContext = &ScopeContext{
			Memory:   mem,
			Stack:    stack,
			Contract: contract,
		}
		// For optimisation reason we're using uint64 as the program counter.
		// It's theoretically possible to go above 2^64. The YP defines the PC
		// to be uint256. Practically much less so feasible.
		pc   = uint64(0) // program counter
		cost uint64
		// copies used by tracer
		pcCopy  uint64 // needed for the deferred EVMLogger
		gasCopy uint64 // for EVMLogger to log gas remaining before execution
		logged  bool   // deferred EVMLogger should ignore already logged steps
		res     []byte // result of the opcode execution function
	)
	// Don't move this deferred function, it's placed before the capturestate-deferred method,
	// so that it get's executed _after_: the capturestate needs the stacks before
	// they are returned to the pools
	// 当执行停止时, 将 stack 放入到 stackPool 中
	defer func() {
		returnStack(stack)
	}()
	contract.Input = input

	if in.cfg.Debug {
		defer func() {
			if err != nil {
				if !logged {
					in.cfg.Tracer.CaptureState(pcCopy, op, gasCopy, cost, callContext, in.returnData, in.evm.depth, err)
				} else {
					in.cfg.Tracer.CaptureFault(pcCopy, op, gasCopy, cost, callContext, in.evm.depth, err)
				}
			}
		}()
	}
	// The Interpreter main run loop (contextual). This loop runs until either an
	// explicit STOP, RETURN or SELFDESTRUCT is executed, an error occurred during
	// the execution of one of the operations or until the done flag is set by the
	// parent context.
	/*
		解释器循环运行（上下文）
		直到执行出现以下情况时停止:
		   1. 遇到显式 STOP、RETURN 或 SELFDESTRUCT
		   2. 执行其中一个操作期间发生错误
		   3. 父上下文设置了 done 标志
	*/
	for {
		if in.cfg.Debug {
			// Capture pre-execution values for tracing.
			logged, pcCopy, gasCopy = false, pc, contract.Gas
		}
		// Get the operation from the jump table and validate the stack to ensure there are
		// enough stack items available to perform the operation.
		// 从跳转表 jump_table.go 中获取一个操作并验证堆栈确保有足够的堆栈项可用于执行该操作
		// pc 一次取一个字节(两个16进制字符), 对应到跳转表中的操作, (创建合约都是60806040开头，详细查看 https://docs.soliditylang.org/en/v0.8.15/internals/layout_in_memory.html)
		op = contract.GetOp(pc)
		operation := in.cfg.JumpTable[op]
		cost = operation.constantGas // For tracing
		// Validate stack
		// 验证堆栈, 以太坊命令执行规定了最大和最小堆栈数量
		if sLen := stack.len(); sLen < operation.minStack {
			return nil, &ErrStackUnderflow{stackLen: sLen, required: operation.minStack}
		} else if sLen > operation.maxStack {
			return nil, &ErrStackOverflow{stackLen: sLen, limit: operation.maxStack}
		}
		if !contract.UseGas(cost) {
			return nil, ErrOutOfGas
		}
		if operation.dynamicGas != nil {
			// All ops with a dynamic memory usage also has a dynamic gas cost.
			// 所有具有动态内存使用的操作也有动态的 gas 成本
			var memorySize uint64
			// 计算新开的内存大小并扩展内存以适应该操作
			// calculate the new memory size and expand the memory to fit
			// the operation
			// 在计算动态 gas 部分之前需要进行内存检查，以检测计算溢出
			// Memory check needs to be done prior to evaluating the dynamic gas portion,
			// to detect calculation overflows
			if operation.memorySize != nil {
				// 计算当前操作所需消耗的内存空间
				memSize, overflow := operation.memorySize(stack)
				if overflow {
					return nil, ErrGasUintOverflow
				}
				// memory is expanded in words of 32 bytes. Gas
				// is also calculated in words.
				if memorySize, overflow = math.SafeMul(toWordSize(memSize), 32); overflow {
					return nil, ErrGasUintOverflow
				}
			}
			// Consume the gas and return an error if not enough gas is available.
			// cost is explicitly set so that the capture state defer method can get the proper cost
			// 如果没有足够的可用 gas ，则消耗 gas 并返回错误
			// 计算该操作的动态 gas 消耗数量
			var dynamicCost uint64
			// 引用该操作的 operation 对象的 gasFunc 方法完成计算
			dynamicCost, err = operation.dynamicGas(in.evm, contract, stack, mem, memorySize)
			cost += dynamicCost // for tracing
			if err != nil || !contract.UseGas(dynamicCost) {
				return nil, ErrOutOfGas
			}
			// Do tracing before memory expansion
			if in.cfg.Debug {
				in.cfg.Tracer.CaptureState(pc, op, gasCopy, cost, callContext, in.returnData, in.evm.depth, err)
				logged = true
			}
			// 分配更多的内存
			if memorySize > 0 {
				// 实际上是在原来的 mem 中加上当前操作需要的内存大小
				mem.Resize(memorySize)
			}
		} else if in.cfg.Debug {
			in.cfg.Tracer.CaptureState(pc, op, gasCopy, cost, callContext, in.returnData, in.evm.depth, err)
			logged = true
		}
		// execute the operation
		// 执行操作, 调用 operation 对象定义的 execute 方法
		res, err = operation.execute(&pc, in, callContext)
		if err != nil {
			break
		}
		// pc 加一读取下一个指令
		pc++
	}

	if err == errStopToken {
		err = nil // clear stop token error
	}

	return res, err
}
