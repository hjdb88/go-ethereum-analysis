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

package core

import (
	"fmt"
	"math"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	cmath "github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/params"
)

// ExecutionResult includes all output after executing given evm
// message no matter the execution itself is successful or not.
type ExecutionResult struct {
	UsedGas    uint64 // Total used gas but include the refunded gas
	Err        error  // Any error encountered during the execution(listed in core/vm/errors.go)
	ReturnData []byte // Returned data from evm(function result or data supplied with revert opcode)
}

// Unwrap returns the internal evm error which allows us for further
// analysis outside.
func (result *ExecutionResult) Unwrap() error {
	return result.Err
}

// Failed returns the indicator whether the execution is successful or not
func (result *ExecutionResult) Failed() bool { return result.Err != nil }

// Return is a helper function to help caller distinguish between revert reason
// and function return. Return returns the data after execution if no error occurs.
func (result *ExecutionResult) Return() []byte {
	if result.Err != nil {
		return nil
	}
	return common.CopyBytes(result.ReturnData)
}

// Revert returns the concrete revert reason if the execution is aborted by `REVERT`
// opcode. Note the reason can be nil if no data supplied with revert opcode.
func (result *ExecutionResult) Revert() []byte {
	if result.Err != vm.ErrExecutionReverted {
		return nil
	}
	return common.CopyBytes(result.ReturnData)
}

/*
	执行成本由该交易需要使用多少以太坊虚拟机(EVM)的资源进行运算来决定的，执行交易的操作越多则执行成本就越高
	固有成本由交易的负载(payload)决定, 交易负载分为一下三种：
		1. 创建智能合约的交易, 负载就是创建智能合约的 EVM 代码
		2. 调用智能合约函数的交易, 负载就是执行消息的输入数据
		3. 两账户间转账的交易, 负载为空
	具体计算方式：(以 go-ethereum 1.11.5 版本)
		设 Ntxdatazeros 代表交易负载中数据为0的字节总数, Ntxdatanozeros 代表交易负载中数据不为0的字节总数,
		那么该交易的固有成本可以通过以下公式进行计算:
			黄皮书(6.2章公式60)，未更新和代码保持一致: https://ethereum.github.io/yellowpaper/paper.pdf
			黄皮书中文版(6.2章公式55、56和57), 比原版旧, 仅供参考: https://github.com/yuange1024/ethereum_yellowpaper/blob/master/ethereum_yellow_paper_cn.pdf
		固有成本 = Gtxdatazeros * Ntxdatazeros + Gtxdatanozeros * Ntxdatanozeros +
					Gtxcreate +
					Gtransaction +
					Ginitcodeword * Ninitcodeword +
					Gtxaccesslistaddress * Ntxaccesslistaddress + Gtxaccessliststorage * Ntxaccessliststorage

		其中:
			Gtxdatazeros: 4 Wei
			Gtxdatanozeros: 68 Wei (伊斯坦布尔硬分叉 EIP2028 之后为 16 Wei)
			Gtxcreate: 53000 Wei
			Gtransaction: 21000 Wei
			Ginitcodeword: 2 Wei
			Gtxaccesslistaddress: 2400 Wei
			Gtxaccessliststorage: 1900 Wei
*/
// IntrinsicGas computes the 'intrinsic gas' for a message with the given data.
// 计算进行该笔交易的固有成本
func IntrinsicGas(data []byte, accessList types.AccessList, isContractCreation bool, isHomestead, isEIP2028 bool, isEIP3860 bool) (uint64, error) {
	// Set the starting gas for the raw transaction
	var gas uint64
	// 1. 如果是创建合约调用起步价是 53000 gas, 如果是普通合约调用起步价是 21000 gas
	if isContractCreation && isHomestead {
		gas = params.TxGasContractCreation
	} else {
		gas = params.TxGas
	}
	dataLen := uint64(len(data))
	// Bump the required gas by the amount of transactional data
	if dataLen > 0 {
		// Zero and non-zero bytes are priced differently
		var nz uint64
		// 2. 计算输入的合约数据中非零字节和零字节的数量
		for _, byt := range data {
			if byt != 0 {
				nz++
			}
		}
		// Make sure we don't exceed uint64 for all data combinations
		nonZeroGas := params.TxDataNonZeroGasFrontier
		if isEIP2028 {
			nonZeroGas = params.TxDataNonZeroGasEIP2028
		}
		// 检查是否溢出
		if (math.MaxUint64-gas)/nonZeroGas < nz {
			return 0, ErrGasUintOverflow
		}
		// 计算零字节所消耗的 gas 数量
		// 零字节 4gas/字节, 非零字节 68(16)gas/字节
		// 零字节消耗 gas 少是因为 RLP 编码协议可以压缩零字节, 在向 Trie 存储这些数据时, 零字节占用空间很少
		gas += nz * nonZeroGas

		// 检查是否溢出
		z := dataLen - nz
		if (math.MaxUint64-gas)/params.TxDataZeroGas < z {
			return 0, ErrGasUintOverflow
		}
		// 计算零字节所消耗的 gas 数量
		gas += z * params.TxDataZeroGas

		// EIP-3860：限制和计量初始化代码
		// 将 initcode 的最大大小限制为 49152，并为每 32 字节的 initcode 块应用额外的 gas 成本 2
		if isContractCreation && isEIP3860 {
			lenWords := toWordSize(dataLen)
			if (math.MaxUint64-gas)/params.InitCodeWordGas < lenWords {
				return 0, ErrGasUintOverflow
			}
			gas += lenWords * params.InitCodeWordGas
		}
	}
	if accessList != nil {
		gas += uint64(len(accessList)) * params.TxAccessListAddressGas
		gas += uint64(accessList.StorageKeys()) * params.TxAccessListStorageKeyGas
	}
	return gas, nil
}

// toWordSize returns the ceiled word size required for init code payment calculation.
func toWordSize(size uint64) uint64 {
	if size > math.MaxUint64-31 {
		return math.MaxUint64/32 + 1
	}

	return (size + 31) / 32
}

// A Message contains the data derived from a single transaction that is relevant to state
// processing.
type Message struct {
	To         *common.Address
	From       common.Address
	Nonce      uint64
	Value      *big.Int
	GasLimit   uint64
	GasPrice   *big.Int
	GasFeeCap  *big.Int
	GasTipCap  *big.Int
	Data       []byte
	AccessList types.AccessList

	// When SkipAccountCheckss is true, the message nonce is not checked against the
	// account nonce in state. It also disables checking that the sender is an EOA.
	// This field will be set to true for operations like RPC eth_call.
	SkipAccountChecks bool
}

// TransactionToMessage converts a transaction into a Message.
func TransactionToMessage(tx *types.Transaction, s types.Signer, baseFee *big.Int) (*Message, error) {
	msg := &Message{
		Nonce:             tx.Nonce(),
		GasLimit:          tx.Gas(),
		GasPrice:          new(big.Int).Set(tx.GasPrice()),
		GasFeeCap:         new(big.Int).Set(tx.GasFeeCap()),
		GasTipCap:         new(big.Int).Set(tx.GasTipCap()),
		To:                tx.To(),
		Value:             tx.Value(),
		Data:              tx.Data(),
		AccessList:        tx.AccessList(),
		SkipAccountChecks: false,
	}
	// If baseFee provided, set gasPrice to effectiveGasPrice.
	if baseFee != nil {
		msg.GasPrice = cmath.BigMin(msg.GasPrice.Add(msg.GasTipCap, baseFee), msg.GasFeeCap)
	}
	var err error
	msg.From, err = types.Sender(s, tx)
	return msg, err
}

// ApplyMessage computes the new state by applying the given message
// against the old state within the environment.
//
// ApplyMessage returns the bytes returned by any EVM execution (if it took place),
// the gas used (which includes gas refunds) and an error if it failed. An error always
// indicates a core error meaning that the message would always fail for that particular
// state and would never be accepted within a block.
// 生成新的状态转换对象
func ApplyMessage(evm *vm.EVM, msg *Message, gp *GasPool) (*ExecutionResult, error) {
	return NewStateTransition(evm, msg, gp).TransitionDb()
}

// StateTransition represents a state transition.
//
// == The State Transitioning Model
//
// A state transition is a change made when a transaction is applied to the current world
// state. The state transitioning model does all the necessary work to work out a valid new
// state root.
//
//  1. Nonce handling
//  2. Pre pay gas
//  3. Create a new state object if the recipient is nil
//  4. Value transfer
//
// == If contract creation ==
//
//	4a. Attempt to run transaction data
//	4b. If valid, use result as code for the new state object
//
// == end ==
//
//  5. Run Script section
//  6. Derive new state root
//
// 状态转换模型
// 状态转换是将事务应用于当前世界时所做的状态更改。状态转换模型完成所有必要的工作来制定一个有效的新状态根。
//
// 1. nonce处理
// 2. 预付gas
// 3. 如果接收者为nil，则创建一个新的状态对象
// 4. 转账
// == 如果创建合约 ==
// 4a. 尝试运行交易数据
// 4b. 如果有效，使用结果作为新状态对象的代码
// == 结束 ==
// 5. 运行脚本部分
// 6. 导出新的状态根
type StateTransition struct {
	gp           *GasPool // 用来追踪区块内的gas使用情况
	msg          *Message // 交易内容
	gasRemaining uint64   // 剩余gas
	initialGas   uint64   // 初始gas
	state        vm.StateDB
	evm          *vm.EVM // 虚拟机
}

// NewStateTransition initialises and returns a new state transition object.
func NewStateTransition(evm *vm.EVM, msg *Message, gp *GasPool) *StateTransition {
	return &StateTransition{
		gp:    gp,
		evm:   evm,
		msg:   msg,
		state: evm.StateDB,
	}
}

// to returns the recipient of the message.
func (st *StateTransition) to() common.Address {
	if st.msg == nil || st.msg.To == nil /* contract creation */ {
		return common.Address{}
	}
	return *st.msg.To
}

func (st *StateTransition) buyGas() error {
	// 1. 计算交易消耗的 eth 数量, 通过交易发起者提供的 gas * gasPrice
	mgval := new(big.Int).SetUint64(st.msg.GasLimit)
	mgval = mgval.Mul(mgval, st.msg.GasPrice)
	balanceCheck := mgval
	if st.msg.GasFeeCap != nil {
		balanceCheck = new(big.Int).SetUint64(st.msg.GasLimit)
		balanceCheck = balanceCheck.Mul(balanceCheck, st.msg.GasFeeCap)
		balanceCheck.Add(balanceCheck, st.msg.Value)
	}
	// 2. 判断当前账户的余额是否能覆盖这笔交易预计消耗的 gas 数量
	if have, want := st.state.GetBalance(st.msg.From), balanceCheck; have.Cmp(want) < 0 {
		return fmt.Errorf("%w: address %v have %v want %v", ErrInsufficientFunds, st.msg.From.Hex(), have, want)
	}
	// 3. 从整个区块的 gaspool 中扣减掉这个交易预计消耗的 gas 数量
	if err := st.gp.SubGas(st.msg.GasLimit); err != nil {
		return err
	}
	// 4. 这部分 gas 数量转移到 st.gasRemaining 中, 用于后续 EVM 中执行命令时真实扣减 gas 数量
	st.gasRemaining += st.msg.GasLimit

	// 5. st.initialGas 记录最初分配的 gas 数量
	st.initialGas = st.msg.GasLimit
	// 6. 从发起者账户中扣减对应的 eth 数量(如果交易未被执行成功, 会被回滚)
	st.state.SubBalance(st.msg.From, mgval)
	return nil
}

func (st *StateTransition) preCheck() error {
	// Only check transactions that are not fake
	// 检查是否为虚假交易
	msg := st.msg
	if !msg.SkipAccountChecks {
		// Make sure this transaction's nonce is correct.
		stNonce := st.state.GetNonce(msg.From)
		if msgNonce := msg.Nonce; stNonce < msgNonce {
			return fmt.Errorf("%w: address %v, tx: %d state: %d", ErrNonceTooHigh,
				msg.From.Hex(), msgNonce, stNonce)
		} else if stNonce > msgNonce {
			return fmt.Errorf("%w: address %v, tx: %d state: %d", ErrNonceTooLow,
				msg.From.Hex(), msgNonce, stNonce)
		} else if stNonce+1 < stNonce {
			return fmt.Errorf("%w: address %v, nonce: %d", ErrNonceMax,
				msg.From.Hex(), stNonce)
		}
		// Make sure the sender is an EOA
		codeHash := st.state.GetCodeHash(msg.From)
		if codeHash != (common.Hash{}) && codeHash != types.EmptyCodeHash {
			return fmt.Errorf("%w: address %v, codehash: %s", ErrSenderNoEOA,
				msg.From.Hex(), codeHash)
		}
	}

	// Make sure that transaction gasFeeCap is greater than the baseFee (post london)
	if st.evm.ChainConfig().IsLondon(st.evm.Context.BlockNumber) {
		// Skip the checks if gas fields are zero and baseFee was explicitly disabled (eth_call)
		if !st.evm.Config.NoBaseFee || msg.GasFeeCap.BitLen() > 0 || msg.GasTipCap.BitLen() > 0 {
			if l := msg.GasFeeCap.BitLen(); l > 256 {
				return fmt.Errorf("%w: address %v, maxFeePerGas bit length: %d", ErrFeeCapVeryHigh,
					msg.From.Hex(), l)
			}
			if l := msg.GasTipCap.BitLen(); l > 256 {
				return fmt.Errorf("%w: address %v, maxPriorityFeePerGas bit length: %d", ErrTipVeryHigh,
					msg.From.Hex(), l)
			}
			if msg.GasFeeCap.Cmp(msg.GasTipCap) < 0 {
				return fmt.Errorf("%w: address %v, maxPriorityFeePerGas: %s, maxFeePerGas: %s", ErrTipAboveFeeCap,
					msg.From.Hex(), msg.GasTipCap, msg.GasFeeCap)
			}
			// This will panic if baseFee is nil, but basefee presence is verified
			// as part of header validation.
			if msg.GasFeeCap.Cmp(st.evm.Context.BaseFee) < 0 {
				return fmt.Errorf("%w: address %v, maxFeePerGas: %s baseFee: %s", ErrFeeCapTooLow,
					msg.From.Hex(), msg.GasFeeCap, st.evm.Context.BaseFee)
			}
		}
	}
	return st.buyGas()
}

// TransitionDb will transition the state by applying the current message and
// returning the evm execution result with following fields.
//
//   - used gas: total gas used (including gas being refunded)
//   - returndata: the returned data from evm
//   - concrete execution error: various EVM errors which abort the execution, e.g.
//     ErrOutOfGas, ErrExecutionReverted
//
// However if any consensus issue encountered, return the error directly with
// nil evm execution result.
func (st *StateTransition) TransitionDb() (*ExecutionResult, error) {
	// First check this message satisfies all consensus rules before
	// applying the message. The rules include these clauses
	//
	// 1. the nonce of the message caller is correct
	// 2. caller has enough balance to cover transaction fee(gaslimit * gasprice)
	// 3. the amount of gas required is available in the block
	// 4. the purchased gas is enough to cover intrinsic usage
	// 5. there is no overflow when calculating intrinsic gas
	// 6. caller has enough balance to cover asset transfer for **topmost** call

	// 在应用消息之前，首先检查该消息是否满足所有共识规则。规则包括这些条款
	//
	// 1. 消息调用者的 nonce 正确
	// 2. 调用者有足够的余额来支付交易费用(gaslimit * gasprice)
	// 3. 所需的 gas 量在区块中可用
	// 4. 支付的 gas 足以覆盖固有成本
	// 5. 计算固有成本的 gas 时没有溢出
	// 6. 调用者有足够的余额来支付 **topmost** 调用的资产转移

	// Check clauses 1-3, buy gas if everything is correct
	// 检查第 1-3 条，如果一切正确，则购买 gas
	if err := st.preCheck(); err != nil {
		return nil, err
	}

	if st.evm.Config.Debug {
		st.evm.Config.Tracer.CaptureTxStart(st.initialGas)
		defer func() {
			st.evm.Config.Tracer.CaptureTxEnd(st.gasRemaining)
		}()
	}

	var (
		msg              = st.msg
		sender           = vm.AccountRef(msg.From) // 交易的发起者地址
		rules            = st.evm.ChainConfig().Rules(st.evm.Context.BlockNumber, st.evm.Context.Random != nil, st.evm.Context.Time)
		contractCreation = msg.To == nil // msg.To() == nil 代表创建合约
	)

	// Check clauses 4-5, subtract intrinsic gas if everything is correct
	// 检查第 4-5 条，如果一切正确，则减去固有成本的 gas
	// 计算固有成本的 gas
	gas, err := IntrinsicGas(msg.Data, msg.AccessList, contractCreation, rules.IsHomestead, rules.IsIstanbul, rules.IsShanghai)
	if err != nil {
		return nil, err
	}
	if st.gasRemaining < gas {
		return nil, fmt.Errorf("%w: have %d, want %d", ErrIntrinsicGas, st.gasRemaining, gas)
	}
	// st.gasRemaining 减去固有成本的 gas
	st.gasRemaining -= gas

	// Check clause 6
	if msg.Value.Sign() > 0 && !st.evm.Context.CanTransfer(st.state, msg.From, msg.Value) {
		return nil, fmt.Errorf("%w: address %v", ErrInsufficientFundsForTransfer, msg.From.Hex())
	}

	// Check whether the init code size has been exceeded.
	if rules.IsShanghai && contractCreation && len(msg.Data) > params.MaxInitCodeSize {
		return nil, fmt.Errorf("%w: code size %v limit %v", ErrMaxInitCodeSizeExceeded, len(msg.Data), params.MaxInitCodeSize)
	}

	// Execute the preparatory steps for state transition which includes:
	// - prepare accessList(post-berlin)
	// - reset transient storage(eip 1153)
	st.state.Prepare(rules, msg.From, st.evm.Context.Coinbase, msg.To, vm.ActivePrecompiles(rules), msg.AccessList)

	var (
		ret   []byte
		vmerr error // vm errors do not effect consensus and are therefore not assigned to err
	)
	// 判断合约类型, 然后根据类型调用 EVM 执行
	if contractCreation {
		// 进行创建合约操作 st.data = message.data() = tx.txdata.payload
		// ret 合约主体, _, st.gas 消耗的gas, vmerr vm错误
		ret, _, st.gasRemaining, vmerr = st.evm.Create(sender, msg.Data, st.gasRemaining, msg.Value)
	} else {
		// Increment the nonce for the next transaction
		// 合约调用
		st.state.SetNonce(msg.From, st.state.GetNonce(sender.Address())+1)
		ret, st.gasRemaining, vmerr = st.evm.Call(sender, st.to(), msg.Data, st.gasRemaining, msg.Value)
	}

	// TODOMARK 为什么要退？要这样退？ 退税是为了奖励大家运行一些能够减轻区块链负担的指令，比如清空账户的storage或者是运行suicide命令来清空账号。
	// 退还未消耗的 gas
	if !rules.IsLondon {
		// Before EIP-3529: refunds were capped to gasUsed / 2
		// EIP-3529 之前退款上限为已用 gas 的一半
		st.refundGas(params.RefundQuotient)
	} else {
		// After EIP-3529: refunds are capped to gasUsed / 5
		// EIP-3529 之后退款上限为已用 gas 的五分之一
		st.refundGas(params.RefundQuotientEIP3529)
	}
	effectiveTip := msg.GasPrice
	if rules.IsLondon {
		effectiveTip = cmath.BigMin(msg.GasTipCap, new(big.Int).Sub(msg.GasFeeCap, st.evm.Context.BaseFee))
	}

	if st.evm.Config.NoBaseFee && msg.GasFeeCap.Sign() == 0 && msg.GasTipCap.Sign() == 0 {
		// Skip fee payment when NoBaseFee is set and the fee fields
		// are 0. This avoids a negative effectiveTip being applied to
		// the coinbase when simulating calls.
		// 设置 NoBaseFee 且费用字段为 0 时跳过费用支付。这避免了在模拟调用时将负有效提示应用于 coinbase。
	} else {
		fee := new(big.Int).SetUint64(st.gasUsed())
		fee.Mul(fee, effectiveTip)
		// 向打包该交易的矿工账户地址添加手续费
		st.state.AddBalance(st.evm.Context.Coinbase, fee)
	}

	return &ExecutionResult{
		UsedGas:    st.gasUsed(),
		Err:        vmerr,
		ReturnData: ret,
	}, nil
}

func (st *StateTransition) refundGas(refundQuotient uint64) {
	// Apply refund counter, capped to a refund quotient
	refund := st.gasUsed() / refundQuotient
	if refund > st.state.GetRefund() {
		refund = st.state.GetRefund()
	}
	st.gasRemaining += refund

	// Return ETH for remaining gas, exchanged at the original rate.
	remaining := new(big.Int).Mul(new(big.Int).SetUint64(st.gasRemaining), st.msg.GasPrice)
	st.state.AddBalance(st.msg.From, remaining)

	// Also return remaining gas to the block gas counter so it is
	// available for the next transaction.
	// 将该交易执行完成后剩余的 gas 退回到 gaspool
	st.gp.AddGas(st.gasRemaining)
}

// gasUsed returns the amount of gas used up by the state transition.
func (st *StateTransition) gasUsed() uint64 {
	return st.initialGas - st.gasRemaining
}
