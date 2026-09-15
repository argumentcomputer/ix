import Compilatrix.Aiur.OracleEval.State

/-! One pinned bytecode operation. Replies to constrained calls, memory,
and gadgets produce exact logical demands; advice produces observations.
No callee body is recursively evaluated inside a row. -/

namespace Compilatrix.Aiur.OracleEval

open _root_.Aiur (G)
open _root_.Aiur.Bytecode (Op Toplevel)

def evalOp (toplevel : Toplevel) (maxValues : Nat) (op : Op) (state : State) :
    Except Error State :=
  match op with
  | .const value => appendValues maxValues state [value]
  | .add a b => fieldBinary maxValues state a b (· + ·)
  | .sub a b => fieldBinary maxValues state a b (· - ·)
  | .mul a b => fieldBinary maxValues state a b (· * ·)
  | .eqZero index => do
      let value ← read state index
      appendValues maxValues state [G.eqZero value]
  | .call function indices outputSize unconstrained => do
      let inputs ← readMany maxValues state indices
      let callee ← match toplevel.functions[function]? with
        | some callee => .ok callee
        | none => .error (.invalidFunction function)
      if inputs.length != callee.layout.inputSize then
        .error (.inputArity function callee.layout.inputSize inputs.length)
      else if unconstrained then
        hint maxValues state (.call function inputs outputSize) outputSize
      else
        let (outputs, state) ← takeReply state outputSize
        let state ← demand state (.function function inputs outputs)
        appendValues maxValues state outputs
  | .store indices => do
      let values ← readMany maxValues state indices
      let (answer, state) ← takeReply state 1
      match answer with
      | [pointer] => do
          let state ← demand state (.memory values.length pointer values)
          appendValues maxValues state [pointer]
      | _ => .error (.replyArity 1 answer.length)
  | .load size index => do
      let pointer ← read state index
      let (values, state) ← takeReply state size
      let state ← demand state (.memory size pointer values)
      appendValues maxValues state values
  | .assertEq left right _ => do
      let left ← readMany maxValues state left
      let right ← readMany maxValues state right
      if left = right then .ok state else .error .assertionFailed
  | .ioGetInfo channel key => do
      let channel ← read state channel
      let key ← readMany maxValues state key
      hint maxValues state (.ioGetInfo channel key) 2
  | .ioRead channel index size => do
      let channel ← read state channel
      let index ← read state index
      hint maxValues state (.ioRead channel index size) size
  | .ioSetInfo .. | .ioWrite .. | .debug .. =>
      -- These have no constrained output/effect in the pinned builder.
      -- In particular, this is not a model of host IO-buffer mutation.
      .ok state
  | .u8BitDecomposition index => unaryGadget maxValues state .bitDecomposition index
  | .u8ShiftLeft index => unaryGadget maxValues state .shiftLeft index
  | .u8ShiftRight index => unaryGadget maxValues state .shiftRight index
  | .u8Xor a b => binaryGadget maxValues state .xor a b
  | .u8Add a b => binaryGadget maxValues state .add a b
  | .u8Mul a b => binaryGadget maxValues state .mul a b
  | .u8Sub a b => binaryGadget maxValues state .sub a b
  | .u8And a b => binaryGadget maxValues state .and a b
  | .u8Or a b => binaryGadget maxValues state .or a b
  | .u8LessThan a b => binaryGadget maxValues state .lessThan a b
  | .u32LessThan a b => binaryGadget maxValues state .u32LessThan a b
  | .u8XorSplit7 a b => binaryGadget maxValues state .xorSplit7 a b
  | .u8XorSplit4 a b => binaryGadget maxValues state .xorSplit4 a b
  | .u8RangeCheck a b => binaryGadget maxValues state .rangeCheck a b
  | .unconstrainedBigUintDivMod a b => do
      let a ← read state a
      let b ← read state b
      hint maxValues state (.bigUintDivMod a b) 2
  | .unconstrainedGToBytes index => do
      let value ← read state index
      hint maxValues state (.gToBytes value) 8
  | .unconstrainedGInverse index => do
      let value ← read state index
      hint maxValues state (.gInverse value) 1
  | .unconstrainedU32Add left right => do
      let left ← readWord maxValues state left
      let right ← readWord maxValues state right
      u32Hint maxValues state (.u32Add left right) (packBytes left + packBytes right)
  | .unconstrainedU32Add3 first second third => do
      let first ← readWord maxValues state first
      let second ← readWord maxValues state second
      let third ← readWord maxValues state third
      u32Hint maxValues state (.u32Add3 first second third)
        (packBytes first + packBytes second + packBytes third)
  | .u32ToField indices => do
      let bytes ← readWord maxValues state indices
      appendValues maxValues state [packBytes bytes]

end Compilatrix.Aiur.OracleEval
