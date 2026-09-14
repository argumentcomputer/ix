import Compilatrix.Ixby.Runtime.ArrayTreeBasic

/-! Shared public-array bounds checks execute both real calls and restore
the complete caller locals before branching. Numeric layouts may be mixed. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem check_index {id : FunctionId} {fn : Function} (checked : Checked program id fn)
    (locals : Array Value) (arrayOperand indexOperand : Operand)
    (firstBlock : fn.blocks[0]? =
      some ⟨locals.size, .letOp (.call links.size [.erased, arrayOperand]) 1⟩)
    (secondBlock : fn.blocks[1]? = some ⟨locals.size + 1,
      .letOp (.call links.arithmetic.less [indexOperand, .local locals.size]) 2⟩)
    (nextInstruction : Instr) (nextBlock : fn.blocks[2]? = some ⟨locals.size + 2, nextInstruction⟩)
    (room : 10 ≤ limits.locals) (callerRoom : locals.size + 2 ≤ limits.locals)
    (capacity : 64 ≤ limits.natBits) (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (height : Nat) (tree : Tree height) (size : Value) (n index : Nat) (indexValue : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (sizeValid : (Scalar.nat n).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ())
    (readArray : Frame.read { function := id, block := 0, locals } arrayOperand =
      .ok (arrayValue links.layout height tree size))
    (readIndex : Frame.read { function := id, block := 1, locals := locals ++ #[size] }
      indexOperand = .ok indexValue)
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 locals continuation)
      (frameState id 2 (locals ++ #[size, .scalar (.bool (decide (index < n)))]) continuation) := by
  have sizePath := certificate.call_size limits (by omega)
    { function := id, block := 0, locals } arrayOperand 1 height tree size
    { function := id, block := 1, locals := locals ++ #[size] }
    (by simp [Frame.check, checked.code, firstBlock, show ¬limits.locals < locals.size by omega,
      bind, Except.bind, pure, Except.pure]) readArray
    (by simp [Frame.transfer, Frame.check, checked.code, secondBlock,
      show ¬limits.locals < locals.size + 1 by omega, bind, Except.bind, pure, Except.pure])
    continuation (by omega)
  have compared := certificate.arithmetic.lt_returns limits room capacity bytesCapacity index n
    indexValue size indexRep sizeRep indexValid sizeValid
    (continuation.push (.resume { function := id, block := 2, locals := locals ++ #[size] }))
    (by simp; omega)
  have readSize : Frame.read { function := id, block := 1, locals := locals ++ #[size] }
      (.local locals.size) = .ok size := by simp [Frame.read]
  have comparisonPath := ArrayTrees.call_returns limits program
    { function := id, block := 1, locals := locals ++ #[size] } links.arithmetic.less
    [indexOperand, .local locals.size] #[indexValue, size] 2 (.scalar (.bool (decide (index < n))))
    { function := id, block := 2,
      locals := locals ++ #[size, .scalar (.bool (decide (index < n)))] }
    continuation (by omega)
    (by simp [Frame.check, checked.code, secondBlock,
      show ¬limits.locals < locals.size + 1 by omega, bind, Except.bind, pure, Except.pure])
    (by simp only [Frame.readOperands, readIndex, readSize, bind, Except.bind, pure, Except.pure])
    (by simp [enter, Frame.check, certificate.arithmetic.less.code, NatArithmetic.less,
      show ¬limits.locals < 2 by omega, bind, Except.bind, pure, Except.pure])
    (by simp [Frame.transfer, Frame.check, checked.code, nextBlock,
      show ¬limits.locals < locals.size + 2 by omega, bind, Except.bind, pure, Except.pure]
        simp only [Array.push_eq_append, Array.append_assoc]
        rfl) compared
  exact sizePath.trans comparisonPath

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
