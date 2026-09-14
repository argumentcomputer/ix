import Compilatrix.Ixby.Runtime.NaturalCall

/-! Calls to the generated low-word observer execute the ordinary scheduler.
The shared entries retain both exact naturals and their consistent caches. -/

namespace Compilatrix.Ixby.Runtime.Conversion.Certificate

open Ix.Ixby Execution Representation

theorem call_lowWord {program : Program} {links : Links} (certificate : Certificate program links)
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (frame : Frame) (operand : Operand) (target : BlockId) (n : Nat) (value : Value)
    (represented : Number links.layout n value) (valid : (Scalar.nat n).validate limits = .ok ())
    (resumed : Frame)
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.call links.lowWord [operand]) target⟩)
    (read : frame.read operand = .ok value)
    (transfer : frame.transfer limits program target #[.scalar (.word32 n.toUInt32)] = .ok resumed)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program { control := .eval frame, continuation }
      { control := .eval resumed, continuation } := by
  let saved : Frame := { frame with block := target }
  have entered : enter limits program links.lowWord #[value] =
      .ok { function := links.lowWord, block := 0, locals := #[value] } := by
    simp [enter, Frame.check, certificate.lowWord.code, Conversion.lowWord,
      show ¬limits.locals < 1 by omega, bind, Except.bind, pure, Except.pure]
  have beforeCall : Reaches limits program { control := .eval frame, continuation }
      (frameState links.lowWord 0 #[value] (continuation.push (.resume saved))) := by
    apply Reaches.of_step
    simp [step, stepEval, code, evalOp, Frame.readOperands, read, State.push,
      entered, frameState, saved, show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
  have callee := certificate.lowWord_returns limits room capacity bytesCapacity n value represented valid
    (continuation.push (.resume saved)) (by simp; omega)
  have afterCall := Execution.resume (.scalar (.word32 n.toUInt32)) continuation saved resumed
    (by simpa [saved, Frame.transfer] using transfer)
  exact beforeCall.trans (callee.trans afterCall)

theorem read_parts {program : Program} {links : Links} (certificate : Certificate program links)
    {id : FunctionId} {fn : Function} (checked : ScalarFunction.Checked program id fn)
    (block : BlockId) (locals : Array Value) (operand : Operand)
    (firstBlock : fn.blocks[block]? =
      some ⟨locals.size, .letOp (.call links.natural [operand]) (block + 1)⟩)
    (secondBlock : fn.blocks[block + 1]? =
      some ⟨locals.size + 1, .letOp (.call links.lowWord [operand]) (block + 2)⟩)
    (nextInstruction : Instr)
    (nextBlock : fn.blocks[block + 2]? = some ⟨locals.size + 2, nextInstruction⟩)
    (limits : Limits) (room : 11 ≤ limits.locals) (callerRoom : locals.size + 2 ≤ limits.locals)
    (capacity : 64 ≤ limits.natBits) (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (n : Nat) (value : Value) (represented : Number links.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (read : Frame.read { function := id, block, locals } operand = .ok value)
    (readAgain : Frame.read { function := id, block := block + 1, locals := locals ++ #[.scalar (.nat n)] }
      operand = .ok value)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id block locals continuation)
      (frameState id (block + 2) (locals ++ #[.scalar (.nat n), .scalar (.word32 n.toUInt32)])
        continuation) := by
  have first := certificate.call_natural limits (by omega) capacity bytesCapacity
    { function := id, block, locals } operand (block + 1) n value represented
    { function := id, block := block + 1, locals := locals ++ #[.scalar (.nat n)] }
    (by simp [Frame.check, checked.code, firstBlock, show ¬limits.locals < locals.size by omega,
      bind, Except.bind, pure, Except.pure]) read
    (by simp [Frame.transfer, Frame.check, checked.code, secondBlock,
      show ¬limits.locals < locals.size + 1 by omega, bind, Except.bind, pure, Except.pure])
    continuation stack
  have second := certificate.call_lowWord limits room (by omega) bytesCapacity
    { function := id, block := block + 1, locals := locals ++ #[.scalar (.nat n)] }
    operand (block + 2) n value represented valid
    { function := id, block := block + 2,
      locals := locals ++ #[.scalar (.nat n), .scalar (.word32 n.toUInt32)] }
    (by simp [Frame.check, checked.code, secondBlock, show ¬limits.locals < locals.size + 1 by omega,
      bind, Except.bind, pure, Except.pure]) readAgain
    (by simp [Frame.transfer, Frame.check, checked.code, nextBlock,
      show ¬limits.locals < locals.size + 2 by omega, bind, Except.bind, pure, Except.pure]
        simp only [Array.push_eq_append, Array.append_assoc]
        rfl)
    continuation (by omega)
  exact first.trans second

theorem read_lowWords {program : Program} {links : Links} (certificate : Certificate program links)
    {id : FunctionId} {fn : Function} (checked : ScalarFunction.Checked program id fn)
    (firstBlock : fn.blocks[0]? = some ⟨2, .letOp (.call links.lowWord [.local 0]) 1⟩)
    (secondBlock : fn.blocks[1]? = some ⟨3, .letOp (.call links.lowWord [.local 1]) 2⟩)
    (nextInstruction : Instr) (nextBlock : fn.blocks[2]? = some ⟨4, nextInstruction⟩)
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (frameState id 2 #[left, right, .scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)]
        continuation) := by
  have localRoom : ∀ n, n ≤ 11 → ¬limits.locals < n := by omega
  have first := certificate.call_lowWord limits room capacity bytesCapacity
    { function := id, block := 0, locals := #[left, right] } (.local 0) 1 a left leftRep leftValid
    { function := id, block := 1, locals := #[left, right, .scalar (.word32 a.toUInt32)] }
    (by simp [Frame.check, checked.code, firstBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, checked.code, secondBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have second := certificate.call_lowWord limits room capacity bytesCapacity
    { function := id, block := 1, locals := #[left, right, .scalar (.word32 a.toUInt32)] }
    (.local 1) 2 b right rightRep rightValid
    { function := id, block := 2,
      locals := #[left, right, .scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] }
    (by simp [Frame.check, checked.code, secondBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, checked.code, nextBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  exact first.trans second

/-- The four observer calls shared by modular arithmetic and subtraction. -/
theorem read_binary_parts {program : Program} {links : Links} (certificate : Certificate program links)
    {id : FunctionId} {fn : Function} (checked : ScalarFunction.Checked program id fn)
    (firstBlock : fn.blocks[0]? = some ⟨2, .letOp (.call links.natural [.local 0]) 1⟩)
    (secondBlock : fn.blocks[1]? = some ⟨3, .letOp (.call links.lowWord [.local 0]) 2⟩)
    (thirdBlock : fn.blocks[2]? = some ⟨4, .letOp (.call links.natural [.local 1]) 3⟩)
    (fourthBlock : fn.blocks[3]? = some ⟨5, .letOp (.call links.lowWord [.local 1]) 4⟩)
    (nextInstruction : Instr) (nextBlock : fn.blocks[4]? = some ⟨6, nextInstruction⟩)
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (frameState id 4 #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
        .scalar (.nat b), .scalar (.word32 b.toUInt32)] continuation) := by
  have first := certificate.read_parts checked 0 #[left, right] (.local 0)
    firstBlock secondBlock _ thirdBlock limits room (by simp; omega) capacity bytesCapacity
    a left leftRep leftValid rfl rfl continuation stack
  have second := certificate.read_parts checked 2
    #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32)] (.local 1)
    thirdBlock fourthBlock _ nextBlock limits room (by simp; omega) capacity bytesCapacity
    b right rightRep rightValid rfl rfl continuation stack
  exact first.trans second

end Compilatrix.Ixby.Runtime.Conversion.Certificate
