import Compilatrix.Ixby.Runtime.NumberConversion

/-! Composing an ordinary call to the generated exact-Nat observer. Both the
call and the return execute the reference scheduler's actual frame checks. -/

namespace Compilatrix.Ixby.Runtime.Conversion.Certificate

open Ix.Ixby Execution Representation

theorem call_natural {program : Program} {links : Links} (certificate : Certificate program links)
    (limits : Limits) (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (frame : Frame) (operand : Operand) (target : BlockId) (n : Nat) (value : Value)
    (represented : Number links.layout n value) (resumed : Frame)
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.call links.natural [operand]) target⟩)
    (read : frame.read operand = .ok value)
    (transfer : frame.transfer limits program target #[.scalar (.nat n)] = .ok resumed)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program { control := .eval frame, continuation }
      { control := .eval resumed, continuation } := by
  let saved : Frame := { frame with block := target }
  have entered : enter limits program links.natural #[value] =
      .ok { function := links.natural, block := 0, locals := #[value] } := by
    simp [enter, Frame.check, certificate.natural.code, Conversion.natural,
      show ¬limits.locals < 1 by omega, bind, Except.bind, pure, Except.pure]
  have beforeCall : Reaches limits program { control := .eval frame, continuation }
      (frameState links.natural 0 #[value] (continuation.push (.resume saved))) := by
    apply Reaches.of_step
    simp [step, stepEval, code, evalOp, Frame.readOperands, read, State.push,
      entered, frameState, saved,
      show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
  have callee := certificate.natural_returns limits room capacity bytesCapacity n value represented
    (continuation.push (.resume saved)) (by simp; omega)
  have afterCall := Execution.resume (.scalar (.nat n)) continuation saved resumed
    (by simpa [saved, Frame.transfer] using transfer)
  exact beforeCall.trans (callee.trans afterCall)

/-- The shared entry of binary Nat helpers observes both inputs in order,
restoring the arithmetic caller after each complete conversion. -/
theorem read_naturals {program : Program} {links : Links} (certificate : Certificate program links)
    {id : FunctionId} {fn : Function} (checked : ScalarFunction.Checked program id fn)
    (firstBlock : fn.blocks[0]? = some ⟨2, .letOp (.call links.natural [.local 0]) 1⟩)
    (secondBlock : fn.blocks[1]? = some ⟨3, .letOp (.call links.natural [.local 1]) 2⟩)
    (nextInstruction : Instr) (nextBlock : fn.blocks[2]? = some ⟨4, nextInstruction⟩)
    (limits : Limits) (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (frameState id 2 #[left, right, .scalar (.nat a), .scalar (.nat b)] continuation) := by
  have localRoom : ∀ n, n ≤ 10 → ¬limits.locals < n := by omega
  have first := certificate.call_natural limits room capacity bytesCapacity
    { function := id, block := 0, locals := #[left, right] } (.local 0) 1 a left leftRep
    { function := id, block := 1, locals := #[left, right, .scalar (.nat a)] }
    (by simp [Frame.check, checked.code, firstBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, checked.code, secondBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have second := certificate.call_natural limits room capacity bytesCapacity
    { function := id, block := 1, locals := #[left, right, .scalar (.nat a)] } (.local 1) 2 b right rightRep
    { function := id, block := 2, locals := #[left, right, .scalar (.nat a), .scalar (.nat b)] }
    (by simp [Frame.check, checked.code, secondBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, checked.code, nextBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  exact first.trans second

end Compilatrix.Ixby.Runtime.Conversion.Certificate
