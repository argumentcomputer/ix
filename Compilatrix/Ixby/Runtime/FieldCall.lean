import Compilatrix.Ixby.Runtime.NumberConversion

/-! Ordinary calls to the generated modular field observer, through the
complete conversion and the reference scheduler's checked caller restoration. -/

namespace Compilatrix.Ixby.Runtime.Conversion.Certificate

open Ix.Ixby Execution Representation

theorem call_asField {program : Program} {links : Links} (certificate : Certificate program links)
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (frame : Frame) (operand : Operand) (target : BlockId) (n : Nat) (value : Value)
    (represented : Number links.layout n value) (valid : (Scalar.nat n).validate limits = .ok ())
    (resumed : Frame)
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.call links.asField [operand]) target⟩)
    (read : frame.read operand = .ok value)
    (transfer : frame.transfer limits program target #[.scalar (.field (Goldilocks.reduce n))] = .ok resumed)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program { control := .eval frame, continuation }
      { control := .eval resumed, continuation } := by
  let saved : Frame := { frame with block := target }
  have entered : enter limits program links.asField #[value] =
      .ok { function := links.asField, block := 0, locals := #[value] } := by
    simp [enter, Frame.check, certificate.asField.code, Conversion.asField,
      show ¬limits.locals < 1 by omega, bind, Except.bind, pure, Except.pure]
  have beforeCall : Reaches limits program { control := .eval frame, continuation }
      (frameState links.asField 0 #[value] (continuation.push (.resume saved))) := by
    apply Reaches.of_step
    simp [step, stepEval, code, evalOp, Frame.readOperands, read, State.push,
      entered, frameState, saved, show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
  have callee := certificate.asField_returns limits room capacity n value represented valid
    (continuation.push (.resume saved)) (by simp; omega)
  have afterCall := Execution.resume (.scalar (.field (Goldilocks.reduce n))) continuation saved resumed
    (by simpa [saved, Frame.transfer] using transfer)
  exact beforeCall.trans (callee.trans afterCall)

/-- Binary field helpers convert both operands in source order and restore
their saved caller after each complete conversion. -/
theorem read_fields {program : Program} {links : Links} (certificate : Certificate program links)
    {id : FunctionId} {fn : Function} (checked : ScalarFunction.Checked program id fn)
    (firstBlock : fn.blocks[0]? = some ⟨2, .letOp (.call links.asField [.local 0]) 1⟩)
    (secondBlock : fn.blocks[1]? = some ⟨3, .letOp (.call links.asField [.local 1]) 2⟩)
    (nextInstruction : Instr) (nextBlock : fn.blocks[2]? = some ⟨4, nextInstruction⟩)
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (frameState id 2 #[left, right, .scalar (.field (Goldilocks.reduce a)),
        .scalar (.field (Goldilocks.reduce b))] continuation) := by
  have localRoom : ∀ n, n ≤ 11 → ¬limits.locals < n := by omega
  have first := certificate.call_asField limits room capacity
    { function := id, block := 0, locals := #[left, right] } (.local 0) 1 a left leftRep leftValid
    { function := id, block := 1, locals := #[left, right, .scalar (.field (Goldilocks.reduce a))] }
    (by simp [Frame.check, checked.code, firstBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, checked.code, secondBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have second := certificate.call_asField limits room capacity
    { function := id, block := 1, locals := #[left, right, .scalar (.field (Goldilocks.reduce a))] }
    (.local 1) 2 b right rightRep rightValid
    { function := id, block := 2, locals := #[left, right, .scalar (.field (Goldilocks.reduce a)),
      .scalar (.field (Goldilocks.reduce b))] }
    (by simp [Frame.check, checked.code, secondBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, checked.code, nextBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  exact first.trans second

end Compilatrix.Ixby.Runtime.Conversion.Certificate
