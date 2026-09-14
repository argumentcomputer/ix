import Compilatrix.Ixby.Runtime.NatArithmeticCertificate
import Compilatrix.Ixby.Runtime.NaturalCall

/-! Equality follows the exact emitted dispatch: two native field operands
use field equality, while every mixed pair compares exact Nat observations. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem equal_segment {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {fn : Function}
    (checked : Checked program id fn) (locals : Array Value) (start first second last : BlockId)
    (firstBlock : fn.blocks[start]? = some ⟨locals.size, .letOp (.call links.natural [.local 0]) first⟩)
    (secondBlock : fn.blocks[first]? = some ⟨locals.size + 1, .letOp (.call links.natural [.local 1]) second⟩)
    (thirdBlock : fn.blocks[second]? = some ⟨locals.size + 2,
      .letOp (.primitive .natEq [.local locals.size, .local (locals.size + 1)]) last⟩)
    (lastBlock : fn.blocks[last]? = some ⟨locals.size + 3, .ret (.local (locals.size + 2))⟩)
    (limits : Limits) (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (leftRead : locals[0]? = some left) (rightRead : locals[1]? = some right)
    (inputSlots : 2 ≤ locals.size) (fits : locals.size + 3 ≤ limits.locals)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id start locals continuation)
      (returned (.scalar (.bool (a == b))) continuation) := by
  have localRoom : ∀ k, k ≤ locals.size + 3 → ¬limits.locals < k := by omega
  have observedLeft := conversions.call_natural limits room capacity bytesCapacity
    { function := id, block := start, locals } (.local 0) first a left leftRep
    { function := id, block := first, locals := locals ++ #[.scalar (.nat a)] }
    (by simp [Frame.check, checked.code, firstBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by simp [Frame.read, leftRead])
    (by simp [Frame.transfer, Frame.check, checked.code, secondBlock, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have observedRight := conversions.call_natural limits room capacity bytesCapacity
    { function := id, block := first, locals := locals ++ #[.scalar (.nat a)] } (.local 1) second b right rightRep
    { function := id, block := second, locals := (locals ++ #[.scalar (.nat a)]) ++ #[.scalar (.nat b)] }
    (by simp [Frame.check, checked.code, secondBlock, localRoom, bind, Except.bind, pure, Except.pure])
    (by simp only [Frame.read, Array.append_singleton, Array.getElem?_push,
      show 1 ≠ locals.size by omega, if_false, rightRead])
    (by simp [Frame.transfer, Frame.check, checked.code, thirdBlock, localRoom, Nat.add_assoc,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have result := eval_natEq limits a b leftValid rightValid
  apply (observedLeft.trans observedRight).trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, thirdBlock, lastBlock,
      returned, Frame.read, Frame.readOperands, Frame.transfer, evalOp, result,
      Array.getElem_push, localRoom, Nat.add_assoc, bind, Except.bind, pure, Except.pure]
  rfl

namespace Certificate

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

/-- The native field/field branch requires only five local slots. It performs
no calls, Nat validation, or byte conversion, at any caller depth. -/
theorem eq_field_returns (room : 5 ≤ limits.locals) (a b : Goldilocks)
    (continuation : Array Continuation) :
    Reaches limits program (frameState links.equal 0
      #[.ctor links.conversions.layout.field #[.scalar (.field a)],
        .ctor links.conversions.layout.field #[.scalar (.field b)]] continuation)
      (returned (.scalar (.bool (a.val == b.val))) continuation) := by
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  have result := eval_fieldEq limits a b
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.equal.code, NatArithmetic.equal,
      certificate.conversions.cached, certificate.conversions.raw, certificate.conversions.field,
      certificate.conversions.cachedField, certificate.conversions.rawField,
      frameState, returned, Frame.read, Frame.readOperands, Frame.transfer, selectCase,
      evalOp, result, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem eq_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.equal 0 #[left, right] continuation)
      (returned (.scalar (.bool (a == b))) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  cases leftRep with
  | cached a =>
    let left : Value := .ctor links.conversions.layout.cached
      #[.scalar (.nat a), .scalar (.word32 a.toUInt32)]
    let locals := #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32)]
    have before : Reaches limits program (frameState links.equal 0 #[left, right] continuation)
        (frameState links.equal 1 locals continuation) := by
      apply Reaches.of_step
      simp [step, stepEval, Frame.check, certificate.equal.code, NatArithmetic.equal,
        certificate.conversions.cached, frameState, left, locals, Frame.read, Frame.transfer,
        selectCase, localRoom, bind, Except.bind, pure, Except.pure]
    exact before.trans (equal_segment certificate.conversions certificate.equal locals 1 4 5 6
      rfl rfl rfl rfl limits room capacity bytesCapacity a b left right (.cached a) rightRep
      leftValid rightValid rfl rfl (by simp [locals]) (by simp [locals]; omega) continuation stack)
  | raw a =>
    let left : Value := .ctor links.conversions.layout.raw #[.scalar (.nat a)]
    let locals := #[left, right, .scalar (.nat a)]
    have before : Reaches limits program (frameState links.equal 0 #[left, right] continuation)
        (frameState links.equal 2 locals continuation) := by
      apply Reaches.of_step
      simp [step, stepEval, Frame.check, certificate.equal.code, NatArithmetic.equal,
        certificate.conversions.cached, certificate.conversions.raw, certificate.conversions.cachedRaw,
        frameState, left, locals, Frame.read, Frame.transfer, selectCase,
        localRoom, bind, Except.bind, pure, Except.pure]
    exact before.trans (equal_segment certificate.conversions certificate.equal locals 2 7 8 9
      rfl rfl rfl rfl limits room capacity bytesCapacity a b left right (.raw a) rightRep
      leftValid rightValid rfl rfl (by simp [locals]) (by simp [locals]; omega) continuation stack)
  | field a =>
    cases rightRep with
    | cached b =>
      let left : Value := .ctor links.conversions.layout.field #[.scalar (.field a)]
      let right : Value := .ctor links.conversions.layout.cached
        #[.scalar (.nat b), .scalar (.word32 b.toUInt32)]
      let locals := #[left, right, .scalar (.field a), .scalar (.nat b), .scalar (.word32 b.toUInt32)]
      have before : Reaches limits program (frameState links.equal 0 #[left, right] continuation)
          (frameState links.equal 10 locals continuation) := by
        apply reaches_of_chunk (fuel := 2) (count := 0)
        iterate 2
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.equal.code, NatArithmetic.equal,
            certificate.conversions.cached, certificate.conversions.raw, certificate.conversions.field,
            certificate.conversions.cachedField, certificate.conversions.rawField,
            frameState, left, right, locals, Frame.read, Frame.transfer, selectCase,
            localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      exact before.trans (equal_segment certificate.conversions certificate.equal locals 10 13 14 15
        rfl rfl rfl rfl limits room capacity bytesCapacity a.val b left right (.field a) (.cached b)
        leftValid rightValid rfl rfl (by simp [locals]) (by simp [locals]; omega) continuation stack)
    | raw b =>
      let left : Value := .ctor links.conversions.layout.field #[.scalar (.field a)]
      let right : Value := .ctor links.conversions.layout.raw #[.scalar (.nat b)]
      let locals := #[left, right, .scalar (.field a), .scalar (.nat b)]
      have before : Reaches limits program (frameState links.equal 0 #[left, right] continuation)
          (frameState links.equal 11 locals continuation) := by
        apply reaches_of_chunk (fuel := 2) (count := 0)
        iterate 2
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.equal.code, NatArithmetic.equal,
            certificate.conversions.cached, certificate.conversions.raw, certificate.conversions.field,
            certificate.conversions.cachedRaw, certificate.conversions.cachedField, certificate.conversions.rawField,
            frameState, left, right, locals, Frame.read, Frame.transfer, selectCase,
            localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      exact before.trans (equal_segment certificate.conversions certificate.equal locals 11 16 17 18
        rfl rfl rfl rfl limits room capacity bytesCapacity a.val b left right (.field a) (.raw b)
        leftValid rightValid rfl rfl (by simp [locals]) (by simp [locals]; omega) continuation stack)
    | field b => exact certificate.eq_field_returns limits (by omega) a b continuation

end Certificate
end Compilatrix.Ixby.Runtime.NatArithmetic
