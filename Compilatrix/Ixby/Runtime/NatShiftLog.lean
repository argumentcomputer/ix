import Compilatrix.Ixby.Runtime.NatLoopCertificate

/-! The emitted halving loops terminate, return the source Nat result, and
preserve arbitrary saved callers. No new continuation is needed by either
loop. The public wrappers compose the certified exact-Nat observations. -/

namespace Compilatrix.Ixby.Runtime.NatLoops.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : NatLoops.Links}
  (certificate : NatLoops.Certificate program links) (limits : Limits)

include certificate

theorem shiftRightLoop_returns (room : 6 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n shift : Nat) (nValid : (Scalar.nat n).validate limits = .ok ())
    (shiftValid : (Scalar.nat shift).validate limits = .ok ()) (continuation : Array Continuation) :
    ∃ value, Reaches limits program
      (frameState links.shiftRightLoop 0 #[.scalar (.nat n), .scalar (.nat shift)] continuation)
      (returned value continuation) ∧ Number links.arithmetic.conversions.layout (n >>> shift) value := by
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  induction shift generalizing n with
  | zero =>
    have beforeLoop : Reaches limits program
        (frameState links.shiftRightLoop 0 #[.scalar (.nat n), .scalar (.nat 0)] continuation)
        (frameState links.arithmetic.conversions.fromRaw 0 #[.scalar (.nat n)] continuation) := by
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.shiftRightLoop.code, NatLoops.shiftRightLoop,
          certificate.arithmetic.conversions.fromRaw.code, fromRaw, frameState, Frame.read,
          Frame.readOperands, Frame.transfer, enter, evalOp, Primitive.eval, Primitive.arity,
          N, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    exact ⟨_, beforeLoop.trans (certificate.arithmetic.conversions.fromRaw_returns limits (by omega)
      n continuation), by simpa using Number.raw (layout := links.arithmetic.conversions.layout) n⟩
  | succ shift ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨_, ?_, by simpa using Number.cached (layout := links.arithmetic.conversions.layout) 0⟩
      apply reaches_of_chunk (fuel := 6) (count := 0)
      iterate 6
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.shiftRightLoop.code, NatLoops.shiftRightLoop,
          certificate.arithmetic.conversions.cached, frameState, returned, Frame.read,
          Frame.readOperands, Frame.transfer, evalOp, Primitive.eval, Primitive.arity,
          N, W, shiftValid, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    · have nextN := validate_nat_mono (Nat.div_le_self n 2) nValid
      have nextShift := validate_nat_mono (show shift ≤ shift + 1 by omega) shiftValid
      have beforeLoop : Reaches limits program
          (frameState links.shiftRightLoop 0 #[.scalar (.nat n), .scalar (.nat (shift + 1))] continuation)
          (frameState links.shiftRightLoop 0 #[.scalar (.nat (n / 2)), .scalar (.nat shift)] continuation) := by
        apply reaches_of_chunk (fuel := 7) (count := 0)
        iterate 7
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.shiftRightLoop.code, NatLoops.shiftRightLoop,
            frameState, Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp,
            Primitive.eval, Primitive.arity, N, nValid, shiftValid, nextN, nextShift, zero,
            smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      obtain ⟨value, path, represented⟩ := ih (n / 2) nextN nextShift
      exact ⟨value, beforeLoop.trans path, by simpa only [Nat.shiftRight_succ_inside] using represented⟩

theorem log2Loop_returns (room : 5 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n accumulator : Nat) (nValid : (Scalar.nat n).validate limits = .ok ())
    (resultValid : (Scalar.nat (accumulator + n.log2)).validate limits = .ok ())
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState links.log2Loop 0 #[.scalar (.nat n), .scalar (.nat accumulator)] continuation)
      (returned (.ctor links.arithmetic.conversions.layout.raw
        #[.scalar (.nat (accumulator + n.log2))]) continuation) := by
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  induction n using Nat.strongRecOn generalizing accumulator with
  | ind n ih =>
    by_cases done : n < 2
    · have result : n.log2 = 0 := by rw [Nat.log2_def]; simp [show ¬2 ≤ n by omega]
      have beforeLoop : Reaches limits program
          (frameState links.log2Loop 0 #[.scalar (.nat n), .scalar (.nat accumulator)] continuation)
          (frameState links.arithmetic.conversions.fromRaw 0 #[.scalar (.nat accumulator)] continuation) := by
        apply reaches_of_chunk (fuel := 3) (count := 0)
        iterate 3
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.log2Loop.code, NatLoops.log2Loop,
            certificate.arithmetic.conversions.fromRaw.code, fromRaw, frameState, Frame.read,
            Frame.readOperands, Frame.transfer, enter, evalOp, Primitive.eval, Primitive.arity,
            N, nValid, done, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      simpa only [result, Nat.add_zero] using beforeLoop.trans
        (certificate.arithmetic.conversions.fromRaw_returns limits (by omega) accumulator continuation)
    · have recursiveLaw : n.log2 = (n / 2).log2 + 1 := by
        conv => lhs; rw [Nat.log2_def]
        simp [show 2 ≤ n by omega]
      have accValid := validate_nat_mono (Nat.le_add_right accumulator n.log2) resultValid
      have nextN := validate_nat_mono (Nat.div_le_self n 2) nValid
      have nextAcc := validate_nat_mono
        (show accumulator + 1 ≤ accumulator + n.log2 by rw [recursiveLaw]; omega) resultValid
      have invariant : accumulator + 1 + (n / 2).log2 = accumulator + n.log2 := by
        rw [recursiveLaw]; omega
      have beforeLoop : Reaches limits program
          (frameState links.log2Loop 0 #[.scalar (.nat n), .scalar (.nat accumulator)] continuation)
          (frameState links.log2Loop 0 #[.scalar (.nat (n / 2)), .scalar (.nat (accumulator + 1))]
            continuation) := by
        apply reaches_of_chunk (fuel := 5) (count := 0)
        iterate 5
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.log2Loop.code, NatLoops.log2Loop,
            frameState, Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp,
            Primitive.eval, Primitive.arity, N, nValid, accValid, nextN, nextAcc, done,
            smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      have recursive := ih (n / 2) (Nat.div_lt_self (by omega) (by decide)) (accumulator + 1)
        nextN (by simpa only [invariant] using resultValid)
      simpa only [invariant] using beforeLoop.trans recursive

theorem shiftRight_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n shift : Nat) (left right : Value)
    (leftRep : Number links.arithmetic.conversions.layout n left)
    (rightRep : Number links.arithmetic.conversions.layout shift right)
    (nValid : (Scalar.nat n).validate limits = .ok ())
    (shiftValid : (Scalar.nat shift).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    ∃ value, Reaches limits program (frameState links.shiftRight 0 #[left, right] continuation)
      (returned value continuation) ∧ Number links.arithmetic.conversions.layout (n >>> shift) value := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have observed := certificate.arithmetic.conversions.read_naturals certificate.shiftRight
    rfl rfl _ rfl limits room capacity bytesCapacity n shift left right leftRep rightRep continuation stack
  have entered : Reaches limits program
      (frameState links.shiftRight 2 #[left, right, .scalar (.nat n), .scalar (.nat shift)] continuation)
      (frameState links.shiftRightLoop 0 #[.scalar (.nat n), .scalar (.nat shift)] continuation) := by
    apply Reaches.of_step
    simp [step, stepEval, Frame.check, certificate.shiftRight.code, NatLoops.shiftRight,
      certificate.shiftRightLoop.code, NatLoops.shiftRightLoop, frameState, Frame.read, Frame.readOperands,
      enter, localRoom, bind, Except.bind, pure, Except.pure]
  obtain ⟨value, path, represented⟩ := certificate.shiftRightLoop_returns limits (by omega) (by omega)
    n shift nValid shiftValid continuation
  exact ⟨value, observed.trans (entered.trans path), represented⟩

theorem log2_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n : Nat) (value : Value)
    (represented : Number links.arithmetic.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.log2 0 #[value] continuation)
      (returned (.ctor links.arithmetic.conversions.layout.raw #[.scalar (.nat n.log2)]) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have observed := certificate.arithmetic.conversions.call_natural limits room capacity bytesCapacity
    { function := links.log2, block := 0, locals := #[value] } (.local 0) 1 n value represented
    { function := links.log2, block := 1, locals := #[value, .scalar (.nat n)] }
    (by simp [Frame.check, certificate.log2.code, NatLoops.log2, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, certificate.log2.code, NatLoops.log2, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have entered : Reaches limits program
      (frameState links.log2 1 #[value, .scalar (.nat n)] continuation)
      (frameState links.log2Loop 0 #[.scalar (.nat n), .scalar (.nat 0)] continuation) := by
    apply Reaches.of_step
    simp [step, stepEval, Frame.check, certificate.log2.code, NatLoops.log2, certificate.log2Loop.code, NatLoops.log2Loop,
      frameState, Frame.read, Frame.readOperands, N, enter, localRoom, bind, Except.bind, pure, Except.pure]
  have loop := certificate.log2Loop_returns limits (by omega) (by omega) n 0 valid
    (by simpa using validate_nat_mono (Nat.log2_le_self n) valid) continuation
  exact observed.trans (entered.trans (by simpa using loop))

end Compilatrix.Ixby.Runtime.NatLoops.Certificate
