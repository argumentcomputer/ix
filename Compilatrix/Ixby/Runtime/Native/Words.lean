import Compilatrix.Ixby.Runtime.Native.Scalars
import Compilatrix.Ixby.Runtime.WordShiftLaws

/-! Word operations use the typed Word32 ABI; UInt8 results are masked to eight
bits and source shift counts are reduced modulo the source width. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion Words

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.u8OfNat_returns (room : 3 ≤ limits.locals) (n : Nat)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 23 0 #[natural n] continuation)
      (returned (word (n % 256).toUInt32) continuation) := by
  have code := (certificate.function 23).code
  change program.getFunction 23 = .ok Code.UInt8_ofNat at code
  change (Scalar.nat n).validate limits = .ok () at valid
  have localRoom : ∀ k, k ≤ 3 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt8_ofNat, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, word,
      Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, valid,
      lowWord_mask8, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u8ToNat_returns (room : 2 ≤ limits.locals) (a : UInt8)
    (valid : NatValid limits a.toNat) (continuation : Array Continuation) :
    Reaches limits program (frameState 24 0 #[word a.toUInt32] continuation)
      (returned (natural a.toNat) continuation) := by
  apply (certificate.function 24).unary_returns limits room _ _ ?_ continuation
  simpa [natural, word] using eval_word32ToNat limits a.toUInt32 valid

theorem Certificate.u8ToUInt32_returns (room : 1 ≤ limits.locals) (a : UInt8)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 25 0 #[word a.toUInt32] continuation)
      (returned (word a.toUInt32) continuation) :=
  (certificate.function 25).identity_returns limits room _ continuation

theorem Certificate.u8Eq_returns (room : 3 ≤ limits.locals) (a b : UInt8)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 26 0 #[word a.toUInt32, word b.toUInt32] continuation)
      (returned (.scalar (.bool (a == b))) continuation) := by
  apply (certificate.function 26).binary_returns limits room _ _ _ ?_ continuation
  have injective : a.toUInt32 = b.toUInt32 ↔ a = b := by
    constructor
    · intro h
      exact UInt8.toNat_inj.mp (by simpa only [UInt8.toNat_toUInt32] using congrArg UInt32.toNat h)
    · intro h; cases h; rfl
  have equal : (a.toUInt32 == b.toUInt32) = (a == b) := by
    simp [BEq.beq, injective]
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word, equal] <;> rfl

theorem Certificate.u8Add_returns (room : 4 ≤ limits.locals) (a b : UInt8)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 27 0 #[word a.toUInt32, word b.toUInt32] continuation)
      (returned (word (a + b).toUInt32) continuation) := by
  have code := (certificate.function 27).code
  change program.getFunction 27 = .ok Code.UInt8_add at code
  have result : (a.toUInt32 + b.toUInt32) &&& 255 = (a + b).toUInt32 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_and, UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_add]
    change ((a.toNat + b.toNat) % 2 ^ 32) &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt8_add, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, word, Primitive.eval,
      Primitive.evalScalarUnchecked, Primitive.arity, result, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u32OfNat_returns (room : 2 ≤ limits.locals) (n : Nat)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 30 0 #[natural n] continuation)
      (returned (word n.toUInt32) continuation) :=
  (certificate.function 30).unary_returns limits room _ _ (eval_natToWord32 limits n valid) continuation

theorem Certificate.u32OfNatLT_returns (room : 3 ≤ limits.locals) (n : Nat) (erasedProof : Value)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 31 0 #[natural n, erasedProof] continuation)
      (returned (word n.toUInt32) continuation) := by
  have code := (certificate.function 31).code
  change program.getFunction 31 = .ok Code.UInt32_ofNatLT at code
  have convert := eval_natToWord32 limits n valid
  have localRoom : ∀ k, k ≤ 3 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt32_ofNatLT, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, word, convert,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u32ToUInt8_returns (room : 2 ≤ limits.locals) (a : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 32 0 #[word a] continuation)
      (returned (word a.toUInt8.toUInt32) continuation) := by
  have code := (certificate.function 32).code
  change program.getFunction 32 = .ok Code.UInt32_toUInt8 at code
  have result : a &&& 255 = a.toUInt8.toUInt32 := by
    apply UInt32.toNat_inj.mp
    simpa [UInt32.toNat_and] using Nat.and_two_pow_sub_one_eq_mod a.toNat 8
  have localRoom : ∀ k, k ≤ 2 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt32_toUInt8, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, word, Primitive.eval,
      Primitive.evalScalarUnchecked, Primitive.arity, result, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u32ToNat_returns (room : 2 ≤ limits.locals) (a : UInt32)
    (valid : NatValid limits a.toNat) (continuation : Array Continuation) :
    Reaches limits program (frameState 33 0 #[word a] continuation)
      (returned (natural a.toNat) continuation) :=
  (certificate.function 33).unary_returns limits room _ _ (eval_word32ToNat limits a valid) continuation

theorem Certificate.u32Add_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 34 0 #[word a, word b] continuation)
      (returned (word (a + b)) continuation) := by
  apply (certificate.function 34).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32Sub_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 35 0 #[word a, word b] continuation)
      (returned (word (a - b)) continuation) := by
  apply (certificate.function 35).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32Mul_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 36 0 #[word a, word b] continuation)
      (returned (word (a * b)) continuation) := by
  apply (certificate.function 36).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32And_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 37 0 #[word a, word b] continuation)
      (returned (word (a &&& b)) continuation) := by
  apply (certificate.function 37).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32Or_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 38 0 #[word a, word b] continuation)
      (returned (word (a ||| b)) continuation) := by
  apply (certificate.function 38).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32Xor_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 39 0 #[word a, word b] continuation)
      (returned (word (a ^^^ b)) continuation) := by
  apply (certificate.function 39).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32Eq_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 42 0 #[word a, word b] continuation)
      (returned (.scalar (.bool (a == b))) continuation) := by
  apply (certificate.function 42).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl

theorem Certificate.u32Lt_returns (room : 3 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 43 0 #[word a, word b] continuation)
      (returned (.scalar (.bool (a < b))) continuation) := by
  apply (certificate.function 43).binary_returns limits room (word a) (word b) _ ?_ continuation
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word] <;> rfl


theorem Certificate.u8ShiftLeft_returns (room : 5 ≤ limits.locals) (a b : UInt8)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 28 0 #[word a.toUInt32, word b.toUInt32] continuation)
      (returned (word ((a <<< b).toUInt32)) continuation) := by
  have code := (certificate.function 28).code
  change program.getFunction 28 = .ok Code.UInt8_shiftLeft at code
  have bounded : b.toUInt32 &&& 7 < (32 : UInt32) := masked_count_lt b.toUInt32 8 (Or.inl rfl)
  have result : (a.toUInt32 <<< (b.toUInt32 &&& 7)) &&& 255 = (a <<< b).toUInt32 := by
    apply UInt32.toNat_inj.mp
    simpa only [UInt8.toNat_toUInt32] using u8_shiftLeft_nat a b
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt8_shiftLeft, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, word, Primitive.eval,
      Primitive.evalScalarUnchecked, Primitive.arity, bounded, result, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u8ShiftRight_returns (room : 5 ≤ limits.locals) (a b : UInt8)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 29 0 #[word a.toUInt32, word b.toUInt32] continuation)
      (returned (word ((a >>> b).toUInt32)) continuation) := by
  have code := (certificate.function 29).code
  change program.getFunction 29 = .ok Code.UInt8_shiftRight at code
  have bounded : b.toUInt32 &&& 7 < (32 : UInt32) := masked_count_lt b.toUInt32 8 (Or.inl rfl)
  have result : (a.toUInt32 >>> (b.toUInt32 &&& 7)) &&& 255 = (a >>> b).toUInt32 := by
    apply UInt32.toNat_inj.mp
    simpa only [UInt8.toNat_toUInt32] using u8_shiftRight_nat a b
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt8_shiftRight, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, word, Primitive.eval,
      Primitive.evalScalarUnchecked, Primitive.arity, bounded, result, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u32ShiftLeft_returns (room : 4 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 40 0 #[word a, word b] continuation)
      (returned (word (a <<< b)) continuation) := by
  have code := (certificate.function 40).code
  change program.getFunction 40 = .ok Code.UInt32_shiftLeft at code
  have bounded : b &&& 31 < (32 : UInt32) := masked_count_lt b 32 (Or.inr rfl)
  have result : a <<< (b &&& 31) = a <<< b := by
    apply UInt32.toNat_inj.mp
    exact u32_shiftLeft_nat a b
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt32_shiftLeft, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, word, Primitive.eval,
      Primitive.evalScalarUnchecked, Primitive.arity, bounded, result, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.u32ShiftRight_returns (room : 4 ≤ limits.locals) (a b : UInt32)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 41 0 #[word a, word b] continuation)
      (returned (word (a >>> b)) continuation) := by
  have code := (certificate.function 41).code
  change program.getFunction 41 = .ok Code.UInt32_shiftRight at code
  have bounded : b &&& 31 < (32 : UInt32) := masked_count_lt b 32 (Or.inr rfl)
  have result : a >>> (b &&& 31) = a >>> b := by
    apply UInt32.toNat_inj.mp
    exact u32_shiftRight_nat a b
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.UInt32_shiftRight, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, word, Primitive.eval,
      Primitive.evalScalarUnchecked, Primitive.arity, bounded, result, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

end Compilatrix.Ixby.Runtime.Native
