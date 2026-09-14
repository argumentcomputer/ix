import Compilatrix.Ixby.Runtime.WordCertificate
import Compilatrix.Ixby.Runtime.WordCall
import Compilatrix.Ixby.Runtime.WordLaws

/-! Modular arithmetic follows every generated observer and constructor call.
The intermediate cache agrees with the exact arithmetic before truncation. -/

namespace Compilatrix.Ixby.Runtime.Words

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem modular_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {natOp wordOp : Primitive}
    (bits : Nat) (width : bits = 8 ∨ bits = 32 ∨ bits = 64)
    (checked : Checked program id (modular links.natural links.lowWord links.cachedCtor bits natOp wordOp))
    (limits : Limits) (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b n : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (resultValid : (Scalar.nat n).validate limits = .ok ())
    (modulusValid : (Scalar.nat (2 ^ bits)).validate limits = .ok ())
    (natResult : natOp.eval limits [.scalar (.nat a), .scalar (.nat b)] = .ok (.scalar (.nat n)))
    (wordResult : wordOp.eval limits [.scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] =
      .ok (.scalar (.word32 n.toUInt32)))
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (cachedValue links.layout (n % 2 ^ bits)) continuation) := by
  have localRoom : ∀ k, k ≤ 14 → ¬limits.locals < k := by omega
  have reduced := eval_natMod limits n (2 ^ bits) resultValid modulusValid
    (validate_nat_mono (Nat.mod_le n (2 ^ bits)) resultValid)
  have masked : Primitive.word32And.eval limits
      [.scalar (.word32 n.toUInt32), .scalar (.word32 255)] =
      .ok (.scalar (.word32 (n % 256).toUInt32)) := by
    simp [Primitive.eval, Primitive.arity, lowWord_mask8] <;> rfl
  have cache32 := (lowWord_mod n 32 (by decide)).symm
  have cache64 := (lowWord_mod n 64 (by decide)).symm
  simp only [Nat.toUInt32, Nat.reducePow] at cache32 cache64
  rcases width with rfl | rfl | rfl
  all_goals
    have observed := conversions.read_binary_parts checked rfl rfl rfl rfl _ rfl limits (by omega)
      capacity bytesCapacity a b left right leftRep rightRep leftValid rightValid continuation stack
    have beforeTruncate : Reaches limits program
        (frameState id 4 #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
          .scalar (.nat b), .scalar (.word32 b.toUInt32)] continuation)
        (frameState id 7 #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
          .scalar (.nat b), .scalar (.word32 b.toUInt32), .scalar (.nat n), .scalar (.word32 n.toUInt32),
          cachedValue links.layout n] continuation) := by
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, checked.code, modular, conversions.cached,
          frameState, cachedValue, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
          natResult, wordResult, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    have observedResult := conversions.read_parts checked 7
      #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
        .scalar (.nat b), .scalar (.word32 b.toUInt32), .scalar (.nat n), .scalar (.word32 n.toUInt32),
        cachedValue links.layout n] (.local 8) rfl rfl _ rfl limits (by omega)
      (by simp; omega) capacity bytesCapacity n (cachedValue links.layout n) (Number.cached n) resultValid
      rfl rfl continuation stack
    apply observed.trans (beforeTruncate.trans (observedResult.trans ?_))
    first
    | (apply reaches_of_chunk (fuel := 4) (count := 0)
       iterate 4
         rw [runChunk]
         simp [step, stepEval, Frame.check, checked.code, modular, conversions.cached,
           frameState, returned, cachedValue, Frame.read, Frame.readOperands,
           Frame.transfer, evalOp, N, W, reduced, masked,
           localRoom, bind, Except.bind, pure, Except.pure]
       rfl)
    | (apply reaches_of_chunk (fuel := 3) (count := 0)
       iterate 3
         rw [runChunk]
         simp [step, stepEval, Frame.check, checked.code, modular, conversions.cached,
           frameState, returned, cachedValue, Frame.read, Frame.readOperands,
           Frame.transfer, evalOp, N, reduced,
           localRoom, bind, Except.bind, pure, Except.pure]
       simp only [cache32, cache64]
       rfl)

theorem subtract_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId}
    (bits : Nat) (width : bits = 32 ∨ bits = 64)
    (checked : Checked program id (subtract links.natural links.lowWord links.cachedCtor bits))
    (limits : Limits) (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ()) (bounded : b < 2 ^ bits)
    (sumValid : (Scalar.nat (a + 2 ^ bits)).validate limits = .ok ())
    (modulusValid : (Scalar.nat (2 ^ bits)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (cachedValue links.layout ((a + 2 ^ bits - b) % 2 ^ bits)) continuation) := by
  have localRoom : ∀ k, k ≤ 14 → ¬limits.locals < k := by omega
  let n := a + 2 ^ bits - b
  have resultValid : (Scalar.nat n).validate limits = .ok () :=
    validate_nat_mono (Nat.sub_le _ _) sumValid
  have added := eval_natAdd limits a (2 ^ bits) leftValid modulusValid sumValid
  have subtracted := eval_natSub limits (a + 2 ^ bits) b sumValid rightValid resultValid
  have wordResult : Primitive.word32Sub.eval limits
      [.scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] = .ok (.scalar (.word32 n.toUInt32)) := by
    have word := lowWord_subtract a b bits (by rcases width with rfl | rfl <;> decide) bounded
    simp [Primitive.eval, Primitive.arity, word, n] <;> rfl
  have reduced := eval_natMod limits n (2 ^ bits) resultValid modulusValid
    (validate_nat_mono (Nat.mod_le n (2 ^ bits)) resultValid)
  have cache := (lowWord_mod n bits (by rcases width with rfl | rfl <;> decide)).symm
  have observed := conversions.read_binary_parts checked rfl rfl rfl rfl _ rfl limits (by omega)
    capacity bytesCapacity a b left right leftRep rightRep leftValid rightValid continuation stack
  have beforeTruncate : Reaches limits program
      (frameState id 4 #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
        .scalar (.nat b), .scalar (.word32 b.toUInt32)] continuation)
      (frameState id 8 #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
        .scalar (.nat b), .scalar (.word32 b.toUInt32), .scalar (.nat (a + 2 ^ bits)), .scalar (.nat n),
        .scalar (.word32 n.toUInt32), cachedValue links.layout n] continuation) := by
    apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, subtract, conversions.cached,
        frameState, cachedValue, Frame.read, Frame.readOperands, Frame.transfer, evalOp, N,
        added, subtracted, wordResult, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have observedResult := conversions.read_parts checked 8
    #[left, right, .scalar (.nat a), .scalar (.word32 a.toUInt32),
      .scalar (.nat b), .scalar (.word32 b.toUInt32), .scalar (.nat (a + 2 ^ bits)), .scalar (.nat n),
      .scalar (.word32 n.toUInt32), cachedValue links.layout n] (.local 9) rfl rfl _ rfl limits (by omega)
    (by simp; omega) capacity bytesCapacity n (cachedValue links.layout n) (Number.cached n) resultValid
    rfl rfl continuation stack
  apply observed.trans (beforeTruncate.trans (observedResult.trans ?_))
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, subtract, conversions.cached,
      frameState, returned, cachedValue, Frame.read, Frame.readOperands,
      Frame.transfer, evalOp, N, reduced, localRoom, bind, Except.bind, pure, Except.pure]
  simp only [Nat.toUInt32] at cache
  rw [cache]
  rfl

end Compilatrix.Ixby.Runtime.Words
