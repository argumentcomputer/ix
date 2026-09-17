import Compilatrix.Ixby.Runtime.ConversionCertificate

/-! Complete executions of the two field/Nat adapters. Native field results
are reduced; the reverse conversion reconstructs the exact canonical Nat. -/

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

@[simp] theorem validate_field (limits : Limits) (field : Goldilocks) :
    (Scalar.field field).validate limits = .ok () := rfl

def fieldChunk (field : Goldilocks) (start : Nat) : Array UInt8 :=
  (bytesLE 8 field.val).extract start (start + 4)

def fieldWord (field : Goldilocks) (start : Nat) : UInt32 :=
  (natOfBytesLE (fieldChunk field start)).toUInt32

theorem fieldChunk_size (field : Goldilocks) (start : Nat) (small : start ≤ 4) :
    (fieldChunk field start).size = 4 := by
  simp [fieldChunk, Array.size_extract]
  omega

theorem eval_fieldChunk (limits : Limits) (field : Goldilocks) (start : UInt32)
    (small : start.toNat ≤ 4) (capacity : 8 ≤ limits.byteArrayBytes) :
    Primitive.bytesSlice.eval limits
      [.scalar (.bytes (bytesLE 8 field.val)), .scalar (.word32 start), .scalar (.word32 4)] =
      .ok (.scalar (.bytes (fieldChunk field start.toNat))) := by
  have fits : start.toNat + 4 ≤ 8 := by omega
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Scalar.validate,
    fieldChunk, Array.size_extract, Nat.not_lt.mpr capacity, fits,
    show ¬limits.byteArrayBytes < 4 by omega] <;> rfl

theorem eval_fieldWord (limits : Limits) (field : Goldilocks) (start : Nat)
    (small : start ≤ 4) (capacity : 8 ≤ limits.byteArrayBytes) :
    Primitive.bytesToWord32.eval limits [.scalar (.bytes (fieldChunk field start))] =
      .ok (.scalar (.word32 (fieldWord field start))) := by
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Scalar.validate, fieldChunk_size field start small,
    fieldWord, show ¬limits.byteArrayBytes < 4 by omega] <;> rfl

theorem fieldWord_pair (field : Goldilocks) :
    (fieldWord field 0).toNat + (fieldWord field 4).toNat * 2 ^ 32 = field.val :=
  field_natural_words field

theorem fieldWord_low (field : Goldilocks) : fieldWord field 0 = field.val.toUInt32 := by
  unfold fieldWord fieldChunk
  rw [bytesLE_extract (by decide : 0 + 4 ≤ 8), natOfBytesLE_bytesLE]
  apply UInt32.toNat.inj
  simp [Nat.toUInt32, UInt32.toNat_ofNat']

namespace Certificate

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem fieldFromNatural_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (n : Nat) (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.fieldFromNatural 0 #[.scalar (.nat n)] continuation)
      (returned (.scalar (.field (Goldilocks.reduce n))) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have modulusValid := validate_nat_of_bits
    (by decide : goldilocksModulus < 2 ^ 64) capacity
  have baseValid := validate_nat_of_bits (by decide : 2 ^ 32 < 2 ^ 64) capacity
  have reducedValid := validate_nat_mono (Nat.mod_le n goldilocksModulus) valid
  have highValid := validate_nat_mono (Nat.div_le_self (n % goldilocksModulus) (2 ^ 32)) reducedValid
  let reduced := n % goldilocksModulus
  let low := reduced.toUInt32
  let highNat := reduced / 2 ^ 32
  let high := highNat.toUInt32
  let savedLow : Frame := { function := links.fieldFromNatural, block := 2, locals :=
     #[.scalar (.nat n), .scalar (.nat reduced)] }
  have beforeLow : Reaches limits program
      (frameState links.fieldFromNatural 0 #[.scalar (.nat n)] continuation)
      (frameState links.toWord 0 #[.scalar (.nat reduced), .scalar (.word32 1), .scalar (.word32 0)]
        (continuation.push (.resume savedLow))) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fieldFromNatural.code, certificate.toWord.code,
        Conversion.fieldFromNatural, Conversion.toWord, frameState, savedLow, reduced,
        evalOp, Frame.readOperands, Frame.read, Frame.transfer, State.push, enter,
        Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, N, W, localRoom, valid, modulusValid, reducedValid,
        show ¬continuation.size ≥ limits.continuations by omega,
        bind, Except.bind, pure, Except.pure]
    rfl
  have lowPath := certificate.toWord_returns limits room (by omega) reduced reducedValid
    (continuation.push (.resume savedLow)) (by simp; omega)
  have resumeLow : Reaches limits program
      (returned (.scalar (.word32 low)) (continuation.push (.resume savedLow)))
      (frameState links.fieldFromNatural 2 (savedLow.locals ++ #[.scalar (.word32 low)]) continuation) := by
    apply Execution.resume
    simp [Frame.transfer, Frame.check, certificate.fieldFromNatural.code, Conversion.fieldFromNatural,
      savedLow, localRoom, bind, Except.bind, pure, Except.pure]
  let savedHigh : Frame := { function := links.fieldFromNatural, block := 4, locals :=
     #[.scalar (.nat n), .scalar (.nat reduced), .scalar (.word32 low), .scalar (.nat highNat)] }
  have beforeHigh : Reaches limits program
      (frameState links.fieldFromNatural 2 (savedLow.locals ++ #[.scalar (.word32 low)]) continuation)
      (frameState links.toWord 0 #[.scalar (.nat highNat), .scalar (.word32 1), .scalar (.word32 0)]
        (continuation.push (.resume savedHigh))) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fieldFromNatural.code, certificate.toWord.code,
        Conversion.fieldFromNatural, Conversion.toWord, frameState, savedLow, savedHigh, reduced, highNat,
        evalOp, Frame.readOperands, Frame.read, Frame.transfer, State.push, enter,
        Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, N, W, localRoom, reducedValid, baseValid, highValid,
        show ¬continuation.size ≥ limits.continuations by omega,
        bind, Except.bind, pure, Except.pure]
    rfl
  have highPath := certificate.toWord_returns limits room (by omega) highNat highValid
    (continuation.push (.resume savedHigh)) (by simp; omega)
  have resumeHigh : Reaches limits program
      (returned (.scalar (.word32 high)) (continuation.push (.resume savedHigh)))
      (frameState links.fieldFromNatural 4 (savedHigh.locals ++ #[.scalar (.word32 high)]) continuation) := by
    apply Execution.resume
    simp [Frame.transfer, Frame.check, certificate.fieldFromNatural.code, Conversion.fieldFromNatural,
      savedHigh, localRoom, bind, Except.bind, pure, Except.pure]
  have suffix : Reaches limits program
      (frameState links.fieldFromNatural 4 (savedHigh.locals ++ #[.scalar (.word32 high)]) continuation)
      (returned (.scalar (.field ((Goldilocks.reduce low.toNat).add
        ((Goldilocks.reduce high.toNat).mul (Goldilocks.reduce (2 ^ 32)))))) continuation) := by
    apply reaches_of_chunk (fuel := 5) (count := 0)
    iterate 5
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fieldFromNatural.code, Conversion.fieldFromNatural,
        frameState, returned, savedHigh, evalOp, Frame.readOperands, Frame.read, Frame.transfer,
        Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have complete := beforeLow.trans (lowPath.trans (resumeLow.trans
    (beforeHigh.trans (highPath.trans (resumeHigh.trans suffix)))))
  simpa only [low, high, highNat, reduced, field_from_natural_words] using complete

theorem fieldNatural_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (field : Goldilocks)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.fieldNatural 0 #[.scalar (.field field)] continuation)
      (returned (.scalar (.nat field.val)) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have fieldBytes := eval_fieldToBytes limits field bytesCapacity
  have sliceLow := eval_fieldChunk limits field 0 (by decide) bytesCapacity
  have sliceHigh := eval_fieldChunk limits field 4 (by decide) bytesCapacity
  have wordLow := eval_fieldWord limits field 0 (by decide) bytesCapacity
  have wordHigh := eval_fieldWord limits field 4 (by decide) bytesCapacity
  let low := fieldWord field 0
  let high := fieldWord field 4
  let savedLow : Frame := {
    function := links.fieldNatural
    block := 4
    locals := #[.scalar (.field field), .scalar (.bytes (bytesLE 8 field.val)),
      .scalar (.bytes (fieldChunk field 0)), .scalar (.word32 low)] }
  have beforeLow : Reaches limits program
      (frameState links.fieldNatural 0 #[.scalar (.field field)] continuation)
      (frameState links.fromWordLoop 0 #[.scalar (.word32 low), .scalar (.nat 1), .scalar (.nat 0)]
        (continuation.push (.resume savedLow))) := by
    apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fieldNatural.code, certificate.fromWordLoop.code,
        Conversion.fieldNatural, Conversion.fromWordLoop, frameState, savedLow, low,
        evalOp, Frame.readOperands, Frame.read, Frame.transfer, State.push, enter, N, W,
        localRoom, fieldBytes, sliceLow, wordLow,
        show ¬continuation.size ≥ limits.continuations by omega,
        bind, Except.bind, pure, Except.pure]
    rfl
  have lowPath := certificate.fromWordLoop_returns limits room (by omega) low
    (continuation.push (.resume savedLow)) (by simp; omega)
  have resumeLow : Reaches limits program
      (returned (.scalar (.nat low.toNat)) (continuation.push (.resume savedLow)))
      (frameState links.fieldNatural 4 (savedLow.locals ++ #[.scalar (.nat low.toNat)]) continuation) := by
    apply Execution.resume
    simp [Frame.transfer, Frame.check, certificate.fieldNatural.code, Conversion.fieldNatural,
      savedLow, localRoom, bind, Except.bind, pure, Except.pure]
  let savedHigh : Frame := {
    function := links.fieldNatural
    block := 7
    locals := #[.scalar (.field field), .scalar (.bytes (bytesLE 8 field.val)),
      .scalar (.bytes (fieldChunk field 0)), .scalar (.word32 low), .scalar (.nat low.toNat),
      .scalar (.bytes (fieldChunk field 4)), .scalar (.word32 high)] }
  have beforeHigh : Reaches limits program
      (frameState links.fieldNatural 4 (savedLow.locals ++ #[.scalar (.nat low.toNat)]) continuation)
      (frameState links.fromWordLoop 0 #[.scalar (.word32 high), .scalar (.nat 1), .scalar (.nat 0)]
        (continuation.push (.resume savedHigh))) := by
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fieldNatural.code, certificate.fromWordLoop.code,
        Conversion.fieldNatural, Conversion.fromWordLoop, frameState, savedLow, savedHigh, high,
        evalOp, Frame.readOperands, Frame.read, Frame.transfer, State.push, enter, N, W,
        localRoom, sliceHigh, wordHigh,
        show ¬continuation.size ≥ limits.continuations by omega,
        bind, Except.bind, pure, Except.pure]
    rfl
  have highPath := certificate.fromWordLoop_returns limits room (by omega) high
    (continuation.push (.resume savedHigh)) (by simp; omega)
  have resumeHigh : Reaches limits program
      (returned (.scalar (.nat high.toNat)) (continuation.push (.resume savedHigh)))
      (frameState links.fieldNatural 7 (savedHigh.locals ++ #[.scalar (.nat high.toNat)]) continuation) := by
    apply Execution.resume
    simp [Frame.transfer, Frame.check, certificate.fieldNatural.code, Conversion.fieldNatural,
      savedHigh, localRoom, bind, Except.bind, pure, Except.pure]
  have resultValid := validate_nat_of_bits
    (Nat.lt_of_lt_of_le field.isLt (by decide : goldilocksModulus ≤ 2 ^ 64)) capacity
  have lowValid := validate_nat_of_bits low.toNat_lt (show 32 ≤ limits.natBits by omega)
  have highValid := validate_nat_of_bits high.toNat_lt (show 32 ≤ limits.natBits by omega)
  have baseValid := validate_nat_of_bits (by decide : 2 ^ 32 < 2 ^ 64) capacity
  have pair : low.toNat + high.toNat * 2 ^ 32 = field.val := fieldWord_pair field
  have weightedValid := validate_nat_mono
    (show high.toNat * 2 ^ 32 ≤ field.val by rw [← pair]; omega) resultValid
  have multiply := eval_natMul limits high.toNat (2 ^ 32) highValid baseValid weightedValid
  have add : Primitive.natAdd.eval limits
      [.scalar (.nat low.toNat), .scalar (.nat (high.toNat * 2 ^ 32))] =
      .ok (.scalar (.nat field.val)) := by
    have exactSum : (Scalar.nat (low.toNat + high.toNat * 2 ^ 32)).validate limits = .ok () :=
      pair.symm ▸ resultValid
    simpa only [pair] using eval_natAdd limits low.toNat (high.toNat * 2 ^ 32)
      lowValid weightedValid exactSum
  have suffix : Reaches limits program
      (frameState links.fieldNatural 7 (savedHigh.locals ++ #[.scalar (.nat high.toNat)]) continuation)
      (returned (.scalar (.nat field.val)) continuation) := by
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fieldNatural.code, Conversion.fieldNatural,
        frameState, returned, savedHigh, evalOp, Frame.readOperands, Frame.read, Frame.transfer,
        N, localRoom, multiply, add, bind, Except.bind, pure, Except.pure]
    rfl
  exact beforeLow.trans (lowPath.trans (resumeLow.trans
    (beforeHigh.trans (highPath.trans (resumeHigh.trans suffix)))))

end Certificate

end Compilatrix.Ixby.Runtime.Conversion
