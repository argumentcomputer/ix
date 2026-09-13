/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofCodec
import Ix.Aiur.Proofs.KeyCodec

/-! Complete proof framing and injective canonical serialization. Bounds
below concern the u64 wire lengths and 32-byte digest arrays, not security. -/

namespace Aiur.NativeAIR.ProofCodec

open KeyCodec (Reader Reads Returns readByte readMany readNat_reads readMany_reads readByte_reads)

def VectorFits (property : α → Prop) (values : List α) : Prop :=
  values.length < 256^8 ∧ ∀ value ∈ values, property value

def CapFits (cap : Cap) : Prop := VectorFits (fun digest => digest.length = 32) cap

def OpeningsFits (values : Openings α) : Prop :=
  VectorFits (VectorFits (VectorFits (fun _ => True))) values

theorem readVector_reads {read : Reader α} (encode : α → List UInt8) (values : List α)
    (bounded : values.length < 256^8)
    (elements : ∀ value ∈ values, Reads read (encode value) value) :
    Reads (readVector read) (encodeVector encode values) values :=
  (readNat_reads 8 values.length bounded).bind (readMany_reads encode values elements)

theorem readOption_reads {read : Reader α} (encode : α → List UInt8) (value : Option α)
    (element : ∀ entry, value = some entry → Reads read (encode entry) entry) :
    Reads (readOption read) (encodeOption encode value) value := by
  cases value with
  | none => intro rest; rfl
  | some value =>
    unfold readOption encodeOption
    exact Reads.byte ((element value rfl).result some)

theorem readBool_reads (value : Bool) : Reads readBool (encodeBool value) value := by
  cases value <;> intro rest <;> rfl

theorem readField_reads (value : G) : Reads readField (encodeField value) value := by
  unfold readField encodeField
  apply Reads.bind (readNat_reads 8 value.n (UInt64.toNat_lt value.val))
  rw [if_pos (UInt64.lt_iff_toNat_lt.mp value.property), G.ofNat_n]
  exact Reads.pure value

theorem readExtension_reads (value : Extension) :
    Reads readExtension (encodeExtension value) value :=
  (readField_reads value.c0).bind ((readField_reads value.c1).result (Extension.mk value.c0))

theorem readCap_reads (cap : Cap) (fits : CapFits cap) : Reads readCap (encodeCap cap) cap := by
  apply readVector_reads id cap fits.1
  intro digest member
  rw [← fits.2 digest member]
  simpa using readMany_reads (fun byte => [byte]) digest
    (fun byte _ => readByte_reads byte)

theorem readOpenings_reads {read : Reader α} (encode : α → List UInt8)
    (element : ∀ value, Reads read (encode value) value)
    (values : Openings α) (fits : OpeningsFits values) :
    Reads (readOpenings read) (encodeOpenings encode values) values := by
  apply readVector_reads _ _ fits.1
  intro matrix member
  apply readVector_reads _ _ (fits.2 matrix member).1
  intro row rowMember
  exact readVector_reads _ _ ((fits.2 matrix member).2 row rowMember).1 (fun value _ => element value)

structure CommitmentsFits (value : Commitments) : Prop where
  stage1 : CapFits value.stage1
  stage2 : CapFits value.stage2
  quotient : CapFits value.quotient

theorem readCommitments_reads (value : Commitments) (fits : CommitmentsFits value) :
    Reads readCommitments (encodeCommitments value) value := by
  unfold readCommitments encodeCommitments
  rw [List.append_assoc]
  apply Reads.bind (readCap_reads value.stage1 fits.stage1)
  exact (readCap_reads value.stage2 fits.stage2).bind
    ((readCap_reads value.quotient fits.quotient).result (Commitments.mk value.stage1 value.stage2))

structure BatchOpeningFits (value : BatchOpening) : Prop where
  values : OpeningsFits value.values
  siblingHashes : CapFits value.siblingHashes

theorem readBatchOpening_reads (value : BatchOpening) (fits : BatchOpeningFits value) :
    Reads readBatchOpening (encodeBatchOpening value) value :=
  (readOpenings_reads encodeField readField_reads value.values fits.values).bind
    ((readCap_reads value.siblingHashes fits.siblingHashes).result (BatchOpening.mk value.values))

structure CommitStepFits (value : CommitStep) : Prop where
  siblingValues : VectorFits (VectorFits (fun _ => True)) value.siblingValues
  siblingHashes : CapFits value.siblingHashes

theorem readCommitStep_reads (value : CommitStep) (fits : CommitStepFits value) :
    Reads readCommitStep (encodeCommitStep value) value := by
  unfold readCommitStep encodeCommitStep
  apply Reads.byte
  apply Reads.bind (readVector_reads _ _ fits.siblingValues.1 (fun row member =>
    readVector_reads _ _ (fits.siblingValues.2 row member).1 (fun item _ => readExtension_reads item)))
  exact (readCap_reads value.siblingHashes fits.siblingHashes).result (CommitStep.mk value.logArity value.siblingValues)

structure FriFits (value : Fri) : Prop where
  commits : VectorFits CapFits value.commits
  commitPowWitnesses : value.commitPowWitnesses.length < 256^8
  inputOpenings : VectorFits BatchOpeningFits value.inputOpenings
  commitOpenings : VectorFits CommitStepFits value.commitOpenings
  finalPoly : value.finalPoly.length < 256^8

theorem readFri_reads (value : Fri) (fits : FriFits value) :
    Reads readFri (encodeFri value) value := by
  unfold readFri encodeFri
  simp only [List.append_assoc]
  apply Reads.bind (readVector_reads _ _ fits.commits.1
    (fun cap member => readCap_reads cap (fits.commits.2 cap member)))
  apply Reads.bind (readVector_reads _ _ fits.commitPowWitnesses (fun item _ => readField_reads item))
  apply Reads.bind (readVector_reads _ _ fits.inputOpenings.1
    (fun opening member => readBatchOpening_reads opening (fits.inputOpenings.2 opening member)))
  apply Reads.bind (readVector_reads _ _ fits.commitOpenings.1
    (fun opening member => readCommitStep_reads opening (fits.commitOpenings.2 opening member)))
  apply Reads.bind (readVector_reads _ _ fits.finalPoly (fun item _ => readExtension_reads item))
  exact (readField_reads value.queryPowWitness).result
    (Fri.mk value.commits value.commitPowWitnesses value.inputOpenings value.commitOpenings value.finalPoly)

structure DataFits (value : Data) : Prop where
  active : value.active.length < 256^8
  commitments : CommitmentsFits value.commitments
  accumulators : value.accumulators.length < 256^8
  logDegrees : value.logDegrees.length < 256^8
  fri : FriFits value.fri
  quotient : OpeningsFits value.quotient
  preprocessed : ∀ openings, value.preprocessed = some openings → OpeningsFits openings
  stage1 : OpeningsFits value.stage1
  stage2 : OpeningsFits value.stage2

theorem readData_reads (value : Data) (fits : DataFits value) :
    Reads readData (encodeData value) value := by
  unfold readData encodeData
  simp only [List.append_assoc]
  apply Reads.bind (readVector_reads _ _ fits.active (fun item _ => readBool_reads item))
  apply Reads.bind (readCommitments_reads value.commitments fits.commitments)
  apply Reads.bind (readVector_reads _ _ fits.accumulators (fun item _ => readExtension_reads item))
  apply Reads.bind (readVector_reads _ _ fits.logDegrees (fun item _ => readByte_reads item))
  apply Reads.bind (readFri_reads value.fri fits.fri)
  apply Reads.bind (readOpenings_reads _ readExtension_reads value.quotient fits.quotient)
  apply Reads.bind (readOption_reads _ _ (fun openings present =>
    readOpenings_reads _ readExtension_reads openings (fits.preprocessed openings present)))
  apply Reads.bind (readOpenings_reads _ readExtension_reads value.stage1 fits.stage1)
  exact (readOpenings_reads _ readExtension_reads value.stage2 fits.stage2).result
    (Data.mk value.active value.commitments value.accumulators value.logDegrees value.fri
      value.quotient value.preprocessed value.stage1)

theorem decode_encode (value : Data) (fits : DataFits value) : decode (encode value) = some value := by
  have read := readData_reads value fits []
  simp only [List.append_nil] at read
  simp only [decode, encode, List.toList_data_toByteArray, read,
    bind, Option.bind_some, List.isEmpty_nil, ite_true]

theorem decode_success {bytes : ByteArray} {value : Data} (accepted : decode bytes = some value) :
    readData bytes.data.toList = some (value, []) := by
  unfold decode at accepted
  cases parsed : readData bytes.data.toList with
  | none => simp [parsed, bind, Option.bind] at accepted
  | some pair =>
    obtain ⟨result, rest⟩ := pair
    simp only [parsed, bind, Option.bind_some] at accepted
    split at accepted
    next empty => cases accepted; simp only [List.isEmpty_iff.mp empty]
    next => cases accepted

theorem decodeCanonical_success {bytes : ByteArray} {value : Data}
    (accepted : decodeCanonical bytes = some value) : decode bytes = some value ∧ encode value = bytes := by
  unfold decodeCanonical at accepted
  cases parsed : decode bytes with
  | none => simp [parsed, bind, Option.bind] at accepted
  | some result =>
    simp only [parsed, bind, Option.bind_some] at accepted
    split at accepted
    next encoded => cases accepted; exact ⟨rfl, encoded⟩
    next => cases accepted

theorem decodeCanonical_encode (value : Data) (fits : DataFits value) :
    decodeCanonical (encode value) = some value := by
  simp only [decodeCanonical, decode_encode value fits, bind, Option.bind_some, ite_true]

theorem canonical_bytes_unique {first second : ByteArray} {value : Data}
    (left : decodeCanonical first = some value) (right : decodeCanonical second = some value) : first = second :=
  (decodeCanonical_success left).2.symm.trans (decodeCanonical_success right).2

theorem encode_injective {first second : Data} (leftFits : DataFits first) (rightFits : DataFits second)
    (equal : encode first = encode second) : first = second := by
  have decoded := congrArg decode equal
  rw [decode_encode first leftFits, decode_encode second rightFits] at decoded
  exact Option.some.inj decoded

theorem decode_append_rejected (value : Data) (fits : DataFits value) (suffix : List UInt8)
    (nonempty : suffix ≠ []) : decode ((encodeData value ++ suffix).toByteArray) = none := by
  have read := readData_reads value fits suffix
  simp only [decode, List.toList_data_toByteArray, read, bind, Option.bind_some]
  rw [if_neg (by simpa only [List.isEmpty_iff] using nonempty)]

theorem readNat_returns (count : Nat) :
    Returns (KeyCodec.readNat count) (fun value => value < 256^count) := by
  induction count with
  | zero => exact Returns.pure (by decide)
  | succ count ih =>
    unfold KeyCodec.readNat
    apply Returns.bind_any (property := fun value => value < 256^(count + 1))
    intro byte
    apply Returns.result (right := fun value => value < 256^(count + 1)) ih
    intro value bounded
    have small := UInt8.toNat_lt byte
    rw [Nat.pow_succ]
    omega

theorem readVector_returns {read : Reader α} {property : α → Prop}
    (valid : Returns read property) : Returns (readVector read) (VectorFits property) := by
  unfold readVector
  apply Returns.bind (right := VectorFits property) (readNat_returns 8)
  intro count bounded
  exact (KeyCodec.readMany_returns valid count).weaken (fun _ known => ⟨known.1 ▸ bounded, known.2⟩)

theorem readOption_returns {read : Reader α} {property : α → Prop}
    (valid : Returns read property) : Returns (readOption read)
      (fun result => ∀ value, result = some value → property value) := by
  unfold readOption
  apply Returns.bind_any (property := fun result => ∀ value, result = some value → property value)
  intro byte
  split
  · exact Returns.pure (by intro value equal; cases equal)
  · apply Returns.result (right := fun result => ∀ value, result = some value → property value) valid
    intro value known result equal
    cases equal
    exact known
  · exact Returns.failure _

theorem readCap_returns : Returns readCap CapFits := by
  apply readVector_returns
  exact (KeyCodec.readMany_returns (read := readByte) (property := fun _ => True)
    (fun _ _ _ _ => True.intro) 32).weaken (fun _ known => known.1)

theorem readOpenings_returns (read : Reader α) : Returns (readOpenings read) OpeningsFits :=
  readVector_returns (readVector_returns (readVector_returns (fun _ _ _ _ => True.intro)))

theorem readCommitments_returns : Returns readCommitments CommitmentsFits := by
  unfold readCommitments
  apply Returns.bind (right := CommitmentsFits) readCap_returns
  intro first hf
  apply Returns.bind (right := CommitmentsFits) readCap_returns
  intro second hs
  apply Returns.result (right := CommitmentsFits) readCap_returns
  intro quotient hq
  exact ⟨hf, hs, hq⟩

theorem readBatchOpening_returns : Returns readBatchOpening BatchOpeningFits := by
  unfold readBatchOpening
  apply Returns.bind (right := BatchOpeningFits) (readOpenings_returns readField)
  intro values hv
  apply Returns.result (right := BatchOpeningFits) readCap_returns
  intro hashes hh
  exact ⟨hv, hh⟩

theorem readCommitStep_returns : Returns readCommitStep CommitStepFits := by
  unfold readCommitStep
  apply Returns.bind_any (property := CommitStepFits)
  intro arity
  apply Returns.bind (right := CommitStepFits)
    (readVector_returns (readVector_returns (property := fun _ => True) (fun _ _ _ _ => True.intro)))
  intro values hv
  apply Returns.result (right := CommitStepFits) readCap_returns
  intro hashes hh
  exact ⟨hv, hh⟩

theorem readFri_returns : Returns readFri FriFits := by
  unfold readFri
  apply Returns.bind (right := FriFits) (readVector_returns readCap_returns)
  intro commits hc
  apply Returns.bind (right := FriFits) (readVector_returns (property := fun _ => True) (fun _ _ _ _ => True.intro))
  intro witnesses hw
  apply Returns.bind (right := FriFits) (readVector_returns readBatchOpening_returns)
  intro inputs hi
  apply Returns.bind (right := FriFits) (readVector_returns readCommitStep_returns)
  intro openings ho
  apply Returns.bind (right := FriFits) (readVector_returns (property := fun _ => True) (fun _ _ _ _ => True.intro))
  intro finalPoly hf
  apply Returns.bind_any (property := FriFits)
  intro witness
  exact Returns.pure ⟨hc, hw.1, hi, ho, hf.1⟩

theorem readData_returns : Returns readData DataFits := by
  unfold readData
  apply Returns.bind (right := DataFits) (readVector_returns (property := fun _ => True) (fun _ _ _ _ => True.intro))
  intro active ha
  apply Returns.bind (right := DataFits) readCommitments_returns
  intro commitments hc
  apply Returns.bind (right := DataFits) (readVector_returns (property := fun _ => True) (fun _ _ _ _ => True.intro))
  intro accumulators hs
  apply Returns.bind (right := DataFits) (readVector_returns (property := fun _ => True) (fun _ _ _ _ => True.intro))
  intro degrees hd
  apply Returns.bind (right := DataFits) readFri_returns
  intro fri hf
  apply Returns.bind (right := DataFits) (readOpenings_returns readExtension)
  intro quotient hq
  apply Returns.bind (right := DataFits) (readOption_returns (readOpenings_returns readExtension))
  intro preprocessed hp
  apply Returns.bind (right := DataFits) (readOpenings_returns readExtension)
  intro first hfirst
  apply Returns.result (right := DataFits) (readOpenings_returns readExtension)
  intro second hsecond
  exact ⟨ha.1, hc, hs.1, hd.1, hf, hq, hp, hfirst, hsecond⟩

theorem decode_fits {bytes : ByteArray} {value : Data} (accepted : decode bytes = some value) : DataFits value :=
  readData_returns _ value [] (decode_success accepted)

end Aiur.NativeAIR.ProofCodec
