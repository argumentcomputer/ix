import Ix.Ixon.Verify.WorkRecord
import Ix.Ixon.Verify.Admission

namespace Ix.Ixon.Verify.Work.Admission

open _root_.Ixon
open Kernel
open Ix.Ixon.Admission

/-! Accounting for the parser portion of the actual byte-admission path.

Canonical validation and re-encoding retain their production results and
short-circuit behavior, but their work is outside this decoder metric, as are
preflight/list administration, the key-uniqueness check (`uniqueKeys`, which
the entries run between preflight and decoding; `parserStage` models the
parser portion only), projection reconstruction, ordering, literal
interpretation, ingress, and kernel checking. Each attempted bounded record
contributes its entire parse work, including failures inside elements; later
records are not charged after an earlier error. No counter executes in the
production admission path.
-/

def canonicalRecord (limits : Limits) (input : ByteArray) : Except String Constant × Nat :=
  let parsed := record limits.maxRecordBytes limits.maxRecordUnivNodes input
  let result := match parsed.1 with
    | .error reason => .error reason
    | .ok value =>
      if WireCheck.validConstant value then
        if serConstant value = input then .ok value
        else .error "getConstantCanonical: noncanonical wire encoding"
      else .error "getConstantCanonical: value outside the wire domain"
  (result, parsed.2)

def decodeLoop (limits : Limits) : Nat → Records → Ingress.Constants →
    Except ByteError Ingress.Constants × Nat
  | _, [], reversed => (.ok reversed.reverse, 0)
  | position, (address, input) :: rest, reversed =>
    let parsed := canonicalRecord limits input
    match parsed.1 with
    | .error reason => (.error (.decode position address reason), parsed.2)
    | .ok value =>
      let tail := decodeLoop limits (position + 1) rest ((address, value) :: reversed)
      (tail.1, parsed.2 + tail.2)

def parserStage (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    Except ByteError Ingress.Constants × Nat :=
  match preflight limits records blobs with
  | .error reason => (.error reason, 0)
  | .ok () => decodeLoop limits 0 records []

theorem canonicalRecord_erases (limits : Limits) (input : ByteArray) :
    (canonicalRecord limits input).1 =
      Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes input := by
  unfold canonicalRecord Canonical.deConstant
  dsimp only
  rw [record_erases]
  cases Bounded.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes input <;> rfl

theorem canonicalRecord_work_le (limits : Limits) (input : ByteArray) :
    (canonicalRecord limits input).2 ≤ 16 * input.size + 2 * limits.maxRecordUnivNodes + 3 :=
  record_work_le limits.maxRecordBytes limits.maxRecordUnivNodes input

theorem decodeLoop_erases (limits : Limits) (position : Nat) (records : Records)
    (reversed : Ingress.Constants) :
    (decodeLoop limits position records reversed).1 =
      Ix.Ixon.Admission.decodeLoop limits position records reversed := by
  induction records generalizing position reversed with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨address, input⟩
    have same := canonicalRecord_erases limits input
    cases parsed : (canonicalRecord limits input).1 with
    | error reason =>
      rw [parsed] at same
      simp [decodeLoop, Ix.Ixon.Admission.decodeLoop, parsed, ← same, Except.mapError,
        Bind.bind, Except.bind]
    | ok value =>
      rw [parsed] at same
      simp [decodeLoop, Ix.Ixon.Admission.decodeLoop, parsed, ← same, Except.mapError,
        Bind.bind, Except.bind, ih]

theorem decodeLoop_work_le (limits : Limits) (position : Nat) (records : Records)
    (reversed : Ingress.Constants) :
    (decodeLoop limits position records reversed).2 ≤
      16 * payloadBytes records + records.length * (2 * limits.maxRecordUnivNodes + 3) := by
  induction records generalizing position reversed with
  | nil => simp [decodeLoop, payloadBytes]
  | cons pair rest ih =>
    rcases pair with ⟨address, input⟩
    have head := canonicalRecord_work_le limits input
    cases parsed : (canonicalRecord limits input).1 with
    | error reason =>
      simp only [decodeLoop, parsed, payloadBytes, List.length_cons, Nat.mul_add,
        Nat.add_mul, Nat.one_mul]
      omega
    | ok value =>
      have tail := ih (position + 1) ((address, value) :: reversed)
      simp only [Nat.mul_add] at tail
      simp only [decodeLoop, parsed, payloadBytes, List.length_cons, Nat.mul_add,
        Nat.add_mul, Nat.one_mul]
      omega

theorem parserStage_erases (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    (parserStage limits records blobs).1 = (do
      preflight limits records blobs
      decodeRecords limits records) := by
  unfold parserStage
  cases preflight limits records blobs with
  | error reason => rfl
  | ok done =>
    cases done
    exact decodeLoop_erases limits 0 records []

/-- The aggregate parser bound holds without a success premise. Preflight
failure performs no record parsing; decoding failure retains the complete
work of the failed element and all preceding records. -/
theorem parserStage_work_le (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    (parserStage limits records blobs).2 ≤
      16 * limits.maxTotalBytes + limits.maxRecords * (2 * limits.maxRecordUnivNodes + 3) := by
  unfold parserStage
  cases checked : preflight limits records blobs with
  | error reason => exact Nat.zero_le _
  | ok done =>
    cases done
    dsimp only
    have fits := (Ix.Ixon.Verify.Admission.preflight_ok_iff limits records blobs).mp checked
    have count := Nat.mul_le_mul_right (2 * limits.maxRecordUnivNodes + 3) fits.1
    have bytes : payloadBytes records ≤ limits.maxTotalBytes := by have := fits.2.2; omega
    have bytesBound := Nat.mul_le_mul_left 16 bytes
    have work := decodeLoop_work_le limits 0 records []
    omega

end Ix.Ixon.Verify.Work.Admission
