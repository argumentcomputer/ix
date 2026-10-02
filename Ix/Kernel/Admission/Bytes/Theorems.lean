import Ix.Kernel.Admission.Bytes
import Ix.Ixon.Verify.Canonical
import Ix.Ixon.Verify.ConstantBounds
import Std.Data.HashSet.Lemmas

/-! # Exact byte admission

The reading relation names every supplied address and canonical payload in
order, independently of any decoder. It is the byte half of the certified
entry's theorems (`Ix.Ixon.Admission.Theorems`).
-/

namespace Ix.Ixon.Verify.Admission

open _root_.Ixon Kernel
open Ix.Ixon.Admission

theorem consume_ok_iff (resource : Resource) (count budget : Nat) (records : Records)
    (remaining : Nat) :
    consume resource count budget records = .ok remaining ↔
      records.length ≤ count ∧ payloadBytes records ≤ budget ∧
        remaining + payloadBytes records = budget := by
  induction records generalizing count budget remaining with
  | nil => simp [consume, payloadBytes, eq_comm]
  | cons pair rest ih =>
    rcases pair with ⟨address, bytes⟩
    cases count with
    | zero => simp [consume]
    | succ count =>
      by_cases fits : bytes.size ≤ budget
      · simp only [consume, ite_eq_left fits, ih, List.length_cons, payloadBytes]
        omega
      · simp only [consume, ite_eq_right fits]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_, bytesFit, _⟩
          simp only [payloadBytes] at bytesFit
          omega

/-- Batch limits concern the supplied payloads, including literal blobs. -/
def WithinBatch (limits : Limits) (records : Records) (blobs : Ingress.Blobs) : Prop :=
  records.length ≤ limits.maxRecords ∧ blobs.length ≤ limits.maxBlobs ∧
    payloadBytes records + payloadBytes blobs ≤ limits.maxTotalBytes

theorem preflight_ok_iff (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    preflight limits records blobs = .ok () ↔ WithinBatch limits records blobs := by
  constructor
  · intro accepted
    cases recordsRead : consume .records limits.maxRecords limits.maxTotalBytes records with
    | error reason => simp [preflight, recordsRead, bind, Except.bind] at accepted
    | ok remaining =>
      cases blobsRead : consume .blobs limits.maxBlobs remaining blobs with
      | error reason => simp [preflight, recordsRead, blobsRead, bind, Except.bind] at accepted
      | ok rest =>
        obtain ⟨recordCount, _, recordBytes⟩ := (consume_ok_iff _ _ _ _ _).mp recordsRead
        obtain ⟨blobCount, blobBytes, _⟩ := (consume_ok_iff _ _ _ _ _).mp blobsRead
        exact ⟨recordCount, blobCount, by omega⟩
  · rintro ⟨recordCount, blobCount, totalBytes⟩
    have recordBytes : payloadBytes records ≤ limits.maxTotalBytes := by omega
    have recordsRead := (consume_ok_iff .records limits.maxRecords limits.maxTotalBytes
      records (limits.maxTotalBytes - payloadBytes records)).mpr
      ⟨recordCount, recordBytes, by omega⟩
    have blobBytes : payloadBytes blobs ≤ limits.maxTotalBytes - payloadBytes records := by omega
    have blobsRead := (consume_ok_iff .blobs limits.maxBlobs
      (limits.maxTotalBytes - payloadBytes records) blobs
      (limits.maxTotalBytes - payloadBytes records - payloadBytes blobs)).mpr
      ⟨blobCount, blobBytes, by omega⟩
    simp [preflight, recordsRead, blobsRead, bind, Except.bind, pure, Except.pure]

/-- Each record address and each blob address of a batch occurs once. -/
def UniqueKeys (records : Records) (blobs : Ingress.Blobs) : Prop :=
  (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup

/-- `firstDuplicate` finds nothing exactly when the table's keys are
distinct and none of them is in `seen` (`Std.HashSet` membership, through
`LawfulBEq Address`). -/
theorem firstDuplicate_eq_none_iff {α : Type} (position : Nat) (seen : Std.HashSet Address)
    (store : List (Address × α)) :
    firstDuplicate position seen store = none ↔
      (store.map Prod.fst).Nodup ∧ ∀ entry ∈ store, seen.contains entry.1 = false := by
  induction store generalizing position seen with
  | nil => simp [firstDuplicate]
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    by_cases hin : seen.contains key = true
    · simp only [firstDuplicate, hin, ite_true, reduceCtorEq, false_iff, not_and]
      intro _ hall
      simpa [hin] using hall (key, value) List.mem_cons_self
    · simp only [firstDuplicate, hin, Bool.false_eq_true, ite_false, ih, Std.HashSet.contains_insert,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, List.map_cons, List.nodup_cons,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨hnd, hall⟩
        refine ⟨⟨fun hmem => ?_, hnd⟩, by simp, fun e he => (hall e he).2⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
        exact (hall e he).1 rfl
      · rintro ⟨⟨hnot, hnd⟩, _, hall⟩
        refine ⟨hnd, fun e he => ⟨fun same => hnot ?_, hall e he⟩⟩
        exact List.mem_map.mpr ⟨e, he, same.symm⟩

theorem firstDuplicate_empty_eq_none_iff {α : Type} (store : List (Address × α)) :
    firstDuplicate 0 {} store = none ↔ (store.map Prod.fst).Nodup := by
  rw [firstDuplicate_eq_none_iff]
  simp

/-- **Key uniqueness**: the byte stage's duplicate check passes exactly when
no two records and no two blobs share an address, so each of its rejections
names a key that is used twice. -/
theorem uniqueKeys_ok_iff (records : Records) (blobs : Ingress.Blobs) :
    uniqueKeys records blobs = .ok () ↔ UniqueKeys records blobs := by
  unfold uniqueKeys UniqueKeys
  cases hr : firstDuplicate 0 {} records with
  | some found =>
    have := mt (firstDuplicate_empty_eq_none_iff records).mpr (by simp [hr])
    simp only [reduceCtorEq, false_iff]
    exact fun h => this h.1
  | none =>
    have hrn := (firstDuplicate_empty_eq_none_iff records).mp hr
    cases hb : firstDuplicate 0 {} blobs with
    | some found =>
      have := mt (firstDuplicate_empty_eq_none_iff blobs).mpr (by simp [hb])
      simp only [reduceCtorEq, false_iff]
      exact fun h => this h.2
    | none => simp [hrn, (firstDuplicate_empty_eq_none_iff blobs).mp hb]

/-- An exact ordered reading of record bytes. Keys are unchanged; each
payload satisfies the per-record canonical contract `Canonical.Reads`: it is
the canonical encoding of its entire wire-well-formed constant, including
sharing and side tables, within the per-record limits. This does not assert
canonical mutual-block order or authenticate address hashes. -/
inductive RecordsRead (limits : Limits) : Records → Ingress.Constants → Prop where
  | nil : RecordsRead limits [] []
  | cons {address : Address} {bytes : ByteArray} {constant : Constant}
      {rest : Records} {constants : Ingress.Constants}
      (reads : Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes constant)
      (tail : RecordsRead limits rest constants) :
      RecordsRead limits ((address, bytes) :: rest) ((address, constant) :: constants)

theorem RecordsRead.encode {limits : Limits} {records : Records} {constants : Ingress.Constants}
    (reading : RecordsRead limits records constants) :
    records = constants.map (fun (address, constant) => (address, serConstant constant)) := by
  induction reading with
  | nil => rfl
  | cons reads _ ih => simp [List.map_cons, reads.encoded, ih]

theorem RecordsRead.keys {limits : Limits} {records : Records} {constants : Ingress.Constants}
    (reading : RecordsRead limits records constants) :
    records.map Prod.fst = constants.map Prod.fst := by
  induction reading with
  | nil => rfl
  | cons _ _ ih => simp [List.map_cons, ih]

/-- The per-record universe budgets imply a bound for the complete batch;
unused universe entries count just like referenced entries. -/
theorem RecordsRead.univNodes_le {limits : Limits} {records : Records}
    {constants : Ingress.Constants} (reading : RecordsRead limits records constants) :
    (constants.map (fun pair => Bounded.univNodes pair.2.univs)).sum ≤
      records.length * limits.maxRecordUnivNodes := by
  induction reading with
  | nil => simp
  | cons reads _ ih =>
    have nodesFit := reads.nodesFit
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Structural units in the decoded records, plus expanded universe nodes.
This measure is proof-only and is not recomputed by byte admission. -/
def resourceUnits (constants : Ingress.Constants) : Nat :=
  (constants.map (fun pair => pair.2.resourceSize + Bounded.univNodes pair.2.univs)).sum

theorem RecordsRead.resourceUnits_le {limits : Limits} {records : Records}
    {constants : Ingress.Constants} (reading : RecordsRead limits records constants) :
    resourceUnits constants ≤ 2 * payloadBytes records + records.length * limits.maxRecordUnivNodes := by
  induction reading with
  | nil => simp [resourceUnits, payloadBytes]
  | cons reads _ ih =>
    have nodesFit := reads.nodesFit
    have exactRead := deConstantExact_serConstant _ reads.wire
    rw [reads.encoded] at exactRead
    have structural := ConstantBounds.deConstantExact_resource_bound _ _ exactRead
    simp only [resourceUnits] at ih
    simp only [resourceUnits, List.map_cons, List.sum_cons, payloadBytes, List.length_cons,
      Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega

theorem decodeLoop_spec {limits : Limits} {position : Nat} {records : Records}
    {reversed output : Ingress.Constants}
    (accepted : decodeLoop limits position records reversed = .ok output) :
    ∃ constants, RecordsRead limits records constants ∧ output = reversed.reverse ++ constants := by
  induction records generalizing position reversed output with
  | nil =>
    simp only [decodeLoop, Except.ok.injEq] at accepted
    exact ⟨[], .nil, by simpa using accepted.symm⟩
  | cons pair rest ih =>
    rcases pair with ⟨address, bytes⟩
    cases decoded : Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes with
    | error reason => simp [decodeLoop, decoded, Except.mapError, bind, Except.bind] at accepted
    | ok constant =>
      have tail : decodeLoop limits (position + 1) rest ((address, constant) :: reversed) =
          .ok output := by
        simpa [decodeLoop, decoded, Except.mapError, bind, Except.bind] using accepted
      obtain ⟨constants, reading, same⟩ := ih tail
      exact ⟨(address, constant) :: constants,
        .cons ((Canonical.deConstant_reads_iff _ _ _ _).mp decoded) reading,
        by simpa [List.reverse_cons, List.append_assoc] using same⟩

theorem decodeLoop_complete {limits : Limits} {records : Records} {constants : Ingress.Constants}
    (reading : RecordsRead limits records constants) (position : Nat) (reversed : Ingress.Constants) :
    decodeLoop limits position records reversed = .ok (reversed.reverse ++ constants) := by
  induction reading generalizing position reversed with
  | nil => simp [decodeLoop]
  | cons reads _ ih =>
    have decoded := (Canonical.deConstant_reads_iff _ _ _ _).mpr reads
    simp only [decodeLoop, decoded, Except.mapError, bind, Except.bind]
    simpa [List.reverse_cons, List.append_assoc] using ih (position + 1) (_ :: reversed)

theorem decodeRecords_ok_iff (limits : Limits) (records : Records) (constants : Ingress.Constants) :
    decodeRecords limits records = .ok constants ↔ RecordsRead limits records constants := by
  constructor
  · intro accepted
    obtain ⟨decoded, reading, same⟩ := decodeLoop_spec accepted
    simpa only [List.reverse_nil, List.nil_append] using same ▸ reading
  · intro reading
    simpa [decodeRecords] using decodeLoop_complete reading 0 []

theorem RecordsRead.deterministic {limits : Limits} {records : Records}
    {first second : Ingress.Constants} (left : RecordsRead limits records first)
    (right : RecordsRead limits records second) : first = second := by
  have h₁ := (decodeRecords_ok_iff _ _ _).mpr left
  have h₂ := (decodeRecords_ok_iff _ _ _).mpr right
  rw [h₁] at h₂
  exact Except.ok.inj h₂

end Ix.Ixon.Verify.Admission
