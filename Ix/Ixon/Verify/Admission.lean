/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission
import Ix.Ixon.Verify.Canonical
import Ix.Ixon.Verify.ConstantBounds

/-! # Exact byte admission

The reading relation names every supplied address and canonical payload in
order, independently of any decoder. It composes with K3's installed reading
and the model theorem for the actual `checkBytes` implementation. The reverse
direction preserves the in-memory checker's successful domain at the same
configuration; its rejected and declined outcomes are also preserved.
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
      · simp only [consume, if_pos fits, ih, List.length_cons, payloadBytes]
        omega
      · simp only [consume, if_neg fits]
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

universe v

theorem checkBytes_run_iff (limits : Limits) (cfg : Config) (records : Records)
    (blobs : Ingress.Blobs) (family : Option (ConstRef Address)) (env : Env Address) :
    checkBytes.{v} limits cfg records blobs family = .ok env ↔
      preflight limits records blobs = .ok () ∧ ∃ constants,
        decodeRecords limits records = .ok constants ∧
        Kernel.checkEnv.{v} cfg constants blobs family = .ok env := by
  cases flight : preflight limits records blobs with
  | error reason => simp [checkBytes, flight, bind, Except.bind]
  | ok value =>
    cases value
    cases decoded : decodeRecords limits records with
    | error reason => simp [checkBytes, flight, decoded, bind, Except.bind]
    | ok constants =>
      cases checked : Kernel.checkEnv.{v} cfg constants blobs family <;>
        simp [checkBytes, flight, decoded, checked, Except.mapError, bind, Except.bind]

/-- Exact acceptance domain: canonical, bounded byte reading followed by the
same certified in-memory checker, at the same fuel and literal family. -/
theorem checkBytes_ok_iff (limits : Limits) (cfg : Config) (records : Records)
    (blobs : Ingress.Blobs) (family : Option (ConstRef Address)) (env : Env Address) :
    checkBytes.{v} limits cfg records blobs family = .ok env ↔
      WithinBatch limits records blobs ∧ ∃ constants,
        RecordsRead limits records constants ∧
        Kernel.checkEnv.{v} cfg constants blobs family = .ok env := by
  simp only [checkBytes_run_iff, preflight_ok_iff, decodeRecords_ok_iff]

/-- Bounded, canonically encoded input preserves every kernel outcome,
including its distinction between rejection and decline. -/
theorem checkBytes_of_reading {limits : Limits} {cfg : Config} {records : Records}
    {constants : Ingress.Constants} {blobs : Ingress.Blobs} {family : Option (ConstRef Address)}
    (within : WithinBatch limits records blobs) (reading : RecordsRead limits records constants) :
    checkBytes.{v} limits cfg records blobs family =
      (Kernel.checkEnv.{v} cfg constants blobs family).mapError Error.kernel := by
  have flight := (preflight_ok_iff _ _ _).mpr within
  have decoded := (decodeRecords_ok_iff _ _ _).mpr reading
  simp [checkBytes, flight, decoded, bind, Except.bind]

/-- The exact byte reading and installed declaration reading use the same
constants, addresses, order, blobs, and literal family as the executed check. -/
theorem checkBytes_reading {limits : Limits} {cfg : Config} {records : Records}
    {blobs : Ingress.Blobs} {family : Option (ConstRef Address)} {env : Env Address}
    (accepted : checkBytes.{v} limits cfg records blobs family = .ok env) :
    WithinBatch limits records blobs ∧ ∃ constants,
      RecordsRead limits records constants ∧ Ingress.Installed constants blobs family env := by
  obtain ⟨within, constants, reading, checked⟩ := (checkBytes_ok_iff _ _ _ _ _ _).mp accepted
  exact ⟨within, constants, reading, Kernel.checkEnv_reading checked⟩

theorem checkBytes_unique_keys {limits : Limits} {cfg : Config} {records : Records}
    {blobs : Ingress.Blobs} {family : Option (ConstRef Address)} {env : Env Address}
    (accepted : checkBytes.{v} limits cfg records blobs family = .ok env) :
    (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup := by
  obtain ⟨_, constants, reading, installed⟩ := checkBytes_reading accepted
  rw [reading.keys]
  exact ⟨installed.constantKeys, installed.blobKeys⟩

/-- The executed byte-admission limits bound the whole decoded constant
representation, including expanded universes, while retaining the exact
reading and installed declarations. No extra runtime traversal is needed. -/
theorem checkBytes_resources {limits : Limits} {cfg : Config} {records : Records}
    {blobs : Ingress.Blobs} {family : Option (ConstRef Address)} {env : Env Address}
    (accepted : checkBytes.{v} limits cfg records blobs family = .ok env) :
    ∃ constants, RecordsRead limits records constants ∧ Ingress.Installed constants blobs family env ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes := by
  obtain ⟨within, constants, reading, installed⟩ := checkBytes_reading accepted
  have resources := reading.resourceUnits_le
  obtain ⟨recordCount, _, totalBytes⟩ := within
  have countProduct := Nat.mul_le_mul_right limits.maxRecordUnivNodes recordCount
  exact ⟨constants, reading, installed, by omega⟩

theorem checkBytes_has_model (V : Type v) [Model.SetTheory V] {limits : Limits} {cfg : Config}
    {records : Records} {blobs : Ingress.Blobs} {family : Option (ConstRef Address)} {env : Env Address}
    (accepted : checkBytes.{v} limits cfg records blobs family = .ok env) : Nonempty (Model V env) := by
  obtain ⟨_, constants, _, checked⟩ := (checkBytes_ok_iff _ _ _ _ _ _).mp accepted
  exact Kernel.checkEnv_has_model V checked

end Ix.Ixon.Verify.Admission
