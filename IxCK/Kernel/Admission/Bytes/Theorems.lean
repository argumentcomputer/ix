import IxCK.Kernel.Admission.Bytes
import IxCK.Ixon.Verify.Canonical
import IxCK.Ixon.Verify.ConstantBounds
import Std.Data.HashSet.Lemmas

/-! # Exact byte admission

The reading relation names every supplied address and canonical payload in
order, independently of any decoder. It is the byte half of the certified
entry's theorems (`Ix.Kernel.Admission.Theorems`).
-/

namespace Ix.Kernel.Admission

open Ixon

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

/-- Every record and every blob of a batch is stored under `hash` of its
bytes, exactly as supplied. -/
def Authentic (hash : ByteArray → Address) (records : Records) (blobs : Ingress.Blobs) : Prop :=
  (∀ entry ∈ records, entry.1 = hash entry.2) ∧ ∀ entry ∈ blobs, entry.1 = hash entry.2

theorem firstMismatch_eq_none_iff (hash : ByteArray → Address) (position : Nat)
    (store : List (Address × ByteArray)) :
    firstMismatch hash position store = none ↔ ∀ entry ∈ store, entry.1 = hash entry.2 := by
  induction store generalizing position with
  | nil => simp [firstMismatch]
  | cons entry rest ih =>
    obtain ⟨address, bytes⟩ := entry
    by_cases same : hash bytes = address
    · simp only [firstMismatch, same, beq_self_eq_true, ite_true, ih, List.mem_cons,
        forall_eq_or_imp, true_and]
    · have differ : (hash bytes == address) = false := by simpa using same
      simp only [firstMismatch, differ, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff,
        List.mem_cons, forall_eq_or_imp, not_and]
      exact fun h => absurd h.symm same

/-- **Authentication**: the byte stage's hash check passes exactly when every
record and every blob is stored under `hash` of its bytes, so each of its
rejections names an entry whose key is not its hash. -/
theorem authenticate_ok_iff (hash : ByteArray → Address) (records : Records) (blobs : Ingress.Blobs) :
    authenticate hash records blobs = .ok () ↔ Authentic hash records blobs := by
  unfold authenticate Authentic
  cases hr : firstMismatch hash 0 records with
  | some found =>
    have := mt (firstMismatch_eq_none_iff hash 0 records).mpr (by simp [hr])
    simp only [reduceCtorEq, false_iff]
    exact fun h => this h.1
  | none =>
    have hrn := (firstMismatch_eq_none_iff hash 0 records).mp hr
    cases hb : firstMismatch hash 0 blobs with
    | some found =>
      have := mt (firstMismatch_eq_none_iff hash 0 blobs).mpr (by simp [hb])
      simp only [reduceCtorEq, false_iff]
      exact fun h => this h.2
    | none => exact iff_of_true rfl ⟨hrn, (firstMismatch_eq_none_iff hash 0 blobs).mp hb⟩

/-- An exact ordered reading of record bytes. Keys are unchanged; each
payload satisfies the per-record canonical contract `Ixon.Verify.Canonical.Reads`: it is
the canonical encoding of its entire wire-well-formed constant, including
sharing and side tables, within the per-record limits. This does not assert
canonical mutual-block order; authentication is `Authentic`, and its
reading for decoded records is `RecordsRead.hashed`. -/
inductive RecordsRead (limits : Limits) : Records → Ingress.Constants → Prop where
  | nil : RecordsRead limits [] []
  | cons {address : Address} {bytes : ByteArray} {constant : Constant}
      {rest : Records} {constants : Ingress.Constants}
      (reads : Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes constant)
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

/-- Every decoded record is stored under `hash` of its canonical encoding. -/
def Hashed (hash : ByteArray → Address) (constants : Ingress.Constants) : Prop :=
  ∀ entry ∈ constants, entry.1 = hash (serConstant entry.2)

/-- Authenticated payloads that read canonically: each decoded record is
stored under `hash` of its canonical encoding, which is its supplied
payload. -/
theorem RecordsRead.hashed {limits : Limits} {records : Records} {constants : Ingress.Constants}
    {hash : ByteArray → Address} (reading : RecordsRead limits records constants)
    (authentic : ∀ entry ∈ records, entry.1 = hash entry.2) : Hashed hash constants := by
  rintro ⟨address, constant⟩ mem
  apply authentic (address, serConstant constant)
  rw [reading.encode]
  exact List.mem_map.mpr ⟨_, mem, rfl⟩

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
    have exactRead := Ixon.Verify.deConstantExact_serConstant _ reads.wire
    rw [reads.encoded] at exactRead
    have structural := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound _ _ exactRead
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
        .cons ((Ixon.Verify.Canonical.deConstant_reads_iff _ _ _ _).mp decoded) reading,
        by simpa [List.reverse_cons, List.append_assoc] using same⟩

theorem decodeLoop_complete {limits : Limits} {records : Records} {constants : Ingress.Constants}
    (reading : RecordsRead limits records constants) (position : Nat) (reversed : Ingress.Constants) :
    decodeLoop limits position records reversed = .ok (reversed.reverse ++ constants) := by
  induction reading generalizing position reversed with
  | nil => simp [decodeLoop]
  | cons reads _ ih =>
    have decoded := (Ixon.Verify.Canonical.deConstant_reads_iff _ _ _ _).mpr reads
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

/-- **Decoding within the depth limit decodes**: what `decodeWithin` returns
is `decodeRecords`'s (so `RecordsRead`). -/
theorem decodeWithin_decodeRecords {limits : Limits} {records : Records}
    {constants : Ingress.Constants} (h : decodeWithin limits records = .ok constants) :
    decodeRecords limits records = .ok constants := by
  unfold decodeWithin at h
  cases hs : scanDepths limits records with
  | error e => simp [hs, bind, Except.bind] at h
  | ok u =>
    cases hd : decodeRecords limits records with
    | error e => simp [hs, hd, bind, Except.bind, Except.mapError] at h
    | ok cs =>
      cases he : expandedDepths limits cs with
      | error e => simp [hs, hd, he, bind, Except.bind, Except.mapError] at h
      | ok v =>
        simp only [hs, hd, he, bind, Except.bind, pure, Except.pure, Except.mapError] at h
        rw [h]

/-- A failing scan is the depth decline. -/
theorem scanDepths_error {limits : Limits} :
    ∀ {records : Records} {e : ByteError}, scanDepths limits records = .error e → e = .limit .depth
  | [], _, h => by simp [scanDepths] at h
  | (_, _) :: _, _, h => by
    rw [scanDepths] at h
    split at h
    · cases h; rfl
    · exact scanDepths_error h

/-- A failing expanded-depth check is the depth decline. -/
theorem expandedDepths_error {limits : Limits} :
    ∀ {constants : Ingress.Constants} {e : ByteError},
      expandedDepths limits constants = .error e → e = .limit .depth
  | [], _, h => by simp [expandedDepths] at h
  | (_, _) :: _, _, h => by
    rw [expandedDepths] at h
    split at h
    · cases h; rfl
    · exact expandedDepths_error h

/-- `asLimit` changes a decode error into a per-record limit's decline, or nothing. -/
theorem ByteError.asLimit_cases (e : ByteError) :
    e.asLimit = e ∨ e.asLimit = .limit .recordBytes ∨ e.asLimit = .limit .recordUnivNodes := by
  cases e with
  | decode p a r =>
    by_cases h₁ : (r == recordBytesExhausted) = true
    · simp [ByteError.asLimit, h₁]
    · by_cases h₂ : (r == univNodesExhausted) = true
      · simp [ByteError.asLimit, h₁, h₂]
      · simp [ByteError.asLimit, h₁, h₂]
  | _ => simp [ByteError.asLimit]

/-- **The limits only decline**: `decodeWithin` fails with `.limit .depth`, or with
`decodeRecords`'s error read by `ByteError.asLimit` (the error itself, or the decline of a
per-record limit, `ByteError.asLimit_cases`); every `.limit` is a decline
(`Ix.Kernel.Admission.Error.outcome`). -/
theorem decodeWithin_error {limits : Limits} {records : Records} {e : ByteError}
    (h : decodeWithin limits records = .error e) :
    e = .limit .depth ∨ ∃ e', decodeRecords limits records = .error e' ∧ e = e'.asLimit := by
  unfold decodeWithin at h
  cases hs : scanDepths limits records with
  | error e' =>
    simp only [hs, bind, Except.bind] at h
    cases h
    exact .inl (scanDepths_error hs)
  | ok u =>
    cases hd : decodeRecords limits records with
    | error e' =>
      simp only [hs, hd, bind, Except.bind, Except.mapError] at h
      cases h
      exact .inr ⟨e', rfl, rfl⟩
    | ok cs =>
      cases he : expandedDepths limits cs with
      | error e' =>
        simp only [hs, hd, he, bind, Except.bind, Except.mapError] at h
        cases h
        exact .inl (expandedDepths_error he)
      | ok v => simp [hs, hd, he, bind, Except.bind, pure, Except.pure, Except.mapError] at h

/-- **Within the depth limit**: the stored-nesting scan of `records` and the
expanded-depth check of their reading `constants` pass. -/
def DepthsWithin (limits : Limits) (records : Records) (constants : Ingress.Constants) : Prop :=
  scanDepths limits records = .ok () ∧ expandedDepths limits constants = .ok ()

/-- **Decoding within the depth limit** reads exactly (`RecordsRead`) and
within the limit. -/
theorem decodeWithin_ok_iff (limits : Limits) (records : Records) (constants : Ingress.Constants) :
    decodeWithin limits records = .ok constants ↔
      RecordsRead limits records constants ∧ DepthsWithin limits records constants := by
  rw [← decodeRecords_ok_iff]
  constructor
  · intro h
    have hd := decodeWithin_decodeRecords h
    refine ⟨hd, ?_⟩
    unfold DepthsWithin
    refine ⟨?_, ?_⟩
    · cases hs : scanDepths limits records with
      | ok u => cases u; rfl
      | error e =>
        unfold decodeWithin at h
        simp [hs, bind, Except.bind] at h
    · cases he : expandedDepths limits constants with
      | ok u => cases u; rfl
      | error e =>
        unfold decodeWithin at h
        cases hs : scanDepths limits records <;> simp [hs, hd, he, bind, Except.bind, Except.mapError] at h
  · rintro ⟨hd, hw⟩
    obtain ⟨hs, he⟩ := hw
    unfold decodeWithin
    simp [hs, hd, he, bind, Except.bind, pure, Except.pure, Except.mapError]

/-- The scan passes every record whose bytes cannot reach the limit (`storedDepthBound`). -/
theorem scanDepths_ok_of_bound {limits : Limits} :
    ∀ {records : Records}, (∀ entry ∈ records, storedDepthBound limits entry.2 ≤ limits.maxDepth) →
      scanDepths limits records = .ok ()
  | [], _ => rfl
  | (a, bytes) :: rest, h => by
    rw [scanDepths, if_neg]
    · exact scanDepths_ok_of_bound (fun e he => h e (List.mem_cons_of_mem _ he))
    · intro hc
      simp only [scanFails, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨-, hlt⟩, -⟩ := hc
      exact absurd (h (a, bytes) (List.mem_cons_self ..)) (Nat.not_le.mpr hlt)

/-- The expanded-depth check passes everything when the limit is at least `expandedDepthBound`. -/
theorem expandedDepths_ok_of_bound {limits : Limits} (h : expandedDepthBound limits ≤ limits.maxDepth) :
    ∀ {constants : Ingress.Constants}, expandedDepths limits constants = .ok ()
  | [] => rfl
  | (_, _) :: _ => by
    rw [expandedDepths, if_neg]
    · exact expandedDepths_ok_of_bound h
    · simp [expandedFails, h]

/-- **Within any limit at least the records' bounds**: a depth limit no record can reach
(`storedDepthBound`, `expandedDepthBound`) is met. -/
theorem DepthsWithin.of_bound {limits : Limits} {records : Records} {constants : Ingress.Constants}
    (stored : ∀ entry ∈ records, storedDepthBound limits entry.2 ≤ limits.maxDepth)
    (expanded : expandedDepthBound limits ≤ limits.maxDepth) :
    DepthsWithin limits records constants := by
  unfold DepthsWithin
  exact ⟨scanDepths_ok_of_bound stored, expandedDepths_ok_of_bound expanded⟩


/-! ## The scan reads with the codec's readers

The depth scan reads one- and two-byte integer headers and single bytes in place
(`Depth.tagAt`, `Depth.u8At`); each equals the codec's reader run at the same
byte. -/

namespace Depth

private theorem getU8_at (state : GetState) : getU8 state =
    if state.idx < state.bytes.size then
      .ok state.bytes[state.idx]! { state with idx := state.idx + 1 }
    else .error "EOF" state := by
  unfold getU8
  change (EStateM.bind (EStateM.get : GetM GetState) _) state = _
  simp only [EStateM.bind, EStateM.get]
  split <;> rfl

private theorem bind_at {α β : Type} (x : GetM α) (g : α → GetM β) (s : GetState) :
    (x >>= g) s = EStateM.bind x g s := rfl

/-- `u8At` is `getU8` run at the same byte. -/
theorem u8At_eq (bytes : ByteArray) (i : Nat) : u8At bytes i = readAt getU8 bytes i := by
  unfold u8At readAt
  rw [EStateM.run, getU8_at]
  by_cases h : i < bytes.size
  · simp [h, getElem!_pos]
  · simp [h]

/-- `tagAt f` is `getTagN f` run at the same byte: the one- and two-byte headers it reads in
place give the codec's value and next index, and it hands every wider header to the codec. -/
theorem tagAt_eq (f : Nat) (bytes : ByteArray) (i : Nat) :
    tagAt f bytes i = readAt (getTagN f) bytes i := by
  unfold tagAt
  by_cases h : i < bytes.size
  · rw [dif_pos h]
    dsimp only
    by_cases h1 : bytes[i].toNat % 2 ^ (8 - f) < 2 ^ (8 - f - 1)
    · rw [if_pos h1]
      unfold readAt getTagN
      rw [EStateM.run, bind_at]
      simp only [EStateM.bind, getU8_at]
      simp [h, getElem!_pos, h1, pure, EStateM.pure]
    · rw [if_neg h1]
      by_cases h2 : bytes[i].toNat % 2 ^ (8 - f) - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2)
      · rw [if_pos h2]
        unfold readAt getTagN
        rw [EStateM.run, bind_at]
        simp only [EStateM.bind, getU8_at]
        by_cases h3 : i + 1 < bytes.size
        · rw [dif_pos h3]
          simp [h, h3, getElem!_pos, h1, h2, pure, EStateM.pure, bind_at, EStateM.bind, getU8_at, tagNEnd1]
        · rw [dif_neg h3]
          simp [h, h3, getElem!_pos, h1, h2, pure, bind_at, EStateM.bind, getU8_at]
      · rw [if_neg h2]
  · rw [dif_neg h]
    unfold readAt getTagN
    rw [EStateM.run, bind_at]
    simp only [EStateM.bind, getU8_at]
    simp [h]

end Depth

end Ix.Kernel.Admission
