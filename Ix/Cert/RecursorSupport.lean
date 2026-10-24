import Ix.Cert.ReaderClosureKeys
import Ix.Ixon.CheckOrder

/-! Unwired family support from the actual canonical catalogue and reader
index. The guard compares the candidate's own index; no closure, acceptance
of a smaller batch, or source/value consequence is inferred. -/
namespace Ix.Cert.RecursorSupport
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission

def payloads (ixe : Ixon.Env) : Records :=
  ixe.consts.toList.map fun (a, lc) => (a, lc.rawBytes)

structure Catalogue (ixe : Ixon.Env) (limits : Limits) where
  constants : Ingress.Constants
  decoded : decodeRecords limits (payloads ixe) = .ok constants

def catalogue (ixe : Ixon.Env) (limits : Limits) : Except ByteError (Catalogue ixe limits) :=
  match h : decodeRecords limits (payloads ixe) with
  | .error e => .error e
  | .ok constants => .ok ⟨constants, h⟩

private theorem decoded_origin {limits records constants} (read : RecordsRead limits records constants)
    {a c} (member : (a, c) ∈ constants) :
    ∃ bytes, (a, bytes) ∈ records ∧
      Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes c := by
  induction read with
  | nil => simp at member
  | cons reads tail ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact ⟨_, List.mem_cons_self, reads⟩
    · obtain ⟨bytes, stored, read⟩ := ih later
      exact ⟨bytes, List.mem_cons_of_mem _ stored, read⟩

theorem Catalogue.origin {ixe limits} (p : Catalogue ixe limits) {a c}
    (member : (a, c) ∈ p.constants) :
    ∃ lc, ixe.consts.get? a = some lc ∧
      Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes lc.rawBytes c := by
  obtain ⟨bytes, stored, read⟩ := decoded_origin (decodeRecords_ok_iff .. |>.mp p.decoded) member
  obtain ⟨⟨owner, lc⟩, present, same⟩ := List.mem_map.mp stored
  cases same
  exact ⟨lc, (Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList).mpr
    ⟨_, BEq.rfl, present⟩, read⟩

def Catalogue.context {ixe limits} (p : Catalogue ixe limits) (t : RoleTable) (pre : Prelude .anon) : Ctx .anon :=
  streamContext Address.admissionHash t pre p.constants ixe.blobs.toList (hintsOf ixe)

private theorem owner_step_mem (b a owner : Address) (acc : Array Address) :
    a ∈ (if owner == b || acc.contains owner then acc else acc.push owner) ↔
      a ∈ acc ∨ owner = a ∧ a ≠ b := by
  by_cases same : owner = b
  · simp [same, eq_comm]
  · by_cases old : owner ∈ acc
    · simp only [Array.contains_iff_mem.mpr old, Bool.or_true, ite_true]
      constructor
      · exact Or.inl
      · rintro (h | ⟨eq, _⟩)
        · exact h
        · exact eq ▸ old
    · have absent : acc.contains owner = false := Bool.eq_false_iff.mpr (fun h => old (Array.contains_iff_mem.mp h))
      simp only [beq_eq_false_iff_ne.mpr same, absent, Bool.false_or, Bool.false_eq_true, ite_false, Array.mem_push]
      constructor
      · rintro (h | eq)
        · exact .inl h
        · exact .inr ⟨eq.symm, eq ▸ same⟩
      · rintro (h | ⟨eq, _⟩)
        · exact .inl h
        · exact .inr eq.symm

private theorem owners_mem (b a : Address) (refs : List (ConstRef Address)) (acc : Array Address) :
    a ∈ refs.foldl (fun out r => if r.block == b || out.contains r.block then out else out.push r.block) acc ↔
      a ∈ acc ∨ ∃ r ∈ refs, r.block = a ∧ a ≠ b := by
  induction refs generalizing acc with
  | nil => simp
  | cons r refs ih =>
    rw [List.foldl_cons, ih, owner_step_mem]
    constructor
    · rintro ((old | now) | ⟨q, member, rest⟩)
      · exact .inl old
      · exact .inr ⟨r, List.mem_cons_self, now⟩
      · exact .inr ⟨q, List.mem_cons_of_mem _ member, rest⟩
    · rintro (old | ⟨q, member, rest⟩)
      · exact .inl (.inl old)
      · rcases List.mem_cons.mp member with rfl | member
        · exact .inl (.inr rest)
        · exact .inr ⟨q, member, rest⟩

/-- Exact non-self support owners; the existing builder preserves its own order. -/
theorem recursorRecords_mem (index : RecIndex) (b a : Address) :
    a ∈ Ixon.CheckOrder.recursorRecords index b ↔
      ∃ shape, index.blocks[b]? = some shape ∧ ∃ ref ∈ shape.recs, ref.block = a ∧ a ≠ b := by
  unfold Ixon.CheckOrder.recursorRecords
  rw [← Array.foldl_toList, owners_mem]
  cases index.blocks[b]? <;> simp

/-- Actual selected references have input canonical-byte origins or unshadowed
scanned fallback origins. No intended Source-recursion identity is assumed. -/
theorem Catalogue.support_origin {ixe limits} (p : Catalogue ixe limits) (t : RoleTable)
    (pre : Prelude .anon) {b a} (member : a ∈ Ixon.CheckOrder.recursorRecords (p.context t pre).index b) :
    ∃ shape ref c position recursor,
      (p.context t pre).index.blocks[b]? = some shape ∧ ref ∈ shape.recs ∧
      ref = .member a position ∧ (position, recursor) ∈ recursorMembers c ∧ a ≠ b ∧
      ((∃ lc, ixe.consts.get? a = some lc ∧
        Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes lc.rawBytes c) ∨
       (a, c) ∈ pre.records ++ pre.evidence ∧ a ∉ p.constants.map Prod.fst) := by
  obtain ⟨shape, found, ref, selected, owner, different⟩ := (recursorRecords_mem ..).mp member
  obtain ⟨a', c, position, recursor, reference, origin, inRecord⟩ :=
    ReaderClosureKeys.selected_origin t p.constants.toArray (pre.records ++ pre.evidence)
      ixe.blobs.toList pre.blobs (hintsOf ixe) (projectionAddress Address.admissionHash) found selected
  rw [reference] at owner
  change a' = a at owner
  subst a'
  refine ⟨shape, ref, c, position, recursor, found, selected, reference, inRecord, different, ?_⟩
  rcases origin with input | fallback
  · exact .inl (p.origin (by simpa using input))
  · exact .inr (by simpa using fallback)

def entryEq : Option RecEntry → Option RecEntry → Bool
  | some a, some b => a.block == b.block && a.motive == b.motive && a.major == b.major && a.large == b.large
  | _, _ => false

theorem entryEq_iff (a b : Option RecEntry) : entryEq a b = true ↔ ∃ e, a = some e ∧ b = some e := by
  cases a with
  | none => simp [entryEq]
  | some a => cases b with
    | none => simp [entryEq]
    | some b =>
      constructor
      · intro h
        simp only [entryEq, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨block, motive⟩, major⟩, large⟩ := h
        have eq : a = b := by
          cases a; cases b
          simp only [RecEntry.mk.injEq]
          exact ⟨block, motive, major, large⟩
        exact ⟨a, rfl, congrArg some eq.symm⟩
      · rintro ⟨e, ha, hb⟩
        cases Option.some.inj ha
        cases Option.some.inj hb
        simp [entryEq]

def familyEq (full batch : RecIndex) (b : Address) : Bool :=
  match full.blocks[b]?, batch.blocks[b]? with
  | some a, some c => a.order == c.order && a.recs == c.recs &&
      a.recs.all (fun r => entryEq full.recs[r]? batch.recs[r]?)
  | _, _ => false

def FamilyAgrees (full batch : RecIndex) (b : Address) : Prop :=
  ∃ shape, full.blocks[b]? = some shape ∧ batch.blocks[b]? = some shape ∧
    ∀ r ∈ shape.recs, ∃ e, full.recs[r]? = some e ∧ batch.recs[r]? = some e

theorem familyEq_iff (full batch : RecIndex) (b : Address) :
    familyEq full batch b = true ↔ FamilyAgrees full batch b := by
  cases hf : full.blocks[b]? with
  | none => simp [familyEq, FamilyAgrees, hf]
  | some a =>
    cases hb : batch.blocks[b]? with
    | none => simp [familyEq, FamilyAgrees, hb]
    | some c =>
      simp only [familyEq, hf, hb, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true']
      constructor
      · rintro ⟨⟨order, recs⟩, entries⟩
        have same : a = c := by
          cases a; cases c
          simp only [BlockShape.mk.injEq]
          exact ⟨order, recs⟩
        exact ⟨a, hf, hb.trans (congrArg some same.symm), fun r member =>
          (entryEq_iff ..).mp (entries r member)⟩
      · rintro ⟨shape, fullHit, batchHit, entries⟩
        have sameA := Option.some.inj (hf.symm.trans fullHit)
        have sameC := Option.some.inj (hb.symm.trans batchHit)
        subst shape; subst c
        exact ⟨⟨rfl, rfl⟩, fun r member => (entryEq_iff ..).mpr (entries r member)⟩

def families (constants : Ingress.Constants) : Array Address := constants.toArray.filterMap fun (a, c) =>
  match c.info with
  | .muts ms => if ms.any (fun | .indc _ => true | _ => false) then some a else none
  | _ => none

/-- Rebuild from the candidate's actual canonical bytes before comparing.
Missing/missing is false for every required family; no empty default shape. -/
def Catalogue.checkBatch {ixe limits} (p : Catalogue ixe limits) (t : RoleTable) (pre : Prelude .anon)
    (order : List Address) : Except ByteError Bool := do
  let constants ← decodeRecords limits (recordsOf ixe order)
  let batch := streamContext Address.admissionHash t pre constants (blobsOf ixe order) (hintsOf ixe)
  return (families constants).all (familyEq (p.context t pre).index batch.index)

theorem Catalogue.checkBatch_iff {ixe limits} (p : Catalogue ixe limits) (t : RoleTable) (pre : Prelude .anon)
    (order : List Address) : p.checkBatch t pre order = .ok true ↔
      ∃ constants, decodeRecords limits (recordsOf ixe order) = .ok constants ∧
        ∀ b ∈ families constants, FamilyAgrees (p.context t pre).index
          (streamContext Address.admissionHash t pre constants (blobsOf ixe order) (hintsOf ixe)).index b := by
  cases decoded : decodeRecords limits (recordsOf ixe order) <;>
    simp [Catalogue.checkBatch, decoded, bind, Except.bind, pure, Except.pure,
      familyEq_iff, ← Array.forall_mem_iff_forall_getElem]

end Ix.Cert.RecursorSupport
