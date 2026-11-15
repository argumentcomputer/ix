import Ix.CompileCert.ReaderIndex
import Ix.Cert.ReaderFallback
import IxC.Kernel.Ixon.ReaderSpec

/-! # Same-record twin provenance

The computed recursor index only files twins at recursor payloads of its scanned records.
When scanned records agree at a shared address, filtering a record's indexed twins by its
actual recursor members loses no indexed twin.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.ReaderIndex
open Ix.CompileCert.CanonUnivMeaning (StepHolds)

def TwinSources (records : Array (_root_.Address × Ixon.Constant)) (index : RecIndex) : Prop :=
  ∀ (ref : ConstRef _root_.Address) (entry : RecEntry), index.twins[ref]? = some entry →
    ∃ (owner : _root_.Address) (c : Ixon.Constant) (j : Nat) (rc : Ixon.Recursor),
      ref = ConstRef.member owner j ∧ (owner, c) ∈ records ∧
      (j, rc) ∈ recursorMembers c

private theorem candidate_twinSources (store : Store)
    (records : Array (_root_.Address × Ixon.Constant)) (owner : _root_.Address)
    (c : Ixon.Constant) (hc : (owner, c) ∈ records) (member : Nat × Ixon.Recursor)
    (hm : member ∈ recursorMembers c) (before : BuildState) (hbefore : TwinSources records before.1) :
    StepHolds (fun after => TwinSources records after.1) (candidate store owner c member before) := by
  obtain ⟨after, hstep, hshape⟩ := candidate_step store owner c member before
  rw [hstep]
  cases hshape with
  | keep => exact hbefore
  | twin inserted =>
    intro ref entry hget
    change (before.1.twins.insert (.member owner member.1) inserted)[ref]? = some entry at hget
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · rename_i hsame
      have href : ConstRef.member owner member.1 = ref := beq_iff_eq.mp hsame
      exact ⟨owner, c, member.1, member.2, href.symm, hc, hm⟩
    · exact hbefore ref entry hget
  | add =>
    unfold added
    dsimp only
    split <;> exact hbefore

private theorem record_twinSources (store : Store)
    (records : Array (_root_.Address × Ixon.Constant)) (record : _root_.Address × Ixon.Constant)
    (hpresent : record ∈ records) (before : BuildState) (hbefore : TwinSources records before.1) :
    StepHolds (fun after => TwinSources records after.1) (recordStep store record before) :=
  Ix.CompileCert.CanonUnivEmit.arrayLoop_preserves
    (fun state : BuildState => TwinSources records state.1) (recursorMembers record.2) before
    (candidate store record.1 record.2) hbefore
    (fun member hm state hs => candidate_twinSources store records record.1 record.2
      hpresent member hm state hs)

/-- Every computed twin entry comes from an actual recursor payload in the scanned array. -/
theorem buildIndex_twinSources (store : Store) (records : Array (_root_.Address × Ixon.Constant)) :
    TwinSources records (buildIndex store records) := by
  rw [← run_eq]
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  have hcollected : TwinSources records collected.1 :=
    Ix.CompileCert.CanonUnivEmit.arrayLoop_preserves
      (fun state : BuildState => TwinSources records state.1) records ({}, {}) (recordStep store)
      (by intro ref entry h; simp at h)
      (fun record hm state hs => record_twinSources store records record hm state hs)
  exact Ix.CompileCert.CanonUnivMeaning.listLoop_preserves
    (TwinSources records) collected.2.toList collected.1 completeStep hcollected
    (fun _ _ _ hs => hs)

theorem computed_twin_is_rec_member (store : Store)
    (records : Array (_root_.Address × Ixon.Constant))
    (hrecords : ∀ a c c', (a, c) ∈ records → (a, c') ∈ records → c = c')
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : (owner, c) ∈ records) (hinfo : c.info = .muts ms) {j : Nat} {entry : RecEntry}
    (hget : (buildIndex store records).twins[ConstRef.member owner j]? = some entry) :
    ∃ rc, ms[j]? = some (.recr rc) := by
  obtain ⟨owner', c', j', rc, href, hsource, hmember⟩ :=
    buildIndex_twinSources store records _ _ hget
  cases href
  have heq := hrecords owner c c' hc hsource
  subst c'
  exact ⟨rc, by simpa only [hinfo] using member_source c j rc hmember⟩

/-- Every indexed member twin of a consistently scanned mutual record is retained by
the shared finishing helper's payload filter. -/
theorem computed_twin_mem_recordTwins (store : Store)
    (records : Array (_root_.Address × Ixon.Constant))
    (hrecords : ∀ a c c', (a, c) ∈ records → (a, c') ∈ records → c = c')
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : (owner, c) ∈ records) (hinfo : c.info = .muts ms) {j : Nat} {entry : RecEntry}
    (hget : (buildIndex store records).twins[ConstRef.member owner j]? = some entry) :
    (ConstRef.member owner j, entry) ∈ recordTwins (buildIndex store records) owner ms := by
  obtain ⟨rc, hmember⟩ := computed_twin_is_rec_member store records hrecords hc hinfo hget
  apply Array.mem_toList_iff.mp
  simp only [recordTwins, List.toList_toArray]
  apply List.mem_filterMap.mpr
  refine ⟨(.recr rc, j), ?_, ?_⟩
  · exact List.mem_zipIdx_iff_getElem?.mpr (by simpa using hmember)
  · simp [hget]

/-- In a real prelude-backed context, every indexed twin at an input record's address
comes from that input's actual recursor payload. Scanned-store agreement is derived from
the prelude and input key uniqueness. -/
theorem contextOf_twin_is_rec_member {md : Mode} (table : RoleTable) (prelude : Prelude md)
    (records : Array (_root_.Address × Ixon.Constant)) (blobs : List (_root_.Address × ByteArray))
    (hint : ConstRef _root_.Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef _root_.Address → Option _root_.Address)
    (hpre : preludeFor table = .ok prelude) (hkeys : (records.toList.map Prod.fst).Nodup)
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : (owner, c) ∈ records) (hinfo : c.info = .muts ms) {j : Nat} {entry : RecEntry}
    (hget : (contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
      prelude.blobs hint reconstruct).index.twins[ConstRef.member owner j]? = some entry) :
    ∃ rc, ms[j]? = some (.recr rc) := by
  let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
    prelude.blobs hint reconstruct
  have hcoherent := Ix.Cert.ReaderFallback.context_coherent table prelude records blobs hint
    reconstruct hpre hkeys
  change (buildIndex cx.store (indexedRecords cx.store records
    (prelude.records ++ prelude.evidence))).twins[ConstRef.member owner j]? = some entry at hget
  obtain ⟨owner', c', j', rc, href, hsource, hmember⟩ :=
    buildIndex_twinSources cx.store _ _ _ hget
  cases href
  have hsourceStored := hcoherent owner c' (Ix.Cert.ReaderClosureKeys.mem_indexed_scanned hsource)
  have hinputStored := Ix.Cert.ReaderClosureKeys.context_input table records
    (prelude.records ++ prelude.evidence) blobs prelude.blobs hint reconstruct hkeys hc
  have heq := Option.some.inj (hinputStored.symm.trans hsourceStored)
  subst c'
  exact ⟨rc, by simpa only [hinfo] using member_source c j rc hmember⟩

theorem contextOf_twin_mem_recordTwins {md : Mode} (table : RoleTable) (prelude : Prelude md)
    (records : Array (_root_.Address × Ixon.Constant)) (blobs : List (_root_.Address × ByteArray))
    (hint : ConstRef _root_.Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef _root_.Address → Option _root_.Address)
    (hpre : preludeFor table = .ok prelude) (hkeys : (records.toList.map Prod.fst).Nodup)
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : (owner, c) ∈ records) (hinfo : c.info = .muts ms) {j : Nat} {entry : RecEntry}
    (hget : (contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
      prelude.blobs hint reconstruct).index.twins[ConstRef.member owner j]? = some entry) :
    (ConstRef.member owner j, entry) ∈ recordTwins
      (contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
        prelude.blobs hint reconstruct).index owner ms := by
  obtain ⟨rc, hmember⟩ := contextOf_twin_is_rec_member table prelude records blobs hint reconstruct
    hpre hkeys hc hinfo hget
  apply Array.mem_toList_iff.mp
  simp only [recordTwins, List.toList_toArray]
  apply List.mem_filterMap.mpr
  refine ⟨(.recr rc, j), List.mem_zipIdx_iff_getElem?.mpr (by simpa using hmember), ?_⟩
  simp [hget]

end IxVM.Refinement.Assembly
