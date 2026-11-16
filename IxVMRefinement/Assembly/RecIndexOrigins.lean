import Ix.Cert.RecursorIndexFacts
import Ix.Cert.ReaderFallback

/-! # Analysis provenance for canonical and twin recursor entries

Both maps retain the successful analysis that filed each actual payload. This permits
analysis transfer without assuming that canonical-versus-twin selection stays unchanged.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.ReaderIndex
open Ix.CompileCert.CanonUnivMeaning (StepHolds)

private def TwinAnalyses (store : Store) (records : Array (_root_.Address × Ixon.Constant))
    (index : RecIndex) : Prop :=
  ∀ ref entry, index.twins[ref]? = some entry → From store records ref entry

private theorem TwinAnalyses.insert {store : Store}
    {records : Array (_root_.Address × Ixon.Constant)} {index : RecIndex}
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    (before : TwinAnalyses store records index) (origin : From store records ref entry) :
    TwinAnalyses store records { index with twins := index.twins.insert ref entry } := by
  intro query value found
  change (index.twins.insert ref entry)[query]? = some value at found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst query
    cases Option.some.inj found
    exact origin
  · exact before query value found

private theorem candidate_twinAnalyses (store : Store)
    (records : Array (_root_.Address × Ixon.Constant)) (owner : _root_.Address)
    (constant : Ixon.Constant) (present : (owner, constant) ∈ records)
    (member : Nat × Ixon.Recursor) (memberPresent : member ∈ recursorMembers constant)
    (before : BuildState) (valid : TwinAnalyses store records before.1) :
    StepHolds (fun after => TwinAnalyses store records after.1)
      (candidate store owner constant member before) := by
  rcases member with ⟨position, recursor⟩
  rcases before with ⟨index, found⟩
  unfold candidate
  dsimp only
  split
  · exact valid
  · split
    · split
      · split
        · split
          · split
            · split
              · split
                · rename_i _fresh _ motive carriers major analysed _ block firstIndex carrier _
                    blockRecord stored _ members kind _ slot first firstFound guarded _taken
                  have origin : From store records (.member owner position)
                      ⟨block, motive, major, recursor.lvls.toNat == first.lvls.toNat + 1⟩ :=
                    ⟨owner, constant, position, recursor, carriers, firstIndex, blockRecord,
                      members, slot, first, rfl, present, memberPresent, analysed, carrier,
                      stored, kind, firstFound, guarded, rfl⟩
                  by_cases already : index.twins.contains (.member owner position) = true
                  · simp only [already, ↓reduceIte]
                    exact valid
                  · simp only [already, Bool.false_eq_true, ↓reduceIte]
                    exact valid.insert origin
                · split <;> exact valid
              · exact valid
            · exact valid
          · exact valid
        · exact valid
      · exact valid
    · exact valid

private theorem record_twinAnalyses (store : Store)
    (records : Array (_root_.Address × Ixon.Constant))
    (record : _root_.Address × Ixon.Constant) (present : record ∈ records)
    (before : BuildState) (valid : TwinAnalyses store records before.1) :
    StepHolds (fun after => TwinAnalyses store records after.1) (recordStep store record before) :=
  Ix.CompileCert.CanonUnivEmit.arrayLoop_preserves
    (fun state : BuildState => TwinAnalyses store records state.1)
    (recursorMembers record.2) before (candidate store record.1 record.2) valid
    (fun member hm state hs => candidate_twinAnalyses store records record.1 record.2
      present member hm state hs)

private theorem buildIndex_twinAnalyses (store : Store)
    (records : Array (_root_.Address × Ixon.Constant)) :
    TwinAnalyses store records (buildIndex store records) := by
  rw [← run_eq]
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  have collectedValid : TwinAnalyses store records collected.1 :=
    Ix.CompileCert.CanonUnivEmit.arrayLoop_preserves
      (fun state : BuildState => TwinAnalyses store records state.1) records ({}, {})
      (recordStep store) (by intro ref entry found; simp at found)
      (fun record present state hs => record_twinAnalyses store records record present state hs)
  exact Ix.CompileCert.CanonUnivMeaning.listLoop_preserves
    (TwinAnalyses store records) collected.2.toList collected.1 completeStep collectedValid
    (fun _ _ _ hs => hs)

/-- Every canonical or twin entry has a real payload and successful filing analysis. -/
theorem buildIndex_any_provenance (store : Store)
    (records : Array (_root_.Address × Ixon.Constant))
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    (found : (buildIndex store records).recs[ref]? = some entry ∨
      (buildIndex store records).twins[ref]? = some entry) : From store records ref entry :=
  found.elim ((buildIndex_valid store records).1 ref entry)
    (buildIndex_twinAnalyses store records ref entry)

/-- A hit at an actual input payload in a prelude-backed context recovers that payload's
successful analysis, including its family, motive and major. -/
theorem contextOf_member_analysis {md : Mode} (table : RoleTable) (prelude : Prelude md)
    (records : Array (_root_.Address × Ixon.Constant)) (blobs : List (_root_.Address × ByteArray))
    (hint : ConstRef _root_.Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef _root_.Address → Option _root_.Address)
    (prepared : preludeFor table = .ok prelude) (keys : (records.toList.map Prod.fst).Nodup)
    {owner : _root_.Address} {constant : Ixon.Constant} {j : Nat} {recursor : Ixon.Recursor}
    (present : (owner, constant) ∈ records) (member : (j, recursor) ∈ recursorMembers constant)
    {entry : RecEntry}
    (found :
      let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
        prelude.blobs hint reconstruct
      cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry) :
    let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
      prelude.blobs hint reconstruct
    ∃ carriers, recursorAnalysis? cx.store owner constant recursor =
      some (entry.block, entry.motive, carriers, entry.major) := by
  let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
    prelude.blobs hint reconstruct
  have coherent := Ix.Cert.ReaderFallback.context_coherent table prelude records blobs hint
    reconstruct prepared keys
  change (buildIndex cx.store (indexedRecords cx.store records
    (prelude.records ++ prelude.evidence))).recs[ConstRef.member owner j]? = some entry ∨
    (buildIndex cx.store (indexedRecords cx.store records
      (prelude.records ++ prelude.evidence))).twins[ConstRef.member owner j]? = some entry at found
  obtain ⟨owner', constant', j', recursor', carriers, same, scanned, payload, analysis⟩ :=
    Ix.Cert.RecursorIndex.analysis_of_from (buildIndex_any_provenance cx.store _ found)
  cases same
  have stored := coherent owner constant' (Ix.Cert.ReaderClosureKeys.mem_indexed_scanned scanned)
  have input := Ix.Cert.ReaderClosureKeys.context_input (md := md) table records
    (prelude.records ++ prelude.evidence) blobs prelude.blobs hint reconstruct keys present
  have equal := Option.some.inj (input.symm.trans stored)
  subst constant'
  have equalRec := member_unique constant j recursor recursor' member payload
  subst recursor'
  exact ⟨carriers, analysis⟩

end IxVM.Refinement.Assembly
