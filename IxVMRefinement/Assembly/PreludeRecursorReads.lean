import IxVMRefinement.Assembly.AdmittedRecursorOrigins
import IxVMRefinement.Assembly.NativePreludeReader

/-! # Actual committed recursor readings

The committed prelude has its own successful reader run. Every recursor payload in its
records is read either through the canonical family or as a twin. Evidence records contain
only definitions, so a committed recursor or inductive family belongs to the prelude itself.
No transport between the prelude and selected reader contexts is assumed here.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

theorem committed_nondefinition_prelude {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) {owner : _root_.Address} {source : Ixon.Constant}
    (present : (owner, source) ∈ prelude.records ++ prelude.evidence)
    (notDefinition : ∀ definition, source.info ≠ .defn definition) :
    (owner, source) ∈ prelude.records := by
  rcases Array.mem_append.mp present with inPrelude | inEvidence
  · exact inPrelude
  · obtain ⟨_, evidenceRead⟩ := Ix.Cert.ReaderFallback.preludeFor_records prepared
    obtain ⟨evidence, read, _, definitions⟩ := RoleVal.evidenceRecords_spec
    have same : prelude.evidence = evidence := Except.ok.inj (evidenceRead.symm.trans read)
    rw [same] at inEvidence
    obtain ⟨definition, info⟩ := definitions (owner, source) (Array.mem_toList_iff.mpr inEvidence)
    exact (notDefinition definition info).elim

private theorem hasInductive_of_first {members : Array Ixon.MutConst} {slot : Nat} {first : Ixon.Inductive}
    (found : (Ix.CompileCert.ReaderIndex.inductives members)[0]? = some (slot, first)) :
    members.any (fun | .indc _ => true | _ => false) = true := by
  have member := Array.mem_of_getElem? found
  unfold Ix.CompileCert.ReaderIndex.inductives at member
  obtain ⟨⟨value, position⟩, present, mapped⟩ := Array.mem_filterMap.mp member
  cases value with
  | indc ind =>
    exact Array.any_eq_true'.mpr ⟨.indc ind,
      Array.mem_of_getElem? (Array.mk_mem_zipIdx_iff_getElem?.mp present), rfl⟩
  | _ => cases mapped

/-- Every committed recursor has a complete raw/type/rule certificate from the actual
prelude run, allowing its canonical-versus-twin choice to remain the one that run used. -/
theorem prelude_rec_inputs {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) {owner : _root_.Address} {source : Ixon.Constant}
    (present : (owner, source) ∈ prelude.records)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source) :
    let cx := nativePreludeReaderCtx table prelude
    ∃ entry blockLps row,
      (cx.index.recs[ConstRef.member owner slot]? = some entry ∨
        cx.index.twins[ConstRef.member owner slot]? = some entry) ∧
      readRecursor cx blockLps (.member owner slot) entry = .ok row ∧
      Nonempty (RecursorReadInputs cx blockLps (.member owner slot) entry row) := by
  let cx := nativePreludeReaderCtx table prelude
  have stream := readRecords_spec (preludeFor_readRecords prepared)
  obtain ⟨_, _, read, _⟩ := stream.mem (Array.mem_toList_iff.mpr present)
  by_cases canonical : cx.index.recs.contains (.member owner slot) = true
  · rw [Std.HashMap.contains_eq_isSome_getElem?] at canonical
    obtain ⟨entry, indexed⟩ := Option.isSome_iff_exists.mp canonical
    have built : ∃ records, cx.index = buildIndex cx.store records := ⟨_, rfl⟩
    obtain ⟨records, indexBuilt⟩ := built
    have indexedBuilt := indexed
    rw [indexBuilt] at indexedBuilt
    obtain ⟨_, _, _, _, _, _, familyRecord, members, firstSlot, first, _, _, _, _, _, stored, kind,
      firstAt, _, _⟩ := buildIndex_any_provenance cx.store records (.inl indexedBuilt)
    have fallback : Ix.Cert.EvidenceCheck.fallbackStore prelude entry.block = some familyRecord := by
      simpa only [cx, nativePreludeReaderCtx_store] using stored
    have familyPresent := committed_nondefinition_prelude prepared
      (Array.mem_toList_iff.mp (Ix.Cert.EvidenceCheck.fallbackStore_mem fallback))
      (fun definition different => by rw [kind] at different; cases different)
    obtain ⟨_, _, familyRead, _⟩ := stream.mem (Array.mem_toList_iff.mpr familyPresent)
    obtain ⟨blockLps, row, rowRead⟩ := readRecord_inductive_canonical_read indexBuilt familyRead kind
      (hasInductive_of_first firstAt) indexed rfl
    exact ⟨entry, blockLps, row, .inl indexed, rowRead, readRecursor_inputs rowRead⟩
  · have absent : cx.index.recs.contains (.member owner slot) = false := Bool.eq_false_iff.mpr canonical
    rcases readRecord_recursors_covered read member with found | found
    · exact (canonical found).elim
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at found
      obtain ⟨entry, indexed⟩ := Option.isSome_iff_exists.mp found
      obtain ⟨blockLps, row, rowRead⟩ := readRecord_twin_read read member absent indexed
      exact ⟨entry, blockLps, row, .inr indexed, rowRead, readRecursor_inputs rowRead⟩

/-- The fallback branch of an admitted payload origin is discharged by a concrete
successful reading in the committed prelude context. -/
theorem admitted_fallback_rec_inputs {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant}
    (present : (owner, source) ∈ witness.prelude.records ++ witness.prelude.evidence)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source) :
    let cx := nativePreludeReaderCtx witness.table witness.prelude
    ∃ entry blockLps row,
      (cx.index.recs[ConstRef.member owner slot]? = some entry ∨
        cx.index.twins[ConstRef.member owner slot]? = some entry) ∧
      readRecursor cx blockLps (.member owner slot) entry = .ok row ∧
      Nonempty (RecursorReadInputs cx blockLps (.member owner slot) entry row) := by
  have inPrelude := committed_nondefinition_prelude witness.preludeRead present (by
    intro definition info
    simp only [recursorMembers, info, Array.not_mem_empty] at member)
  exact prelude_rec_inputs witness.preludeRead inPrelude member

end IxVM.Refinement.Assembly
