import IxVMRefinement.Assembly.RecursorPayloadRead
import IxVMRefinement.Assembly.AdmittedRecEntry
import IxVMRefinement.Assembly.AdmittedIndexFilter
import IxVMRefinement.Assembly.RolePreludeBridge

/-! # Concrete origins of admitted recursor payloads

A non-fallback input payload has an input family, by the actual reader eligibility check.
Canonical payloads are therefore read by that family's accepted run, and twins by their
own record run. A positive fallback test gives an exact committed record using coherent
decoding and the admission overlap check, rather than assuming its Boolean equality test
is extensional equality on constants.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

theorem admitted_fallback_contains_exact {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    (contained : (witness.prelude.records ++ witness.prelude.evidence).contains (owner, source) = true) :
    (owner, source) ∈ witness.prelude.records ++ witness.prelude.evidence := by
  obtain ⟨⟨address, value⟩, present, compared⟩ := Array.contains_iff_exists_mem_beq.mp contained
  change ((owner == address) && (source == value)) = true at compared
  have sameAddress : owner = address := beq_iff_eq.mp (Bool.and_eq_true.mp compared).1
  subst address
  obtain ⟨entry, stored, decoded⟩ := ReaderFootprint.coherent_recordAt_exact witness.coherent record
  have bytes := witness.fallbackRecordsAgree owner selected entry stored value present
  have wire := (rolePreludeInputs.serConstant_mem_committedImages witness.preludeRead present).2.2.1
  rw [bytes, Ixon.Verify.deConstantExact_serConstant value wire] at decoded
  have same : value = source := Except.ok.inj decoded
  rwa [same] at present

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

/-- The canonical family is physically selected when its payload is not an exact
fallback candidate. Its kind and nonempty inductive content come from the actual analysis. -/
theorem admitted_nonfallback_canonical_family {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source)
    (notFallback : (witness.prelude.records ++ witness.prelude.evidence).contains (owner, source) = false)
    {entry : RecEntry}
    (indexed : (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).index.recs[
      ConstRef.member owner slot]? = some entry) :
    ∃ familyRecord members,
      entry.block ∈ witness.order ∧ Ix.Cert.recordAt witness.env entry.block = some familyRecord ∧
      familyRecord.info = .muts members ∧ members.any (fun | .indc _ => true | _ => false) = true := by
  have origin := ReaderStoreTransfer.admitted_rec_entry_origin witness selected record member (.inl indexed)
  obtain ⟨carriers, analysis, _⟩ := origin
  obtain ⟨rawAnalysis, firstIndex, familyRecord, members, firstSlot, first, carrier, stored, kind, firstAt, _⟩ :=
    Ix.Cert.RecursorIndex.recursorAnalysis_spec.mp analysis
  have eligible := admitted_input_indexed witness selected record member
  obtain ⟨actual, actualPresent⟩ := input_indexed_family eligible notFallback member rawAnalysis carrier
  obtain ⟨familySelected, familyAt⟩ := Ix.Cert.RecursorIndex.mem_decoded.mp actualPresent
  have actualStored := ReaderStoreTransfer.selected
    (table := witness.table) (prelude := witness.prelude) familySelected familyAt
  have same : actual = familyRecord := Option.some.inj (actualStored.symm.trans stored)
  subst actual
  exact ⟨familyRecord, members, familySelected, familyAt, kind, hasInductive_of_first firstAt⟩

/-- Every selected non-fallback recursor has its actual successful payload reading in the
admission context, whether its index entry is canonical or a twin. -/
theorem admitted_nonfallback_rec_inputs {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source)
    (notFallback : (witness.prelude.records ++ witness.prelude.evidence).contains (owner, source) = false) :
    let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
    ∃ entry blockLps row,
      (cx.index.recs[ConstRef.member owner slot]? = some entry ∨
        cx.index.twins[ConstRef.member owner slot]? = some entry) ∧
      readRecursor cx blockLps (.member owner slot) entry = .ok row ∧
      Nonempty (RecursorReadInputs cx blockLps (.member owner slot) entry row) := by
  rcases admitted_rec_payload_inputs witness selected record member with
    ⟨entry, indexed⟩ | ⟨entry, blockLps, row, indexed, read, inputs⟩
  · obtain ⟨familyRecord, members, familySelected, familyAt, kind, hasInductive⟩ :=
      admitted_nonfallback_canonical_family witness selected record member notFallback indexed
    obtain ⟨blockLps, row, read, inputs⟩ :=
      admitted_inductive_canonical_inputs witness familySelected familyAt kind hasInductive indexed rfl
    exact ⟨entry, blockLps, row, .inl indexed, read, inputs⟩
  · exact ⟨entry, blockLps, row, .inr indexed, read, inputs⟩

/-- The remaining case is an exact committed fallback payload, identified from checked
bytes. It is not an unconstructed successful-read premise. -/
theorem admitted_rec_input_origin {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source) :
    let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
    (owner, source) ∈ witness.prelude.records ++ witness.prelude.evidence ∨
      ∃ entry blockLps row,
        (cx.index.recs[ConstRef.member owner slot]? = some entry ∨
          cx.index.twins[ConstRef.member owner slot]? = some entry) ∧
        readRecursor cx blockLps (.member owner slot) entry = .ok row ∧
        Nonempty (RecursorReadInputs cx blockLps (.member owner slot) entry row) := by
  by_cases contained : (witness.prelude.records ++ witness.prelude.evidence).contains (owner, source) = true
  · exact .inl (admitted_fallback_contains_exact witness selected record contained)
  · exact .inr (admitted_nonfallback_rec_inputs witness selected record member (Bool.eq_false_iff.mpr contained))

end IxVM.Refinement.Assembly
