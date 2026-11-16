import IxVMRefinement.Assembly.AdmittedStoreTransfer
import IxVMRefinement.Assembly.RolePreludeBridge

/-! # Stored prelude projections in every admitted role environment

Non-mutual prelude records are bound roles, so admission stores them at their exact
committed bytes. Evidence records are definitions and cannot point to a different owner.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency

/-- Every committed prelude record outside a mutual block is selected and stored by the
admission witness, with the committed decoded value. -/
theorem admitted_prelude_nonmutual {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {a : _root_.Address} {c : Ixon.Constant}
    (present : (a, c) ∈ w.prelude.records) (nonmutual : ∀ ms, c.info ≠ .muts ms) :
    a ∈ w.order ∧ Ix.Cert.recordAt w.env a = some c := by
  obtain ⟨role, _, notTrust, bound⟩ := prelude_nonmutual_bound w.preludeRead present nonmutual
  have seed : IxVM.Refinement.BindingSeeds w.table a := .inl ⟨role, notTrust,
    Ix.Cert.ReadingKeys.addressOf_of_bound (check_of_admitBinding w.admitted) bound⟩
  have stored := w.seedsStored a seed
  have selected := (w.closure.complete a).mpr (.seed seed stored)
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?] at stored
  obtain ⟨lc, found⟩ := Option.isSome_iff_exists.mp stored
  have fallback : (a, c) ∈ w.prelude.records ++ w.prelude.evidence :=
    Array.mem_append.mpr (.inl present)
  have bytes := w.fallbackRecordsAgree a selected lc found c fallback
  have wire := (rolePreludeInputs.serConstant_mem_committedImages w.preludeRead fallback).2.2.1
  have cache : lc.get? = some c := by
    rw [w.coherent a lc found, bytes, Ixon.Verify.deConstantExact_serConstant c wire]
    rfl
  refine ⟨selected, ?_⟩
  unfold Ix.Cert.recordAt
  rw [found]
  exact cache

/-- A fallback record whose owner differs from its address belongs to the prelude:
every evidence row is a definition and owns itself. -/
theorem fallback_nonself_prelude {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) {a : _root_.Address} {c : Ixon.Constant}
    (found : Ix.Cert.EvidenceCheck.fallbackStore prelude a = some c)
    (nonself : Ix.Cert.ownerOf a c ≠ a) : (a, c) ∈ prelude.records := by
  have member := Ix.Cert.EvidenceCheck.fallbackStore_mem found
  rw [Array.toList_append, List.mem_append] at member
  rcases member with inPrelude | inEvidence
  · exact Array.mem_toList_iff.mp inPrelude
  · obtain ⟨_, evRecords⟩ := Ix.Cert.ReaderFallback.preludeFor_records prepared
    obtain ⟨evidence, evRead, _, definitions⟩ := RoleVal.evidenceRecords_spec
    have evEq : prelude.evidence = evidence := Except.ok.inj (evRecords.symm.trans evRead)
    rw [evEq] at inEvidence
    obtain ⟨definition, info⟩ := definitions (a, c) inEvidence
    dsimp only at info
    exact (nonself (by simp only [Ix.Cert.ownerOf, info])).elim

/-- A resolving fallback projection is already a selected admission row. -/
theorem admitted_fallback_nonself {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {a : _root_.Address} {c : Ixon.Constant}
    (found : Ix.Cert.EvidenceCheck.fallbackStore w.prelude a = some c)
    (nonself : Ix.Cert.ownerOf a c ≠ a) (nonmutual : ∀ ms, c.info ≠ .muts ms) :
    a ∈ w.order ∧ Ix.Cert.recordAt w.env a = some c :=
  admitted_prelude_nonmutual w (fallback_nonself_prelude w.preludeRead found nonself) nonmutual

end IxVM.Refinement.Assembly
