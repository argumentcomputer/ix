import IxVMRefinement.RoleVal.CommittedBase
import IxVMRefinement.RoleVal.CommittedPrelude
import IxVMRefinement.RoleVal.CommittedEv0
import IxVMRefinement.RoleVal.CommittedEv1
import IxVMRefinement.RoleVal.CommittedEv2
import IxVMRefinement.RoleVal.CommittedEv3
import IxVMRefinement.RoleVal.CommittedEv4

/-! # Kernel-verified decoding and hashing of `RoleData` (`table`, `prelude`, `evidence`, `blobs`)

Umbrella module combining `CommittedBase`, `CommittedPrelude`, and `CommittedEv0..4`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 500000

namespace IxVM.Refinement.RoleVal

def rawEvRows : List (List UInt8 × List (List UInt8)) :=
  rawEvRows_0 ++ (rawEvRows_1 ++ (rawEvRows_2 ++ (rawEvRows_3 ++ rawEvRows_4)))

def committedEvAddrs : List _root_.Address :=
  rawEvRows.map fun p => mkAddr p.1

private theorem roleData_evidence_eq :
    Ix.Kernel.Reader.RoleData.evidence = (rawEvRows.map fun p => hexRowOfChunks p.1 p.2).toArray :=
  Eq.refl Ix.Kernel.Reader.RoleData.evidence

private theorem rawEvRows_all_spec : ∀ r ∈ rawEvRows, EvRowSpec r := by
  intro r hr
  unfold rawEvRows at hr
  rcases List.mem_append.mp hr with h0 | h14
  · exact evRows_spec_0 r h0
  · rcases List.mem_append.mp h14 with h1 | h24
    · exact evRows_spec_1 r h1
    · rcases List.mem_append.mp h24 with h2 | h34
      · exact evRows_spec_2 r h2
      · rcases List.mem_append.mp h34 with h3 | h4
        · exact evRows_spec_3 r h3
        · exact evRows_spec_4 r h4

theorem evidenceRecords_spec :
    ∃ ev : Array (_root_.Address × Ixon.Constant),
      Ix.Kernel.Reader.evidenceRecords = .ok ev ∧
      ev.toList.map Prod.fst = committedEvAddrs ∧
      ∀ p ∈ ev.toList, ∃ d, p.2.info = .defn d := by
  obtain ⟨_, out, hf, hfst, hdefn⟩ := evRows_spec_of_forall rawEvRows_all_spec
  refine ⟨out.toArray, ?_, ?_, ?_⟩
  · exact Eq.trans rfl
      (Eq.trans
        (congrArg (Ix.Kernel.Reader.decodeCommitted "evidence") roleData_evidence_eq)
        (decodeCommitted_of_forall₂ "evidence" hf))
  · simpa [committedEvAddrs] using hfst
  · intro p hp
    exact hdefn p (by simpa using hp)

/-- Unconditional proof of `Ix.Cert.RoleClosure.FallbackHashed`. -/
theorem fallbackHashed : Ix.Cert.RoleClosure.FallbackHashed := by
  intro row hmem
  rw [Array.toList_append, List.mem_append] at hmem
  rcases hmem with hpre | hev
  · exact preludeRowsHashed row hpre
  · exact (evRows_spec_of_forall rawEvRows_all_spec).1 row
      (mem_of_array_eq roleData_evidence_eq hev)

end IxVM.Refinement.RoleVal
