import IxVMRefinement.RoleVal.ReaderTableDecide
import Ix.Cert.EvidenceCheck
import Ix.Cert.ReaderFallback

/-! # Owner closure of the actual committed fallback

Prelude projections point to prelude records. Committed evidence rows are definitions, whose
owner is their own address. The proof uses the already kernel-checked committed data.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

private theorem lookup_member {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {rows : List (α × β)} {key : α} {value : β},
      rows.lookup key = some value → (key, value) ∈ rows
  | [], _, _, h => nomatch h
  | (first, val) :: rest, key, value, h => by
    rw [List.lookup_cons] at h
    cases same : key == first with
    | true =>
      rw [same] at h
      cases h
      rw [beq_iff_eq.mp same]
      exact List.mem_cons_self
    | false =>
      rw [same] at h
      exact List.mem_cons_of_mem _ (lookup_member h)

private theorem committed_prelude_owner_member {a : _root_.Address} {c : Ixon.Constant}
    (member : (a, c) ∈ RoleVal.committedPreludeList) :
    ∃ ownerRecord, (Ix.Cert.ownerOf a c, ownerRecord) ∈ RoleVal.committedPreludeList := by
  have checked := List.all_eq_true.mp RoleVal.preRefsAndProjClosed (a, c) member
  have projection := (Bool.and_eq_true.mp checked).2
  have ownerMember : Ix.Cert.ownerOf a c ∈ RoleVal.committedPreAddrs := by
    cases info : c.info with
    | dPrj p | iPrj p | rPrj p | cPrj p =>
      simp only [Ix.Cert.ownerOf, info]
      rw [info] at projection
      rw [RoleVal.containsAddrFast_eq, List.contains_iff_mem] at projection
      exact projection
    | defn _ | recr _ | axio _ | quot _ | muts _ =>
      simp only [Ix.Cert.ownerOf, info]
      exact List.mem_map.mpr ⟨(a, c), member, rfl⟩
  obtain ⟨⟨owner, ownerRecord⟩, stored, same⟩ := List.mem_map.mp ownerMember
  dsimp only at same
  subst owner
  exact ⟨ownerRecord, stored⟩

/-- Every record returned by the actual prelude/evidence fallback has a stored owner. -/
theorem fallback_owner_stored {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) {a : _root_.Address} {c : Ixon.Constant}
    (found : Ix.Cert.EvidenceCheck.fallbackStore prelude a = some c) :
    ∃ ownerRecord,
      Ix.Cert.EvidenceCheck.fallbackStore prelude (Ix.Cert.ownerOf a c) = some ownerRecord := by
  obtain ⟨preRecords, evRecords⟩ := Ix.Cert.ReaderFallback.preludeFor_records prepared
  have preEq : prelude.records = RoleVal.committedPrelude :=
    Except.ok.inj (preRecords.symm.trans RoleVal.preludeRecords_eq)
  obtain ⟨evidence, evRead, _, definitions⟩ := RoleVal.evidenceRecords_spec
  have evEq : prelude.evidence = evidence := Except.ok.inj (evRecords.symm.trans evRead)
  have lookup := found
  change (recordMap (prelude.records ++ prelude.evidence))[a]? = some c at lookup
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get] at lookup
  have member := lookup_member lookup
  rw [Array.toList_append, List.mem_append] at member
  rcases member with inPrelude | inEvidence
  · rw [preEq] at inPrelude
    have committed : (a, c) ∈ RoleVal.committedPreludeList := by
      simpa only [RoleVal.committedPrelude, List.toList_toArray] using inPrelude
    obtain ⟨ownerRecord, ownerMember⟩ := committed_prelude_owner_member committed
    refine ⟨ownerRecord, ?_⟩
    change (recordMap (prelude.records ++ prelude.evidence))[Ix.Cert.ownerOf a c]? = some ownerRecord
    rw [Ix.Cert.ReaderClosureKeys.recordMap_get]
    apply Ix.Cert.ReaderClosureKeys.lookup_of_nodup (Ix.Cert.ReaderFallback.preludeFor_keys prepared)
    rw [Array.toList_append]
    apply List.mem_append_left
    rw [preEq]
    simpa only [RoleVal.committedPrelude, List.toList_toArray] using ownerMember
  · rw [evEq] at inEvidence
    obtain ⟨definition, info⟩ := definitions (a, c) inEvidence
    exact ⟨c, by simpa only [Ix.Cert.ownerOf, info] using found⟩

end IxVM.Refinement.Assembly
