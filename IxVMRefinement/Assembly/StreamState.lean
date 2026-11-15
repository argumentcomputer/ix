import IxVMRefinement.Assembly.RecordState

/-! # Constructing a bare stream from its full reader run

The same records and context are replayed with generated declarations omitted. The output
is an actual bare declaration array, and a sublist of the full array. Restricting the input
order and its recursor index is a separate construction.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.Cert.ReaderUnits (RolesKeyed)

private theorem note_projRewrites (st : State md) (d : CDecl md) :
    (st.note d).projRewrites = st.projRewrites := by
  cases d <;> (refine Ix.Cert.CtxAgree.foldl_keep State.projRewrites _ (fun _ _ => ?_) _ _; rfl)

private theorem noteGenerated_projRewrites (st : State md) (d : CDecl md) :
    (st.noteGenerated d).projRewrites = st.projRewrites := by
  unfold State.noteGenerated
  (split <;> (try split) <;> (try split)) <;> simp only [note_projRewrites]

theorem commit_projRewrites (st : State md) (r : Read md) :
    (st.commit r).projRewrites = st.projRewrites + r.projRewrites := by
  rw [Ix.Cert.CtxAgree.commit_eq]
  dsimp only
  rw [Ix.Cert.CtxAgree.foldl_keep State.projRewrites _
    (fun s x => by split <;> simp only [noteGenerated_projRewrites, note_projRewrites])]
  rw [Ix.Cert.CtxAgree.commit_pre_keep State.projRewrites r st (fun _ _ => rfl) (fun _ _ => rfl)]

theorem streamRead_projRewrites_le {md : Mode} {cx : Ctx md} {source final : State md}
    {records : List (_root_.Address × Ixon.Constant)} {decls : Array (CDecl md)}
    (h : StreamRead cx source records final decls) : source.projRewrites ≤ final.projRewrites := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ ih =>
    rw [commit_projRewrites] at ih
    omega

/-- A full stream with zero projection rewrites has a concrete bare replay. Only actual
generated prefixes are omitted, and the final public heights agree with the checked run. -/
theorem streamRead_full_bare {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source final target : State md} {records : List (_root_.Address × Ixon.Constant)}
    {fullDecls : Array (CDecl md)} (h : StreamRead cx source records final fullDecls)
    (hzero : final.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none) :
    ∃ bareFinal bareDecls, StreamReadBare cx target records bareFinal bareDecls ∧
      (∀ (k : CName md), NonAuxKey k → bareFinal.heights[k]? = final.heights[k]?) ∧
      bareDecls.toList.Sublist fullDecls.toList := by
  induction h generalizing target with
  | nil => exact ⟨target, #[], .nil, hh, List.Sublist.refl _⟩
  | @cons source final owner c full rest fullTail hread htail ih =>
    have hcounter := streamRead_projRewrites_le htail
    rw [commit_projRewrites, hzero] at hcounter
    have hrecordZero : full.projRewrites = 0 := by omega
    obtain ⟨generated, bare, hbare, hdecls, _, hbareGen, hgenerated⟩ :=
      readRecord_full_bare_replay hrk hread hrecordZero hh hempty
    have hheights := commit_heights_after_generated_prefix hdecls hgenerated hh
    have hlevels : ∀ (k : CName md), (target.commit bare).projLevels[k]? = none := by
      intro k
      rw [projLevels_commit_of_generated_zero target hbareGen]
      exact hempty k
    obtain ⟨bareFinal, bareTail, htailBare, hheightsFinal, hsubTail⟩ :=
      ih hzero hheights hlevels
    refine ⟨bareFinal, bare.decls ++ bareTail, .cons hbare htailBare, hheightsFinal, ?_⟩
    rw [Array.toList_append, Array.toList_append]
    apply List.Sublist.append _ hsubTail
    rw [hdecls]
    exact List.sublist_append_right _ _

end IxVM.Refinement.Assembly
