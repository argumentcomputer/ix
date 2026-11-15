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

theorem readRecord_suffix_notGenerated {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {st : State md} {owner : _root_.Address} {c : Ixon.Constant} {r : Read md}
    (h : readRecord cx st owner c = .ok r) :
    ∀ d ∈ r.decls.toList.drop r.generated, d.isGenerated = false := by
  intro d hd
  rcases Ix.Cert.ReaderUnits.readRecord_lowering h with ⟨hzero, hnames⟩ |
      ⟨generated, suffix, hdecls, hcount, _, hnames⟩
  · rw [hzero, List.drop_zero] at hd
    exact Ix.Cert.ReaderUnits.isGenerated_false fun k hk => (hnames d hd k hk).not_derived hrk
  · rw [hdecls, hcount, List.drop_left] at hd
    exact Ix.Cert.ReaderUnits.isGenerated_false fun k hk => (hnames d hd k hk).not_derived hrk

theorem readRecord_bare_filter {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {st : State md} {owner : _root_.Address} {c : Ixon.Constant} {full bare : Read md}
    (hread : readRecord cx st owner c = .ok full) {generated : List (CDecl md)}
    (hdecls : full.decls.toList = generated ++ bare.decls.toList)
    (hcount : full.generated = generated.length)
    (hgenerated : ∀ d ∈ generated, d.isGenerated = true) :
    full.decls.toList.filter (fun d => !d.isGenerated) = bare.decls.toList := by
  have hbare : ∀ d ∈ bare.decls.toList, d.isGenerated = false := by
    intro d hd
    apply readRecord_suffix_notGenerated hrk hread d
    rw [hdecls, hcount, List.drop_left]
    exact hd
  have hgenFilter : generated.filter (fun d => !d.isGenerated) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd hpass
    simp [hgenerated d hd] at hpass
  have hbareFilter : bare.decls.toList.filter (fun d => !d.isGenerated) = bare.decls.toList :=
    List.filter_eq_self.mpr fun d hd => by simp [hbare d hd]
  rw [hdecls, List.filter_append, hgenFilter, hbareFilter, List.nil_append]

/-- The constructed bare output is exactly the full output with generated declarations
filtered out, including when one input record emits several public declarations. -/
theorem streamReadBare_filter_full {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source final target bareFinal : State md} {records : List (_root_.Address × Ixon.Constant)}
    {fullDecls bareDecls : Array (CDecl md)} (h : StreamRead cx source records final fullDecls)
    (hzero : final.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none)
    (hbare : StreamReadBare cx target records bareFinal bareDecls) :
    fullDecls.toList.filter (fun d => !d.isGenerated) = bareDecls.toList := by
  induction h generalizing target bareFinal bareDecls with
  | nil => cases hbare; rfl
  | @cons source final owner c full rest fullTail hread htail ih =>
    obtain ⟨actual, actualTail, hactual, htailBare, rfl⟩ := streamReadBare_cons_inv hbare
    have hcounter := streamRead_projRewrites_le htail
    rw [commit_projRewrites, hzero] at hcounter
    have hrecordZero : full.projRewrites = 0 := by omega
    obtain ⟨generated, bare, hbare, hdecls, hcount, hbareGen, hgenerated⟩ :=
      readRecord_full_bare_replay hrk hread hrecordZero hh hempty
    have heq := Except.ok.inj (hactual.symm.trans hbare)
    subst actual
    have hheights := commit_heights_after_generated_prefix hdecls hgenerated hh
    have hlevels : ∀ (k : CName md), (target.commit bare).projLevels[k]? = none := by
      intro k
      rw [projLevels_commit_of_generated_zero target hbareGen]
      exact hempty k
    rw [Array.toList_append, List.filter_append, Array.toList_append,
      readRecord_bare_filter hrk hread hdecls hcount hgenerated,
      ih hzero hheights hlevels htailBare]

/-- The approved coherent admission witness supplies an actual, separately constructed
bare role stream. Its declarations are the generated-declaration filter of the checked stream. -/
theorem admitted_streamReadBare {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
    ∃ final decls, StreamReadBare cx w.prelude.state (Ix.Cert.Stream.decodedOf w.env w.order)
      final decls ∧ w.fullDecls.toList.filter (fun d => !d.isGenerated) = decls.toList := by
  dsimp only
  have hrk := streamContext_rolesKeyed _root_.Address.admissionHash w.table w.prelude
    (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
  have hstream := readRecords_spec w.read
  have hheight : ∀ k : CName .anon, NonAuxKey k → w.prelude.state.heights[k]? = w.prelude.state.heights[k]? :=
    fun _ _ => rfl
  have hlevels := preludeFor_projLevels_empty w.preludeRead
  obtain ⟨final, decls, hbare, _, _⟩ := streamRead_full_bare hrk hstream w.noProjRewrites hheight hlevels
  exact ⟨final, decls, hbare, streamReadBare_filter_full hrk hstream w.noProjRewrites hheight hlevels hbare⟩

end IxVM.Refinement.Assembly
