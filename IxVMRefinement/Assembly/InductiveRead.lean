import IxVMRefinement.Assembly.ReadBare

/-! # Relating full and bare inductive lowerings

Both lowerings check the same block header. The full lowering additionally generates model
declarations; its bare counterpart retains the family's own declaration and the same distinct
public names.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel
open Ix.Kernel.Reader

theorem lowerInductiveDeclsBare_of_full {md : Mode} {st : State md}
    {rb : BlockRead md} {r : Read md}
    (h : lowerInductiveDecls st rb = .ok r) :
    ∃ bare, lowerInductiveDeclsBare rb = .ok bare := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  unfold lowerInductiveDecls at h
  unfold lowerInductiveDeclsBare
  simp only [ite_not, bne_iff_ne, ne_eq] at h ⊢
  rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hc, h⟩ | ⟨hc, h⟩
  all_goals
    simp only [hc, ↓reduceIte]
    obtain ⟨result, hloop, _⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    rw [hloop]
    exact ⟨_, rfl⟩

/-- Every successful full inductive lowering has a successful bare lowering. Its actual
generated prefix is kept separate from the bare declaration array. -/
theorem lowerInductive_full_bare {md : Mode} {st : State md}
    {rb : BlockRead md} {full : Read md}
    (h : lowerInductive st rb = .ok full) :
    ∃ (generated : List (Declaration md)) (bare : Read md),
      lowerInductiveBare rb = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧
      bare.generated = 0 ∧
      (∀ d ∈ generated, d.isGenerated = true) := by
  obtain ⟨generated, hdecls, hcount, _, _⟩ := Ix.Cert.CtxAgree.lowerInductive_ok h
  obtain ⟨bare, hbare⟩ := lowerInductiveDeclsBare_of_full
    (Ix.Cert.LowerDistinct.lowerInductiveDecls_of_ok h)
  obtain ⟨hzero, hbare_decls⟩ := lowerInductiveDeclsBare_spec hbare
  have hbare_eq : bare.decls = #[Ix.Cert.CtxAgree.indDeclOf rb] := hbare_decls
  have hnames := Ix.Cert.LowerDistinct.lowerInductive_names_nodup h
  rw [hdecls] at hnames
  simp only [Array.toList_push, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nodup_append] at hnames
  have hbare_names : (bare.decls.toList.flatMap Declaration.names).Nodup := by
    rw [hbare_eq]
    simpa using hnames.2.1
  have hdistinct := Ix.Cert.LowerDistinct.firstRepeatedKey_eq_none_iff.mpr hbare_names
  have hbare_run : lowerInductiveBare rb = .ok bare := by
    unfold lowerInductiveBare
    rw [hbare]
    simp only [bind, Except.bind, hdistinct, pure, Except.pure]
  refine ⟨generated, bare, hbare_run, ?_, hcount, hzero, ?_⟩
  · rw [hdecls, hbare_eq]
    simp
  · intro d hd
    apply Ix.Cert.SourceNames.lowerInductive_generated h d
    rw [hdecls, hcount]
    simpa using hd

end IxVM.Refinement.Assembly
