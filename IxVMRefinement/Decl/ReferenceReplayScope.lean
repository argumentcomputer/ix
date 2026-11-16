import IxVMRefinement.Decl.ReferenceFold

/-! # Raw definition types at their actual reference prefix -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- The actual prefix model and checking front supply raw type support at its declared scope. -/
theorem ReferenceReplay.definition_type_scope {V : Type u} [SetTheory V]
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty declarations sourceOut targetOut)
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint}
    (member : Declaration.defnDecl cv value hint ∈ declarations) :
    ∃ before after sourceBefore targetBefore sourceAfter targetAfter,
      declarations = before ++ .defnDecl cv value hint :: after ∧
      ReferenceReplay fuel ev Env.empty Env.empty before sourceBefore targetBefore ∧
      checkDecl .verified (fueledOps .verified fuel) ev sourceBefore (.defnDecl cv value hint) =
        .ok sourceAfter ∧
      CheckedReferenceStep fuel targetBefore (.defnDecl cv value hint) targetAfter ∧
      ReferenceReplay fuel ev sourceAfter targetAfter after sourceOut targetOut ∧
      cv.type.Good (nameScope (before.flatMap Declaration.names)) := by
  obtain ⟨before, after, sourceBefore, targetBefore, sourceAfter, targetAfter,
    split, prefixRun, sourceStep, targetStep, suffixRun⟩ := replay.declarationStep member
  have prefixModel : EnvModelT V .verified targetBefore := prefixRun.checked.envModelT EnvModelT.empty
  obtain ⟨⟨model, _⟩, _⟩ := prefixModel
  have store : Ix.Kernel.Open.StoreInv targetBefore :=
    ⟨model.base2.wf, model.base2.rec_ctors, model.base2.proj_ok⟩
  obtain ⟨type, value', header, _, _, _, _⟩ := targetStep.definition
  exact ⟨before, after, sourceBefore, targetBefore, sourceAfter, targetAfter,
    split, prefixRun, sourceStep, targetStep, suffixRun,
    constantValRun_good_input store prefixRun.declaredScope header⟩

end IxVM.Refinement.Decl
