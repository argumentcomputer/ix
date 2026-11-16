import IxVMRefinement.Decl.NativeConstructorFieldChecks
import IxVMRefinement.Decl.ReferenceDefinitionSorts

/-! # A checked-prefix producer for beta/alias field correspondence

The reference replay supplies the alias's original definition check, and the constructor
run supplies both actual domain checks. For a constant-body beta redex followed by that
alias, these checks force the old and final product annotations to carry the same datum.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

/-- Construct the original/final field frames and the beta/alias metadata correspondence from
actual prefix, former, and constructor checks. The original header retains reader storage shape. -/
theorem ReferenceReplay.constructor_beta_alias_correspondence {V : Type u} [SetTheory V]
    {replayFuel : Nat} {ev : Evidences .anon} {sourceOut targetOut env : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay replayFuel ev Env.empty Env.empty declarations sourceOut targetOut)
    {formerFuel : Nat} {p completed : InductiveShape .anon} {checkedFormer : ConstantVal .anon}
    {capsOf : InductiveShape .anon → IndCaps .anon}
    (formerRun : checkSumInd (fueledOps .verified formerFuel) targetOut p capsOf =
      .ok (env, checkedFormer, completed))
    (model : EnvModelM V .verified env)
    {T : Key .anon} {levels : List LevelParam} {nP nIdx nF fuel : Nat} {sortLevel : Level}
    {isProp large : Bool} {raw checked : ConstantVal .anon} {sorts : List Level}
    (constructorRun : checkSumCtor (fueledOps .verified fuel) targetOut env T levels nP nIdx sortLevel
      isProp large raw nF checkedFormer = .ok (checked, sorts))
    {name bodyName : Key .anon} {cv : ConstantVal .anon} {bodyCI : ConstantInfo .anon}
    {bodyLevels : List Level} {hint : ReducibilityHint} {declared actual : Level}
    (aliasFound : env.find? name = some (.defnInfo cv (.const bodyName bodyLevels) hint))
    (noLevels : cv.levelParams = [])
    (bodyFound : env.find? bodyName = some bodyCI)
    (header : cv.type = .sort declared)
    (bodyHeader : bodyCI.toConstantVal.type.instantiateLevelParams bodyCI.toConstantVal.levelParams bodyLevels =
      .sort actual) :
    ∃ initial originalVars originalResidual finalVars finalResidual,
      checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      IxVM.Consistency.ValStored initial raw ∧
      openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual) ∧
      openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual) ∧
      ∀ (j : Nat) (original final : Expr .anon), originalVars[j]? = some original → finalVars[j]? = some final →
        ∀ (inputDomain outputDomain betaDomain betaArgument : Expr .anon)
          (beforeMeta afterMeta lambdaMeta : BinderMeta),
          original.fvarTypeD = .forallE inputDomain
            (.app (.lam betaDomain (.const name []) lambdaMeta) betaArgument) beforeMeta →
          final.fvarTypeD = .forallE outputDomain (.const bodyName bodyLevels) afterMeta →
          beforeMeta.pw = afterMeta.pw := by
  have typed := replay.constructor_definitionsTyped formerRun
  obtain ⟨initial, originalVars, originalResidual, finalVars, finalResidual,
      first, originalOpen, finalOpen, _, _, domains⟩ :=
    checkSumCtor_paired_domain_checks model.base2.wf constructorRun
  refine ⟨initial, originalVars, originalResidual, finalVars, finalResidual,
    first, NativeFormerRestore.initiallyStored first, originalOpen, finalOpen, ?_⟩
  intro j original final originalAt finalAt inputDomain outputDomain betaDomain betaArgument
    beforeMeta afterMeta lambdaMeta originalShape finalShape
  obtain ⟨_, _, _, _, beforeInfer, _, afterInfer, _⟩ := domains j original final originalAt finalAt
  rw [originalShape] at beforeInfer
  rw [finalShape] at afterInfer
  exact DefinitionsTyped.beta_constant_alias_binder_pw model typed aliasFound noLevels bodyFound header bodyHeader
    (Ix.Kernel.Rules.inferTypeCore_bridge beforeInfer) (Ix.Kernel.Rules.inferTypeCore_bridge afterInfer)

end IxVM.Refinement.Decl
