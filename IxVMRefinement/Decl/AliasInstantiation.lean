import IxVMRefinement.Decl.ReferenceDefinitionSorts
import IxC.Kernel.Verify.InstLevels

/-! # Universe instances of actually checked constant aliases

The alias front supplies the comparison of its declared sort with the target instance's
sort. The target's own level scope comes from the real environment invariant, and the body
application's level arity comes from its recorded inference. Together they justify composing
universe substitutions, including the binder zero-ness readout.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

/-- The actual delta step exposes the same substituted target levels, guarded by the use's
real universe arity. This equation does not assume that an ill-arity use unfolds. -/
theorem constant_alias_unfoldAt {md : Mode} {env : Env md} {aliasName targetName : Key md}
    {aliasCV : ConstantVal md} {bodyLevels useLevels : List Level} {hint : ReducibilityHint}
    (found : env.find? aliasName = some (.defnInfo aliasCV (.const targetName bodyLevels) hint)) :
    unfoldDefinition env (.const aliasName useLevels) =
      if useLevels.length = aliasCV.levelParams.length then
        some (.const targetName (bodyLevels.map (Level.subst aliasCV.levelParams useLevels)))
      else none := by
  simp only [unfoldDefinition, Expr.getAppFn, Expr.getAppArgs, found,
    Expr.instantiateLevelParams, Expr.mkAppN]

/-- Actual prefix typing and target scope determine the alias's zero-ness at every universe
instance. No substitution-closure premise or new annotation equality is supplied by the caller. -/
theorem DefinitionsTyped.polymorphic_alias_zero {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (definitions : DefinitionsTyped env)
    {aliasName targetName : Key .anon} {aliasCV targetCV : ConstantVal .anon}
    {bodyLevels : List Level} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared targetSort : Level}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName bodyLevels) hint))
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type = .sort targetSort) (useLevels : List Level) :
    Level.zeronessOf (Level.subst aliasCV.levelParams useLevels declared) =
      Level.zeronessOf (Level.subst targetCV.levelParams
        (bodyLevels.map (Level.subst aliasCV.levelParams useLevels)) targetSort) := by
  obtain ⟨_, _, _, _, _, bodyTyped, _, _, _⟩ := definitions aliasName aliasCV _ hint aliasFound
  obtain ⟨bodyCI, bodyFound, _, bodyArity, _⟩ := Rules.Infer.const_inv bodyTyped
  obtain rfl := Option.some.inj (bodyFound.symm.trans targetFound)
  have scoped : targetSort.allParamsDefined targetCV.levelParams = true := by
    have bounds := (model.base2.wf _ (List.mem_of_find?_eq_some targetFound)).2.1
    change targetCV.type.allLevelParamsDefined targetCV.levelParams = true at bounds
    rw [targetHeader] at bounds
    exact bounds
  have targetInstance : targetCV.type.instantiateLevelParams targetCV.levelParams bodyLevels =
      .sort (Level.subst targetCV.levelParams bodyLevels targetSort) := by rw [targetHeader]; rfl
  have original := (DefinitionsTyped.constant_alias_sort model definitions aliasFound targetFound
    aliasHeader targetInstance).2
  have instantiated := congrArg (Level.substPW aliasCV.levelParams useLevels) original
  rw [← Level.zeronessOf_subst, ← Level.zeronessOf_subst] at instantiated
  rw [Level.subst_subst bodyArity scoped] at instantiated
  exact instantiated

end IxVM.Refinement.Decl
