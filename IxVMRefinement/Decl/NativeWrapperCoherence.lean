import IxVMRefinement.Decl.ReferenceDefinitionSorts

/-! # Sort coherence for checked universe-preserving type wrappers

The application check compares its argument's actual inferred type with the wrapper's
universe domain. When normalization exposes that family application, the retained comparison
fixes its universe and therefore the datum a surrounding product check validates.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term
open Ix.Kernel.Model.Rules (Frame)

universe u

/-- A sort conversion at any depth equates its levels. The two closed sort subjects can be
read in an inhabited context of that length, so no satisfiability of a caller's context is assumed. -/
theorem converted_sort_levels_at {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {left right : Level}
    (converted : Ix.Kernel.Rules.DefEq env depth (.sort left) (.sort right))
    (φ : LevelParam → Nat) : left.eval φ = right.eval φ := by
  let context : List AnnotTerm := List.replicate depth (.sort 0)
  have satisfied : Sat V context (fun _ => SetTheory.empty) := by
    intro i entry atIndex
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp (List.mem_of_getElem? atIndex)
    exact SetTheory.empty_mem_univ 0
  have leftFrame : Frame depth (Expr.sort left : Expr md) := .of_not_hasFvar rfl rfl
  have rightFrame : Frame depth (Expr.sort right : Expr md) := .of_not_hasFvar rfl rfl
  have leftContext : CtxOk model.base2 φ depth context (.sort left) :=
    CtxOk.of_fvarLeaves_nil (by simp only [context, List.length_replicate])
      (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  have rightContext : CtxOk model.base2 φ depth context (.sort right) :=
    CtxOk.of_fvarLeaves_nil (by simp only [context, List.length_replicate])
      (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  have equal := Ix.Kernel.Model.Rules.defeq_sound (φ := φ)
    (fun ψ => Ix.Kernel.Model.Rules.RulesInputs.ofSem model ψ) converted
    leftFrame rightFrame leftContext rightContext (denoteMeta_sort _ _ _) (denoteMeta_sort _ _ _)
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ _ => ⟨trivial, trivial⟩)
  apply SetTheory.univ_inj (V := V)
  simpa only [interp_sort] using equal _ satisfied

/-- Actual inference reads a fully applied family at its stored telescope's result sort. -/
theorem infer_family_application_sort {md : Mode} {env : Env md} {depth : Nat}
    {subject inferred : Expr md} {name : Key md} {levels : List Level} {ci : ConstantInfo md}
    {binders : List (Expr md × BinderMeta)} {sortLevel : Level}
    (typed : Ix.Kernel.Rules.Infer env .full depth subject inferred)
    (head : subject.getAppFn = .const name levels)
    (found : env.find? name = some ci)
    (header : (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams levels).stripPis
      subject.getAppArgs.length = some (binders, .sort sortLevel)) :
    inferred = .sort sortLevel := by
  have named : Ix.Kernel.Rules.Infer env .full depth (Expr.mkAppN (.const name levels) subject.getAppArgs) inferred := by
    rw [← head, Expr.mkAppN_getApp]
    exact typed
  exact judgeInv_rulesJ.infer_spine_sort named found header

/-- The actual wrapper application fixes the inferred universe of its family argument.
This uses its own argument conversion, not an annotation-to-conversion principle. -/
theorem checked_type_wrapper_sort {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat}
    {wrapper family : Key md} {wrapperLevels familyLevels : List Level}
    {wrapperCI familyCI : ConstantInfo md} {wrapperMeta : BinderMeta}
    {wrapperSort familySort : Level} {argument inferred : Expr md}
    {familyBinders : List (Expr md × BinderMeta)}
    (wrapperFound : env.find? wrapper = some wrapperCI)
    (wrapperHeader : wrapperCI.toConstantVal.type.instantiateLevelParams
      wrapperCI.toConstantVal.levelParams wrapperLevels = .forallE (.sort wrapperSort) (.sort wrapperSort) wrapperMeta)
    (familyFound : env.find? family = some familyCI)
    (argumentHead : argument.getAppFn = .const family familyLevels)
    (familyHeader : (familyCI.toConstantVal.type.instantiateLevelParams familyCI.toConstantVal.levelParams familyLevels).stripPis
      argument.getAppArgs.length = some (familyBinders, .sort familySort))
    (typed : Ix.Kernel.Rules.Infer env .full depth (.app (.const wrapper wrapperLevels) argument) inferred) :
    inferred = .sort wrapperSort ∧
      (∀ φ : LevelParam → Nat, wrapperSort.eval φ = familySort.eval φ) ∧
      Level.zeronessOf wrapperSort = Level.zeronessOf familySort := by
  obtain ⟨_, _, _, _, argumentType, functionTyped, functionReduced, argumentTyped, argumentCompared, result⟩ :=
    Ix.Kernel.Rules.Infer.app_inv typed
  obtain ⟨foundWrapper, found, _, _, functionType⟩ := Ix.Kernel.Rules.Infer.const_inv functionTyped
  have same : foundWrapper = wrapperCI := Option.some.inj (found.symm.trans wrapperFound)
  subst foundWrapper
  rw [functionType, wrapperHeader] at functionReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Ix.Kernel.Rules.Red.rigid functionReduced rfl)
  have argumentTypeEq := infer_family_application_sort argumentTyped argumentHead familyFound familyHeader
  rw [argumentTypeEq] at argumentCompared
  have levelsEqual : ∀ φ : LevelParam → Nat, wrapperSort.eval φ = familySort.eval φ :=
    fun φ => (converted_sort_levels_at model argumentCompared φ).symm
  refine ⟨by simpa only [Expr.instantiate1] using result, levelsEqual, ?_⟩
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound, levelsEqual φ]

end IxVM.Refinement.Decl
