import IxVMRefinement.Decl.NativeFront
import IxC.Kernel.Verify.Denote.TeleOpen

/-! # Semantic constructor stages from actual scoped outputs

The checked parameter-agreement trace supplies shared-parameter certificates. The constructor
output therefore builds the existing SumCtorRunJ relation directly at its actual environment.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal Expr Level)
open Ix.Kernel.Semantics (SumCtorRunJ SumCtorsRunJ)
open Ix.Kernel.Model (rulesJ)

/-- A concrete checked constructor output supplies its semantic stage, transporting only
semantic level equivalence when the former's chosen sort differs syntactically. -/
theorem NativeCtorOut.toSumCtorRunJ {env : Ix.Kernel.Env .anon} {T : KKey}
    {levels : List Ix.Kernel.LevelParam} {params indices : Nat} {observedSort sort : KLevel}
    {former : ConstantVal .anon} {raw : KExpr} {ctor annotated : KConstantVal × Nat} {sorts : List KLevel}
    (checked : NativeCtorOut env T levels params indices observedSort former.type raw ctor annotated sorts)
    (sortEq : LvEq observedSort sort) (closed : ctor.1.type.hasFvar = false) :
    SumCtorRunJ rulesJ env env T levels params indices sort
      (Level.isEquiv sort .zero == some true) false ctor.1 ctor.2 former annotated.1 sorts := by
  obtain ⟨_, _, binders, arguments, _, _, telescope, _, argumentCount, _⟩ := checked.residual
  obtain ⟨parameterVars, residual, fieldVars, indexArgs, parameterOpen, fieldOpen,
    indexCount, fieldResolve, indexResolve, fieldSorts⟩ := checked.opened
  obtain ⟨formerVars, formerResidual, formerOpen, _⟩ := checked.domsShared
  obtain ⟨formerBinders, formerBody, formerStrip, _⟩ :=
    Ix.Kernel.Verify.openPisAtFvars_stripPis params formerOpen
  obtain ⟨ctorBinders, ctorBody, ctorStrip, _⟩ :=
    Ix.Kernel.Verify.openPisAtFvars_stripPis params parameterOpen
  have annotatedClosed := annotates_hasFvar_false checked.stored.2.2 closed
  have shared := checked.domsShared.toSharedPins formerOpen parameterOpen formerStrip ctorStrip annotatedClosed
  exact ⟨⟨annotated.1, checked.cvCheck, .inl rfl⟩,
    ⟨binders, arguments, telescope, argumentCount⟩,
    parameterVars, residual, formerVars, formerResidual, fieldVars, indexArgs,
    parameterOpen, formerOpen, .inr shared, fieldOpen, indexCount, fieldResolve, indexResolve,
    fieldSortsJ_congr_sort sortEq fieldSorts⟩

/-- The whole actual constructor output family builds the semantic constructor pass. -/
theorem native_ctor_outputs_to_runs {env : Ix.Kernel.Env .anon} {T : KKey}
    {levels : List Ix.Kernel.LevelParam} {params indices : Nat} {observedSort sort : KLevel}
    {former : ConstantVal .anon} {ctors annotated : List (KConstantVal × Nat)}
    {rawTypes : List KExpr} {sortss : List (List KLevel)}
    (count : annotated.length = ctors.length) (sortCount : sortss.length = ctors.length)
    (outputs : ∀ slot < ctors.length, ∃ ctor stored sorts,
      ctors[slot]? = some ctor ∧ annotated[slot]? = some stored ∧ sortss[slot]? = some sorts ∧
      NativeCtorOut env T levels params indices observedSort former.type
        (rawTypes.getD slot default) ctor stored sorts)
    (sortEq : LvEq observedSort sort) (closed : ∀ ctor ∈ ctors, ctor.1.type.hasFvar = false) :
    SumCtorsRunJ rulesJ env env T levels params indices sort
      (Level.isEquiv sort .zero == some true) false former ctors annotated sortss := by
  refine ⟨count, sortCount, ?_⟩
  intro slot ctor stored atCtor atStored
  have inside : slot < ctors.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at atCtor
    cases atCtor
  obtain ⟨actual, actualStored, sorts, actualAt, storedAt, sortsAt, checked⟩ := outputs slot inside
  have same := Option.some.inj (actualAt.symm.trans atCtor)
  have sameStored := Option.some.inj (storedAt.symm.trans atStored)
  subst actual actualStored
  exact ⟨checked.nF_eq, sorts, sortsAt,
    checked.toSumCtorRunJ sortEq (closed ctor (List.mem_of_getElem? atCtor))⟩

end IxVM.Refinement.Decl
