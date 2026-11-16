import IxVMRefinement.Decl.NativeCtorRun
import IxVMRefinement.Decl.NativeFieldUse

/-! # Native field classification from checked constructor outputs

The constructor check retains the type's scope and resolution evidence. For a non-indexed
constructor with at most one field, its checked return spine also discharges the dependency
condition, so classification and native field validation need no separate unused-field witness.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal Expr Level)

/-- Scope and resolution of the stored constructor type follow from its actual constant check. -/
theorem NativeCtorOut.typeProperties {env : Ix.Kernel.Env .anon} {T : KKey}
    {levels : List Ix.Kernel.LevelParam} {params indices : Nat} {sortLevel : KLevel}
    {former raw : KExpr} {ctor annotated : KConstantVal × Nat} {sorts : List KLevel}
    (checked : NativeCtorOut env T levels params indices sortLevel former raw ctor annotated sorts) :
    annotated.1.type.hasFvar = false ∧
      annotated.1.type.looseBVarsBounded 0 = true ∧
      annotated.1.type.allLevelParamsDefined ctor.1.levelParams = true ∧
      annotated.1.type.constsResolve env = true := by
  obtain ⟨type, ⟨_, _, _, _, bounded, closed, _, defined, resolved, _⟩, annotatedEq⟩ := checked.cvCheck
  have typeEq : annotated.1.type = type := by rw [annotatedEq]
  refine ⟨annotates_hasFvar_false checked.stored.2.2 closed,
    annotates_looseBVarsBounded checked.stored.2.2 0 bounded, ?_, ?_⟩
  · rwa [typeEq]
  · rwa [typeEq]

/-- An actual non-indexed output with at most one field supplies valid field kinds at the
original prefix, while its type check retains the selected former capabilities. -/
theorem NativeCtorOut.fieldKinds_single_field {env : Ix.Kernel.Env .anon}
    {former : ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon} {T : KKey}
    {levels : List Ix.Kernel.LevelParam} {params : Nat} {sortLevel : KLevel}
    {raw : KExpr} {ctor annotated : KConstantVal × Nat} {sorts : List KLevel}
    (checked : NativeCtorOut ⟨.indInfo former caps :: env.consts⟩ T levels params 0
      sortLevel former.type raw ctor annotated sorts)
    (store : Ix.Kernel.Open.StoreInv env) (named : former.name = T)
    (notBasis : Ix.Kernel.reservedBasisNames.contains former.name = false)
    (telescope : ∃ count binders level, former.type.stripPis count = some (binders, .sort level))
    (atMostOne : ctor.2 ≤ 1) :
    ∃ kinds,
      Ix.Kernel.recCtorKinds T levels params 0 annotated = some kinds ∧
      kinds.length = annotated.2 ∧
      (∀ kind ∈ kinds, kind ≠ .negative ∧ kind ≠ .unsupported) ∧
      Ix.Kernel.nativeOpenedOk env T levels params 0 annotated.1.type annotated.2 kinds = true := by
  obtain ⟨_, _, binders, arguments, _, _, stripped, _, argumentCount, noSelf, positive, _⟩ :=
    checked.residual
  obtain ⟨_, _, inferred, _⟩ := checked.inferSort
  have properties := checked.typeProperties
  have literals := litResolve_of_infer_cons_former (ci := .indInfo former caps)
    store rfl notBasis telescope inferred properties.1
  have stripped' : annotated.1.type.stripPis (params + annotated.2) =
      some (binders, Expr.mkAppN (.const T (levels.map .param))
        (Ix.Kernel.structPsAt annotated.2 params ++ arguments)) := by
    rwa [checked.nF_eq]
  have positive' : ∀ index < annotated.2,
      Ix.Kernel.recFieldKind T levels params 0 index (binders.getD (params + index) default).1 ≠ .negative ∧
      Ix.Kernel.recFieldKind T levels params 0 index (binders.getD (params + index) default).1 ≠ .unsupported := by
    rw [checked.nF_eq]
    exact positive
  exact recCtorKinds_and_nativeOpenedOk (ci := .indInfo former caps) rfl named stripped'
    argumentCount noSelf properties.1 properties.2.2.2 literals positive'
    (fun index inside _ => checked.unused_single_field rfl (by rw [checked.nF_eq]; exact atMostOne) index inside)

/-- A complete actual non-indexed constructor family with at most one field per constructor
constructs both the field classification and the native field check at the original prefix. -/
theorem native_ctor_outputs_classified_single_field {env : Ix.Kernel.Env .anon}
    {former : ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon} {T : KKey}
    {levels : List Ix.Kernel.LevelParam} {params : Nat} {sortLevel : KLevel}
    {ctors annotated : List (KConstantVal × Nat)} {rawTypes : List KExpr} {sortss : List (List KLevel)}
    (count : annotated.length = ctors.length)
    (outputs : ∀ slot < ctors.length, ∃ ctor stored sorts,
      ctors[slot]? = some ctor ∧ annotated[slot]? = some stored ∧ sortss[slot]? = some sorts ∧
      NativeCtorOut ⟨.indInfo former caps :: env.consts⟩ T levels params 0 sortLevel former.type
        (rawTypes.getD slot default) ctor stored sorts)
    (store : Ix.Kernel.Open.StoreInv env) (named : former.name = T)
    (notBasis : Ix.Kernel.reservedBasisNames.contains former.name = false)
    (telescope : ∃ arity binders level, former.type.stripPis arity = some (binders, .sort level))
    (atMostOne : ∀ ctor ∈ ctors, ctor.2 ≤ 1) :
    ∃ kinds,
      Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) T levels params 0 annotated = .ok kinds ∧
      Ix.Kernel.nativeFieldsOk env T levels params 0 annotated kinds = true := by
  have classified : ∀ index : Fin annotated.length, ∃ kinds,
      Ix.Kernel.recCtorKinds T levels params 0 annotated[index.val] = some kinds ∧
      kinds.length = annotated[index.val].2 ∧
      (∀ kind ∈ kinds, kind ≠ .negative ∧ kind ≠ .unsupported) ∧
      Ix.Kernel.nativeOpenedOk env T levels params 0 annotated[index.val].1.type
        annotated[index.val].2 kinds = true := by
    intro ⟨slot, bound⟩
    have inside : slot < ctors.length := by omega
    obtain ⟨ctor, stored, sorts, ctorAt, storedAt, _, checked⟩ := outputs slot inside
    have storedEq : stored = annotated[slot] :=
      Option.some.inj (storedAt.symm.trans (List.getElem?_eq_getElem bound))
    subst stored
    exact checked.fieldKinds_single_field store named notBasis telescope
      (atMostOne ctor (List.mem_of_getElem? ctorAt))
  let kinds := (List.finRange annotated.length).map fun index => Classical.choose (classified index)
  have allKinds : List.Forall₂
      (fun stored ks =>
        Ix.Kernel.recCtorKinds T levels params 0 stored = some ks ∧
        ks.length = stored.2 ∧
        (∀ kind ∈ ks, kind ≠ .negative ∧ kind ≠ .unsupported) ∧
        Ix.Kernel.nativeOpenedOk env T levels params 0 stored.1.type stored.2 ks = true)
      annotated kinds := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [kinds], fun slot inside _ => ?_⟩
    have specification := Classical.choose_spec (classified ⟨slot, inside⟩)
    have selected : kinds[slot] = Classical.choose (classified ⟨slot, inside⟩) := by simp [kinds]
    simpa [selected] using specification
  exact ⟨kinds, classifyFixKinds_and_nativeFieldsOk allKinds⟩

end IxVM.Refinement.Decl
