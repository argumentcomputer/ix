import IxVMRefinement.Decl.TelescopeResultSort

/-! # Product metadata retained by checked type constructors

A definition front checks the value and compares its inferred type with the declared type.
If the value's lambda telescope returns a product, inference fixes that product's datum.
The actual telescope conversion then identifies its result sort with the declared one,
even when the formal parameter types are dependent or only convertible.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

private theorem stripLams_instantiate_result {md : Mode} (value : Expr md) :
    ∀ {count : Nat} {e output : Expr md} {binders : List (Expr md × BinderMeta)} (cut : Nat),
      e.stripLams count = some (binders, output) →
      ∃ openedBinders, (e.instantiate1 value cut).stripLams count =
        some (openedBinders, output.instantiate1 value (cut + count))
  | 0, _, _, _, cut, stripped => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj stripped)
    exact ⟨[], by simp only [Expr.stripLams, Nat.add_zero]⟩
  | count + 1, e, _, _, cut, stripped => by
    cases e with
    | lam domain body bm =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at stripped
      obtain ⟨⟨tail, output⟩, bodyStrip, same⟩ := stripped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      obtain ⟨openedTail, opened⟩ := stripLams_instantiate_result value (cut + 1) bodyStrip
      refine ⟨(domain.instantiate1 value cut, bm) :: openedTail, ?_⟩
      simpa only [Expr.instantiate1, Expr.stripLams, opened, Option.map_some, Nat.add_succ, Nat.succ_add]
    | _ => cases stripped

private theorem stripPis_abstract_result {md : Mode} (index : Nat) :
    ∀ {count : Nat} {e output : Expr md} {binders : List (Expr md × BinderMeta)} (cut : Nat),
      e.stripPis count = some (binders, output) →
      ∃ closedBinders, (e.abstract1 index cut).stripPis count =
        some (closedBinders, output.abstract1 index (cut + count))
  | 0, _, _, _, cut, stripped => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj stripped)
    exact ⟨[], by simp only [Expr.stripPis, Nat.add_zero]⟩
  | count + 1, e, _, _, cut, stripped => by
    cases e with
    | forallE domain body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at stripped
      obtain ⟨⟨tail, output⟩, bodyStrip, same⟩ := stripped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      obtain ⟨closedTail, closed⟩ := stripPis_abstract_result index (cut + 1) bodyStrip
      refine ⟨(domain.abstract1 index cut, bm) :: closedTail, ?_⟩
      simpa only [Expr.abstract1, Expr.stripPis, closed, Option.map_some, Nat.add_succ, Nat.succ_add]
    | _ => cases stripped

/-- Inference of a lambda telescope returning a product records that product's datum in the
result sort of the inferred function type. -/
theorem infer_type_constructor_product {md : Mode} {env : Env md} {count depth : Nat}
    {value valueType domain body : Expr md} {binders : List (Expr md × BinderMeta)} {binderMeta : BinderMeta}
    (typed : Rules.Infer env .full depth value valueType)
    (bodyShape : value.stripLams count = some (binders, .forallE domain body binderMeta)) :
    ∃ typeBinders resultSort,
      valueType.stripPis count = some (typeBinders, .sort resultSort) ∧
      Level.zeronessOf resultSort = binderMeta.pw := by
  induction count generalizing depth value valueType domain body binders with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj bodyShape)
    obtain ⟨_, domainSort, _, bodySort, _, _, _, _, metadata, result⟩ := Rules.Infer.forallE_inv typed
    subst valueType
    exact ⟨[], .imax domainSort bodySort, rfl, metadata⟩
  | succ count ih =>
    cases value with
    | lam parameter valueBody parameterMeta =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at bodyShape
      obtain ⟨⟨tail, resultBody⟩, tailStrip, same⟩ := bodyShape
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      cases typed with
      | lam _ _ bodyTyped _ _ _ _ =>
        obtain ⟨openedBinders, openedStrip⟩ := stripLams_instantiate_result (.fvar depth parameter) 0 tailStrip
        simp only [Expr.instantiate1] at openedStrip
        obtain ⟨inferredBinders, resultSort, inferredStrip, metadata⟩ := ih bodyTyped openedStrip
        obtain ⟨closedBinders, closedStrip⟩ := stripPis_abstract_result depth 0 inferredStrip
        simp only [Expr.abstract1] at closedStrip
        exact ⟨(parameter, parameterMeta) :: closedBinders, resultSort,
          by simp only [Expr.stripPis, closedStrip, Option.map_some], metadata⟩
    | _ => cases bodyShape

/-- An actual checked definition fixes a returned product's datum at its declared result sort.
No equality between the value's and declaration's formal parameter annotations is required. -/
theorem DefinitionsTyped.type_constructor_product_zero {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (typed : DefinitionsTyped env)
    {name : Key .anon} {cv : ConstantVal .anon} {value domain body : Expr .anon} {hint : ReducibilityHint}
    {count : Nat} {valueBinders typeBinders : List (Expr .anon × BinderMeta)}
    {binderMeta : BinderMeta} {declaredSort : Level}
    (found : env.find? name = some (.defnInfo cv value hint))
    (valueShape : value.stripLams count = some (valueBinders, .forallE domain body binderMeta))
    (typeShape : cv.type.stripPis count = some (typeBinders, .sort declaredSort)) :
    binderMeta.pw = Level.zeronessOf declaredSort := by
  obtain ⟨_, _, valueType, _, _, valueTyped, compared, _, _⟩ := typed name cv value hint found
  obtain ⟨inferredBinders, inferredSort, inferredShape, metadata⟩ := infer_type_constructor_product valueTyped valueShape
  have resultZero := converted_telescope_result_zero model compared inferredShape typeShape
  exact metadata.symm.trans resultZero

/-- The required definition typing comes from the actual accepted reference prefix. -/
theorem ReferenceReplay.type_constructor_product_zero {V : Type u} [SetTheory V]
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon} {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty declarations sourceOut targetOut)
    (model : EnvModelM V .verified targetOut)
    {name : Key .anon} {cv : ConstantVal .anon} {value domain body : Expr .anon} {hint : ReducibilityHint}
    {count : Nat} {valueBinders typeBinders : List (Expr .anon × BinderMeta)}
    {binderMeta : BinderMeta} {declaredSort : Level}
    (found : targetOut.find? name = some (.defnInfo cv value hint))
    (valueShape : value.stripLams count = some (valueBinders, .forallE domain body binderMeta))
    (typeShape : cv.type.stripPis count = some (typeBinders, .sort declaredSort)) :
    binderMeta.pw = Level.zeronessOf declaredSort :=
  DefinitionsTyped.type_constructor_product_zero model replay.definitionsTyped_from_empty found valueShape typeShape

end IxVM.Refinement.Decl
