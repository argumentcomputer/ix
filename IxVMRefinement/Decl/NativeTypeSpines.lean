import IxVMRefinement.Decl.NativeCommon
import IxC.Kernel.Rules.Inversion

/-! # Inferred shapes along an inductive type telescope

Applying a prefix of a syntactic telescope ending in a sort leaves a product or a sort.
The statement holds at either inference grade and does not assume argument typing at the
io skip rule. It uses the actual inference derivation and rigidity of product reduction.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open Ix.Kernel.Rules (Infer Red Grade isSortOrPi)

private theorem telescope_sortOrPi {md : Mode} {type : Expr md} {count : Nat}
    {binders : List (Expr md × BinderMeta)} {level : Level}
    (telescope : type.stripPis count = some (binders, .sort level)) :
    isSortOrPi type = true := by
  cases count with
  | zero =>
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at telescope
    rw [telescope.2]
    rfl
  | succ count =>
    cases type <;> first | rfl | simp [Expr.stripPis] at telescope

private theorem inferred_app_type {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {fn arg domain body type : Expr md} {meta : BinderMeta}
    (headType : ∀ inferred, Infer env grade depth fn inferred →
      inferred = .forallE domain body meta)
    (run : Infer env grade depth (.app fn arg) type) : type = body.instantiate1 arg := by
  cases run with
  | app functionRead reduced _ _ =>
    obtain rfl := headType _ functionRead
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Red.rigid reduced rfl)
    rfl
  | appSkip functionRead reduced _ =>
    obtain rfl := headType _ functionRead
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Red.rigid reduced rfl)
    rfl

/-- A partially applied sort-valued telescope cannot infer a constant-headed type. -/
theorem infer_spine_sortOrPi {md : Mode} {env : Env md} {grade : Grade} {depth : Nat} :
    ∀ (args : List (Expr md)) {fn type result : Expr md} {arity : Nat}
      {binders : List (Expr md × BinderMeta)} {level : Level},
      (∀ inferred, Infer env grade depth fn inferred → inferred = type) →
      type.stripPis arity = some (binders, .sort level) → args.length ≤ arity →
      Infer env grade depth (Expr.mkAppN fn args) result → isSortOrPi result = true
  | [], _, _, _, _, _, _, unique, telescope, _, run => by
    rw [unique _ run]
    exact telescope_sortOrPi telescope
  | arg :: rest, fn, type, result, arity, binders, level, unique, telescope, within, run => by
    cases arity with
    | zero => simp at within
    | succ arity =>
      obtain ⟨domain, body, meta, rfl⟩ : ∃ domain body meta, type = .forallE domain body meta := by
        cases type <;> first | exact ⟨_, _, _, rfl⟩ | simp [Expr.stripPis] at telescope
      simp only [Expr.stripPis, Option.map_eq_some_iff] at telescope
      obtain ⟨⟨tailBinders, residual⟩, tail, equal⟩ := telescope
      simp only [Prod.mk.injEq] at equal
      obtain ⟨_, rfl⟩ := equal
      have existsOpen := Expr.stripPis_instantiate1_isSome (v := arg) arity
        (e := body) 0 (by rw [tail]; rfl)
      obtain ⟨⟨openedBinders, openedResidual⟩, opened⟩ := Option.isSome_iff_exists.mp existsOpen
      have residualEq := (Expr.stripPis_instantiate1_eq (v := arg) arity 0 tail opened).1
      rw [Expr.instantiate1_sort] at residualEq
      subst openedResidual
      exact infer_spine_sortOrPi rest
        (fun _ inferred => inferred_app_type unique inferred) opened (by simpa using within) run

/-- The corresponding fact for an actual stored constant, at the requested universe instance. -/
theorem infer_stored_spine_sortOrPi {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {name : Key md} {levels : List Level} {constant : ConstantInfo md} {args : List (Expr md)}
    {arity : Nat} {binders : List (Expr md × BinderMeta)} {level : Level} {result : Expr md}
    (stored : env.find? name = some constant)
    (telescope : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams levels).stripPis arity = some (binders, .sort level))
    (within : args.length ≤ arity)
    (run : Infer env grade depth (Expr.mkAppN (.const name levels) args) result) :
    isSortOrPi result = true := by
  apply infer_spine_sortOrPi args ?_ telescope within run
  intro inferred headRead
  obtain ⟨found, lookup, _, _, equal⟩ := Infer.const_inv headRead
  rw [stored] at lookup
  cases Option.some.inj lookup
  exact equal

end IxVM.Refinement.Decl
