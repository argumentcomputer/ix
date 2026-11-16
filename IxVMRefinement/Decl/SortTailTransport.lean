import IxVMRefinement.Decl.SortFunctionTransport

/-! # Product telescopes ending in a computed sort

The domains and their annotations may vary, but a sort-valued residual forces every
surrounding product's result universe to be nonzero. The fragment is preserved by actual
positivity normalization, substitution, abstraction and annotation without semantic
inhabitance assumptions.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- A product telescope whose residual is a fully applied sort-returning fragment. -/
inductive SortTail (sortLevel : Level) : Nat → Expr md → Prop
  | result {e : Expr md} : SortFunction sortLevel 0 e → SortTail sortLevel 0 e
  | pi {count : Nat} {domain body : Expr md} {metadata : BinderMeta} :
      SortTail sortLevel count body → SortTail sortLevel (count + 1) (.forallE domain body metadata)

theorem SortTail.instantiate1 {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortTail sortLevel count e) (value : Expr md) :
    ∀ cut, SortTail sortLevel count (e.instantiate1 value cut) := by
  induction shape with
  | result fragment => intro cut; exact .result (fragment.instantiate1 value cut)
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem SortTail.abstract1 {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortTail sortLevel count e) (index : Nat) :
    ∀ cut, SortTail sortLevel count (e.abstract1 index cut) := by
  induction shape with
  | result fragment => intro cut; exact .result (fragment.abstract1 index cut)
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem SortTail.annotated {sortLevel : Level} {count : Nat} {e out : Expr .anon}
    (shape : SortTail sortLevel count e) (annotation : IxVM.Consistency.Annotates out e) :
    SortTail sortLevel count out := by
  induction shape generalizing out with
  | result fragment => exact .result (fragment.annotated annotation)
  | pi _ ih =>
    cases annotation with
    | forallE _ body => exact .pi (ih body)

theorem SortTail.reduced {md : Mode} {env : Env md} {depth count : Nat} {e out : Expr md}
    {sortLevel : Level} (shape : SortTail sortLevel count e) (reduced : Rules.Red env depth e out) :
    SortTail sortLevel count out := by
  cases shape with
  | result fragment => exact .result (fragment.reduced reduced)
  | pi body =>
    rw [Rules.Red.rigid reduced rfl]
    exact .pi body

/-- Actual recursion under a product keeps the fragment after reopening and reclosing its body. -/
theorem SortTail.normalized {md : Mode} {env : Env md} {fuel steps depth count : Nat}
    {T : Key md} {e out : Expr md} {sortLevel : Level}
    (shape : SortTail sortLevel count e)
    (run : normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out) :
    SortTail sortLevel count out := by
  induction steps generalizing depth count e out with
  | zero => cases run
  | succ steps ih =>
    simp only [normPosDom] at run
    split at run
    · obtain rfl := (Except.ok.inj run).symm
      exact shape
    · obtain ⟨head, reduced, rest⟩ := exceptBind_ok run
      change whnf .verified env fuel depth e = .ok head at reduced
      have headShape := shape.reduced (Rules.whnf_bridge reduced)
      split at rest
      · obtain rfl := (Except.ok.inj rest).symm
        exact headShape
      · cases head with
        | forallE domain body metadata =>
          cases headShape with
          | result impossible => cases impossible
          | pi bodyShape =>
            dsimp only at rest
            split at rest
            · cases rest
            · obtain ⟨bodyOut, recursive, result⟩ := exceptBind_ok rest
              obtain rfl := (Except.ok.inj result).symm
              exact .pi ((ih (bodyShape.instantiate1 (.fvar depth domain) 0) recursive).abstract1 depth 0)
        | _ =>
          obtain rfl := (Except.ok.inj rest).symm
          exact headShape

/-- The actual checked result sort is nonzero, independently of product-domain universes
and of whether the surrounding context or telescope domains have inhabitants. -/
theorem SortTail.checked_zero {md : Mode} {env : Env md} {count depth : Nat}
    {sortLevel resultSort : Level} {e inferred : Expr md}
    (shape : SortTail sortLevel count e) (typed : Rules.Infer env .full depth e inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) :
    Level.zeronessOf resultSort = .never := by
  induction count generalizing depth e inferred resultSort with
  | zero =>
    cases shape with
    | result fragment => rw [fragment.checked_sort typed sorted]; rfl
  | succ count ih =>
    cases shape with
    | @pi _ domain _ _ bodyShape =>
      obtain ⟨_, _, _, _, _, _, bodyTyped, bodySorted, _, typeEq⟩ := Rules.Infer.forallE_inv typed
      have bodyZero := ih (bodyShape.instantiate1 (.fvar depth domain) 0) bodyTyped bodySorted
      rw [typeEq] at sorted
      rw [Rules.Red.sort_eq sorted]
      exact bodyZero

/-- A checked product whose body is in this fragment has the non-proposition binder datum. -/
theorem SortTail.product_metadata {md : Mode} {env : Env md} {count depth : Nat}
    {sortLevel : Level} {domain body inferred : Expr md} {metadata : BinderMeta}
    (shape : SortTail sortLevel count body)
    (typed : Rules.Infer env .full depth (.forallE domain body metadata) inferred) :
    metadata.pw = .never := by
  obtain ⟨_, _, _, _, _, _, bodyTyped, bodySorted, datum, _⟩ := Rules.Infer.forallE_inv typed
  exact datum.symm.trans ((shape.instantiate1 (.fvar depth domain) 0).checked_zero bodyTyped bodySorted)

end IxVM.Refinement.Decl
