import IxVMRefinement.Decl.SortFunctionReduction
import IxVMRefinement.Decl.NativeNormalization
import Ix.IxVM.Consistency.Statement

/-! # Sort-returning fragments through normalization and annotation

The fragment is preserved by abstraction and arbitrary substitution, including substitution
with changed free-variable type annotations. Its actual reductions and subsequent annotation
therefore retain the same literal result sort. This is syntactic evidence and does not use
inhabitants of the surrounding context.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- Closing free variables preserves the fragment's result sort and remaining arity. -/
theorem SortFunction.abstract1 {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortFunction sortLevel count e) (index : Nat) :
    ∀ cut, SortFunction sortLevel count (e.abstract1 index cut) := by
  induction shape with
  | sort => intro cut; exact .sort
  | lam _ ih => intro cut; exact .lam (ih (cut + 1))
  | app _ ih => intro cut; exact .app (ih cut)

/-- Binder annotation preserves this fragment even when it changes all binder metadata. -/
theorem SortFunction.annotated {sortLevel : Level} {count : Nat} {e out : Expr .anon}
    (shape : SortFunction sortLevel count e) (annotation : IxVM.Consistency.Annotates out e) :
    SortFunction sortLevel count out := by
  induction shape generalizing out with
  | sort => cases annotation; exact .sort
  | lam bodyShape ih =>
    cases annotation with
    | lam _ body => exact .lam (ih body)
  | app functionShape ih =>
    cases annotation with
    | app functionExpr _ => exact .app (ih functionExpr)

/-- The actual positivity normalizer preserves a sort-returning fragment. Its weak-head
result cannot enter the product-body recursion, because the fragment has no product head. -/
theorem SortFunction.normalized {md : Mode} {env : Env md} {fuel steps depth count : Nat}
    {T : Key md} {e out : Expr md} {sortLevel : Level}
    (shape : SortFunction sortLevel count e)
    (run : normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out) :
    SortFunction sortLevel count out := by
  cases steps with
  | zero => cases run
  | succ steps =>
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
        | forallE => cases headShape
        | _ =>
          obtain rfl := (Except.ok.inj rest).symm
          exact headShape

/-- Actual inference and sorting of a fully applied fragment return its exact successor sort. -/
theorem SortFunction.checked_sort {md : Mode} {env : Env md} {depth : Nat}
    {sortLevel resultSort : Level} {e inferred : Expr md}
    (shape : SortFunction sortLevel 0 e) (typed : Rules.Infer env .full depth e inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) : resultSort = .succ sortLevel := by
  rw [shape.inferred_zero typed] at sorted
  exact Rules.Red.sort_eq sorted

end IxVM.Refinement.Decl
