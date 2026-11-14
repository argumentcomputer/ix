import IxVMRefinement.Iota.Basic

/-! # Kernel-side lemmas of ι: a telescope's binder domain under the spine's arguments

`piDomInst T As n` (the domain of binder `n` after instantiating the binders before it by `As`,
one at a time) is the domain `piDomAt n T` instantiated by the first `n` arguments at once,
innermost first (`instantiateList`). -/

namespace IxVM.Refinement.Core

open Ix.Kernel.Rules (Red)

/-- Instantiating a bound variable of a telescope instantiates its domains, each under the
binders before it. -/
theorem piDomAt_instantiate1 (a : KExpr) : ∀ (n : Nat) (b : KExpr) (k : Nat) (D : KExpr),
    piDomAt n b = some D → piDomAt n (b.instantiate1 a k) = some (D.instantiate1 a (k + n)) := by
  intro n
  induction n with
  | zero =>
    intro b k D hb
    cases b with
    | forallE ty body m =>
      simp only [piDomAt, Option.some.injEq] at hb
      subst hb
      simp [piDomAt, Ix.Kernel.Expr.instantiate1]
    | _ => simp [piDomAt] at hb
  | succ n ih =>
    intro b k D hb
    cases b with
    | forallE ty body m =>
      simp only [piDomAt] at hb
      have h := ih body (k + 1) D hb
      simp only [Ix.Kernel.Expr.instantiate1, piDomAt]
      rw [h, show k + 1 + n = k + (n + 1) by omega]
    | _ => simp [piDomAt] at hb

/-- **The binder domain under the spine's arguments**: one instantiation at a time is the
domain instantiated by the arguments before it at once. -/
theorem piDomInst_of_piDomAt : ∀ (n : Nat) (T : KExpr) (As : List KExpr) (D : KExpr),
    piDomAt n T = some D → n ≤ As.length →
      Specs.Whnf.piDomInst T As n = some (D.instantiateList (As.take n).reverse 0)
  | 0, T, As, D, hT, _ => by
    cases T with
    | forallE ty body m =>
      simp only [piDomAt, Option.some.injEq] at hT
      subst hT
      simp [Specs.Whnf.piDomInst, Ix.Kernel.Expr.instantiateList_nil]
    | _ => simp [piDomAt] at hT
  | n + 1, T, As, D, hT, hlen => by
    cases T with
    | forallE ty body m =>
      cases As with
      | nil => simp at hlen
      | cons a as =>
        have hle : n ≤ as.length := by simpa using hlen
        simp only [piDomAt] at hT
        have h1 := piDomAt_instantiate1 a n body 0 D hT
        have h2 := piDomInst_of_piDomAt n _ as _ h1 hle
        simp only [Specs.Whnf.piDomInst]
        rw [h2, List.take_succ_cons, List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one,
          List.length_reverse, List.length_take, Nat.min_eq_left hle]
    | _ => simp [piDomAt] at hT

end IxVM.Refinement.Core
