import Ix.CompileCert.Pj.TeleTyped

namespace Ix.CompileCert.Pj

open Ix.CompileCert (pushArguments ValuationLift)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Remove an inserted valuation segment from a graded lifted expression.
The product membership and zero-regime facts are transported unchanged. -/
theorem graded_unlift (amount : Nat) : ∀ (e : Kernel.Expr)
    {cutoff : Nat} {ρ target : Nat → V},
    ValuationLift amount cutoff ρ target →
    Bridge.Graded cval env φ target (e.liftLooseBVars amount cutoff) →
    Bridge.Graded cval env φ ρ e := by
  intro e
  induction e with
  | bvar i => intro cutoff ρ target related graded; trivial
  | fvar i t ih => intro cutoff ρ target related graded; exact graded.elim
  | sort l => intro cutoff ρ target related graded; trivial
  | const n us =>
    intro cutoff ρ target related graded
    obtain ⟨v, read⟩ := graded
    exact ⟨v, denotes_unlift amount (.const n us) related read⟩
  | app f a ihf iha =>
    intro cutoff ρ target related graded
    obtain ⟨gf, ga, F, X, r, A, B, readF, readX, memberF, memberX, zero⟩ := graded
    exact ⟨ihf related gf, iha related ga, F, X, r, A, B,
      denotes_unlift amount f related readF, denotes_unlift amount a related readX,
      memberF, memberX, zero⟩
  | lam t b bm iht ihb =>
    intro cutoff ρ target related graded
    obtain ⟨gt, A, readA, body, zero⟩ := graded
    refine ⟨iht related gt, A, denotes_unlift amount t related readA,
      fun x hx => ihb (related.push x) (body x hx), ?_⟩
    intro regime x hx y read
    exact zero regime x hx y (Ix.CompileCert.denotes_lift read (related.push x))
  | forallE t b bm iht ihb =>
    intro cutoff ρ target related graded
    obtain ⟨gt, A, readA, body, zero⟩ := graded
    refine ⟨iht related gt, A, denotes_unlift amount t related readA,
      fun x hx => ihb (related.push x) (body x hx), ?_⟩
    intro regime x hx y read
    exact zero regime x hx y (Ix.CompileCert.denotes_lift read (related.push x))
  | letE t v b iht ihv ihb =>
    intro cutoff ρ target related graded
    exact graded.elim
  | lit l =>
    intro cutoff ρ target related graded
    obtain ⟨v, read⟩ := graded
    exact ⟨v, denotes_unlift amount (.lit l) related read⟩
  | proj s i e ih =>
    intro cutoff ρ target related graded
    obtain ⟨ge, v, read⟩ := graded
    exact ⟨ih related ge, v, denotes_unlift amount (.proj s i e) related read⟩

/-- Grading of an actual dependent telescope supplies its next domain at
every typed prefix, including prefixes selected while constructing minors. -/
theorem graded_piJoin_domain_at_split
    {bs before after : List (Kernel.Expr × Kernel.BinderMeta)}
    {t b : Kernel.Expr} {bm : Kernel.BinderMeta} {ρ : Nat → V} {xs : List V}
    (split : bs = before ++ (t, bm) :: after)
    (graded : Bridge.Graded cval env φ ρ (piJoin bs b))
    (typed : TeleTyped cval env φ ρ (before.map Prod.fst) xs) :
    Bridge.Graded cval env φ (pushArguments ρ xs) t := by
  rw [split, piJoin_append] at graded
  have remainder := graded_piJoin graded typed
  exact remainder.1

end Ix.CompileCert.Pj
