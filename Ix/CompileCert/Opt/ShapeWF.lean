import Ix.CompileCert.Opt.Total
import Ix.CompileCert.Canon.Cache

/-!
# M7 L3-def: invariants for the shape reader

The successful `Option` loop invariant supports the bounds checked by `readShape`. The reader
and the block-building loops must still discharge `ShapesWF`, the hypothesis used by the
totality of O1, O4 and O6 (`Total.lean`).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Pass.Opt

/-- **An invariant of a loop** (in `Option`): kept by every successful step, it holds of the result. -/
theorem forIn_option_inv {α σ : Type} (f : α → σ → Option (ForInStep σ)) (P : σ → Prop)
    (hstep : ∀ x a r, P a → f x a = some r → P r.value) :
    ∀ (l : List α) (a res : σ), P a → forIn l a f = some res → P res
  | [], a, res, ha, h => by
    rw [List.forIn_nil] at h
    simp only [pure, Option.some.injEq] at h
    exact h ▸ ha
  | x :: l, a, res, ha, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := obind.1 h
    have hp := hstep x a r ha hr
    cases r with
    | done b =>
      simp only [pure, Option.some.injEq] at h
      exact h ▸ hp
    | yield b => exact forIn_option_inv f P hstep l b res hp h


end Ix.CompileCert.Opt
