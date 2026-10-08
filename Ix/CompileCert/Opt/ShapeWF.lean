import Ix.CompileCert.Opt.Total
import Ix.CompileCert.Canon.Cache

/-!
# M7 L3-def: the shapes the passes read are within Lean's ranges (`ShapesWF`, discharged)

`readShape` checks that every motive source is one of Lean's motives and every minor source one of
Lean's minors (`readShape_wf`); `optBlockOf` keeps only shapes `readShape` read (`optBlockOf_wf`);
`Driver.optBlocks` keeps only `optBlockOf`'s blocks; so the environment of the hook
(`Driver.optLookup`) satisfies `ShapesWF` (`shapesWF_optLookup`), the hypothesis of the totality
of O1, O4 and O6 (`Total.lean`).
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
