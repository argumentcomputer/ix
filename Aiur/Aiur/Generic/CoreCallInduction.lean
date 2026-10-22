import Aiur.Generic.OpenCore
import Aiur.Generic.Simulation

namespace Aiur.Generic.Engine

theorem EvalExpr.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String} {hintType : Aiur.Ty → Bool}
    (closed : ∀ n ∈ names, ∀ args ls e, world.prepare n args = .ok (ls, e) →
      inScope names hintType e = true)
    (step : ∀ n ∈ names, ∀ args ls e b v a,
      world.prepare n args = .ok (ls, e) → EvalExpr world ls e b v a →
      OpenCore.EvalExpr world calls ls e b v a → calls n args b v a)
    (ev : EvalExpr world locals expr before result after) :
    inScope names hintType expr = true → OpenCore.EvalExpr world calls locals expr before result after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ls es b vs h _ => (∀ e ∈ es, inScope names hintType e = true) → OpenCore.EvalArgs world calls ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → calls n xs b v h) with
  | literal => intro _; exact .literal
  | var h => intro _; exact .var h
  | tuple _ ih => intro h; exact .tuple (ih (by simpa [inScope] using h))
  | construct _ ih => intro h; exact .construct (ih (by simpa [inScope] using h))
  | project _ op ih => intro h; exact .project (ih (by simpa [inScope] using h)) op
  | letValue _ matched _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .letValue (ih1 h.1) matched (ih2 h.2)
  | store _ ih => intro h; exact .store (ih (by simpa [inScope] using h))
  | load _ op ih => intro h; exact .load (ih (by simpa [inScope] using h)) op
  | hint _ typed ih =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .hint (ih h.2) typed
  | neg _ op ih => intro h; exact .neg (ih (by simpa [inScope] using h)) op
  | assertEq _ _ op ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .assertEq (ih1 h.1) (ih2 h.2) op
  | binary _ _ op ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binary (ih1 h.1) (ih2 h.2) op
  | call _ _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.contains_iff_mem, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .call (ih1 h.2) (ih2 h.1)
  | matchValue _ selected _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchValue (ih1 h.1) selected (ih2 (selected_inScope selected h.2))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h
      exact .cons (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))
  | intro prepared body ih =>
      rename_i hn
      exact step _ hn _ _ _ _ _ _ prepared body (ih (closed _ hn _ _ _ prepared))

theorem EvalFn.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String} {hintType : Aiur.Ty → Bool}
    (closed : ∀ n ∈ names, ∀ args ls e, world.prepare n args = .ok (ls, e) →
      inScope names hintType e = true)
    (step : ∀ n ∈ names, ∀ args ls e b v a,
      world.prepare n args = .ok (ls, e) → EvalExpr world ls e b v a →
      OpenCore.EvalExpr world calls ls e b v a → calls n args b v a)
    (ev : EvalFn world name args before result after) (member : name ∈ names) :
    calls name args before result after := by
  cases ev with
  | intro prepared body =>
      exact step _ member _ _ _ _ _ _ prepared body
        (body.openCalls closed step (closed _ member _ _ _ prepared))

end Aiur.Generic.Engine
