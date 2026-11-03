import Aiur.Generic.Engine

namespace Aiur.Generic.Engine

def inScope (names : List String) (hintType : Aiur.Ty → Bool) : Aiur.Expr α → Bool
  | .literal _ | .var _ => true
  | .tuple xs | .construct _ _ xs => (xs.map (inScope names hintType)).all id
  | .call n xs => names.contains n && (xs.map (inScope names hintType)).all id
  | .project x _ | .store x | .load x | .neg x => inScope names hintType x
  | .hint t x channel => hintType t && inScope names hintType x
  | .letValue _ x b | .binary _ x b | .assertEq _ x b => inScope names hintType x && inScope names hintType b
  | .matchValue x arms => inScope names hintType x && (arms.map fun a => inScope names hintType a.2).all id
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

theorem selected_inScope [DecidableEq F] {input : SourceValue F} {arms : List (Aiur.Pattern F × Aiur.Expr F)}
    (selected : selectArm input arms = some (bindings, body))
    (safe : ∀ a ∈ arms, inScope names hintType a.2 = true) : inScope names hintType body = true := by
  induction arms with
  | nil => simp [selectArm] at selected
  | cons a rest ih =>
      rcases a with ⟨p, e⟩
      cases matched : p.bindings input with
      | none => exact ih (by simpa [selectArm, matched] using selected) (fun a h => safe a (by simp [h]))
      | some bs =>
          obtain ⟨rfl, rfl⟩ := (by simpa [selectArm, matched] using selected : bs = bindings ∧ e = body)
          exact safe (p, e) (by simp)

/-- The finite certificate concerns syntax and lookup, not evaluation or
termination. This simulation works for all finite evaluations and all hints. -/
structure Agreement (left right : World F) (names : List String) (hintType : Aiur.Ty → Bool) : Prop where
  prepare : ∀ n ∈ names, ∀ args locals body,
    left.prepare n args = .ok (locals, body) ↔ right.prepare n args = .ok (locals, body)
  hint : ∀ t, hintType t = true → ∀ v, left.typed t v = true ↔ right.typed t v = true
  closed : ∀ n ∈ names, ∀ args locals body,
    left.prepare n args = .ok (locals, body) → inScope names hintType body = true

def Agreement.symm (a : Agreement left right names hintType) : Agreement right left names hintType where
  prepare n hn args locals body := (a.prepare n hn args locals body).symm
  hint t ht v := (a.hint t ht v).symm
  closed n hn args locals body h := a.closed n hn args locals body ((a.prepare n hn args locals body).mpr h)

variable {F : Type} {left right : World F} {names : List String} {hintType : Aiur.Ty → Bool}

theorem EvalExpr.transfer [Field F] [DecidableEq F]
    (a : Agreement left right names hintType)
    (ev : EvalExpr left locals expr before result after) :
    inScope names hintType expr = true → EvalExpr right locals expr before result after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ls es b vs h _ => (∀ e ∈ es, inScope names hintType e = true) → EvalArgs right ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → EvalFn right n xs b v h) with
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
      exact .hint (ih h.2) ((a.hint _ h.1 _).mp typed)
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
  | intro prepared _ ih =>
      rename_i hn
      exact .intro ((a.prepare _ hn _ _ _).mp prepared) (ih (a.closed _ hn _ _ _ prepared))

theorem EvalFn.transfer [Field F] [DecidableEq F]
    (a : Agreement left right names hintType) (hn : n ∈ names)
    (ev : EvalFn left n args before result after) : EvalFn right n args before result after := by
  cases ev with
  | intro prepared body =>
      exact .intro ((a.prepare _ hn _ _ _).mp prepared)
        (body.transfer a (a.closed _ hn _ _ _ prepared))

theorem evalFn_iff [Field F] [DecidableEq F]
    (a : Agreement left right names hintType) (hn : n ∈ names) :
    EvalFn left n args before result after ↔ EvalFn right n args before result after :=
  ⟨EvalFn.transfer a hn, EvalFn.transfer a.symm hn⟩

theorem EvalExpr.toCore [Field F] [DecidableEq F] {p : Aiur.Program F}
    (ev : EvalExpr (.ofProgram p) locals expr before result after) :
    Aiur.EvalExpr p locals expr before result after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ls es b vs h _ => Aiur.EvalArgs p ls es b vs h)
    (motive_3 := fun n xs b v h _ => Aiur.EvalFn p n xs b v h) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ op ih => exact .project ih op
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ op ih => exact .load ih op
  | hint _ typed ih => exact .hint ih typed
  | neg _ op ih => exact .neg ih op
  | assertEq _ _ op ih1 ih2 => exact .assertEq ih1 ih2 op
  | binary _ _ op ih1 ih2 => exact .binary ih1 ih2 op
  | call _ _ ih1 ih2 => exact .call ih1 ih2
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | intro h _ ih => exact .intro h ih

theorem ofCore [Field F] [DecidableEq F] {p : Aiur.Program F}
    (ev : Aiur.EvalExpr p locals expr before result after) :
    EvalExpr (.ofProgram p) locals expr before result after := by
  induction ev using Aiur.EvalExpr.rec
    (motive_2 := fun ls es b vs h _ => EvalArgs (.ofProgram p) ls es b vs h)
    (motive_3 := fun n xs b v h _ => EvalFn (.ofProgram p) n xs b v h) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ op ih => exact .project ih op
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ op ih => exact .load ih op
  | hint _ typed ih => exact .hint ih typed
  | neg _ op ih => exact .neg ih op
  | assertEq _ _ op ih1 ih2 => exact .assertEq ih1 ih2 op
  | binary _ _ op ih1 ih2 => exact .binary ih1 ih2 op
  | call _ _ ih1 ih2 => exact .call ih1 ih2
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | intro h _ ih => exact .intro h ih

theorem core_iff [Field F] [DecidableEq F] {p : Aiur.Program F} :
    EvalFn (.ofProgram p) n args before result after ↔ Aiur.EvalFn p n args before result after := by
  constructor
  · rintro ⟨prepared, body⟩; exact .intro prepared body.toCore
  · rintro ⟨prepared, body⟩; exact .intro prepared (ofCore body)

end Aiur.Generic.Engine
