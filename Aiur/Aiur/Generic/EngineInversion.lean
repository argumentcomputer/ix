import Aiur.Generic.OpenCore

namespace Aiur.Generic.OpenCore

variable {calls : CallRelation F}

variable [Field F] [DecidableEq F] {world : Engine.World F}

theorem letValue_iff :
    EvalExpr world calls locals (.letValue pat value body) before result after ↔
      ∃ input middle bindings, EvalExpr world calls locals value before input middle ∧
        pat.bindings input = some bindings ∧
        EvalExpr world calls (bindings ++ locals) body middle result after := by
  constructor
  · intro h; cases h with
    | letValue v m b => exact ⟨_, _, _, v, m, b⟩
  · rintro ⟨_, _, _, v, m, b⟩; exact .letValue v m b

theorem bind_iff :
    EvalExpr world calls locals (.letValue (.bind name) value body) before result after ↔
      ∃ input middle, EvalExpr world calls locals value before input middle ∧
        EvalExpr world calls ((name, input) :: locals) body middle result after := by
  simp only [letValue_iff, Aiur.Pattern.bindings, Option.some.injEq]
  constructor
  · rintro ⟨v, h, _, ev, rfl, eb⟩; exact ⟨v, h, ev, eb⟩
  · rintro ⟨v, h, ev, eb⟩; exact ⟨v, h, _, ev, rfl, eb⟩

theorem load_iff :
    EvalExpr world calls locals (.load expr) before result after ↔
      ∃ input, EvalExpr world calls locals expr before input after ∧ loadValue after input = .ok result := by
  constructor
  · intro h; cases h with
    | load ev loaded => exact ⟨_, ev, loaded⟩
  · rintro ⟨_, ev, loaded⟩; exact .load ev loaded

theorem matchValue_iff :
    EvalExpr world calls locals (.matchValue expr arms) before result after ↔
      ∃ input middle bindings body, EvalExpr world calls locals expr before input middle ∧
        Aiur.selectArm input arms = some (bindings, body) ∧
        EvalExpr world calls (bindings ++ locals) body middle result after := by
  constructor
  · intro h; cases h with
    | matchValue v m b => exact ⟨_, _, _, _, v, m, b⟩
  · rintro ⟨_, _, _, _, v, m, b⟩; exact .matchValue v m b

end Aiur.Generic.OpenCore
