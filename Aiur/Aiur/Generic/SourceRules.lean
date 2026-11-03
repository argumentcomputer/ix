import Aiur.Generic.SourceSemantics

namespace Aiur.Generic.SourceSemantics

variable [Field F] [DecidableEq F] {world : World F}

/-- Repetition copies the result of one source evaluation, including length zero. -/
theorem repeat_iff :
    EvalExpr world types locals (.repeat operand length) before result after ↔
      ∃ value, EvalExpr world types locals operand before value after ∧
        result = .tuple (List.replicate length value) := by
  constructor
  · intro h
    cases h with
    | «repeat» value => exact ⟨_, value, rfl⟩
  · rintro ⟨value, evaluated, rfl⟩
    exact .repeat evaluated

/-- A pointer pattern reads the pointer before matching the inner pattern.
This is a source-level law and does not refer to generated core syntax. -/
theorem let_load_iff :
    EvalExpr world types locals (.letValue (.load pat) operand body) before result after ↔
      EvalExpr world types locals (.letValue pat (.load operand) body) before result after := by
  constructor
  · intro h
    cases h with
    | letValue value matched body =>
        simp only [World.matchPattern, matchPatternWith, except_bind_ok] at matched
        obtain ⟨input, loaded, matched⟩ := matched
        exact .letValue (.load value loaded) matched body
  · intro h
    cases h with
    | letValue value matched body =>
        cases value with
        | load pointer loaded =>
            exact .letValue pointer (by simp only [World.matchPattern, matchPatternWith, except_bind_ok]; exact ⟨_, loaded, matched⟩) body

end Aiur.Generic.SourceSemantics
