import Aiur.Generic.PatternContinuationFacts

namespace Aiur.Generic.PatternLowering

variable {calls : CallRelation F}


variable [DecidableEq F] {heap : Heap F} {locals final : Environment F Nat}
  {steps : List (Step F)} {input : String} {value : SourceValue F}

theorem Attempt.append_wildcard_iff
    (found : locals.find? (·.1 == input) = some (input, value))
    (fresh : input ∉ writtenNames steps) :
    Attempt heap (steps ++ [.test .wildcard input]) locals accepted final ↔
      Attempt heap steps locals accepted final := by
  rw [Attempt.append_iff]
  constructor
  · rintro (⟨middle, first, last⟩ | ⟨rfl, failed⟩)
    · cases last with
      | testHit _ matched rest =>
          simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
          subst_vars
          cases rest
          exact first
      | testMiss _ missed => simp [Aiur.Pattern.bindings] at missed
    · exact failed
  · intro attempted
    cases accepted with
    | false => exact Or.inr ⟨rfl, attempted⟩
    | true =>
        exact Or.inl ⟨final, attempted, .testHit (bindings := [])
          (by rw [attempted.unchanged fresh]; exact found) (by simp [Aiur.Pattern.bindings]) .done⟩

theorem Plan.retained_attempt_iff (p : Plan F)
    (found : locals.find? (·.1 == input) = some (input, value))
    (fresh : input ∉ writtenNames p.steps) :
    Attempt heap (p.retainedSteps input) locals accepted final ↔ Attempt heap p.steps locals accepted final := by
  unfold Plan.retainedSteps
  split
  · rfl
  · exact Attempt.append_wildcard_iff found fresh

theorem Plan.retained_match_iff [Field F] {world : Engine.World F}
    {failure : Option (Aiur.Expr F)} (p : Plan F)
    (found : locals.find? (·.1 == input) = some (input, value))
    (fresh : input ∉ writtenNames p.steps) :
    OpenCore.EvalExpr world calls locals (matchSteps (p.retainedSteps input) body failure) heap result after ↔
      OpenCore.EvalExpr world calls locals (matchSteps p.steps body failure) heap result after := by
  rw [matchSteps_iff, matchSteps_iff]
  apply exists_congr; intro accepted
  apply exists_congr; intro final
  exact and_congr (p.retained_attempt_iff found fresh) Iff.rfl

end Aiur.Generic.PatternLowering
