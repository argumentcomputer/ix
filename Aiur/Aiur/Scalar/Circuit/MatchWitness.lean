import Aiur.Scalar.Circuit.InactiveCorrectness

namespace Aiur.Scalar.Circuit.Compiler

/-- A selected default admits inverse witnesses for every excluded literal. -/
theorem excludeLiterals_complete [Field F] {function : String}
    {selector scrutinee : ArithExpr F} {literals : List F} {before after : BuildState F}
    (compiled : (excludeLiterals selector scrutinee literals).run before = .ok ((), after))
    (layout : before.WellFormed)
    (selectorBound : selector.inBounds before.nextVar = true)
    (scrutineeBound : scrutinee.inBounds before.nextVar = true)
    {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
    (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
    (active : selector.denote (Row.assignment ⟨function, initial⟩) = 1)
    (excluded : ∀ literal ∈ literals, scrutinee.denote (Row.assignment ⟨function, initial⟩) ≠ literal) :
    ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧
      after.WellFormed ∧ after.Valid calls (Row.assignment ⟨function, values⟩) := by
  cases literals with
  | nil =>
      simp [excludeLiterals, StateT.run, StateT.pure, pure, Except.pure] at compiled
      subst after
      exact ⟨initial, ⟨[], by simp⟩, size, layout, valid⟩
  | cons value rest =>
      let equation : ArithExpr F :=
        .mul selector (.sub (.mul (.sub scrutinee (.const value)) (.var before.nextVar)) (.const 1))
      let next : BuildState F := {
        before with nextVar := before.nextVar + 1
                    constraints := before.constraints.push equation }
      cases restRun : excludeLiterals selector scrutinee rest next with
      | error error =>
          simp [excludeLiterals, StateT.run, StateT.bind, bind, Except.bind, next, equation,
            restRun] at compiled
      | ok output =>
          rcases output with ⟨finished, state⟩
          cases finished
          simp [excludeLiterals, StateT.run, StateT.bind, bind, Except.bind, next, equation,
            restRun] at compiled
          subst after
          let inverse := (scrutinee.denote (Row.assignment ⟨function, initial⟩) - value)⁻¹
          let padded := initial ++ [inverse]
          have extension : initial.IsPrefix padded := List.prefix_append _ _
          have inverseValue : Row.assignment ⟨function, padded⟩ before.nextVar = inverse := by
            rw [← size]
            exact assignment_append_value _ _ _
          have selectorValue := denote_of_prefix (function := function) extension size selectorBound
          have scrutineeValue := denote_of_prefix (function := function) extension size scrutineeBound
          have oldValid := valid.of_prefix layout size extension
          have freshValid : { before with nextVar := before.nextVar + 1 }.Valid calls
              (Row.assignment ⟨function, padded⟩) := ⟨oldValid.constraints, oldValid.calls⟩
          have nextValid : next.Valid calls (Row.assignment ⟨function, padded⟩) :=
            freshValid.constrain (by
              simp [equation, ArithExpr.denote, selectorValue, active, scrutineeValue, inverseValue,
                inverse, sub_ne_zero.mpr (excluded value (by simp))])
          have nextLayout : next.WellFormed := layout.fresh.constrain (by
            simp [equation, ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) selectorBound,
              ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound])
          obtain ⟨values, finalExtension, finalSize, finalLayout, finalValid⟩ :=
            excludeLiterals_complete restRun nextLayout
              (ArithExpr.inBounds_mono (Nat.le_succ _) selectorBound)
              (ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound)
              (by simp [padded, next, size]) nextValid
              (selectorValue.trans active)
              (fun literal member => by rw [scrutineeValue]; exact excluded literal (by simp [member]))
          exact ⟨values, extension.trans finalExtension, finalSize, finalLayout, finalValid⟩
termination_by literals.length

end Aiur.Scalar.Circuit.Compiler
