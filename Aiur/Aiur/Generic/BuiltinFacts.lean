import Aiur.Generic.Builtin
import Aiur.Generic.Lower
import Aiur.Generic.OpenCore

namespace Aiur.Generic.BuiltinLowering

variable [Field F] [DecidableEq F] {world : Engine.World F} {calls : CallRelation F}

/-- Late compilation preserves operand evaluation, including heap effects.
Debug messages themselves impose no additional premise or constraint. -/
theorem expression_iff {op : Builtin} {operands : List (Aiur.Expr F)} :
    OpenCore.EvalExpr world calls locals (expression op operands) before result after ↔
      ∃ values, OpenCore.EvalArgs world calls locals operands before values after ∧
        op.apply values = .ok result := by
  cases op with
  | assertEq message =>
      constructor
      · intro h
        cases h with
        | letValue value matched body =>
            cases value with
            | tuple items =>
                rename_i values
                cases values with
                | nil => simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                | cons left rest =>
                    cases rest with
                    | nil => simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                    | cons right rest =>
                        cases rest with
                        | cons => simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                        | nil =>
                            simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                            subst_vars
                            cases body with
                            | assertEq lhs rhs applied =>
                                cases lhs with
                                | var found =>
                                    simp at found
                                    subst_vars
                                    cases rhs with
                                    | var found =>
                                        simp at found
                                        subst_vars
                                        exact ⟨_, items, applied⟩
      · rintro ⟨values, items, applied⟩
        cases values with
        | nil => simp [Builtin.apply] at applied
        | cons left rest =>
            cases rest with
            | nil => simp [Builtin.apply] at applied
            | cons right rest =>
                cases rest with
                | cons => simp [Builtin.apply] at applied
                | nil =>
                    exact .letValue (bindings := [("$assertLeft", left), ("$assertRight", right)])
                      (.tuple items) (by simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList])
                      (.assertEq (.var (by simp)) (.var (by simp)) applied)
  | ascribe type =>
      constructor
      · intro h
        cases h with
        | letValue value matched body =>
            cases value with
            | tuple items =>
                rename_i values
                cases values with
                | nil => simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                | cons value rest =>
                    cases rest with
                    | cons => simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                    | nil =>
                        simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList] at matched
                        subst_vars
                        cases body with
                        | var lookup =>
                            simp at lookup
                            subst_vars
                            exact ⟨_, items, rfl⟩
      · rintro ⟨values, items, applied⟩
        cases values with
        | nil => simp [Builtin.apply] at applied
        | cons value rest =>
            cases rest with
            | cons => simp [Builtin.apply] at applied
            | nil =>
                simp only [Builtin.apply, Except.ok.injEq] at applied
                subst result
                exact .letValue (bindings := [("$annotation", value)]) (.tuple items) (by simp [Aiur.Pattern.bindings, Aiur.Pattern.bindingsList])
                  (.var (by simp))
  | debug message =>
      constructor
      · intro h
        cases h with
        | letValue value matched body =>
            cases value with
            | tuple items =>
                simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
                subst_vars
                cases body with
                | tuple result => cases result; exact ⟨_, items, rfl⟩
      · rintro ⟨values, items, applied⟩
        simp only [Builtin.apply, Except.ok.injEq] at applied
        subst result
        exact .letValue (bindings := []) (.tuple items) (by simp [Aiur.Pattern.bindings]) (.tuple .nil)

end Aiur.Generic.BuiltinLowering
