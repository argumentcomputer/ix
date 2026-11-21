import Aiur.Tuple.Circuit.ExpressionCorrectness
import Aiur.Tuple.Circuit.CompileFacts

namespace Aiur.Tuple.Circuit

theorem Chip.premises_forall [Field F] [DecidableEq F] (chip : Chip F) (row : Row F)
    (property : Message F → Prop) :
    (∀ message ∈ chip.premises row, property message) ↔
      ∀ send ∈ chip.sends, send.enable.denote row.assignment = 1 →
        property (send.message row.assignment) := by
  constructor
  · intro valid send member enabled
    apply valid (send.message row.assignment)
    apply List.mem_filterMap.mpr
    exact ⟨send, member, by simp [enabled]⟩
  · intro valid message member
    obtain ⟨send, sendMember, selected⟩ := List.mem_filterMap.mp member
    split at selected
    · rename_i enabled
      cases selected
      exact valid send sendMember enabled
    · cases selected

namespace Compiler

theorem parameter_environment [Field F] (names : List String) (inputs : List (Value Var))
    (assignment : Var → F) :
    localsEnvironment (names.zip (inputs.map (Value.map ArithExpr.var))) assignment =
      names.zip (inputs.map (Value.map assignment)) := by
  induction names generalizing inputs with
  | nil => simp [localsEnvironment]
  | cons name names ih =>
      cases inputs with
      | nil => simp [localsEnvironment]
      | cons input inputs =>
          simp only [List.map_cons, List.zip_cons_cons]
          change (name, _) :: localsEnvironment _ assignment = _
          rw [ih]
          simp only [Value.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote]

/-- One compiled chip recovers its source body using its enabled messages as call premises. -/
theorem lowerFunction_sound [Field F] [DecidableEq F]
    {program : Program F} {fn : Function F} {chip : Chip F}
    (compiled : lowerFunction program fn = .ok chip)
    {calls : CallRelation F} {row : Row F} (valid : chip.ValidRow row)
    (premises : ∀ message ∈ chip.premises row,
      calls message.channel message.args message.result) :
    EvalExprWith calls ((fn.params.map Prod.fst).zip (chip.receive row).args) fn.body
      (chip.receive row).result := by
  obtain ⟨inputs, output, s₁, s₂, body, s₃, s₄, _, _, bodyRun, outputRun, rfl⟩ :=
    lowerFunction_stages compiled
  have stateValid : s₄.Valid calls row.assignment := ⟨valid.2.2,
    (Chip.premises_forall _ row (fun message =>
      calls message.channel message.args message.result)).mp premises⟩
  obtain ⟨s₃Valid, resultEq⟩ := constrainValue_sound outputRun stateValid
  have evaluated := (lowerExpr_sound bodyRun s₃Valid).2 rfl
  have result := resultEq rfl
  simp only [Value.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] at result
  change output.map row.assignment = body.map (ArithExpr.denote row.assignment) at result
  simpa only [parameter_environment, Chip.receive, result] using evaluated

end Compiler
end Aiur.Tuple.Circuit
