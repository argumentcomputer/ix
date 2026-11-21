import Aiur.Scalar.Semantics.WithCalls
import Aiur.Scalar.Circuit.CompileFacts
import Aiur.Scalar.Circuit.Derivation
import Aiur.Scalar.Circuit.ExpressionCorrectness
import Aiur.Scalar.Circuit.WitnessCorrectness

namespace Aiur.Scalar.Circuit.Compiler

/--
Satisfying a compiled body recovers its
source evaluation, provided every enabled call is justified by `calls`.
This lemma does not assume anything about recursive function evaluation.
-/
theorem lowerFunction_sound [Field F] [DecidableEq F]
    {defn : Function F} {chip : Chip F} (compiled : lowerFunction defn = .ok chip)
    {calls : CallRelation F} {row : Row F} (valid : chip.ValidRow row)
    (premises : ∀ message ∈ chip.premises row,
      calls message.channel message.args message.result) :
    EvalExprWith calls (defn.params.zip (chip.receive row).args) defn.body
      (chip.receive row).result := by
  cases lowered :
      (lowerExpr defn.name (defn.params.zip (List.range defn.params.length))
        (.const 1) defn.body).run { nextVar := defn.params.length + 1 } with
  | error error => simp [lowerFunction, lowered] at compiled
  | ok output =>
      rcases output with ⟨polynomial, state⟩
      simp [lowerFunction, lowered] at compiled
      subst chip
      have callsValid := (Chip.premises_forall _ row
        (fun message => calls message.channel message.args message.result)).mp premises
      have stateValid : state.Valid calls row.assignment := {
        constraints := fun equation member =>
          valid.2.2 equation (by simp [member])
        calls := callsValid
      }
      have body := (lowerExpr_sound lowered stateValid).2 rfl
      have outputEquation := valid.2.2 (.sub (.var defn.params.length) polynomial) (by simp)
      have result : row.assignment defn.params.length = polynomial.denote row.assignment := by
        exact sub_eq_zero.mp outputEquation
      have enough : defn.params.length ≤ row.values.length := by
        have arity := valid.receive_arity
        simp only [Chip.receive, List.length_take] at arity
        omega
      simpa only [localsEnvironment, parameter_environment defn.params row enough,
        Chip.receive, result] using body

/--
Construct a simultaneous assignment for
one compiled body. Inactive branches must be satisfiable without evaluating them.
-/
theorem lowerFunction_complete [Field F] [DecidableEq F]
    {defn : Function F} {chip : Chip F} (compiled : lowerFunction defn = .ok chip)
    {calls : CallRelation F} {args : List F} {result : F}
    (arity : defn.params.length = args.length)
    (body : EvalExprWith calls (defn.params.zip args) defn.body result) :
    ∃ row, row.chip = defn.name ∧ chip.ValidRow row ∧
      chip.receive row = ⟨defn.name, args, result⟩ ∧
      ∀ message ∈ chip.premises row, calls message.channel message.args message.result := by
  cases lowered :
      (lowerExpr defn.name (defn.params.zip (List.range defn.params.length))
        (.const 1) defn.body).run { nextVar := defn.params.length + 1 } with
  | error error => simp [lowerFunction, lowered] at compiled
  | ok output =>
      rcases output with ⟨polynomial, state⟩
      simp [lowerFunction, lowered] at compiled
      subst chip
      let initial : Row F := ⟨defn.name, args ++ [result]⟩
      have environment : localsEnvironment
          (defn.params.zip (List.range defn.params.length)) initial.assignment = defn.params.zip args := by
        simpa [localsEnvironment, initial, arity] using
          parameter_environment defn.params initial (by simp [initial, arity])
      have sourceBody : EvalExprWith calls
          (localsEnvironment (defn.params.zip (List.range defn.params.length)) initial.assignment)
          defn.body result := by rw [environment]; exact body
      have localsBound : ∀ binding ∈ defn.params.zip (List.range defn.params.length),
          binding.2 < defn.params.length + 1 := by
        intro binding member
        have bound := List.mem_range.mp (List.of_mem_zip member).2
        omega
      obtain ⟨values, extension, size, layout, polynomialBound, stateValid, resultValue⟩ :=
        lowerExpr_complete lowered
          ⟨by simp, by simp⟩ localsBound rfl (initial := initial.values)
          (by simp [initial, arity]) ⟨by simp [Satisfies], by simp⟩ rfl sourceBody
      let row : Row F := ⟨defn.name, values⟩
      change polynomial.denote row.assignment = result at resultValue
      have outputBound : defn.params.length < state.nextVar := by
        have bound := extension.length_le
        simp only [initial, List.length_append, List.length_singleton, ← arity] at bound
        omega
      have outputValue : row.assignment defn.params.length = result := by
        rw [Row.assignment_of_prefix (before := initial) (after := row) extension
          (by simp [initial, arity])]
        simp [initial, Row.assignment, arity]
      have inputs : values.take defn.params.length = args := by
        obtain ⟨extra, shape⟩ := extension
        rw [← shape]
        simp [initial, List.append_assoc, arity]
      refine ⟨row, rfl, ⟨?_, size, ?_⟩, ?_, ?_⟩
      · simp [Chip.wellFormed, outputBound, layout.constraints, layout.sends,
          ArithExpr.inBounds, polynomialBound]
      · intro equation member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | same
        · exact stateValid.constraints equation member
        · subst equation
          simp only [ArithExpr.denote, outputValue, resultValue, sub_self]
      · simp only [Chip.receive, row, inputs, outputValue]
      · exact (Chip.premises_forall _ row
          (fun message => calls message.channel message.args message.result)).mpr stateValid.calls

end Aiur.Scalar.Circuit.Compiler
