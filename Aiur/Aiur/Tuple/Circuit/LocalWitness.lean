import Aiur.Tuple.Circuit.ExpressionWitness
import Aiur.Tuple.Circuit.LocalCorrectness
import Aiur.Tuple.Circuit.RowWitness

namespace Aiur.Tuple.Circuit.Compiler

private theorem parameter_types (params : List (String × Ty)) (args : List (Value F))
    (types : params.map Prod.snd = args.map Value.type) :
    environmentTypes ((params.map Prod.fst).zip args) = params := by
  induction params generalizing args with
  | nil => cases args <;> simp_all [environmentTypes]
  | cons param params ih =>
      cases args with
      | nil => simp at types
      | cons arg args =>
          simp only [List.map_cons, List.cons.injEq] at types
          simp only [List.map_cons, List.zip_cons_cons, environmentTypes, List.map_cons]
          rw [← types.1]
          exact congrArg (param :: ·) (ih args types.2)

private theorem parameter_bounded {names : List String} {inputs : List (Value Var)} {bound : Nat}
    (bounded : ∀ input ∈ inputs, Bounded (F := F) bound (input.map ArithExpr.var)) :
    LocalsBounded (F := F) bound (names.zip (inputs.map (Value.map ArithExpr.var))) := by
  intro binding member
  obtain ⟨_, inside⟩ := List.of_mem_zip member
  obtain ⟨input, member, same⟩ := List.mem_map.mp inside
  rw [← same]
  exact bounded input member

/-- A finite source body evaluation yields a finite chip row, with exactly its enabled premises. -/
theorem lowerFunction_complete [Field F] [DecidableEq F]
    {program : Program F} {fn : Function F} {chip : Chip F}
    (compiled : lowerFunction program fn = .ok chip)
    {calls : CallRelation F} (typed : CallsTyped program calls)
    (checked : inferType program fn.name fn.params fn.body = .ok fn.result)
    {args : List (Value F)} {value : Value F}
    (types : fn.params.map Prod.snd = args.map Value.type)
    (evaluated : EvalExprWith calls ((fn.params.map Prod.fst).zip args) fn.body value) :
    ∃ row, row.chip = fn.name ∧ chip.ValidRow row ∧ chip.receive row = ⟨fn.name, args, value⟩ ∧
      ∀ message ∈ chip.premises row, calls message.channel message.args message.result := by
  have resultType : value.type = fn.result :=
    evaluated.type typed fn.name fn.result (by rw [parameter_types fn.params args types]; exact checked)
  obtain ⟨inputs, output, s₁, s₂, body, s₃, s₄, inputsRun, outputRun, bodyRun, constraintRun, rfl⟩ :=
    lowerFunction_stages compiled
  have emptyLayout : ({} : BuildState F).WellFormed := ⟨by simp, by simp⟩
  have emptyValid : ({} : BuildState F).Valid calls (fun _ => 0) := ⟨by simp [Satisfies, Scalar.Circuit.Satisfies], by simp⟩
  obtain ⟨a, e₁, inputsBound, inputsEq⟩ := freshValues_complete inputsRun emptyLayout emptyValid args types.symm
  obtain ⟨b, e₂, outputBound, outputEq⟩ := freshValue_complete outputRun e₁.layout e₁.valid value resultType
  have inputsEqB : inputs.map (Value.map b) = args := by
    rw [← inputsEq]
    exact List.map_congr_left (fun input member => e₂.variables (inputsBound input member))
  obtain ⟨c, e₃, bodyBound, bodyEq⟩ := lowerExpr_complete bodyRun typed e₂.layout e₂.valid
    (parameter_bounded (fun input member => (inputsBound input member).mono e₂.increase)) rfl rfl
    (by rw [parameter_environment, inputsEqB]; exact evaluated)
  have resultEq : (output.map ArithExpr.var).map (ArithExpr.denote c) = value := by
    simpa only [Value.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using (e₃.variables outputBound).trans outputEq
  have e₄ := constrainValue_complete constraintRun e₃.layout e₃.valid rfl
    (outputBound.mono e₃.increase) bodyBound (Or.inr (resultEq.trans bodyEq.symm))
  let row := Row.ofAssignment fn.name s₄.nextVar c
  have finiteExt := BuildState.finite_witness e₄.layout e₄.valid fn.name
  have inputFinal : ∀ input ∈ inputs, Bounded (F := F) s₄.nextVar (input.map ArithExpr.var) :=
    fun input member => (inputsBound input member).mono ((e₂.trans e₃).trans e₄).increase
  have outputFinal := outputBound.mono (e₃.trans e₄).increase
  have rowValid : (Chip.mk fn.name inputs output s₄.nextVar s₄.constraints.toList s₄.sends.toList).ValidRow row :=
    ⟨chip_wellFormed e₄.layout inputFinal outputFinal, Row.ofAssignment_length _ _ _, finiteExt.valid.constraints⟩
  refine ⟨row, rfl, rowValid, ?_, ?_⟩
  · change Message.mk fn.name (inputs.map (Value.map row.assignment)) (output.map row.assignment) = _
    have ins : inputs.map (Value.map row.assignment) = args := by
      rw [← inputsEq]
      apply List.map_congr_left
      intro input member
      exact (((e₂.trans e₃).trans e₄).trans finiteExt).variables (inputsBound input member)
    have out : output.map row.assignment = value :=
      (((e₃.trans e₄).trans finiteExt).variables outputBound).trans outputEq
    rw [ins, out]
  · exact (Chip.premises_forall _ row (fun message =>
      calls message.channel message.args message.result)).mpr finiteExt.valid.calls

end Aiur.Tuple.Circuit.Compiler
