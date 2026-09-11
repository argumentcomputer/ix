import Ix.Compiler.X86.ScalarCalls

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem Checked.function_valid (checked : Checked) {index : Nat} {function : Function}
    (found : checked.program.functions[index]? = some function) :
    function.parameters ≤ 2 ∧ function.body.valid checked.program.functions index function.parameters = true := by
  have valid := checked.valid
  simp only [Program.valid, Bool.and_eq_true] at valid
  have member : (function, index) ∈ checked.program.functions.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using found)
  have accepted := List.all_eq_true.mp valid.2 (function, index) member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.1, accepted.2⟩

theorem Output.function_code {checked : Checked} (output : Output checked) {index : Nat} {function : Function}
    (found : checked.program.functions[index]? = some function) :
    ∃ plan, output.plans[index]? = some plan ∧
      FunctionCode output.target (output.plans.map (·.entry)) function plan := by
  obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
  have planBound : index < output.plans.size := by rw [output.size]; exact bound
  have accepted := Array.all_eq_true.mp output.verified index (by simp [Array.size_zip, output.size, bound])
  simp only [Array.getElem_zip, equal] at accepted
  exact ⟨output.plans[index], Array.getElem?_eq_getElem planBound, FunctionPlan.code accepted⟩

/-- Structural compilation preserves every evaluation in the admitted
language, including overflow. The stack premise depends only on function
rank, never on runtime values or an x86 execution certificate. -/
theorem Evaluates.native {checked : Checked} (output : Output checked)
    {expression : Expr} {values : Array Word} {result : Option Word}
    (evaluated : Evaluates checked.program.functions expression values result) :
    ∀ (current : Nat) (plan : Plan) (success failure : BlockId) (layout : Layout) (frame : Frame layout)
      (rootTop : Nat) (returns : List ReturnFrame),
      expression.valid checked.program.functions current values.size = true →
      plan.expression = expression →
      plan.matches output.target.program (output.plans.map (·.entry)) values.size success failure = true →
      output.target.program.hasBlock success = true → output.target.program.hasBlock failure = true →
      frameStride * (current + 1) - 1 ≤ frame.top → frame.top ≤ rootTop →
      ExprContract output.target plan success failure layout frame values rootTop returns result := by
  induction evaluated with
  | atom found =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      intro outside memory state holes framed valuesAt safeHoles frames represented
      exact atom_run (blockMatches_code matched) successValid framed valuesAt safeHoles represented found
  | add leftValue rightValue =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      intro outside memory state holes framed valuesAt safeHoles frames represented
      exact add_run (blockMatches_code matched) successValid failureValid framed valuesAt safeHoles represented leftValue rightValue
  | sub leftValue rightValue =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      simp only [Plan.matches, Bool.and_eq_true] at matched
      intro outside memory state holes framed valuesAt safeHoles frames represented
      exact sub_run (blockMatches_code matched.1.1) (blockMatches_code matched.1.2) (blockMatches_code matched.2)
        successValid framed valuesAt safeHoles represented leftValue rightValue
  | @letE values value body bound result first rest ihFirst ihRest =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      rename_i join valuePlan bodyPlan
      simp only [Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact let_contract valid.1.1 (blockMatches_code matched.1.1) (Plan.entry_valid matched.2)
        (ihFirst current valuePlan join failure layout frame rootTop returns valid.1.2 rfl matched.1.2
          (blockMatches_code matched.1.1).hasBlock failureValid capacity below)
        (ihRest current bodyPlan success failure layout frame rootTop returns (by simpa using valid.2) rfl
          (by simpa using matched.2) successValid failureValid capacity below)
  | @letOverflow values value body first ihFirst =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      rename_i join valuePlan bodyPlan
      simp only [Expr.valid, Bool.and_eq_true] at valid
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact let_overflow_contract (ihFirst current valuePlan join failure layout frame rootTop returns valid.1.2 rfl matched.1.2
        (blockMatches_code matched.1.1).hasBlock failureValid capacity below)
  | @zero values scrutinee zero successor result scrutineeValue taken ih =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      rename_i entry zeroPlan successorPlan
      simp only [Expr.valid, Bool.and_eq_true] at valid
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact branch_contract scrutineeValue (blockMatches_code matched.1.1)
        (by simpa using Plan.entry_valid matched.1.2)
        (by simpa using (ih current zeroPlan success failure layout frame rootTop returns valid.1.2 rfl matched.1.2
          successValid failureValid capacity below))
  | @successor values scrutinee zero successor value result scrutineeValue positive taken ih =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      rename_i entry zeroPlan successorPlan
      simp only [Expr.valid, Bool.and_eq_true] at valid
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact branch_contract scrutineeValue (blockMatches_code matched.1.1)
        (by simpa [positive] using Plan.entry_valid matched.2)
        (by simpa [positive] using (ih current successorPlan success failure layout frame rootTop returns valid.2 rfl matched.2
          successValid failureValid capacity below))
  | @call values supplied function arguments callee result found argumentsAt arity evaluated ih =>
      intro current plan success failure layout frame rootTop returns valid same matched successValid failureValid capacity below
      cases plan <;> cases same
      rename_i entry
      simp only [Expr.valid, found, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
      obtain ⟨calleePlan, planFound, calleeCode⟩ := output.function_code found
      have entryFound : (output.plans.map (·.entry))[function]? = some calleePlan.entry := by simp [planFound]
      simp only [Plan.matches, entryFound] at matched
      have enough : 67 ≤ frame.top := by simp only [frameStride] at capacity; omega
      apply call_contract enough below valid.1.1.2 argumentsAt (blockMatches_code matched) calleeCode successValid failureValid
      intro activeReturns
      apply function_contract calleeCode arity
      apply ih function calleePlan.body calleePlan.success calleePlan.failure layout (frame.child enough) rootTop activeReturns
      · simpa only [arity] using (checked.function_valid found).2
      · exact calleeCode.expression
      · simpa only [arity] using calleeCode.body
      · exact calleeCode.success.hasBlock
      · exact calleeCode.failure.hasBlock
      · simp only [Frame.child, frameStride] at *
        omega
      · simp only [Frame.child, frameStride]
        omega

theorem Output.function_contract {checked : Checked} (output : Output checked)
    {index : Nat} {function : Function} {plan : FunctionPlan} {values : Array Word} {result : Option Word}
    {layout : Layout} {frame : Frame layout} {rootTop : Nat} {returns : List ReturnFrame}
    (found : checked.program.functions[index]? = some function)
    (code : FunctionCode output.target (output.plans.map (·.entry)) function plan)
    (arity : values.size = function.parameters)
    (evaluated : Evaluates checked.program.functions function.body values result)
    (capacity : frameStride * (index + 1) - 1 ≤ frame.top) (below : frame.top ≤ rootTop) :
    FunctionContract output.target plan layout frame values rootTop returns result :=
  Scalar.function_contract code arity
    (evaluated.native output index plan.body plan.success plan.failure layout frame rootTop returns
      (by simpa only [arity] using (checked.function_valid found).2) code.expression
      (by simpa only [arity] using code.body) code.success.hasBlock code.failure.hasBlock capacity below)

end Ix.Compiler.X86.Scalar
