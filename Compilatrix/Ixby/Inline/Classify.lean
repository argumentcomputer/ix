import Compilatrix.Ixby.Inline.Frames

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

inductive StepChoice (limits : Limits) (source target : Program) : State → Prop
  | same (state : State) (equal : step limits source state = step limits target state) :
      StepChoice limits source target state
  | inlineCall (frame : Frame) (continuation : Array Continuation) (locals : Nat)
      (callee : FunctionId) (args : List Operand) (next : BlockId) (leaf : Leaf) (replacement : PureOp)
      (before : frame.check limits source = .ok ⟨locals, .letOp (.call callee args) next⟩)
      (after : frame.check limits target = .ok ⟨locals, .letOp replacement.toOp next⟩)
      (body : source.getFunction callee = .ok leaf.function)
      (arity : args.length = leaf.arity) (arguments : operandsBound locals args)
      (room : leaf.arity + 1 ≤ limits.locals)
      (substituted : leaf.operation.substitute args = some replacement) :
      StepChoice limits source target ⟨.eval frame, continuation⟩

theorem SameLayout.check_error {source target} (same : SameLayout source target)
    {limits : Limits} {frame : Frame} {error : Error}
    (checked : frame.check limits source = .error error) : frame.check limits target = .error error := by
  have checks := same.check limits frame
  cases candidate : frame.check limits target with
  | error error' => simpa [checked, candidate, Except.map] using checks.symm
  | ok block => simp [checked, candidate, Except.map] at checks

/-- Classification is derived from complete-image evidence for any machine
state. It assumes no successful source run, concrete input, or source program. -/
theorem ProgramRelated.classify {limits source target} (related : ProgramRelated limits source target)
    (state : State) : StepChoice limits source target state := by
  cases state with
  | mk control continuation =>
    cases control with
    | ret value => exact .same _ (step_ret_same related.layout value continuation)
    | apply value args => exact .same _ (related.layout.stepApply limits _ value args)
    | eval frame =>
      cases checked : frame.check limits source with
      | error error =>
        have after := related.layout.check_error checked
        exact .same _ (by simp [step, stepEval, checked, after, bind, Except.bind])
      | ok before =>
        obtain ⟨after, checkedAfter, blockRelated⟩ := related.checked checked
        rcases before with ⟨locals, instruction⟩
        rcases after with ⟨afterLocals, afterInstruction⟩
        rcases blockRelated with ⟨localsEq, instructions⟩
        change locals = afterLocals at localsEq
        subst afterLocals
        cases instructions with
        | same instruction =>
          exact .same _ (stepEval_same related.layout _ frame _ _ checked checkedAfter rfl)
        | inlineCall callee args next leaf replacement body arity arguments room substituted =>
          exact .inlineCall frame continuation locals callee args next leaf replacement
            checked checkedAfter body arity arguments room substituted

end Compilatrix.Ixby.Inline
