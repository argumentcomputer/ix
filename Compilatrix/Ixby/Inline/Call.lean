import Compilatrix.Ixby.Inline.Leaf

namespace Compilatrix.Ixby.Inline

open Ix.Ixby Runtime.Execution

/-- Every successful original call must complete its four nonterminal steps.
This extracts the actual result and saved-frame transfer from that run; neither
callee success nor continuation validity is assumed as an external callback. -/
theorem call_success {limits : Limits} {program : Program} {frame : Frame} {locals : Nat}
    {callee : FunctionId} {args : List Operand} {values : Array Value} {next : BlockId} {leaf : Leaf}
    (code : frame.check limits program = .ok ⟨locals, .letOp (.call callee args) next⟩)
    (read : frame.readOperands args = .ok values.toList)
    (body : program.getFunction callee = .ok leaf.function)
    (arity : values.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals)
    (continuation : Array Continuation) {fuel : Nat} {output : Value}
    (accepted : Ix.Ixby.run limits program fuel ⟨.eval frame, continuation⟩ = .ok output) :
    ∃ value resumed remaining,
      leaf.operation.eval limits program ⟨callee, 0, values⟩ = .ok value ∧
      frame.transfer limits program next #[value] = .ok resumed ∧
      fuel = remaining + 4 ∧
      Ix.Ixby.run limits program remaining ⟨.eval resumed, continuation⟩ = .ok output := by
  by_cases stack : continuation.size < limits.continuations
  · obtain ⟨afterCallFuel, countCall, afterCall⟩ :=
      run_after_step (call_step code read body arity room continuation stack) accepted
    cases evaluated : leaf.operation.eval limits program ⟨callee, 0, values⟩ with
    | error error =>
      have failed := Leaf.step_operation_error body values arity room error evaluated
        (continuation.push (.resume { frame with block := next }))
      cases afterCallFuel <;> simp [Ix.Ixby.run, failed] at afterCall
    | ok value =>
      have leafPath : Steps limits program 2
          (frameState callee 0 values (continuation.push (.resume { frame with block := next })))
          (returned value (continuation.push (.resume { frame with block := next }))) :=
        .cons (Leaf.step_operation body values arity room value evaluated _)
          (.cons (Leaf.step_return body values arity room value _) (.refl _))
      obtain ⟨afterReturnFuel, countLeaf, afterReturn⟩ := run_after_steps leafPath afterCall
      cases afterReturnFuel with
      | zero => simp [Ix.Ixby.run] at afterReturn
      | succ remaining =>
        cases transfer : frame.transfer limits program next #[value] with
        | error error =>
          have saved : ({ frame with block := next } : Frame).transfer limits program next #[value] =
              .error error := by simpa [Frame.transfer] using transfer
          simp [Ix.Ixby.run, step, returned, saved, bind, Except.bind] at afterReturn
        | ok resumed =>
          refine ⟨value, resumed, remaining, rfl, transfer, by omega, ?_⟩
          simpa [Ix.Ixby.run, resume_step continuation transfer] using afterReturn
  · have failed : step limits program ⟨.eval frame, continuation⟩ = .error (.limit .continuations) := by
      simp [step, stepEval, code, evalOp, read, State.push,
        show continuation.size ≥ limits.continuations by omega, bind, Except.bind]
    cases fuel <;> simp [Ix.Ixby.run, failed] at accepted

end Compilatrix.Ixby.Inline
