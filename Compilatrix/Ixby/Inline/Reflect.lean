import Compilatrix.Ixby.Inline.Forward
import Compilatrix.Ixby.Inline.StackBound

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

/-- Optimized success reflects to the original with at most four times the
fuel and one additional continuation slot. All scalar, collection, local-frame,
input, and code limits are unchanged. This rules out new successful values
arising from a changed computation rather than eliminated call overhead. -/
theorem ProgramRelated.run_reflect {limits source target} (related : ProgramRelated limits source target)
    {fuel : Nat} {state : State} {output : Value}
    (within : state.continuation.size ≤ limits.continuations)
    (accepted : run limits target fuel state = .ok output) :
    run (extraStack limits) source (4 * fuel) state = .ok output := by
  induction fuel generalizing state with
  | zero => simp [run] at accepted
  | succ fuel ih =>
    cases related.classify state with
    | same state equal =>
      cases first : step limits target state with
      | error error => simp [run, first] at accepted
      | ok transition =>
        have original := step_extraStack (equal.trans first)
        cases transition with
        | halted value =>
          have result : value = output := by simpa [run, first] using accepted
          have done : run (extraStack limits) source 1 state = .ok output := by simp [run, original, result]
          have padded := run_add_fuel done (4 * fuel + 3)
          have count : 1 + (4 * fuel + 3) = 4 * (fuel + 1) := by omega
          simpa only [count] using padded
        | next next =>
          have rest : run limits target fuel next = .ok output := by simpa [run, first] using accepted
          have reflected := ih (step_bound within first) rest
          have done : run (extraStack limits) source (4 * fuel + 1) state = .ok output := by
            simpa [run, original] using reflected
          simpa [Nat.mul_add, Nat.add_assoc] using run_add_fuel done 3
    | inlineCall frame continuation locals callee args next leaf replacement before after body arity arguments room substituted =>
      change continuation.size ≤ limits.continuations at within
      cases evaluated : replacement.eval limits target frame with
      | error error =>
        simp [run, step, stepEval, after, PureOp.eval_toOp, evaluated, Except.map, bind, Except.bind] at accepted
      | ok value =>
        cases transfer : frame.transfer limits target next #[value] with
        | error error =>
          simp [run, step, stepEval, after, PureOp.eval_toOp, evaluated, transfer,
            Except.map, bind, Except.bind] at accepted
        | ok resumed =>
          have first := PureOp.step_value (continuation := continuation) after evaluated transfer
          have rest : run limits target fuel ⟨.eval resumed, continuation⟩ = .ok output := by
            simpa [run, first] using accepted
          obtain ⟨_, _, _, _, localSize⟩ := check_success before
          obtain ⟨values, read⟩ := readOperands_of_bound frame (by simpa [localSize] using arguments)
          have valueArity : values.toArray.size = leaf.arity := by
            simpa [readOperands_length read] using arity
          have readArray : frame.readOperands args = .ok values.toArray.toList := by simpa using read
          have operation : leaf.operation.eval (extraStack limits) source ⟨callee, 0, values.toArray⟩ = .ok value := by
            rw [pureOp_extraStack, PureOp.substitute_sound read substituted,
              PureOp.eval_sameLayout related.layout]
            exact evaluated
          have originalBefore : frame.check (extraStack limits) source = .ok ⟨locals, .letOp (.call callee args) next⟩ := by
            rw [check_extraStack]
            exact before
          have originalTransfer : frame.transfer (extraStack limits) source next #[value] = .ok resumed := by
            rw [transfer_extraStack, related.layout.transfer]
            exact transfer
          have stack : continuation.size < (extraStack limits).continuations := by
            simp only [extraStack]
            omega
          have path := call_path originalBefore readArray body valueArity room continuation stack
            value operation resumed originalTransfer
          have completed := (path.run (4 * fuel)).trans (ih within rest)
          simpa [Nat.mul_add, Nat.add_comm] using completed

end Compilatrix.Ixby.Inline
