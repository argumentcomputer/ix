import Compilatrix.Ixby.Inline.Call
import Compilatrix.Ixby.Inline.Classify

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

/-- Every successful original execution is preserved with the identical fuel
and resource bounds. Each contracted ordinary call saves exactly three steps;
the optimized run may finish before exhausting the supplied original fuel. -/
theorem ProgramRelated.run_forward {limits source target} (related : ProgramRelated limits source target)
    {fuel : Nat} {state : State} {output : Value}
    (accepted : run limits source fuel state = .ok output) : run limits target fuel state = .ok output := by
  induction fuel using Nat.strongRecOn generalizing state with
  | ind fuel ih =>
    cases related.classify state with
    | same state equal =>
      cases fuel with
      | zero => simp [run] at accepted
      | succ fuel =>
        cases first : step limits source state with
        | error error => simp [run, first] at accepted
        | ok transition =>
          cases transition with
          | halted value => simpa [run, ← equal, first] using accepted
          | next next =>
            have rest : run limits source fuel next = .ok output := by simpa [run, first] using accepted
            simpa [run, ← equal, first] using ih fuel (by omega) rest
    | inlineCall frame continuation locals callee args next leaf replacement before after body arity arguments room substituted =>
      obtain ⟨_, _, _, _, localSize⟩ := check_success before
      obtain ⟨values, read⟩ := readOperands_of_bound frame (by simpa [localSize] using arguments)
      have valueArity : values.toArray.size = leaf.arity := by
        simpa [readOperands_length read] using arity
      have readArray : frame.readOperands args = .ok values.toArray.toList := by simpa using read
      obtain ⟨value, resumed, remaining, evaluated, transfer, count, rest⟩ :=
        call_success before readArray body valueArity room continuation accepted
      have replaced : replacement.eval limits source frame = .ok value := by
        rw [← PureOp.substitute_sound read substituted limits source callee 0]
        exact evaluated
      have operation : replacement.eval limits target frame = .ok value := by
        rw [← PureOp.eval_sameLayout related.layout]
        exact replaced
      have transferred : frame.transfer limits target next #[value] = .ok resumed := by
        rw [← related.layout.transfer]
        exact transfer
      have first := PureOp.step_value (continuation := continuation) after operation transferred
      have completed : run limits target (remaining + 1) ⟨.eval frame, continuation⟩ = .ok output := by
        simpa [run, first] using ih remaining (by omega) rest
      simpa [count, Nat.add_assoc] using run_add_fuel completed 3

end Compilatrix.Ixby.Inline
