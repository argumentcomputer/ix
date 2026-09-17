import Compilatrix.Ixby.Inline.Limits

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem push_extraStack {limits : Limits} {state nextState : State} {continuation : Continuation}
    (pushed : state.push limits continuation = .ok nextState) :
    state.push (extraStack limits) continuation = .ok nextState := by
  by_cases room : state.continuation.size < limits.continuations
  · have equal : nextState = { state with continuation := state.continuation.push continuation } := by
      simpa [State.push, show ¬state.continuation.size ≥ limits.continuations by omega] using pushed.symm
    subst nextState
    simp [State.push, extraStack, show ¬state.continuation.size ≥ limits.continuations + 1 by omega]
  · simp [State.push, show state.continuation.size ≥ limits.continuations by omega] at pushed

theorem push_bound {limits : Limits} {state nextState : State} {continuation : Continuation}
    (pushed : state.push limits continuation = .ok nextState) :
    nextState.continuation.size ≤ limits.continuations := by
  by_cases room : state.continuation.size < limits.continuations
  · have equal : nextState = { state with continuation := state.continuation.push continuation } := by
      simpa [State.push, show ¬state.continuation.size ≥ limits.continuations by omega] using pushed.symm
    subst nextState
    simp only [Array.size_push]
    omega
  · simp [State.push, show state.continuation.size ≥ limits.continuations by omega] at pushed

theorem stepEval_extraStack {limits : Limits} {program : Program} {state : State} {frame : Frame}
    {transition : Transition} (accepted : stepEval limits program state frame = .ok transition) :
    stepEval (extraStack limits) program state frame = .ok transition := by
  cases checked : frame.check limits program with
  | error error => simp [stepEval, checked, bind, Except.bind] at accepted
  | ok block =>
    cases instruction : block.instruction with
    | letOp operation next =>
      cases evaluated : evalOp limits program frame operation with
      | error error => simp [stepEval, checked, instruction, evaluated, bind, Except.bind] at accepted
      | ok action =>
        cases action with
        | value value =>
          simpa only [stepEval, check_extraStack, checked, instruction, evalOp_extraStack, evaluated,
            transfer_extraStack, bind, Except.bind] using accepted
        | call callee args =>
          cases pushed : state.push limits (.resume { frame with block := next }) with
          | error error => simp [stepEval, checked, instruction, evaluated, pushed, bind, Except.bind] at accepted
          | ok nextState =>
            have more := push_extraStack pushed
            simpa only [stepEval, check_extraStack, checked, instruction, evalOp_extraStack, evaluated,
              pushed, more, enter_extraStack, bind, Except.bind] using accepted
        | apply function args =>
          cases pushed : state.push limits (.resume { frame with block := next }) with
          | error error => simp [stepEval, checked, instruction, evaluated, pushed, bind, Except.bind] at accepted
          | ok nextState =>
            have more := push_extraStack pushed
            simpa only [stepEval, check_extraStack, checked, instruction, evalOp_extraStack, evaluated,
              pushed, more, bind, Except.bind] using accepted
    | _ =>
      simpa only [stepEval, check_extraStack, checked, instruction, enter_extraStack, transfer_extraStack,
        bind, Except.bind] using accepted

theorem stepApply_extraStack {limits : Limits} {program : Program} {state : State}
    {value : Value} {args : Array Value} {transition : Transition}
    (accepted : stepApply limits program state value args = .ok transition) :
    stepApply (extraStack limits) program state value args = .ok transition := by
  cases value with
  | pap callee captured =>
    cases found : program.getFunction callee with
    | error error => simpa only [stepApply, found, bind, Except.bind] using accepted
    | ok function =>
      by_cases empty : args.isEmpty = true
      · simpa only [stepApply, if_pos empty] using accepted
      · by_cases valid : captured.size < function.arity
        · have noInvalid : ¬captured.size ≥ function.arity := by omega
          by_cases under : (captured ++ args).size < function.arity
          · simpa only [stepApply, if_neg empty, found, if_neg noInvalid, if_pos under,
              bind, Except.bind] using accepted
          · by_cases restEmpty : ((captured ++ args).extract function.arity).isEmpty = true
            · simpa only [stepApply, if_neg empty, found, if_neg noInvalid, if_neg under,
                if_pos restEmpty, enter_extraStack,
                bind, Except.bind] using accepted
            · cases pushed : state.push limits (.apply ((captured ++ args).extract function.arity)) with
              | error error =>
                simp only [stepApply, if_neg empty, found, if_neg noInvalid, if_neg under,
                  if_neg restEmpty, pushed, bind, Except.bind] at accepted
                cases accepted
              | ok nextState =>
                have more := push_extraStack pushed
                simpa only [stepApply, if_neg empty, found, if_neg noInvalid, if_neg under,
                  if_neg restEmpty, pushed, more, enter_extraStack,
                  bind, Except.bind] using accepted
        · simp [stepApply, empty, found, show captured.size ≥ function.arity by omega,
            bind, Except.bind] at accepted
  | _ => exact accepted

theorem step_extraStack {limits : Limits} {program : Program} {state : State} {transition : Transition}
    (accepted : step limits program state = .ok transition) :
    step (extraStack limits) program state = .ok transition := by
  cases state with
  | mk control continuation =>
    cases control with
    | eval frame => exact stepEval_extraStack accepted
    | apply value args => exact stepApply_extraStack accepted
    | ret value =>
      simpa only [step, transfer_extraStack] using accepted

end Compilatrix.Ixby.Inline
