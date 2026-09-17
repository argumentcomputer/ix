import Compilatrix.Ixby.Inline.StackSteps

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

private def Bounded (limit : Nat) (result : Except Error Transition) : Prop :=
  ∀ next, result = .ok (.next next) → next.continuation.size ≤ limit

private theorem bind_bounded {action : Except Error α} {next : α → Except Error Transition}
    {limit : Nat} (bound : ∀ value, action = .ok value → Bounded limit (next value)) :
    Bounded limit (action >>= next) := by
  cases found : action with
  | error error => intro _ impossible; cases impossible
  | ok value => exact bound value found

private theorem next_bounded {limit : Nat} {state : State}
    (bound : state.continuation.size ≤ limit) (control : Control) :
    Bounded limit (.ok (.next { state with control })) := by
  intro next same
  cases same
  exact bound

private theorem error_bounded (limit : Nat) (error : Error) : Bounded limit (.error error) := by
  intro _ impossible
  cases impossible

private theorem stepEval_bounded (limits : Limits) (program : Program) (state : State) (frame : Frame)
    (incoming : state.continuation.size ≤ limits.continuations) :
    Bounded limits.continuations (stepEval limits program state frame) := by
  unfold stepEval
  apply bind_bounded
  intro block _
  cases block.instruction with
  | letOp operation next =>
    apply bind_bounded
    intro action _
    cases action with
    | value value =>
      apply bind_bounded
      intro resumed _
      exact next_bounded incoming _
    | call callee args =>
      apply bind_bounded
      intro pushed accepted
      apply bind_bounded
      intro entered _
      exact next_bounded (push_bound accepted) _
    | apply function args =>
      apply bind_bounded
      intro pushed accepted
      exact next_bounded (push_bound accepted) _
  | ret operand =>
    apply bind_bounded
    intro value _
    exact next_bounded incoming _
  | tailCall callee args =>
    apply bind_bounded
    intro values _
    apply bind_bounded
    intro entered _
    exact next_bounded incoming _
  | tailCallSelf args =>
    apply bind_bounded
    intro values _
    apply bind_bounded
    intro entered _
    exact next_bounded incoming _
  | tailApply operand args =>
    apply bind_bounded
    intro function _
    apply bind_bounded
    intro values _
    exact next_bounded incoming _
  | caseCtor operand alternatives =>
    apply bind_bounded
    intro value _
    cases value with
    | ctor id fields =>
      apply bind_bounded
      intro next _
      apply bind_bounded
      intro resumed _
      exact next_bounded incoming _
    | _ => exact error_bounded _ _
  | caseNat operand ifZero ifSucc =>
    apply bind_bounded
    intro value _
    cases value with
    | scalar scalar =>
      cases scalar with
      | nat n =>
        cases n <;> apply bind_bounded <;> intro resumed _ <;> exact next_bounded incoming _
      | _ => exact error_bounded _ _
    | _ => exact error_bounded _ _
  | branch operand yes no =>
    apply bind_bounded
    intro value _
    cases value with
    | scalar scalar =>
      cases scalar with
      | bool condition =>
        apply bind_bounded
        intro resumed _
        exact next_bounded incoming _
      | _ => exact error_bounded _ _
    | _ => exact error_bounded _ _

private theorem stepApply_bounded (limits : Limits) (program : Program) (state : State)
    (value : Value) (args : Array Value) (incoming : state.continuation.size ≤ limits.continuations) :
    Bounded limits.continuations (stepApply limits program state value args) := by
  unfold stepApply
  by_cases empty : args.isEmpty = true
  · simp only [if_pos empty]
    exact next_bounded incoming _
  · simp only [if_neg empty]
    cases value with
    | erased => exact next_bounded incoming _
    | pap callee captured =>
      apply bind_bounded
      intro function _
      by_cases invalid : captured.size ≥ function.arity
      · simp only [if_pos invalid, except_throw, bind, Except.bind]
        exact error_bounded _ _
      · simp only [if_neg invalid]
        by_cases under : (captured ++ args).size < function.arity
        · simp only [if_pos under]
          exact next_bounded incoming _
        · simp only [if_neg under]
          by_cases restEmpty : ((captured ++ args).extract function.arity).isEmpty = true
          · simp only [if_pos restEmpty, except_pure, bind, Except.bind]
            apply bind_bounded
            intro entered _
            exact next_bounded incoming _
          · simp only [if_neg restEmpty]
            apply bind_bounded
            intro pushed accepted
            apply bind_bounded
            intro entered _
            exact next_bounded (push_bound accepted) _
    | _ => exact error_bounded _ _

/-- Every successful next state stays within the admitted continuation budget,
including dynamic application and over-application. -/
theorem step_bound {limits : Limits} {program : Program} {state next : State}
    (incoming : state.continuation.size ≤ limits.continuations)
    (accepted : step limits program state = .ok (.next next)) :
    next.continuation.size ≤ limits.continuations := by
  cases state with
  | mk control continuation =>
    cases control with
    | eval frame => exact stepEval_bounded limits program _ frame incoming next accepted
    | apply value args => exact stepApply_bounded limits program _ value args incoming next accepted
    | ret value =>
      change continuation.size ≤ limits.continuations at incoming
      have popped : continuation.pop.size ≤ limits.continuations := by
        simp only [Array.size_pop]
        omega
      cases last : continuation.back? with
      | none => simp [step, last] at accepted
      | some cont =>
        cases cont with
        | apply args =>
          have bounded : Bounded limits.continuations (step limits program ⟨.ret value, continuation⟩) := by
            simpa only [step, last, except_pure] using
              next_bounded (state := ⟨.ret value, continuation.pop⟩) popped (.apply value args)
          exact bounded next accepted
        | resume frame =>
          have bounded : Bounded limits.continuations (step limits program ⟨.ret value, continuation⟩) := by
            simp only [step, last]
            apply bind_bounded
            intro resumed _
            exact next_bounded (state := ⟨.ret value, continuation.pop⟩) popped (.eval resumed)
          exact bounded next accepted

end Compilatrix.Ixby.Inline
