import Compilatrix.Sim

/-! The public application corollary of erasure simulation, for exported
functions invoked with runtime values. It uses the existing relation and
member coverage, including their sharing and oracle premises. -/

namespace Compilatrix.Sim

variable [scope : MemberScope]

theorem apply_sim_with_members {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {fuel : Nat} {function argument result : Ixon.Eval.Value}
    {targetFunction targetArgument : IxIR0.Value}
    (members : MemberCoverage ectx ictx scope.plan) (oracles : OracleRel ectx ictx)
    (applied : Ixon.Eval.apply ectx fuel function argument = .ok result)
    (functionRel : ValRel ectx ictx function targetFunction)
    (argumentRel : ValRel ectx ictx argument targetArgument) :
    ∃ targetFuel targetResult,
      IxIR0.apply ictx targetFuel targetFunction targetArgument = .ok targetResult ∧
      ValRel ectx ictx result targetResult := by
  cases fuel with
  | zero => simp [Ixon.Eval.apply] at applied
  | succ fuel =>
    have source : Ixon.Eval.eval ectx (fuel + 2) {}
        [function, argument] (.app (.var 0) (.var 1)) = .ok result := by
      simpa [Ixon.Eval.eval, bind, Except.bind] using applied
    have erased : PErase ectx ictx none #[] #[] none [true, true]
        (.app (.var 0) (.var 1)) (.app (.var 0) (.var 1)) := .app (.var rfl) (.var rfl)
    have related : EnvRel ectx ictx none #[] #[] none [true, true]
        [function, argument] [targetFunction, targetArgument] :=
      .keep functionRel (.keep argumentRel .nil)
    obtain ⟨_, targetResult, trace, resultRel⟩ :=
      erasure_sim_projectionSafe_with_members members oracles source erased related
    cases trace with
    | app functionTrace argumentTrace appliedTrace =>
      cases functionTrace with
      | var functionAt =>
        simp only [List.getElem?_cons_zero] at functionAt
        cases functionAt
        cases argumentTrace with
        | var argumentAt =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at argumentAt
          cases argumentAt
          exact ⟨_, targetResult, appliedTrace.run, resultRel⟩

theorem apply_sim_inlineSharing {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {fuel : Nat} {function argument result : Ixon.Eval.Value}
    {targetFunction targetArgument : IxIR0.Value}
    (members : MemberCoverage ectx.inlineSharing ictx scope.plan)
    (oracles : OracleRel ectx.inlineSharing ictx)
    (contextWF : ectx.SharingWF) (functionWF : function.SharingWF) (argumentWF : argument.SharingWF)
    (applied : Ixon.Eval.apply ectx fuel function argument = .ok result)
    (functionRel : InlinedValRel ectx ictx function targetFunction)
    (argumentRel : InlinedValRel ectx ictx argument targetArgument) :
    ∃ targetFuel targetResult,
      IxIR0.apply ictx targetFuel targetFunction targetArgument = .ok targetResult ∧
      InlinedValRel ectx ictx result targetResult :=
  apply_sim_with_members members oracles
    (Ixon.Eval.apply_inlineSharing contextWF functionWF argumentWF applied).1 functionRel argumentRel

end Compilatrix.Sim
