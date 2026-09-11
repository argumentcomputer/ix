import Ix.Compiler.Sim

/-! The public application corollary of erasure simulation, for exported
functions invoked with runtime values. It uses the existing relation and
member coverage, including their sharing and oracle premises. -/

namespace Ix.Compiler.Sim

variable [scope : MemberScope]

/-- Retain the call-aware application trace needed by lowering progress. -/
theorem apply_sim_projectionSafe_with_members {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {fuel : Nat} {function argument result : Ixon.Eval.Value}
    {targetFunction targetArgument : IxIR0.Value}
    (members : MemberCoverage ectx ictx scope.plan) (oracles : OracleRel ectx ictx)
    (applied : Ixon.Eval.apply ectx fuel function argument = .ok result)
    (functionRel : ValRel ectx ictx function targetFunction)
    (argumentRel : ValRel ectx ictx argument targetArgument) :
    ∃ targetFuel targetResult,
      IxIR0.ProjectionSafe.Apply ictx targetFuel targetFunction targetArgument targetResult ∧
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
          exact ⟨_, targetResult, appliedTrace, resultRel⟩

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
  obtain ⟨targetFuel, targetResult, trace, related⟩ :=
    apply_sim_projectionSafe_with_members members oracles applied functionRel argumentRel
  exact ⟨targetFuel, targetResult, trace.run, related⟩

/-- A runtime application vector gets one finite trace bound, constructed
from its individual source applications. No target execution is assumed. -/
theorem applyMany_sim_projectionSafe_with_members {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    (members : MemberCoverage ectx ictx scope.plan) (oracles : OracleRel ectx ictx)
    {fuel : Nat} {function result : Ixon.Eval.Value} {arguments : List Ixon.Eval.Value}
    {targetFunction : IxIR0.Value} {targetArguments : List IxIR0.Value}
    (applied : Ixon.Eval.applyMany ectx fuel function arguments = .ok result)
    (functionRel : ValRel ectx ictx function targetFunction)
    (argumentsRel : ValsRel ectx ictx arguments targetArguments) :
    ∃ limit targetResult,
      IxIR0.ProjectionSafe.AppliesBelow ictx limit targetFunction targetArguments targetResult ∧
      ValRel ectx ictx result targetResult := by
  induction fuel generalizing function result arguments targetFunction targetArguments with
  | zero => simp [Ixon.Eval.applyMany] at applied
  | succ fuel ih =>
    cases argumentsRel with
    | nil =>
      simp only [Ixon.Eval.applyMany, Except.ok.injEq] at applied
      subst result
      exact ⟨0, targetFunction, .nil, functionRel⟩
    | @cons argument targetArgument arguments targetArguments argumentRel argumentsRel =>
      cases first : Ixon.Eval.apply ectx fuel function argument with
      | error error => simp [Ixon.Eval.applyMany, first, bind, Except.bind] at applied
      | ok middle =>
        have rest : Ixon.Eval.applyMany ectx fuel middle arguments = .ok result := by
          simpa [Ixon.Eval.applyMany, first, bind, Except.bind] using applied
        obtain ⟨firstFuel, targetMiddle, firstTrace, middleRel⟩ :=
          apply_sim_projectionSafe_with_members members oracles first functionRel argumentRel
        obtain ⟨limit, targetResult, restTrace, resultRel⟩ := ih rest middleRel argumentsRel
        exact ⟨firstFuel + limit + 1, targetResult,
          .cons (by omega) firstTrace (restTrace.mono_limit (by omega)), resultRel⟩

theorem applyMany_sim_projectionSafe_inlineSharing {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    (members : MemberCoverage ectx.inlineSharing ictx scope.plan)
    (oracles : OracleRel ectx.inlineSharing ictx)
    {fuel : Nat} {function result : Ixon.Eval.Value} {arguments : List Ixon.Eval.Value}
    {targetFunction : IxIR0.Value} {targetArguments : List IxIR0.Value}
    (contextWF : ectx.SharingWF) (functionWF : function.SharingWF)
    (argumentsWF : Ixon.Eval.ValuesSharingWF arguments)
    (applied : Ixon.Eval.applyMany ectx fuel function arguments = .ok result)
    (functionRel : InlinedValRel ectx ictx function targetFunction)
    (argumentsRel : ValsRel ectx.inlineSharing ictx
      (Ixon.Eval.valuesInlineSharing arguments) targetArguments) :
    ∃ limit targetResult,
      IxIR0.ProjectionSafe.AppliesBelow ictx limit targetFunction targetArguments targetResult ∧
      InlinedValRel ectx ictx result targetResult := by
  exact applyMany_sim_projectionSafe_with_members members oracles
    (Ixon.Eval.applyMany_inlineSharing contextWF functionWF argumentsWF applied).1 functionRel argumentsRel

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

end Ix.Compiler.Sim
