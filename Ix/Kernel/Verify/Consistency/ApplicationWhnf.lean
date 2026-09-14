/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaPublicWhnf

/-! The application branch's actual Pi-exposure call and its subsequent
argument check, comparison, and dependent codomain substitution. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

structure ApplicationWhnfInferenceTrace (fuel : Nat) (before : TcState .anon)
    (fn arg : KExpr .anon) where
  functionType : KExpr .anon
  domain : KExpr .anon
  codomain : KExpr .anon
  functionState : TcState .anon
  exposedState : TcState .anon
  argumentType : KExpr .anon
  argumentState : TcState .anon
  comparedState : TcState .anon
  functionRun : RecM.infer fn (methodsN fuel) before = .ok functionType functionState
  exposureRun : (RecM.ensureForallDirect functionType).run (methodsN (fuel + 1)) functionState =
    .ok (domain, codomain) exposedState
  argumentRun : RecM.infer arg (methodsN fuel) exposedState = .ok argumentType argumentState
  ordinary : TcM.isEagerReduce arg argumentState = .ok false argumentState
  compareRun : RecM.isDefEq argumentType domain (methodsN fuel) argumentState = .ok true comparedState
  contextPreserved : functionState.lctx = before.lctx

theorem ApplicationWhnfInferenceTrace.output_state {fuel : Nat} {before after : TcState .anon}
    {fn arg result : KExpr .anon} {info : ExprInfo .anon}
    (trace : ApplicationWhnfInferenceTrace fuel before fn arg)
    (accepted : RecM.inferUncached RecM.inferCall false (.app fn arg info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (subst trace.codomain arg 0 trace.comparedState.env.intern).1 ∧
      after = { trace.comparedState with env := { trace.comparedState.env with
        intern := (subst trace.codomain arg 0 trace.comparedState.env.intern).2 } } := by
  change (RecM.inferUncached RecM.inferCall false (.app fn arg info)).run
    (methodsN (fuel + 1)) before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer fn (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.functionRun] at accepted
  change EStateM.bind ((RecM.ensureForallDirect trace.functionType).run (methodsN (fuel + 1)))
    _ trace.functionState = _ at accepted
  rw [EStateM.bind, trace.exposureRun] at accepted
  change EStateM.bind (RecM.infer arg (methodsN fuel)) _ trace.exposedState = _ at accepted
  rw [EStateM.bind, trace.argumentRun] at accepted
  change EStateM.bind (TcM.isEagerReduce arg) _ trace.argumentState = _ at accepted
  rw [EStateM.bind, trace.ordinary] at accepted
  change EStateM.bind (RecM.isDefEq trace.argumentType trace.domain (methodsN fuel))
    _ trace.argumentState = _ at accepted
  rw [EStateM.bind, trace.compareRun] at accepted
  cases accepted
  exact ⟨rfl, rfl⟩

theorem ApplicationWhnfInferenceTrace.output {fuel : Nat} {before after : TcState .anon}
    {fn arg result : KExpr .anon} {info : ExprInfo .anon}
    (trace : ApplicationWhnfInferenceTrace fuel before fn arg)
    (accepted : RecM.inferUncached RecM.inferCall false (.app fn arg info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (subst trace.codomain arg 0 trace.comparedState.env.intern).1 :=
  (trace.output_state accepted).1

theorem ApplicationWhnfInferenceTrace.exposure_state {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {fn arg : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (trace : ApplicationWhnfInferenceTrace fuel before fn arg)
    (exposure : BetaPiExposure resolve locals fuel trace.functionState trace.functionType term
      condition domain body trace.domain trace.codomain) : trace.exposedState = exposure.after := by
  have accepted := trace.exposureRun
  rw [exposure.run] at accepted
  exact (EStateM.Result.ok.inj accepted).2.symm

theorem ApplicationWhnfInferenceTrace.exposure_context {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {fn arg : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (trace : ApplicationWhnfInferenceTrace fuel before fn arg)
    (exposure : BetaPiExposure resolve locals fuel trace.functionState trace.functionType term
      condition domain body trace.domain trace.codomain) : trace.exposedState.lctx = before.lctx := by
  rw [trace.exposure_state exposure, exposure.context]
  exact trace.contextPreserved

/-- Build the Pi-exposure part from its public beta path. The argument
check begins in the computed post-exposure state. -/
def ApplicationWhnfInferenceTrace.ofBeta {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId} {fuel : Nat}
    {before functionState argumentState comparedState : TcState .anon}
    {fn arg functionType domain codomain argumentType : KExpr .anon}
    {term A B : AExpr β} {condition : Certified.PropWhen}
    (functionRun : RecM.infer fn (methodsN fuel) before = .ok functionType functionState)
    (exposure : BetaPiExposure resolve locals fuel functionState functionType term condition A B domain codomain)
    (argumentRun : RecM.infer arg (methodsN fuel) exposure.after = .ok argumentType argumentState)
    (ordinary : TcM.isEagerReduce arg argumentState = .ok false argumentState)
    (compareRun : RecM.isDefEq argumentType domain (methodsN fuel) argumentState = .ok true comparedState)
    (contextPreserved : functionState.lctx = before.lctx) :
    ApplicationWhnfInferenceTrace fuel before fn arg :=
  { functionType, domain, codomain, functionState, exposedState := exposure.after,
    argumentType, argumentState, comparedState, functionRun, exposureRun := exposure.run,
    argumentRun, ordinary, compareRun, contextPreserved }

end Ix.Kernel.Consistency
