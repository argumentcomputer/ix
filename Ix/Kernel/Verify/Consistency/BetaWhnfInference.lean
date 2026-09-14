/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaInference
import Ix.Kernel.Verify.Consistency.BetaWhnf

/-! Derive every semantic beta-step origin from the original inference.
The supplied WHNF path contains only actual operational and representation
resources, including the finite substitution and interning collision domains. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

def BetaStepPlan.betaTyping {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {before : TcState .anon}
    {source : KExpr .anon} {term type : AExpr β}
    (plan : BetaStepPlan resolve locals before source term)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context plan.modelResult type ×
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term plan.modelResult type := by
  have same : BetaSyntax.steps plan.consumed.size term = plan.modelResult := by
    calc
      BetaSyntax.steps plan.consumed.size term =
          BetaSyntax.steps plan.consumed.size ((AExpr.lam plan.condition plan.domain plan.inner).appN plan.arguments) :=
        congrArg (BetaSyntax.steps plan.consumed.size) plan.modelSource
      _ = plan.modelResult := BetaSyntax.steps_betaPrefix _ _ _ plan.counts.1 plan.counts.2
  exact same ▸ typing.betaSteps plan.consumed.size

/-- A finite production path without semantic step origins. All intermediate
expressions and states are computed by its raw beta plans. -/
inductive BetaWhnfTrace {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (reductionFuel : Nat) (flags : WhnfFlags) :
    Nat → TcState .anon → KExpr .anon → AExpr β → TcState .anon → KExpr .anon → AExpr β → Type u
  | done {before source term}
      (finished : (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
        .ok (.done source) before) :
      BetaWhnfTrace resolve locals reductionFuel flags 0 before source term before source term
  | next {steps before after source result term target}
      (plan : BetaStepPlan resolve locals before source term)
      (rest : BetaWhnfTrace resolve locals reductionFuel flags
        steps plan.after plan.result plan.modelResult after result target) :
      BetaWhnfTrace resolve locals reductionFuel flags (steps + 1) before source term after result target

def BetaWhnfTrace.annotate {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {reductionFuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target type : AExpr β}
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
        steps before source term after result target ×
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context target type :=
  match trace with
  | .done finished => ⟨.done finished, typing⟩
  | .next plan rest =>
      let first := plan.betaTyping typing
      let step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals
          _ _ _ type := { toBetaStepPlan := plan, meaning := first.2 }
      let remaining := rest.annotate first.1
      ⟨.next step remaining.1, remaining.2⟩
termination_by structural trace

/-- The original inference supplies every later lambda and argument origin.
Only the operational WHNF path and finite representation resources remain as
inputs to the actual uncached-loop refinement. -/
theorem SynthesisInference.beta_whnf_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel steps : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {result : KExpr .anon} {target : AExpr β}
    (path : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target)
    (coherent : before.env.intern.WF) (enough : steps < maxWhnfCoreFuel.toNat) :
    (RecM.whnfCoreWithFlagsUncached source flags).run (methodsN (reductionFuel + 1)) before = .ok result after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  let typing := support.betaTyping .current agreement reading accepted formed
  exact (path.annotate typing).1.uncached_sound typing.origin formed reading coherent enough

end Ix.Kernel.Consistency
