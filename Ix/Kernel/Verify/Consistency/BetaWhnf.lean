/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTrace
import Ix.Kernel.Verify.Consistency.BetaWhnfPlan

/-! Finite beta/let traces for the actual structural-WHNF loop. Every next
state is computed by production's single or simultaneous substitution and suffix
interning, and the loop consumes the same fuel as `runBounded`. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- A raw beta plan together with its derived source-checking evidence. -/
structure SynthesisBetaStep {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term type : AExpr β)
    extends BetaStepPlan resolve locals before source term where
  meaning : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term
    (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments) type

namespace SynthesisBetaStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
  {incomingBounds : List VLevel} {locals : List FVarId} {before : TcState .anon}
  {source : KExpr .anon} {term type : AExpr β}

def output (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.output

def result (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.result

def after (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.after

def modelResult (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.modelResult

theorem run (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
    (reductionFuel : Nat) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
      .ok (.next step.result) step.after :=
  step.toBetaStepPlan.run reductionFuel flags

theorem sourceReading
    (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    readScopedExpr? resolve locals source = some term.erase :=
  step.toBetaStepPlan.sourceReading

theorem reading
    (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals step.result = some step.modelResult.erase ∧ step.after.env.intern.WF :=
  step.toBetaStepPlan.reading coherent

end SynthesisBetaStep

/-- A finite structural path annotated from the original source check.
Recursive head calls retain their real cache execution and derived conversion. -/
inductive SynthesisBetaWhnfTrace {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β) (locals : List FVarId) :
    Nat → WhnfFlags → Nat → TcState .anon → KExpr .anon → AExpr β → TcState .anon → KExpr .anon → AExpr β → Type u
  | done {fuel flags before source term}
      (finished : (RecM.whnfCoreWithFlagsStep source flags).run (methodsN fuel) before =
        .ok (.done source) before) :
      SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals fuel flags
        0 before source term before source term
  | next {fuel flags steps before after source result term target type}
      (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
      (rest : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals (fuel + 1) flags
        steps step.after step.result step.modelResult after result target) :
      SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals (fuel + 1) flags
        (steps + 1) before source term after result target
  | zeta {fuel flags steps before after source result term target}
      (step : LetStepPlan before source)
      (rest : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals fuel flags
        steps step.after step.result term after result target) :
      SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals fuel flags
        (steps + 1) before source term after result target
  | head {fuel flags steps before middle after source result term target type}
      (plan : BetaHeadStepPlan resolve locals middle source term)
      (call : BetaHeadReduction resolve locals fuel flags
        before plan.rawHead plan.headTerm middle plan.rawLambda plan.modelLambda)
      (meaning : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term plan.modelResult type)
      (rest : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals (fuel + 1) flags
        steps plan.after plan.result plan.modelResult after result target) :
      SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals (fuel + 1) flags
        (steps + 1) before source term after result target

namespace SynthesisBetaWhnfTrace

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
  {incomingBounds : List VLevel} {locals : List FVarId} {reductionFuel steps : Nat} {flags : WhnfFlags}
  {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}

def toBetaTrace {reductionFuel steps : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) {type : AExpr β}
    (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term target type :=
  match trace with
  | .done _ => .refl origin
  | .next step rest =>
      let first := SynthesisBetaTrace.atType origin step.meaning
      first.trans (rest.toBetaTrace (.reduced first))
  | .zeta _ rest => rest.toBetaTrace origin
  | .head _ _ meaning rest =>
      let first := SynthesisBetaTrace.atType origin meaning
      first.trans (rest.toBetaTrace (.reduced first))
termination_by structural trace

def toRawTrace {reductionFuel steps : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) :
    BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target :=
  match trace with
  | .done finished => .done finished
  | .next step rest => .next step.toBetaStepPlan rest.toRawTrace
  | .zeta plan rest => .zeta plan rest.toRawTrace
  | .head plan call _ rest => .head plan call rest.toRawTrace
termination_by structural trace

theorem run
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) {loopFuel : Nat} (enough : steps < loopFuel) :
    (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags) loopFuel source).run
      (methodsN reductionFuel) before = .ok result after := trace.toRawTrace.run enough

theorem reading
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ after.env.intern.WF :=
  trace.toRawTrace.reading sourceReading coherent

/-- The production loop returns the final beta result with the original
source's type and a coherent intern table. The finite path uses the real
loop bound and the same recursive method table at every iteration. -/
theorem uncached_sound
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) {type : AExpr β}
    (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (enough : steps < maxWhnfCoreFuel.toNat) :
    (RecM.whnfCoreWithFlagsUncached source flags).run (methodsN reductionFuel) before = .ok result after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  obtain ⟨reading, preserved⟩ := trace.reading sourceReading coherent
  obtain ⟨converted, typed⟩ := (trace.toBetaTrace origin).sound formed
  exact ⟨trace.run enough, reading, converted, typed, preserved⟩

end SynthesisBetaWhnfTrace
end Ix.Kernel.Consistency
