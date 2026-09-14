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

/-- Annotating the raw public path derives its semantic trace from the
retained checking derivation, including every later beta step. -/
def BetaPublicWhnfPlan.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target type : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term target type :=
  (plan.path.annotate typing).1.toBetaTrace typing.origin

/-- The cached result retains the executed beta origin; the source's current
checking derivation supplies its meaning in the current model context. -/
def BetaCoreExecution.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target type : AExpr β}
    (execution : BetaCoreExecution resolve locals fuel before source term result target)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term target type :=
  match execution with
  | .reduce path .. => (path.annotate typing).1.toBetaTrace typing.origin
  | .cached origin .. => origin.betaTrace typing

/-- The cached result retains the executed beta origin; the source's current
checking derivation supplies its meaning in the current model context. -/
def BetaNoDeltaExecution.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target type : AExpr β}
    (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term target type :=
  match execution with
  | .reduce core _ => core.betaTrace typing
  | .cached origin .. => origin.betaTrace typing

/-- The cached result retains the executed beta origin; the source's current
checking derivation supplies its meaning in the current model context. -/
def BetaPublicExecution.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target type : AExpr β}
    (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term target type :=
  match execution with
  | .reduce inner .. => inner.betaTrace typing
  | .cached origin .. => origin.betaTrace typing

/-- Cache reuse retains the originating path's checked meaning. The
current cache lookup establishes which exact raw Pi result is returned. -/
def BetaPiExposure.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body type : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      term (.forallE condition domain body) type :=
  match exposure with
  | .reduce plan => plan.betaTrace typing
  | .cached origin _ _ => origin.betaTrace typing
  | .execute execution => execution.betaTrace typing

/-- Sort exposure obtains its meaning from the same complete source
derivation as public beta WHNF; a direct sort uses reflexivity. -/
def BetaSortExposure.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source : KExpr .anon} {term type : AExpr β} {level : KUniv .anon}
    (exposure : BetaSortExposure resolve locals fuel before source term level)
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      term (.sort (readLevel level)) type :=
  match exposure with
  | .direct .. => .refl typing.origin
  | .reduce plan => plan.betaTrace typing
  | .cached origin _ => origin.betaTrace typing
  | .execute execution => execution.betaTrace typing

/-- Earlier type checks retain every beta origin, including after interface
growth or insertion beneath binders. No check of the exposed sort is required. -/
def BetaSortExposure.checkedTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source : KExpr .anon} {term : AExpr β} {level : KUniv .anon} {typeLevel typeBound : VLevel}
    (exposure : BetaSortExposure resolve locals fuel before source term level)
    (checked : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context
      term (.sort typeLevel) typeBound) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      term (.sort (readLevel level)) (.sort typeLevel) :=
  exposure.betaTrace checked.betaTyping

/-- Construct the sort-check resource from actual term inference and an
earlier check of its returned type. Its formation origin selects the bound
used by the enclosing inference, independently of the earlier check's bound. -/
def SynthesisSortCheck.ofRetainedType {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {before : TcState .anon} {source : KExpr .anon} {trace : SortInferenceTrace fuel before source}
    {term type : AExpr β} {bound typeLevel typeBound : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type bound)
    (exposure : trace.Exposure resolve locals type)
    (checked : SynthesisRetainedCheck resolve entries context bounds entries context type (.sort typeLevel) typeBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    SynthesisSortCheck resolve entries locals context bounds trace term :=
  .checked tree exposure
    (.atType (.inferredType .current tree agreement reading trace.inferRun) (exposure.checkedTrace checked))

/-- An actual earlier check of the function type supplies the conversion
field of application inference. No check of the generated Pi is needed. -/
def BetaPiExposure.checkedTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals typeLocals : List FVarId} {fuel typeFuel : Nat}
    {before typeBefore typeAfter : TcState .anon} {source rawDomain rawBody typeSource typeResult : KExpr .anon}
    {term domain body : AExpr β} {condition : Certified.PropWhen} {level bound : VLevel}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (typeTree : SynthesisInference resolve entries typeLocals context bounds typeFuel typeBefore typeSource
      term (.sort level) bound)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve typeLocals typeBefore.lctx context)
    (reading : readScopedExpr? resolve typeLocals typeSource = some term.erase)
    (accepted : RecM.infer typeSource (methodsN typeFuel) typeBefore = .ok typeResult typeAfter) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      term (.forallE condition domain body) (.sort level) :=
  exposure.betaTrace (typeTree.betaTyping contextOrigin agreement reading accepted)

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
  let typing := support.betaTyping .current agreement reading accepted
  exact (path.annotate typing).1.uncached_sound typing.origin formed reading coherent enough

/-- The public WHNF call includes instrumentation, fuel, and all three
cache layers. Its beta result has the type derived by the original check. -/
theorem SynthesisInference.beta_public_whnf_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel : Nat} {before : TcState .anon} {result : KExpr .anon} {target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals reductionFuel before source term result target)
    (coherent : before.env.intern.WF) :
    (RecM.whnf source).run (methodsN (reductionFuel + 1)) before = .ok result plan.after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      plan.after.env.intern.WF := by
  obtain ⟨resultReading, preserved⟩ := plan.reading reading coherent
  obtain ⟨converted, typed⟩ :=
    (plan.betaTrace (support.betaTyping .current agreement reading accepted)).sound formed
  exact ⟨plan.run, resultReading, converted, typed, preserved⟩

/-- Executed cached reduction preserves the type proved by the original
source check, including when a lower layer supplied the result. -/
theorem SynthesisInference.beta_core_execution_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel : Nat} {before : TcState .anon} {result : KExpr .anon} {target : AExpr β}
    (plan : BetaCoreExecution resolve locals reductionFuel before source term result target)
    (coherent : before.env.intern.WF) :
    (RecM.whnfCore source).run (methodsN (reductionFuel + 1)) before = .ok result plan.after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      plan.after.env.intern.WF := by
  obtain ⟨resultReading, preserved⟩ := plan.reading reading coherent
  obtain ⟨converted, typed⟩ :=
    (plan.betaTrace (support.betaTyping .current agreement reading accepted)).sound formed
  exact ⟨plan.run, resultReading, converted, typed, preserved⟩

/-- Executed cached reduction preserves the type proved by the original
source check, including when a lower layer supplied the result. -/
theorem SynthesisInference.beta_noDelta_execution_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel : Nat} {before : TcState .anon} {result : KExpr .anon} {target : AExpr β}
    (plan : BetaNoDeltaExecution resolve locals reductionFuel before source term result target)
    (coherent : before.env.intern.WF) :
    (RecM.whnfNoDelta source).run (methodsN (reductionFuel + 1)) before = .ok result plan.after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      plan.after.env.intern.WF := by
  obtain ⟨resultReading, preserved⟩ := plan.reading reading coherent
  obtain ⟨converted, typed⟩ :=
    (plan.betaTrace (support.betaTyping .current agreement reading accepted)).sound formed
  exact ⟨plan.run, resultReading, converted, typed, preserved⟩

/-- Executed cached reduction preserves the type proved by the original
source check, including when a lower layer supplied the result. -/
theorem SynthesisInference.beta_public_execution_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel : Nat} {before : TcState .anon} {result : KExpr .anon} {target : AExpr β}
    (plan : BetaPublicExecution resolve locals reductionFuel before source term result target)
    (coherent : before.env.intern.WF) :
    (RecM.whnf source).run (methodsN (reductionFuel + 1)) before = .ok result plan.after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      plan.after.env.intern.WF := by
  obtain ⟨resultReading, preserved⟩ := plan.reading reading coherent
  obtain ⟨converted, typed⟩ :=
    (plan.betaTrace (support.betaTyping .current agreement reading accepted)).sound formed
  exact ⟨plan.run, resultReading, converted, typed, preserved⟩

end Ix.Kernel.Consistency
