/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaHistorySource
import Ix.Kernel.Verify.Consistency.BetaSourceInference
import Ix.Kernel.Verify.Consistency.BetaExposureConstruction

/-! Original source checking supplies the semantics of a cache history.
Pi and sort exposure preserve that same operational history for later calls. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

def BetaPiExposure.cacheHistory {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (history : BetaCacheHistory β before) (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) : BetaCacheHistory β exposure.after := by
  cases exposure with
  | reduce plan =>
      simpa only [BetaPiExposure.after, plan.execution_after] using history.afterPublic plan.execution reading coherent
  | execute execution => exact history.afterPublic execution reading coherent
  | cached => exact history.instrument.key source

def BetaSortExposure.cacheHistory {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source : KExpr .anon} {term : AExpr β} {level : KUniv .anon}
    (exposure : BetaSortExposure resolve locals fuel before source term level)
    (history : BetaCacheHistory β before) (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) : BetaCacheHistory β exposure.after := by
  cases exposure with
  | direct => exact history
  | reduce plan =>
      simpa only [BetaSortExposure.after, plan.execution_after] using history.afterPublic plan.execution reading coherent
  | execute execution => exact history.afterPublic execution reading coherent
  | cached => exact history.instrument.key source

/-- A successful public call consumes one retained history and returns the
history of its complete result state. Individual cache typing, annotation,
and producing-execution premises are recovered by selection. -/
theorem SynthesisInference.beta_public_of_history {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (inferredRun : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel : Nat} {before after : TcState .anon} {result : KExpr .anon}
    (chosen : BetaWhnfSource.selected source = true)
    (history : BetaCacheHistory β before) (data : history.KeyData source)
    (cold : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[(BetaPublicWhnf.outerKey source before).1]? = none →
      (BetaPublicWhnf.noDeltaKey source before).2.env.whnfNoDeltaCache[(BetaPublicWhnf.noDeltaKey source before).1]? = none →
      (BetaPublicWhnf.coreKey source before).2.env.whnfCoreCache[(BetaPublicWhnf.coreKey source before).1]? = none →
        BetaWhnfSource.Resources resolve locals (reductionFuel + 1) .FULL maxWhnfCoreFuel.toNat (BetaPublicWhnf.coreKey source before).2 source)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnf source).run (methodsN (reductionFuel + 1)) before = .ok result after) :
    ∃ target, BetaWhnfTerminal result ∧ readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF ∧ Nonempty (BetaCacheHistory β after) := by
  obtain ⟨target, execution, stateEq, preserved⟩ :=
    BetaPublicExecution.exists_of_history chosen history data cold reading coherent accepted
  have sound := (support.beta_public_execution_sound formed agreement reading inferredRun execution coherent).2
  rw [stateEq] at sound
  exact ⟨target, execution.terminal, sound.1, sound.2.1, sound.2.2.1, sound.2.2.2, preserved⟩

end Ix.Kernel.Consistency
