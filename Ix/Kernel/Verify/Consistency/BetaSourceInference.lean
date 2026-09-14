/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheConstruction
import Ix.Kernel.Verify.Consistency.BetaWhnfInference

/-! Successful production beta/let calls preserve the type established by the
original inference. Their operational traces, iteration counts, intermediate
readings, and annotations are constructed from source resources. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

theorem SynthesisInference.beta_whnf_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (inferredRun : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    {reductionFuel : Nat} {flags : WhnfFlags} {before after : TcState .anon} {result : KExpr .anon}
    (resources : BetaWhnfSource.Resources (reductionFuel + 1) flags maxWhnfCoreFuel.toNat before source)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfCoreWithFlagsUncached source flags).run (methodsN (reductionFuel + 1)) before =
      .ok result after) :
    ∃ target, BetaWhnfTerminal result ∧ readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  let witness := BetaWhnfSource.construct resources reading coherent accepted
  exact ⟨witness.target, witness.terminal,
    (support.beta_whnf_sound formed agreement reading inferredRun witness.trace coherent witness.enough).2⟩

theorem SynthesisInference.beta_core_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
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
    (resources : BetaWhnfSource.CoreResources resolve locals reductionFuel before source term)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfCore source).run (methodsN (reductionFuel + 1)) before = .ok result after) :
    ∃ target, BetaWhnfTerminal result ∧ readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  obtain ⟨target, execution, stateEq⟩ := BetaCoreExecution.exists_of_success chosen resources reading coherent accepted
  refine ⟨target, execution.terminal, ?_⟩
  simpa only [stateEq] using
    (support.beta_core_execution_sound formed agreement reading inferredRun execution coherent).2

theorem SynthesisInference.beta_noDelta_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
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
    (resources : BetaWhnfSource.NoDeltaResources resolve locals reductionFuel before source term)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfNoDelta source).run (methodsN (reductionFuel + 1)) before = .ok result after) :
    ∃ target, BetaWhnfTerminal result ∧ readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  obtain ⟨target, execution, stateEq⟩ := BetaNoDeltaExecution.exists_of_success chosen resources reading coherent accepted
  refine ⟨target, execution.terminal, ?_⟩
  simpa only [stateEq] using
    (support.beta_noDelta_execution_sound formed agreement reading inferredRun execution coherent).2

theorem SynthesisInference.beta_public_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
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
    (resources : BetaWhnfSource.PublicResources resolve locals reductionFuel before source term)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnf source).run (methodsN (reductionFuel + 1)) before = .ok result after) :
    ∃ target, BetaWhnfTerminal result ∧ readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  obtain ⟨target, execution, stateEq⟩ := BetaPublicExecution.exists_of_success chosen resources reading coherent accepted
  refine ⟨target, execution.terminal, ?_⟩
  simpa only [stateEq] using
    (support.beta_public_execution_sound formed agreement reading inferredRun execution coherent).2

end Ix.Kernel.Consistency
