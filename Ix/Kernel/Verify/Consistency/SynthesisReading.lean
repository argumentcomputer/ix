/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisSupport

/-! Recover returned syntax readings before the synthesis semantic induction.
The caller supplies no context-formation or semantic typing evidence. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

theorem SynthesisInference.outputReading {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase :=
  match support with
  | .known inference _ | .reuseType inference .. | .fvar inference .. =>
      (BinderInference.sound.{u,u} inference agreement reading accepted).1
  | .cached _ _ _ _ hit cacheMatch resultReading => by
      rw [hit.run] at accepted
      cases accepted
      exact cacheMatch.symm ▸ resultReading
  | .cachedFrom _ hit resultReading => by
      rw [hit.run] at accepted
      cases accepted
      exact resultReading
  | .app full miss trace functionTree _ _ _ _
      bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have functionTypeReads := functionTree.outputReading keyedAgreement fnReads trace.functionRun
      obtain ⟨_, codomainReads⟩ := readScopedExpr?_all_parts functionTypeReads
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | .appBeta full miss trace functionTree exposure exposureCoherent _ _ _ _ _
      bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have functionTypeReads := functionTree.outputReading keyedAgreement fnReads trace.functionRun
      obtain ⟨_, codomainReads, _⟩ := exposure.reading functionTypeReads exposureCoherent
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | .forallE miss trace _ _ _ _ _ _ coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [trace.output run, internExpr_readScopedExpr? coherent faithful]
      rfl
  | .lam full miss trace opening _ bodyTree _ constructed bound coherent closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.absent keyedAgreement) domainReads bodyReads trace.openRun
      have bodyTypeReads := bodyTree.outputReading openedAgreement openedReads trace.bodyRun
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound coherent
        closingFaithful bodyTypeReads
      rw [trace.output run,
        internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
      simp [LambdaInferenceTrace.abstracted, domainReads, closedReads, AExpr.erase]
  | .lamBeta full miss trace opening _ bodyTree _ reduction _ constructed bound closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.absent keyedAgreement) domainReads bodyReads trace.openRun
      have bodyTypeReads := bodyTree.outputReading openedAgreement openedReads trace.bodyRun
      obtain ⟨_, reducedReads, reducedCoherent⟩ := reduction.reading bodyTypeReads
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound
        reducedCoherent closingFaithful reducedReads
      rw [trace.output run,
        internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
      simp [LambdaBodyTrace.abstracted, LambdaBodyTrace.reduced, domainReads, AExpr.erase] at ⊢ closedReads
      exact closedReads
  | .letE full localState miss trace opening _ _ bodyTree domainReading valueReading bodyReading
      _ _ _ substitution reduction => by
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨openedReading, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      have bodyTypeReading := bodyTree.outputReading openedAgreement openedReading trace.bodyRun
      obtain ⟨substitutedReading, substitutedCoherent⟩ :=
        trace.substituted_reading substitution bodyTypeReading valueReading
      obtain ⟨middle, uncached⟩ := infer_uncached_success miss accepted
      rw [full] at uncached
      rw [(trace.output_state uncached).1]
      exact (reduction.reading substitutedCoherent substitutedReading).1
termination_by structural support

end Ix.Kernel.Consistency
