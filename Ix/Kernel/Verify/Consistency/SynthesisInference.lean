/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisShapes

/-! Recursive inference, retained source derivations, and their semantic
soundness at the original production calls. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

mutual

/-- Simultaneous soundness of the term and formation of its returned type.
The context hypothesis is discharged by actual domain inference at each
binder, and by the empty context at the production declaration boundary. -/
theorem SynthesisInference.soundWithHereditary {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context term type ∧
      TypingClaim.{u,v} entries context type (.sort level) ∧
      HereditaryTyping.{u,v} entries context term type :=
  match support with
  | .known inference formation => by
      obtain ⟨reads, checked⟩ := inference.sound agreement reading accepted
      have typed := checked.typing formation.sound
      exact ⟨reads, typed, formation.sound, inference.hereditary typed agreement reading⟩
  | .cached tree priorAgreement priorReading priorRun hit cacheMatch resultReading => by
      obtain ⟨_, typed, formation, spine⟩ :=
        tree.soundWithHereditary formed priorAgreement priorReading priorRun
      rw [hit.run] at accepted
      cases accepted
      exact ⟨cacheMatch.symm ▸ resultReading, typed, formation, spine⟩
  | .cachedFrom check hit resultReading => by
      obtain ⟨typed, formation, spine⟩ := check.soundWithHereditary formed
      rw [hit.run] at accepted
      cases accepted
      exact ⟨resultReading, typed, formation, spine⟩
  | .reuseType inference typeTree extension typeReading typeRun same => by
      obtain ⟨reads, checked⟩ := inference.sound agreement reading accepted
      obtain ⟨_, typeTyped, _, _⟩ :=
        typeTree.soundWithHereditary (.empty _) (.empty _ _) typeReading typeRun
      have typeFormed := same.termTyping
        (typing_instL_closed (context := context) (extension.typing typeTyped) _)
      have typed := checked.typing typeFormed
      exact ⟨reads, typed, typeFormed, inference.hereditary typed agreement reading⟩
  | .fvar inference atIndex boundAtIndex => by
      obtain ⟨reads, typed⟩ := inference.synthesis (.bvar _) agreement reading accepted
      exact ⟨reads, typed, formed _ _ _ atIndex boundAtIndex, .bvar typed atIndex⟩
  | .natLit binding inference => by
      have reads := (BinderInference.sound.{u,v} inference agreement reading accepted).1
      exact ⟨reads, binding.typing _ _, binding.formation _, .atom (binding.typing _ _) (.natLit _)⟩
  | .app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, functionTyped, functionFormed, functionSpine⟩ :=
        functionTree.soundWithHereditary formed keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, codomainReads⟩ := readScopedExpr?_all_parts functionTypeReads
      have argumentAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨argumentTypeReads, argumentTyped, _, argumentSpine⟩ :=
        argumentTree.soundWithHereditary formed argumentAgreement argReads trace.argumentRun
      have sameReading := beq_readScopedExpr? (resolve := resolve) (locals := locals)
        (depth := 0) comparisonFaithful hashPath
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans (sameReading.trans domainReads))) conditions
      have checked := sameType ▸ argumentTyped.checking
      refine ⟨?_, functionTyped.appChecking checked,
        functionTyped.applicationType functionFormed checked,
        .app functionSpine (sameType ▸ argumentSpine)⟩
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | .appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, functionTyped, _, functionSpine⟩ :=
        functionTree.soundWithHereditary formed keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, codomainReads, _⟩ := exposure.reading functionTypeReads exposureCoherent
      have argumentAgreement := keyedAgreement.congr trace.exposure_context.symm
      obtain ⟨argumentTypeReads, argumentTyped, _, argumentSpine⟩ :=
        argumentTree.soundWithHereditary formed argumentAgreement argReads trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      obtain ⟨converted, functionFormed⟩ := reduction.sound formed
      have exposedTyped := functionTyped.conv functionFormed converted
      have checked := sameType ▸ argumentTyped.checking
      refine ⟨?_, exposedTyped.appChecking checked,
        exposedTyped.applicationType functionFormed checked,
        .app (.convert functionSpine reduction.rigid converted functionFormed) (sameType ▸ argumentSpine)⟩
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | .forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound
      coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, domainSpine⟩ :=
        domainTree.soundWithHereditary formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨_, bodyTyped, _, bodySpine⟩ :=
        bodyTree.soundWithHereditary (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      have typed := AExpr.LevelEquivalent.sort
        (Theory.VLevel.equiv_def.mpr fun levels =>
          (Theory.VLevel.equiv_def.mp (readLevel_mkIMax levelFaithful domainBound bodyBound)
            levels).symm) |>.typing (TypingClaim.forallE domainTyped bodyTyped rfl)
      refine ⟨?_, typed, TypingClaim.sort _, .forallE typed domainSpine bodySpine rfl⟩
      · rw [trace.output run, internExpr_readScopedExpr? coherent faithful]
        rfl
  | .lam full miss trace opening domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithHereditary formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyTyped, bodyFormed, bodySpine⟩ :=
        bodyTree.soundWithHereditary (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound coherent
        closingFaithful bodyTypeReads
      have typed := TypingClaim.lam domainTyped bodyFormed bodyTyped conditionAgrees
      refine ⟨?_, typed, TypingClaim.forallE domainTyped bodyFormed conditionAgrees,
        .lam typed bodySpine⟩
      rw [trace.output run,
        internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
      simp [LambdaInferenceTrace.abstracted, domainReads, closedReads, AExpr.erase]
  | .lamBeta full miss trace opening domainTree bodyTree origin reduction conditionAgrees
      constructed bound closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithHereditary formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyTyped, _, bodySpine⟩ :=
        bodyTree.soundWithHereditary (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨conversion, reducedTyped⟩ := origin.sound formed
      obtain ⟨_, reducedReads, reducedCoherent⟩ := reduction.reading bodyTypeReads
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound
        reducedCoherent closingFaithful reducedReads
      have typed := TypingClaim.lam domainTyped reducedTyped
        (bodyTyped.conv reducedTyped conversion) conditionAgrees
      refine ⟨?_, typed, TypingClaim.forallE domainTyped reducedTyped conditionAgrees,
        .lam typed (.convert bodySpine (SynthesisBetaTrace.rigid (.origin origin)) conversion reducedTyped)⟩
      · rw [trace.output run,
          internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
        simp [LambdaBodyTrace.abstracted, LambdaBodyTrace.reduced, domainReads,
          AExpr.erase, Option.bind_eq_some_iff] at ⊢ closedReads
        exact closedReads
  | .letE full localState miss trace opening domainTree valueTree bodyTree domainReading valueReading bodyReading
      conditions hashPath comparisonFaithful substitution reduction => by
      let node := SynthesisInference.letE full localState miss trace opening domainTree valueTree bodyTree
        domainReading valueReading bodyReading conditions hashPath comparisonFaithful substitution reduction
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have valueAgreement := keyedAgreement.congr (trace.domainContext keyedValid).symm
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithHereditary formed keyedAgreement domainReading trace.domainRun
      obtain ⟨valueTypeReading, valueTyped, _, valueHereditary⟩ :=
        valueTree.soundWithHereditary formed valueAgreement valueReading trace.valueRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (valueTypeReading.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReading))) conditions
      obtain ⟨openedReading, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      obtain ⟨_, bodyTyped, bodyFormed, bodyHereditary⟩ :=
        bodyTree.soundWithHereditary (formed.push domainTyped) openedAgreement openedReading trace.bodyRun
      have valueAtDomain := sameType ▸ valueTyped
      obtain ⟨converted, typeFormed⟩ := reduction.sound formed (bodyFormed.instAt valueAtDomain .root)
      exact ⟨node.outputReading agreement reading accepted,
        (bodyTyped.instAt valueAtDomain .root).conv typeFormed converted, typeFormed,
        .convert (bodyHereditary.substituteAt (sameType ▸ valueHereditary) .root)
          reduction.rigid converted typeFormed⟩
  | .forallSort miss trace opening domainCheck bodyCheck levelFaithful domainBound bodyBound
      coherent faithful => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨domainTyped, domainHereditary⟩ :=
        domainCheck.soundWithHereditary formed keyedAgreement domainReads
      obtain ⟨openedReads, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedAgreement domainReads bodyReads
      obtain ⟨bodyTyped, bodyHereditary⟩ :=
        bodyCheck.soundWithHereditary (formed.push domainTyped) openedAgreement openedReads
      have typed := AExpr.LevelEquivalent.sort
        (Theory.VLevel.equiv_def.mpr fun levels =>
          (Theory.VLevel.equiv_def.mp (readLevel_mkIMax levelFaithful domainBound bodyBound)
            levels).symm) |>.typing (TypingClaim.forallE domainTyped bodyTyped rfl)
      let node := SynthesisInference.forallSort miss trace opening domainCheck bodyCheck
        levelFaithful domainBound bodyBound coherent faithful
      exact ⟨node.outputReading agreement reading accepted, typed, TypingClaim.sort _,
        .forallE typed domainHereditary bodyHereditary rfl⟩
  | .lamSort full miss trace opening domainCheck bodyTree reduction conditionAgrees
      constructed bound coherent closingFaithful faithful => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨domainTyped, _⟩ := domainCheck.soundWithHereditary formed keyedAgreement domainReads
      obtain ⟨openedReads, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedAgreement domainReads bodyReads
      obtain ⟨_, bodyTyped, bodyFormed, bodyHereditary⟩ :=
        bodyTree.soundWithHereditary (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨converted, reducedFormed⟩ := reduction.sound (formed.push domainTyped) bodyFormed
      have typed := TypingClaim.lam domainTyped reducedFormed
        (bodyTyped.conv reducedFormed converted) conditionAgrees
      let node := SynthesisInference.lamSort full miss trace opening domainCheck bodyTree reduction
        conditionAgrees constructed bound coherent closingFaithful faithful
      exact ⟨node.outputReading agreement reading accepted, typed,
        TypingClaim.forallE domainTyped reducedFormed conditionAgrees,
        .lam typed (.convert bodyHereditary reduction.rigid converted reducedFormed)⟩
  | .letSort full localState miss trace opening domainCheck valueTree bodyTree domainReading valueReading bodyReading
      conditions hashPath comparisonFaithful substitution reduction => by
      let node := SynthesisInference.letSort full localState miss trace opening domainCheck valueTree bodyTree
        domainReading valueReading bodyReading conditions hashPath comparisonFaithful substitution reduction
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have valueAgreement := keyedAgreement.congr (trace.domainContext keyedValid).symm
      obtain ⟨domainTyped, _⟩ := domainCheck.soundWithHereditary formed keyedAgreement domainReading
      obtain ⟨valueTypeReading, valueTyped, _, valueHereditary⟩ :=
        valueTree.soundWithHereditary formed valueAgreement valueReading trace.valueRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (valueTypeReading.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReading))) conditions
      obtain ⟨openedReading, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      obtain ⟨_, bodyTyped, bodyFormed, bodyHereditary⟩ :=
        bodyTree.soundWithHereditary (formed.push domainTyped) openedAgreement openedReading trace.bodyRun
      have valueAtDomain := sameType ▸ valueTyped
      obtain ⟨converted, typeFormed⟩ := reduction.sound formed (bodyFormed.instAt valueAtDomain .root)
      exact ⟨node.outputReading agreement reading accepted,
        (bodyTyped.instAt valueAtDomain .root).conv typeFormed converted, typeFormed,
        .convert (bodyHereditary.substituteAt (sameType ▸ valueHereditary) .root)
          reduction.rigid converted typeFormed⟩
termination_by structural support

/-- The actual inferred-type conversion establishes the sort used to form
the next binder context; the checked source derivation survives that conversion. -/
theorem SynthesisSortCheck.soundWithHereditary {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {source : KExpr .anon} {trace : SortInferenceTrace fuel before source}
    {term : AExpr β} (check : SynthesisSortCheck resolve entries locals context bounds trace term)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    TypingClaim.{u,v} entries context term (.sort (readLevel trace.level)) ∧
      HereditaryTyping.{u,v} entries context term (.sort (readLevel trace.level)) :=
  match check with
  | .checked tree _ reduction => by
      obtain ⟨_, typed, _, hereditary⟩ := tree.soundWithHereditary formed agreement reading trace.inferRun
      obtain ⟨converted, typeFormed⟩ := reduction.sound formed
      exact ⟨typed.conv typeFormed converted, .convert hereditary reduction.rigid converted typeFormed⟩
termination_by structural check

theorem LetTypeReduction.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {source : KExpr .anon} {table : InternTable .anon} {level : VLevel} {term result : AExpr β}
    (reduction : LetTypeReduction resolve entries context bounds source table level term result)
    (formed : ContextFormation.{u,v} entries context bounds)
    (original : TypingClaim.{u,v} entries context term (.sort level)) :
    ConversionClaim.{u,v} entries context term result ∧ TypingClaim.{u,v} entries context result (.sort level) :=
  match reduction with
  | .unchanged _ => ⟨.refl _, original⟩
  | .beta _ origin => origin.sound formed
termination_by structural reduction

theorem SynthesisContext.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries earlier : Model.Environment β} {context priorContext : Model.Context β}
    {bounds priorBounds : List VLevel}
    (support : SynthesisContext resolve entries context bounds earlier priorContext priorBounds)
    (formed : ContextFormation.{u,v} entries context bounds) :
    ContextFormation.{u,v} earlier priorContext priorBounds :=
  match support with
  | .current => formed
  | .empty earlier => .empty earlier
  | .push prior domainTree agreement reading accepted => by
      have priorFormation := prior.sound formed
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithHereditary priorFormation agreement reading accepted
      exact priorFormation.push domainTyped
  | .pushSort prior check agreement reading => by
      have priorFormation := prior.sound formed
      exact priorFormation.push (check.soundWithHereditary priorFormation agreement reading).1
  | .extend prior extension => by
      intro index type bound found indexed
      exact extension.typing (prior.sound formed index type bound found indexed)
  | .compose prior next => next.sound (prior.sound formed)
termination_by structural support

theorem SynthesisTypeTransport.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming origin entries : Model.Environment β} {incomingContext originContext context : Model.Context β}
    {incomingBounds : List VLevel} {source reduced current result : AExpr β} {level bound : VLevel}
    (support : SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries context current result bound)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds)
    (converted : ConversionClaim.{u,v} origin originContext source reduced)
    (typed : TypingClaim.{u,v} origin originContext reduced (.sort level)) :
    ConversionClaim.{u,v} entries context current result ∧
      TypingClaim.{u,v} entries context result (.sort bound) :=
  match support with
  | .pure transport => transport.sound converted typed
  | .map prior transport => by
      obtain ⟨conversion, resultTyped⟩ := prior.sound formed converted typed
      exact transport.sound conversion resultTyped
  | .substituteAt prior argumentOrigin substitution => by
      obtain ⟨conversion, resultTyped⟩ := prior.sound formed converted typed
      have argumentAtDomain := argumentOrigin.sound formed
      exact ⟨conversion.instAt argumentAtDomain substitution, resultTyped.instAt argumentAtDomain substitution⟩
termination_by structural support

theorem SynthesisRetainedCheck.soundWithHereditary {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ TypingClaim.{u,v} entries context type (.sort level) ∧
      HereditaryTyping.{u,v} entries context term type :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      (tree.soundWithHereditary (contextOrigin.sound formed) agreement reading accepted).2
  | .extend prior extension => by
      obtain ⟨typed, typeFormed, spine⟩ := prior.soundWithHereditary formed
      exact ⟨extension.typing typed, extension.typing typeFormed, spine.extend extension⟩
  | .weakenAt prior insertion => by
      obtain ⟨typed, typeFormed, spine⟩ := prior.soundWithHereditary formed
      exact ⟨insertion.typing typed, insertion.typing typeFormed, spine.weakenAt insertion⟩
  | .rebase origin prior => prior.soundWithHereditary (origin.sound formed)
termination_by structural check

theorem SynthesisTypingOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type :=
  match support with
  | .source check => (check.soundWithSpine formed).1
  | .inferredType contextOrigin tree agreement reading accepted =>
      (tree.soundWithHereditary (contextOrigin.sound formed) agreement reading accepted).2.2.1
  | .lambdaBody check => (check.sound formed).lambdaBody
  | .application functionOrigin argumentOrigin => (functionOrigin.sound formed).app (argumentOrigin.sound formed)
  | .reduced trace => (trace.sound formed).2
  | .convert value trace => by
      obtain ⟨converted, typeTyped⟩ := trace.sound formed
      exact (value.sound formed).conv typeTyped converted
  | .weaken prior domain => typing_weaken (prior.sound formed)
  | .weakenAt prior insertion => insertion.typing (prior.sound formed)
  | .instantiate prior arguments => typing_instL_context (prior.sound formed) arguments
  | .appendContext prior outer => typing_append_context (prior.sound formed) outer
  | .extend prior extension => extension.typing (prior.sound formed)
  | .rebase origin prior => prior.sound (origin.sound formed)
  | .termEquivalent prior same => same.termTyping (prior.sound formed)
  | .typeEquivalent prior same => same.typing (prior.sound formed)
  | .substituteAt body value substitution => (body.sound formed).instAt (value.sound formed) substitution
termination_by structural support

theorem SynthesisCheckedOrigin.soundWithSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ LambdaPrefix term type term.lambdaDepth ∧
      LambdaSpineTyping.{u,v} entries context term type :=
  match support with
  | .checked contextOrigin tree agreement reading accepted => by
      obtain ⟨_, typed, _, spine⟩ := tree.soundWithHereditary (contextOrigin.sound formed) agreement reading accepted
      exact ⟨typed, spine.lambdaPrefix, spine.lambdaSpine⟩
  | .binderHead tree head agreement reading accepted => by
      have typed := (tree.synthesis head agreement reading accepted).2
      exact ⟨typed, tree.lambdaPrefix, tree.lambdaSpineTyping typed⟩
  | .binderType tree agreement reading accepted => by
      have typed := (tree.sound agreement reading accepted).2.typing (TypingClaim.sort _)
      exact ⟨typed, tree.lambdaPrefix, tree.lambdaSpineTyping typed⟩
  | .applicationArgument contextOrigin trace functionTree argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful => by
      have contextFormation := contextOrigin.sound formed
      have functionTypeReads :=
        (functionTree.soundWithHereditary contextFormation agreement functionReading trace.functionRun).1
      have domainReads := (readScopedExpr?_all_parts functionTypeReads).1
      obtain ⟨argumentTypeReads, argumentTyped, _, argumentSpine⟩ :=
        argumentTree.soundWithHereditary contextFormation (agreement.congr trace.contextPreserved.symm)
          argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      exact ⟨sameType ▸ argumentTyped, sameType ▸ argumentSpine.lambdaPrefix, sameType ▸ argumentSpine.lambdaSpine⟩
  | .applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree agreement
      functionReading argumentReading conditions hashPath comparisonFaithful => by
      have contextFormation := contextOrigin.sound formed
      have functionTypeReads :=
        (functionTree.soundWithHereditary contextFormation agreement functionReading trace.functionRun).1
      have domainReads := (exposure.reading functionTypeReads exposureCoherent).1
      obtain ⟨argumentTypeReads, argumentTyped, _, argumentSpine⟩ :=
        argumentTree.soundWithHereditary contextFormation (agreement.congr trace.exposure_context.symm)
          argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      exact ⟨sameType ▸ argumentTyped, sameType ▸ argumentSpine.lambdaPrefix, sameType ▸ argumentSpine.lambdaSpine⟩
  | .binderArgument trace functionTree head argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful => by
      obtain ⟨functionTypeReads, functionTyped⟩ :=
        functionTree.synthesis head agreement functionReading trace.functionRun
      have domainReads := (readScopedExpr?_all_parts functionTypeReads).1
      obtain ⟨argumentTypeReads, argumentChecked⟩ :=
        argumentTree.sound (agreement.congr trace.contextPreserved.symm) argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      have checked := sameType ▸ argumentChecked
      have typed : TypingClaim.{u,v} entries context term type := by
        intro V _ constants realizes levels env valid
        have domainValid := (functionTyped V constants realizes levels env valid).2.1.1
        have checkedAt := checked V constants realizes levels env valid domainValid
        exact ⟨checkedAt.1, domainValid, checkedAt.2⟩
      exact ⟨typed, sameType ▸ argumentTree.lambdaPrefix,
        sameType ▸ argumentTree.lambdaSpineTyping (sameType.symm ▸ typed)⟩
termination_by structural support

theorem SynthesisArgumentSpineOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context start arguments result)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ArgumentSpine.{u,v} entries context start arguments result :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => (prior.sound formed).append (.cons (checked.sound formed) (.nil _))
  | .convert prior trace => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      simpa only [List.append_nil] using
        (prior.sound formed).append (ArgumentSpine.convert trace.rigid converted typed (.nil _))
termination_by structural support

theorem SynthesisReductionOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head : AExpr β} {arguments : List (AExpr β)} {count : Nat} {level : VLevel}
    (support : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
      entries context head arguments count level)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ConversionClaim.{u,v} entries context (head.appN arguments) (AExpr.betaPrefix count head arguments) ∧
      TypingClaim.{u,v} entries context (AExpr.betaPrefix count head arguments) (.sort level) :=
  match support with
  | .traced trace => trace.sound formed
  | .checked typeContextSupport typeTree typeAgreement typeReading typeRun originPrefix transport => by
      obtain ⟨_, _, _, originSpine⟩ := typeTree.soundWithHereditary
        (typeContextSupport.sound formed) typeAgreement typeReading typeRun
      obtain ⟨originConversion, originReducedTyped⟩ := originSpine.lambdaSpine.betaPrefix originPrefix
      exact transport.sound formed originConversion originReducedTyped
  | .substitutedVariable spine atIndex checked substitution enough => by
      obtain ⟨typed, leading, _⟩ := checked.soundWithSpine formed
      have instantiated := (spine.sound formed).instAt typed substitution
      rw [substitution.instantiate_removed_type atIndex] at instantiated
      exact ((leading.liftN _ 0).truncate enough).beta_sound (substitution.lift_typing typed) instantiated
  | .substitutedApplication spine atIndex checked substitution enough =>
      (checked.soundWithSpine formed).2.2.substituteHead (spine.sound formed) atIndex substitution enough
  | .substitutedResult spine atIndex checked substitution enough sourceOrigin => by
      obtain ⟨converted, resultTyped⟩ :=
        (checked.soundWithSpine formed).2.2.substituteHead (spine.sound formed) atIndex substitution enough
      exact ⟨converted, (sourceOrigin.sound formed).termConv resultTyped converted⟩
  | .map prior transport => by
      obtain ⟨converted, typed⟩ := prior.sound formed
      exact transport.sound formed converted typed
termination_by structural support

theorem SynthesisBetaTrace.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {source result type : AExpr β}
    (support : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ConversionClaim.{u,v} entries context source result ∧ TypingClaim.{u,v} entries context result type :=
  match support with
  | .refl origin => ⟨.refl _, origin.sound formed⟩
  | .prefix headOrigin leading argumentsOrigin =>
      leading.beta_sound (headOrigin.sound formed) (argumentsOrigin.sound formed)
  | .origin retained => retained.sound formed
  | .trans prior next => by
      obtain ⟨first, middleTyped⟩ := prior.sound formed
      obtain ⟨second, resultTyped⟩ := next.sound formed
      exact ⟨first.trans second, middleTyped.termConv resultTyped second⟩
  | .atType sourceOrigin trace => by
      obtain ⟨converted, resultTyped⟩ := trace.sound formed
      exact ⟨converted, (sourceOrigin.sound formed).termConv resultTyped converted⟩
  | .application functionTrace argumentOrigin => by
      obtain ⟨converted, functionTyped⟩ := functionTrace.sound formed
      exact ⟨converted.app (.refl _), functionTyped.app (argumentOrigin.sound formed)⟩
  | .argument functionOrigin argumentOrigin argumentTrace => by
      obtain ⟨converted, resultTyped⟩ := argumentTrace.sound formed
      have functionTyped := functionOrigin.sound formed
      have argumentTyped := argumentOrigin.sound formed
      refine ⟨(ConversionClaim.refl _).app converted, ?_⟩
      exact (functionTyped.app argumentTyped).termConv
        (functionTyped.app (argumentTyped.termConv resultTyped converted)) ((ConversionClaim.refl _).app converted)
  | .substituteAt trace value substitution => by
      obtain ⟨converted, resultTyped⟩ := trace.sound formed
      have valueTyped := value.sound formed
      exact ⟨converted.instAt valueTyped substitution, resultTyped.instAt valueTyped substitution⟩
  | .weakenAt trace insertion => by
      obtain ⟨converted, resultTyped⟩ := trace.sound formed
      exact ⟨insertion.conversion converted, insertion.typing resultTyped⟩
  | .rebase origin trace => trace.sound (origin.sound formed)
  | .convertType trace typeTrace => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      obtain ⟨typeConversion, targetFormed⟩ := typeTrace.sound formed
      exact ⟨converted, typed.conv targetFormed typeConversion⟩
  | .instantiate trace arguments => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      refine ⟨?_, typing_instL_context typed arguments⟩
      intro V _ constants realizes levels env valid
      simpa only [interp_instL] using
        converted V constants realizes (arguments.map (VLevel.eval levels)) env (context_valid_instL valid)
  | .appendContext trace outer => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      refine ⟨?_, typing_append_context typed outer⟩
      intro V _ constants realizes levels env valid
      exact converted V constants realizes levels env (context_valid_prefix valid)
  | .extend trace extension => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      refine ⟨?_, extension.typing typed⟩
      intro V _ constants realizes levels env valid
      exact converted V constants (extension.realizes realizes) levels env valid
termination_by structural support

end

/-- The sort used by binder inference is justified after the actual exposure
of the returned type, without requiring that return to be a syntactic sort. -/
theorem SynthesisSortCheck.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {source : KExpr .anon} {trace : SortInferenceTrace fuel before source}
    {term : AExpr β} (check : SynthesisSortCheck resolve entries locals context bounds trace term)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    TypingClaim.{u,v} entries context term (.sort (readLevel trace.level)) :=
  (check.soundWithHereditary formed agreement reading).1

/-- The hereditary invariant supplies the existing application-spine
contract, including after a let substitutes an entire checked derivation. -/
theorem SynthesisInference.soundWithSpine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context term type ∧
      TypingClaim.{u,v} entries context type (.sort level) ∧
      LambdaSpineTyping.{u,v} entries context term type := by
  obtain ⟨reads, typed, typeFormed, hereditary⟩ := support.soundWithHereditary formed agreement reading accepted
  exact ⟨reads, typed, typeFormed, hereditary.lambdaSpine⟩

theorem SynthesisRetainedCheck.soundWithSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ TypingClaim.{u,v} entries context type (.sort level) ∧
      LambdaSpineTyping.{u,v} entries context term type := by
  obtain ⟨typed, typeFormed, hereditary⟩ := check.soundWithHereditary formed
  exact ⟨typed, typeFormed, hereditary.lambdaSpine⟩

/-- Ordinary argument typing and its syntactic leading domains remain
available without exposing the stronger application-spine result. -/
theorem SynthesisCheckedOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ LambdaPrefix term type term.lambdaDepth := by
  obtain ⟨typed, leading, _⟩ := support.soundWithSpine formed
  exact ⟨typed, leading⟩

/-- The public inference result projects ordinary typing and formation from
the stronger induction that also retains checked lambda domains. -/
theorem SynthesisInference.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context term type ∧
      TypingClaim.{u,v} entries context type (.sort level) := by
  obtain ⟨reads, typed, formation, _⟩ := support.soundWithSpine formed agreement reading accepted
  exact ⟨reads, typed, formation⟩

/-- Closed production inference supplies its own formation facts. No local
or whole-term semantic typing premise remains at this boundary. -/
theorem SynthesisInference.closed_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries [] [] [] fuel before source term type level)
    (reading : readScopedExpr? resolve [] source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve [] result = some type.erase ∧
      TypingClaim.{u,v} entries [] term type ∧ TypingClaim.{u,v} entries [] type (.sort level) :=
  support.sound (.empty entries) (.empty _ _) reading accepted

/-- An already supported type-inference call is a synthesis leaf because
its returned sort has an unconditional formation rule. -/
def SynthesisInference.ofSort {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term : AExpr β} {level : VLevel}
    (inference : BinderInference resolve entries locals context fuel before source term (.sort level)) :
    SynthesisInference resolve entries locals context bounds fuel before source term (.sort level) (.succ level) :=
  .known inference (.sort level)

/-- A retained type derivation with its local scope. Dependent substitution
keeps the original checking origins for each function-type child, so walking
the type still recovers its checked domains and codomains. -/
structure SynthesisScopedTypeCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (type : AExpr β) where
  context : Model.Context β
  level : VLevel
  check : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context type (.sort level)

theorem SynthesisScopedTypeCheck.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β}
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries check.context type (.sort check.level) :=
  check.check.origin.sound formed

def SynthesisScopedTypeCheck.forallBody {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {condition : Certified.PropWhen} {domain body : AExpr β}
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds
      entries (.forallE condition domain body)) :
    SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries body := by
  let child := check.check.forallView rfl
  exact {
    context := Context.push domain check.context
    level := child.bodyLevel
    check := child.bodyCheck }

def SynthesisScopedTypeCheck.variableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {index : Nat} {arguments : List (AExpr β)}
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds
      entries ((AExpr.bvar index).appN arguments)) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries
      check.context index arguments (.sort check.level) :=
  check.check.variableSpineOrigin index arguments rfl

/-- Package an executed closed type check so later declarations can retain
its origin. The check itself may contain direct lambda applications. -/
structure SynthesisTypeCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (type : AExpr β) (level : VLevel) where
  fuel : Nat
  before : TcState .anon
  after : TcState .anon
  source : KExpr .anon
  result : KExpr .anon
  bound : VLevel
  inference : SynthesisInference resolve entries [] [] [] fuel before source type (.sort level) bound
  reading : readScopedExpr? resolve [] source = some type.erase
  run : RecM.infer source (methodsN fuel) before = .ok result after

theorem SynthesisTypeCheck.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {type : AExpr β} {level : VLevel}
    (check : SynthesisTypeCheck resolve entries type level) :
    TypingClaim.{u,v} entries [] type (.sort level) :=
  (check.inference.closed_sound check.reading check.run).2.1

def SynthesisTypeCheck.scoped {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β} {level : VLevel}
    (check : SynthesisTypeCheck resolve entries type level) :
    SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries type :=
  { context := []
    level := level
    check := check.inference.betaTyping (.empty entries) (.empty _ _) check.reading check.run }

def SynthesisTypeCheck.forallBody {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {condition : Certified.PropWhen} {domain body : AExpr β} {level : VLevel}
    (check : SynthesisTypeCheck resolve entries (.forallE condition domain body) level) :
    SynthesisForallBodyCheck resolve entries [] [] condition domain body :=
  check.inference.forallBodyCheck (.empty _ _) check.reading check.run

/-- An instantiated constant can recover formation from an earlier actual
declaration type check, with exact interface preservation and structural
level congruence. -/
def SynthesisInference.ofTypeCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {earlier entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {term type declaredType : AExpr β} {level : VLevel}
    (inference : BinderInference resolve entries locals context fuel before source term type)
    (check : SynthesisTypeCheck resolve earlier declaredType level)
    (extension : InterfaceExtends earlier entries) (arguments : List VLevel)
    (same : AExpr.LevelEquivalent (declaredType.instL arguments) type) :
    SynthesisInference resolve entries locals context bounds fuel before source term type (level.inst arguments) :=
  .reuseType inference check.inference extension check.reading check.run same

end Ix.Kernel.Consistency
