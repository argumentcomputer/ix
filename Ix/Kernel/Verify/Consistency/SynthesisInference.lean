/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Formation
import Ix.Theory.Model.UniverseBounds

/-!
Inference with formation of the returned type. Local bounds come from the
executed checks of binder domains; external type bounds retain their actual
checking origin. Applications recover a codomain bound from an inhabited
product. Lambdas therefore synthesize full typing, including when they occur
directly in function position.

The recorded level is an upper bound for the inferred type. It preserves the
exact zero condition, but its positive value need not be the sort the kernel
would infer on a separate call. No such extra call is assumed.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Finite support for the actual production calls, enriched with the
origins and syntactic levels needed to derive formation. There are no
semantic typing or conversion fields. -/
inductive SynthesisInference {β : Type u}
    (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → List FVarId → Model.Context β → List VLevel → Nat → TcState .anon → KExpr .anon →
      AExpr β → AExpr β → VLevel → Type u
  | known {entries locals context bounds fuel before source term type level}
      (inference : BinderInference resolve entries locals context fuel before source term type)
      (formation : TypeFormation resolve entries context type level) :
      SynthesisInference resolve entries locals context bounds fuel before source term type level
  | reuseType {earlier entries locals context bounds fuel before source term type
      typeFuel typeBefore typeAfter typeSource typeResult declaredType level typeBound arguments}
      (inference : BinderInference resolve entries locals context fuel before source term type)
      (typeTree : SynthesisInference resolve earlier [] [] [] typeFuel typeBefore typeSource
        declaredType (.sort level) typeBound)
      (extension : InterfaceExtends earlier entries)
      (typeReading : readScopedExpr? resolve [] typeSource = some declaredType.erase)
      (typeRun : RecM.infer typeSource (methodsN typeFuel) typeBefore = .ok typeResult typeAfter)
      (same : AExpr.LevelEquivalent (declaredType.instL arguments) type) :
      SynthesisInference resolve entries locals context bounds fuel before source term type (level.inst arguments)
  | fvar {entries locals context bounds fuel before source index type level}
      (inference : BinderInference resolve entries locals context fuel before source (.bvar index) type)
      (atIndex : context[index]? = some type)
      (boundAtIndex : bounds[index]? = some level) :
      SynthesisInference resolve entries locals context bounds fuel before source (.bvar index) type level
  | app {entries locals context bounds fuel before fn arg info f a A A' B condition functionLevel argumentLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.app fn arg info))
      (trace : ApplicationInferenceTrace fuel miss.keyed fn arg)
      (functionTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed fn
        f (.forallE condition A B) functionLevel)
      (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState
        arg a A' argumentLevel)
      (conditions : A'.annotations = A.annotations)
      (hashPath : (trace.argumentType == trace.domain) = true)
      (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain)
      (bodyConstructed : trace.codomain.Constructed)
      (argConstructed : arg.Constructed)
      (bodyBound : trace.codomain.size + 1 < UInt64.size)
      (argBound : arg.size < UInt64.size)
      (coherent : trace.comparedState.env.intern.WF)
      (faithful : KExpr.CollisionFree fun term => trace.comparedState.env.intern.ExprSupport term ∨
        KExpr.SubstReach arg trace.codomain 0 term) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.app fn arg info)
        (.app f a) (B.inst a) (applicationLevel functionLevel condition)
  | forallE {entries locals context bounds fuel before name bi domain body info A B domainBoundLevel bodyBoundLevel}
      (miss : UncachedInference before (.all name bi domain body info))
      (trace : ForallInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (absent : (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBoundLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened
        B (.sort (readLevel trace.bodyLevel)) bodyBoundLevel)
      (levelFaithful : ∀ a b,
        (KUniv.Sub a trace.domainLevel ∨ KUniv.Sub a trace.bodyLevel) →
        (KUniv.Sub b trace.domainLevel ∨ KUniv.Sub b trace.bodyLevel) → a.AddrFaithful b)
      (domainBound : trace.domainLevel.size < UInt64.size)
      (bodyBound : trace.bodyLevel.size < UInt64.size)
      (coherent : trace.bodyState.env.intern.WF)
      (faithful : KExpr.KeyCollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
        term = KExpr.mkSort (KUniv.mkIMax trace.domainLevel trace.bodyLevel)) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.all name bi domain body info)
        (.forallE (Certified.zeroCondition (readLevel trace.bodyLevel)) A B)
        (.sort (readLevel (KUniv.mkIMax trace.domainLevel trace.bodyLevel)))
        (.succ (readLevel (KUniv.mkIMax trace.domainLevel trace.bodyLevel)))
  | lam {entries locals context bounds fuel before name bi domain body info A b B condition domainBoundLevel bodyLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (absent : (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBoundLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened b B bodyLevel)
      (conditionAgrees : condition = Certified.zeroCondition bodyLevel)
      (constructed : trace.bodyType.Constructed)
      (bound : trace.bodyType.size + 1 < UInt64.size)
      (coherent : trace.bodyState.env.intern.WF)
      (closingFaithful : KExpr.CollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
        KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert trace.fresh 0)
          1 trace.bodyType 0 term)
      (faithful : KExpr.KeyCollisionFree fun term => trace.abstracted.2.ExprSupport term ∨
        term = KExpr.mkAll () () domain trace.abstracted.1) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.lam name bi domain body info)
        (.lam condition A b) (.forallE condition A B) (.imax (readLevel trace.domainLevel) bodyLevel)

/-- Simultaneous soundness of the term and formation of its returned type.
The context hypothesis is discharged by actual domain inference at each
binder, and by the empty context at the production declaration boundary. -/
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
  induction support generalizing result after with
  | known inference formation =>
      obtain ⟨reads, checked⟩ := inference.sound agreement reading accepted
      exact ⟨reads, checked.typing formation.sound, formation.sound⟩
  | @reuseType earlier entries locals context bounds fuel before source term type
      typeFuel typeBefore typeAfter typeSource typeResult declaredType level typeBound arguments
      inference typeTree extension typeReading typeRun same ihType =>
      obtain ⟨reads, checked⟩ := inference.sound agreement reading accepted
      obtain ⟨_, typeTyped, _⟩ := ihType (.empty _) (.empty _ _) typeReading typeRun
      have typeFormed : TypingClaim.{u,v} entries context type (.sort (level.inst arguments)) :=
        same.termTyping (typing_instL_closed (extension.typing typeTyped) _)
      exact ⟨reads, checked.typing typeFormed, typeFormed⟩
  | fvar inference atIndex boundAtIndex =>
      obtain ⟨reads, typed⟩ := inference.synthesis (.bvar _) agreement reading accepted
      exact ⟨reads, typed, formed _ _ _ atIndex boundAtIndex⟩
  | @app entries locals context bounds fuel before fn arg info f a A A' B condition functionLevel argumentLevel
      full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful ihFunction ihArgument =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, functionTyped, functionFormed⟩ :=
        ihFunction formed keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, codomainReads⟩ := readScopedExpr?_all_parts functionTypeReads
      have argumentAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨argumentTypeReads, argumentTyped, _⟩ :=
        ihArgument formed argumentAgreement argReads trace.argumentRun
      have sameReading := beq_readScopedExpr? (resolve := resolve) (locals := locals)
        (depth := 0) comparisonFaithful hashPath
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans (sameReading.trans domainReads))) conditions
      have checked := sameType ▸ argumentTyped.checking
      refine ⟨?_, functionTyped.appChecking checked,
        functionTyped.applicationType functionFormed checked⟩
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | forallE miss trace opening absent domainTree bodyTree levelFaithful domainBound bodyBound
      coherent faithful ihDomain ihBody =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _⟩ := ihDomain formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement absent domainReads bodyReads trace.openRun
      obtain ⟨_, bodyTyped, _⟩ :=
        ihBody (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      refine ⟨?_, ?_, TypingClaim.sort _⟩
      · rw [trace.output run, internExpr_readScopedExpr? coherent faithful]
        rfl
      · exact AExpr.LevelEquivalent.sort
          (Theory.VLevel.equiv_def.mpr fun levels =>
            (Theory.VLevel.equiv_def.mp (readLevel_mkIMax levelFaithful domainBound bodyBound)
              levels).symm) |>.typing (TypingClaim.forallE domainTyped bodyTyped rfl)
  | lam full miss trace opening absent domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful ihDomain ihBody =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _⟩ := ihDomain formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement absent domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyTyped, bodyFormed⟩ :=
        ihBody (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound coherent
        closingFaithful bodyTypeReads
      refine ⟨?_, TypingClaim.lam domainTyped bodyFormed bodyTyped conditionAgrees,
        TypingClaim.forallE domainTyped bodyFormed conditionAgrees⟩
      rw [trace.output run,
        internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
      simp [LambdaInferenceTrace.abstracted, domainReads, closedReads, AExpr.erase]

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
