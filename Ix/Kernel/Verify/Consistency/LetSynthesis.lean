/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LetInference
import Ix.Kernel.Verify.Consistency.BetaInference

/-! Connect the full let branch to its original domain, value, and body
checks. The generated term retains their complete beta derivations after
substitution. No semantic typing or conversion is supplied as a resource. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The actual final cheap-beta choice, with an original checking origin
for a selected reduction. The unchanged case needs only the planner result. -/
inductive LetTypeReduction {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (context : Model.Context β) (bounds : List VLevel)
    (source : KExpr .anon) (table : InternTable .anon) (level : VLevel) :
    AExpr β → AExpr β → Type u
  | unchanged {term : AExpr β} (plan : cheapBetaPlan? source = none) :
      LetTypeReduction resolve entries context bounds source table level term term
  | beta {condition : Certified.PropWhen} {domain body : AExpr β} {arguments : List (AExpr β)}
      (support : CheapBetaSupport source table)
      (origin : SynthesisBetaTrace resolve entries context bounds entries context
        ((AExpr.lam condition domain body).appN arguments)
        (AExpr.betaPrefix (cheapBetaCount source) (.lam condition domain body) arguments) (.sort level)) :
      LetTypeReduction resolve entries context bounds source table level
        ((AExpr.lam condition domain body).appN arguments)
        (AExpr.betaPrefix (cheapBetaCount source) (.lam condition domain body) arguments)

theorem LetTypeReduction.reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {locals : List FVarId} {source : KExpr .anon} {table : InternTable .anon}
    {level : VLevel} {term result : AExpr β}
    (reduction : LetTypeReduction resolve entries context bounds source table level term result)
    (coherent : table.WF)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    readScopedExpr? resolve locals (cheapBetaReduce source table).1 = some result.erase ∧
      (cheapBetaReduce source table).2.WF := by
  cases reduction with
  | unchanged plan =>
      rw [cheapBetaReduce, plan]
      exact ⟨reading, coherent⟩
  | beta support _ => exact (support.reading reading).2

def LetTypeReduction.trace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {source : KExpr .anon} {table : InternTable .anon} {level : VLevel} {term result : AExpr β}
    (reduction : LetTypeReduction resolve entries context bounds source table level term result)
    (original : SynthesisTypingOrigin resolve entries context bounds entries context term (.sort level)) :
    SynthesisBetaTrace resolve entries context bounds entries context term result (.sort level) :=
  match reduction with
  | .unchanged _ => .refl original
  | .beta _ origin => origin

/-- All three children are the original executed synthesis checks. Because
let erasure loses its constructor, their separate source readings are retained
explicitly. The comparison relates the inferred value type to the declaration. -/
structure LetInferenceCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (locals : List FVarId) (context : Model.Context β)
    (bounds : List VLevel) (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (domain value body : KExpr .anon) (nonDep : Bool) (info : ExprInfo .anon)
    (A v b B resultType : AExpr β) (level : VLevel) where
  full : before.inferOnly = false
  localState : LocalStateInvariant before
  miss : UncachedInference before (.letE name domain value body nonDep info)
  execution : LetInferenceTrace fuel miss.keyed name domain value body
  opening : BinderOpeningSupport execution.comparedState body
  domainBound : VLevel
  valueLevel : VLevel
  valueType : AExpr β
  domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
    A (.sort (readLevel execution.domainLevel)) domainBound
  valueTree : SynthesisInference resolve entries locals context bounds fuel execution.domainState value
    v valueType valueLevel
  bodyTree : SynthesisInference resolve entries (execution.fresh :: locals) (context.push A)
    (readLevel execution.domainLevel :: bounds) fuel execution.openedState execution.opened b B level
  domainReading : readScopedExpr? resolve locals domain = some A.erase
  valueReading : readScopedExpr? resolve locals value = some v.erase
  bodyReading : readScopedExpr? resolve locals body 1 = some b.erase
  conditions : valueType.annotations = A.annotations
  hashPath : (execution.valueType == domain) = true
  comparisonFaithful : execution.valueType.AddrFaithful domain
  substitution : execution.SubstitutionSupport
  reduction : LetTypeReduction resolve entries context bounds execution.substituted.1 execution.substituted.2
    level (B.inst v) resultType

namespace LetInferenceCheck

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
  {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name} {domain value body : KExpr .anon}
  {nonDep : Bool} {info : ExprInfo .anon} {A val b B resultType : AExpr β} {level : VLevel}

/-- The initial invariant survives production's key computation. -/
theorem keyedValid
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level) : LocalStateInvariant check.miss.keyed :=
  ((FramesLocalState.inferKey _).ok check.localState check.miss.keyRun).invariant check.localState

/-- All recursive checks preserve the counter bound; the selected let id
therefore cannot name an existing model local. -/
theorem absent
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    (⟨check.execution.comparedState.env.nextFVarId⟩ : FVarId) ∉ locals := by
  have frame := check.execution.openingFrame check.keyedValid
  exact (frame.invariant check.keyedValid).freshReading
    ((check.miss.localContext.symm ▸ agreement).congr frame.context.symm)

theorem source_reading
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level) :
    readScopedExpr? resolve locals (.letE name domain value body nonDep info) = some (b.inst val).erase := by
  simp [readScopedExpr?, check.domainReading, check.valueReading, check.bodyReading, AExpr.erase_inst]

private theorem value_type
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context) : check.valueType = A := by
  have valueAgreement := (check.miss.localContext.symm ▸ agreement).congr (check.execution.domainContext check.keyedValid).symm
  have returned := (check.valueTree.soundWithSpine formed valueAgreement check.valueReading
    check.execution.valueRun).1
  exact AExpr.eq_of_erase_annotations
    (Option.some.inj (returned.symm.trans
      ((beq_readScopedExpr? check.comparisonFaithful check.hashPath).trans check.domainReading))) check.conditions

/-- Typing origins for the substituted inferred type come from the original
body inference and the value comparison, with the actual domain check forming
the body's context. -/
def substituted_type_origin
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    SynthesisTypingOrigin resolve entries context bounds entries context (B.inst val) (.sort level) := by
  have keyedAgreement := check.miss.localContext.symm ▸ agreement
  have valueAgreement := keyedAgreement.congr (check.execution.domainContext check.keyedValid).symm
  have opened := openLet_sound check.opening (keyedAgreement.congr (check.execution.openingContext check.keyedValid).symm)
    (check.absent agreement) check.domainReading check.bodyReading check.execution.openRun
  have bodyOrigin := SynthesisTypingOrigin.inferredType
    (SynthesisContext.push .current check.domainTree keyedAgreement check.domainReading check.execution.domainRun)
    check.bodyTree opened.2.2.1 opened.2.1 check.execution.bodyRun
  have valueOrigin := SynthesisTypingOrigin.source
    (SynthesisCheckedOrigin.checked .current check.valueTree valueAgreement check.valueReading check.execution.valueRun)
  have same := check.value_type formed agreement
  exact .substituteAt bodyOrigin (same ▸ valueOrigin) .root

/-- Substitution retains the body's entire beta derivation, including a
lambda introduced by substituting the value for the let-bound variable. -/
def betaTyping
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    SynthesisBetaTyping resolve entries context bounds entries context (b.inst val) resultType := by
  have keyedAgreement := check.miss.localContext.symm ▸ agreement
  have valueAgreement := keyedAgreement.congr (check.execution.domainContext check.keyedValid).symm
  have opened := openLet_sound check.opening (keyedAgreement.congr (check.execution.openingContext check.keyedValid).symm)
    (check.absent agreement) check.domainReading check.bodyReading check.execution.openRun
  have inner := check.bodyTree.betaTyping
    (SynthesisContext.push .current check.domainTree keyedAgreement check.domainReading check.execution.domainRun)
    opened.2.2.1 opened.2.1 check.execution.bodyRun formed
  have argument := check.valueTree.betaTyping .current valueAgreement check.valueReading check.execution.valueRun formed
  have same := check.value_type formed agreement
  exact .convert (inner.substituteAt (same ▸ argument) .root)
    (check.reduction.trace (check.substituted_type_origin formed agreement))

/-- Full-mode let success returns the checked type after the actual closing,
substitution, cheap reduction, scope cleanup, and outer cache publication. -/
theorem sound {result : KExpr .anon} {after : TcState .anon}
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (accepted : RecM.infer (.letE name domain value body nonDep info) (methodsN (fuel + 1)) before =
      .ok result after) :
    readScopedExpr? resolve locals result = some resultType.erase ∧
      TypingClaim.{u,v} entries context (b.inst val) resultType ∧
      TypingClaim.{u,v} entries context resultType (.sort level) := by
  have keyedAgreement := check.miss.localContext.symm ▸ agreement
  obtain ⟨_, domainTyped, _, _⟩ := check.domainTree.soundWithSpine formed keyedAgreement
    check.domainReading check.execution.domainRun
  have opened := openLet_sound check.opening (keyedAgreement.congr (check.execution.openingContext check.keyedValid).symm)
    (check.absent agreement) check.domainReading check.bodyReading check.execution.openRun
  obtain ⟨bodyTypeReading, _, _, _⟩ := check.bodyTree.soundWithSpine (formed.push domainTyped)
    opened.2.2.1 opened.2.1 check.execution.bodyRun
  obtain ⟨substitutedReading, substitutedCoherent⟩ :=
    check.execution.substituted_reading check.substitution bodyTypeReading check.valueReading
  have reducedReading := check.reduction.reading substitutedCoherent substitutedReading
  obtain ⟨middle, uncached⟩ := infer_uncached_success check.miss accepted
  rw [check.full] at uncached
  have output := (check.execution.output_state uncached).1
  refine ⟨?_, (check.betaTyping formed agreement).origin.sound formed, ?_⟩
  · rw [output]
    exact reducedReading.1
  · exact ((check.reduction.trace (check.substituted_type_origin formed agreement)).sound formed).2

theorem closed_sound {result : KExpr .anon} {after : TcState .anon}
    (check : LetInferenceCheck resolve entries [] [] [] fuel before name domain value body nonDep info
      A val b B resultType level)
    (accepted : RecM.infer (.letE name domain value body nonDep info) (methodsN (fuel + 1)) before =
      .ok result after) :
    readExpr? resolve result = some resultType.erase ∧
      TypingClaim.{u,v} entries [] (b.inst val) resultType ∧
      TypingClaim.{u,v} entries [] resultType (.sort level) := by
  obtain ⟨reading, typed, formed⟩ := check.sound (.empty entries) (LocalContextReading.empty _ _) accepted
  exact ⟨readScopedExpr?_closed reading, typed, formed⟩

/-- Every further head-beta step uses the substituted original checks,
without asking inference to check any generated intermediate expression. -/
theorem beta_steps_sound
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context) (count : Nat) :
    ConversionClaim.{u,v} entries context (b.inst val) (BetaSyntax.steps count (b.inst val)) ∧
      TypingClaim.{u,v} entries context (BetaSyntax.steps count (b.inst val)) resultType :=
  ((check.betaTyping formed agreement).betaSteps count).2.sound formed

end LetInferenceCheck

end Ix.Kernel.Consistency
