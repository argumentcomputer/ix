import Ix.Tc.Verify.Inductive.GeneratedRecursorComparison
import Ix.Tc.Verify.RecursiveMethods.CallDomains

/-!
# Semantic acceptance of a generated-recursor candidate

This module interprets the exhaustive operational comparison trace.  Its only
semantic callback is one successful production `isDefEq` call at a time.  The
caller supplies structural translations for the frozen stored type and rule
RHSs; the callback transports each such expression to the exact target already
proved for the generated artifact.

Consequently, a successful comparison against an exact canonical generated
entry yields a DefEq-quotiented canonical stored type and every same-index
stored rule.  No coherence-only or whole-comparison oracle is available.
-/

namespace Ix.Tc

open Lean4Lean (VEnv VExpr VInductDecl)
open GeneratedRecursorSemantics

namespace GeneratedRecursorSemantics

/-- Reuse the generated entry's verified header while replacing its semantic
artifacts with the frozen stored declaration being checked. -/
def withStoredArtifacts (generated : GeneratedRecursor m)
    (ty : KExpr m) (rules : Array (RecRule m)) : GeneratedRecursor m :=
  { generated with ty, rules }

/-- Structural translations of the stored artifact snapshot.  Rule evidence
is positional and therefore cannot exchange equal RHSs at different indices. -/
structure StoredArtifactTranslationPlan
    (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) (ty : KExpr .anon)
    (rules : Array (RecRule .anon)) : Prop where
  type : ∃ translated,
    TrKExprS env uvars nameOf trProj [] ty translated
  ruleAt : ∀ index (hindex : index < rules.size),
    ∃ translated,
      TrKExprS env uvars nameOf trProj [] rules[index].rhs translated

/-- Exact finite DefEq footprint of a positional rule-comparison suffix. -/
def GeneratedRuleCallPlan (calls : Methods.CallDomain)
    (generatedRules storedRules : Array (RecRule .anon)) : Nat → Nat → Prop
  | _, 0 => True
  | index, remaining + 1 =>
      calls.isDefEq generatedRules[index]!.rhs storedRules[index]!.rhs ∧
        GeneratedRuleCallPlan calls generatedRules storedRules (index + 1)
          remaining

/-- The only DefEq calls needed to interpret one successful selected-candidate
comparison: its type call and every same-index rule call. -/
structure GeneratedArtifactCallPlan (calls : Methods.CallDomain)
    (generated : GeneratedRecursor .anon) (ty : KExpr .anon)
    (storedRules : Array (RecRule .anon)) : Prop where
  type : calls.isDefEq generated.ty ty
  rules : GeneratedRuleCallPlan calls generated.rules storedRules 0
    generated.rules.size

/-- The exact finite DefEq domain of one exhaustive candidate comparison.
All other recursive-method fields are empty; rule calls retain their concrete
same-index position. -/
def GeneratedArtifactCallDomain (generated : GeneratedRecursor .anon)
    (ty : KExpr .anon) (storedRules : Array (RecRule .anon)) :
    Methods.CallDomain where
  whnf := fun _ => False
  whnfCore := fun _ => False
  whnfMode := fun _ _ => False
  whnfCoreFlags := fun _ _ => False
  infer := fun _ => False
  isDefEq := fun left right =>
    (left = generated.ty ∧ right = ty) ∨
      ∃ index, index < generated.rules.size ∧
        left = generated.rules[index]!.rhs ∧
        right = storedRules[index]!.rhs

namespace GeneratedArtifactCallDomain

/-- Every positional suffix is admitted by its exact candidate-comparison
domain.  The span premise prevents the totalized stored lookup from admitting
an index beyond the generated rule array. -/
theorem rulePlan (generated : GeneratedRecursor .anon) (ty : KExpr .anon)
    (storedRules : Array (RecRule .anon)) :
    ∀ (index remaining : Nat),
      index + remaining = generated.rules.size →
      GeneratedRuleCallPlan
        (GeneratedArtifactCallDomain generated ty storedRules)
        generated.rules storedRules index remaining
  | _, 0, _ => trivial
  | index, remaining + 1, span => by
      refine ⟨Or.inr ⟨index, by omega, rfl, rfl⟩, ?_⟩
      apply rulePlan generated ty storedRules (index + 1) remaining
      omega

/-- Canonical call plan for the exact finite domain of one candidate. -/
theorem callPlan (generated : GeneratedRecursor .anon) (ty : KExpr .anon)
    (storedRules : Array (RecRule .anon)) :
    GeneratedArtifactCallPlan
      (GeneratedArtifactCallDomain generated ty storedRules)
      generated ty storedRules := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
  apply rulePlan generated ty storedRules 0 generated.rules.size
  omega

end GeneratedArtifactCallDomain

/-- Exact semantic meaning required from one actual successful DefEq call.
The contract cannot certify an entire candidate: it receives one exact target,
one independently translated stored expression, and the corresponding
production execution. -/
def ArtifactDefEqContract
    (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) (calls : Methods.CallDomain)
    (methods : Methods .anon)
    (invariant : TcState .anon → Prop) : Prop :=
  ∀ {state final : TcState .anon} {generated stored : KExpr .anon}
      {target storedV : VExpr},
    calls.isDefEq generated stored →
    invariant state →
    TrKExprS env uvars nameOf trProj [] generated target →
    TrKExprS env uvars nameOf trProj [] stored storedV →
    (RecM.isDefEq generated stored).run methods state = .ok true final →
    invariant final ∧
      TrKExpr env uvars nameOf trProj [] stored target

/-- Canonical stored-rule facts for one contiguous positional suffix. -/
inductive CanonicalStoredRuleSuffix
    (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) {source : VInductDecl}
    (generation : source.GenerationChecked)
    (rules : Array (RecRule .anon)) : Nat → Nat → Prop
  | nil (index) :
      CanonicalStoredRuleSuffix env nameOf trProj generation rules index 0
  | cons {index remaining normalized}
      (normalizedAt :
        generation.block.ctorPairs[index]? = some normalized)
      (fields : rules[index]!.fields.toNat =
        (normalized.fieldsR source.uvars source.nparams).length)
      (rhs : TrKExpr env generation.recursor.uvars nameOf trProj []
        rules[index]!.rhs (generation.rule index normalized).rhs)
      (tail : CanonicalStoredRuleSuffix env nameOf trProj generation rules
        (index + 1) remaining) :
      CanonicalStoredRuleSuffix env nameOf trProj generation rules index
        (remaining + 1)

namespace CanonicalStoredRuleSuffix

/-- Select any relative position from a canonical suffix. -/
theorem get
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {source : VInductDecl}
    {generation : source.GenerationChecked}
    {rules : Array (RecRule .anon)} {index remaining offset : Nat}
    (suffix : CanonicalStoredRuleSuffix env nameOf trProj generation rules
      index remaining)
    (hoffset : offset < remaining) :
    ∃ normalized,
      generation.block.ctorPairs[index + offset]? = some normalized ∧
      rules[index + offset]!.fields.toNat =
        (normalized.fieldsR source.uvars source.nparams).length ∧
      TrKExpr env generation.recursor.uvars nameOf trProj []
        rules[index + offset]!.rhs
        (generation.rule (index + offset) normalized).rhs := by
  induction suffix generalizing offset with
  | nil index => omega
  | @cons index remaining normalized normalizedAt fields rhs tail ih =>
      cases offset with
      | zero =>
          simpa using ⟨normalized, normalizedAt, fields, rhs⟩
      | succ offset =>
          have selected := ih (offset := offset) (by omega)
          have positionEq :
              index + 1 + offset = index + (offset + 1) := by
            omega
          rw [positionEq] at selected
          exact selected

/-- A complete position-zero suffix is the quotient-level canonical rule
array consumed by recursor acceptance. -/
theorem canonicalRules
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {source : VInductDecl}
    {generation : source.GenerationChecked}
    {rules : Array (RecRule .anon)}
    (suffix : CanonicalStoredRuleSuffix env nameOf trProj generation rules 0
      rules.size)
    (size : rules.size = generation.block.ctorPairs.length) :
    CanonicalRules env nameOf trProj generation rules := by
  refine ⟨size, ?_⟩
  intro index hindex
  have selected := suffix.get (offset := index) hindex
  simpa only [Nat.zero_add, getElem!_pos rules index hindex] using selected

end CanonicalStoredRuleSuffix

/-- Complete semantic result of one successful selected-candidate check. -/
structure CanonicalCandidateAcceptance
    (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) {source : VInductDecl}
    (generation : source.GenerationChecked)
    (ty : KExpr .anon) (declaredLvls : UInt64)
    (declaredIsUnsafe : Bool) (params motives minors indices : UInt64)
    (storedRules : Array (RecRule .anon))
    (generated : GeneratedRecursor .anon)
    (invariant : TcState .anon → Prop) (final : TcState .anon) : Prop where
  levels : declaredLvls = generated.lvls
  safety : declaredIsUnsafe = generated.isUnsafe
  params : params = generated.params
  motives : motives = generated.motives
  minors : minors = generated.minors
  indices : indices = generated.indices
  finalInvariant : invariant final
  artifacts : CanonicalArtifacts env nameOf trProj generation
    (withStoredArtifacts generated ty storedRules)

/-- Semantic result of a complete frozen-cache selection and comparison.
The selected position and post-selection state remain visible, so neither
signature disambiguation nor array lookup can be hidden by an existential
canonical artifact unrelated to the candidate that was actually checked. -/
def CanonicalCacheAcceptance
    (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) {source : VInductDecl}
    (generation : source.GenerationChecked)
    (recBlock id : KId .anon) (ty : KExpr .anon)
    (declaredLvls : UInt64) (declaredIsUnsafe : Bool)
    (params motives minors indices : UInt64) (indId : KId .anon)
    (storedRules : Array (RecRule .anon))
    (generated : Array (GeneratedRecursor .anon))
    (methods : Methods .anon) (invariant : TcState .anon → Prop)
    (initial final : TcState .anon) : Prop :=
  ∃ (index : Nat) (selected : GeneratedRecursor .anon)
      (afterSelection : TcState .anon),
    (RecM.selectGeneratedRecursorIndex recBlock id ty params motives minors
      indId generated).run methods initial = .ok (some index) afterSelection ∧
    generated[index]? = some selected ∧
    CanonicalCandidateAcceptance env nameOf trProj generation ty declaredLvls
      declaredIsUnsafe params motives minors indices storedRules selected
        invariant final

end GeneratedRecursorSemantics

open GeneratedRecursorSemantics

namespace GeneratedRuleComparisonTrace

/-- Interpret a complete operational rule suffix using only the exact
generated rule relation, stored structural translations, and one-call DefEq
semantics. -/
theorem canonicalSuffix
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {source : VInductDecl}
    {generation : source.GenerationChecked}
    {generatedRules storedRules : Array (RecRule .anon)}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {index remaining : Nat} {initial final : TcState .anon}
    (trace : GeneratedRuleComparisonTrace generatedRules storedRules methods
      index remaining initial final)
    (span : index + remaining = generatedRules.size)
    (sameSize : generatedRules.size = storedRules.size)
    (canonical : CanonicalRulesS env nameOf trProj generation generatedRules)
    (translations : ∀ position (hposition : position < storedRules.size),
      ∃ translated,
        TrKExprS env generation.recursor.uvars nameOf trProj []
          storedRules[position].rhs translated)
    (callPlan : GeneratedRuleCallPlan calls generatedRules storedRules index
      remaining)
    (defEq : ArtifactDefEqContract env generation.recursor.uvars nameOf trProj
      calls methods invariant)
    (initialInvariant : invariant initial) :
    invariant final ∧
      CanonicalStoredRuleSuffix env nameOf trProj generation storedRules index
        remaining := by
  induction trace with
  | nil index state =>
      exact ⟨initialInvariant, .nil index⟩
  | @cons index remaining before afterComparison final fields comparison tail ih =>
      rcases callPlan with ⟨comparisonCall, tailCalls⟩
      have generatedBound : index < generatedRules.size := by omega
      have storedBound : index < storedRules.size := by omega
      obtain ⟨normalized, normalizedAt, generatedFields, generatedRhs⟩ :=
        canonical.ruleAt index generatedBound
      obtain ⟨storedV, storedRhs⟩ := translations index storedBound
      have generatedRhs' :
          TrKExprS env generation.recursor.uvars nameOf trProj []
            generatedRules[index]!.rhs
            (generation.rule index normalized).rhs := by
        simpa only [getElem!_pos generatedRules index generatedBound] using
          generatedRhs
      have storedRhs' :
          TrKExprS env generation.recursor.uvars nameOf trProj []
            storedRules[index]!.rhs storedV := by
        simpa only [getElem!_pos storedRules index storedBound] using storedRhs
      obtain ⟨afterInvariant, storedCanonicalRhs⟩ :=
        defEq comparisonCall initialInvariant generatedRhs' storedRhs'
          comparison
      have tailSpan : index + 1 + remaining = generatedRules.size := by
        omega
      obtain ⟨finalInvariant, canonicalTail⟩ :=
        ih tailSpan tailCalls afterInvariant
      have storedFields : storedRules[index]!.fields.toNat =
          (normalized.fieldsR source.uvars source.nparams).length := by
        rw [← fields]
        simpa only [getElem!_pos generatedRules index generatedBound] using
          generatedFields
      exact ⟨finalInvariant,
        .cons normalizedAt storedFields storedCanonicalRhs canonicalTail⟩

end GeneratedRuleComparisonTrace

namespace RecM

/-- A successful exhaustive production comparison consumes an exact canonical
generated entry and yields a canonical stored artifact in the DefEq quotient. -/
theorem checkGeneratedRecursorCandidate_canonical
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {source : VInductDecl}
    {generation : source.GenerationChecked}
    {ty : KExpr .anon} {declaredLvls : UInt64}
    {declaredIsUnsafe : Bool} {params motives minors indices : UInt64}
    {storedRules : Array (RecRule .anon)}
    {generated : GeneratedRecursor .anon} {methods : Methods .anon}
    {calls : Methods.CallDomain}
    {invariant : TcState .anon → Prop} {initial final : TcState .anon}
    (run : (checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe
      params motives minors indices storedRules generated).run methods initial =
        .ok () final)
    (canonical : CanonicalArtifactsS env nameOf trProj generation generated)
    (translations : StoredArtifactTranslationPlan env
      generation.recursor.uvars nameOf trProj ty storedRules)
    (callPlan : GeneratedArtifactCallPlan calls generated ty storedRules)
    (defEq : ArtifactDefEqContract env generation.recursor.uvars nameOf trProj
      calls methods invariant)
    (initialInvariant : invariant initial) :
    CanonicalCandidateAcceptance env nameOf trProj generation ty declaredLvls
      declaredIsUnsafe params motives minors indices storedRules generated
      invariant final := by
  have trace := checkGeneratedRecursorCandidate_success run
  rcases trace with ⟨levels, safety, paramsEq, motivesEq, minorsEq, indicesEq,
    afterType, typeRun, ruleCount, ruleTrace⟩
  obtain ⟨storedTypeV, storedType⟩ := translations.type
  obtain ⟨afterTypeInvariant, storedCanonicalType⟩ :=
    defEq callPlan.type initialInvariant canonical.type storedType typeRun
  have span : 0 + generated.rules.size = generated.rules.size := by omega
  obtain ⟨finalInvariant, storedCanonicalSuffix⟩ :=
    ruleTrace.canonicalSuffix span ruleCount canonical.rules
      translations.ruleAt callPlan.rules defEq afterTypeInvariant
  have storedRuleSize :
      storedRules.size = generation.block.ctorPairs.length :=
    ruleCount.symm.trans canonical.rules.size
  have storedCanonicalRules :
      CanonicalRules env nameOf trProj generation storedRules := by
    rw [ruleCount] at storedCanonicalSuffix
    apply storedCanonicalSuffix.canonicalRules
    exact storedRuleSize
  refine ⟨levels, safety, paramsEq, motivesEq, minorsEq, indicesEq,
    finalInvariant, ?_⟩
  exact ⟨storedCanonicalType, storedCanonicalRules⟩

/-- Compose frozen-cache selection with exhaustive semantic comparison.  All
selected-entry premises are indexed by the exact lookup exposed by the
production run; a proof about a different cache entry cannot discharge them. -/
theorem checkGeneratedRecursorFromCache_canonical
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {source : VInductDecl}
    {generation : source.GenerationChecked}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {declaredLvls : UInt64} {declaredIsUnsafe : Bool}
    {params motives minors indices : UInt64} {indId : KId .anon}
    {storedRules : Array (RecRule .anon)}
    {generated : Array (GeneratedRecursor .anon)}
    {methods : Methods .anon} {calls : Methods.CallDomain}
    {invariant : TcState .anon → Prop} {initial final : TcState .anon}
    (run : (checkGeneratedRecursorFromCache recBlock id ty declaredLvls
      declaredIsUnsafe params motives minors indices indId storedRules
      generated).run methods initial = .ok () final)
    (canonicalAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      generated[index]? = some selected →
        CanonicalArtifactsS env nameOf trProj generation selected)
    (translations : StoredArtifactTranslationPlan env
      generation.recursor.uvars nameOf trProj ty storedRules)
    (callPlanAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      generated[index]? = some selected →
        GeneratedArtifactCallPlan calls selected ty storedRules)
    (selectionInvariant : ∀ {index : Nat}
        {selected : GeneratedRecursor .anon} {afterSelection : TcState .anon},
      (selectGeneratedRecursorIndex recBlock id ty params motives minors indId
        generated).run methods initial = .ok (some index) afterSelection →
      generated[index]? = some selected → invariant afterSelection)
    (defEq : ArtifactDefEqContract env generation.recursor.uvars nameOf trProj
      calls methods invariant) :
    CanonicalCacheAcceptance env nameOf trProj generation recBlock id ty
      declaredLvls declaredIsUnsafe params motives minors indices indId
      storedRules generated methods invariant initial final := by
  obtain ⟨index, selected, afterSelection, selection, lookup, comparison⟩ :=
    checkGeneratedRecursorFromCache_success run
  refine ⟨index, selected, afterSelection, selection, lookup, ?_⟩
  exact checkGeneratedRecursorCandidate_canonical comparison
    (canonicalAt lookup) translations (callPlanAt lookup) defEq
      (selectionInvariant selection lookup)

end RecM

end Ix.Tc
