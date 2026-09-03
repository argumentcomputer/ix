import Ix.Tc.Verify.Inductive.GeneratedRecursorSelection
import Ix.Tc.Verify.Inductive.GeneratedRecursorAcceptanceClosure
import Ix.Tc.Verify.Inductive.GeneratedRecursorCommitFixture

/-!
# Production generated-recursor checker fixture

This module runs the production frozen-cache selection and exhaustive
candidate comparison on the canonical `IndexedVec` transaction.  The cache
contains exactly one entry, so the operational trace identifies the same
entry whose type and rules were independently proved canonical at commit.

The stored recursor is translated independently from the generated cache.
Consequently, later semantic closure cannot justify the stored declaration by
silently reusing the generated artifact's translation.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open GeneratedRecursorSemantics
open IndexedRecursiveCertificateFixture
open Lean4Lean.InductiveReplayFixtures

/-! ## Actual frozen-cache checker execution -/

def familyCacheCheckOutcome :=
  (RecM.checkGeneratedRecursorFromCache recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors).run checkerMethods familyRuleCommitAfter

def familyCacheCheckAfter : TcState .anon :=
  match familyCacheCheckOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyCacheCheckSucceeded : Bool :=
  match familyCacheCheckOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyCacheCheckSucceededNative :
    familyCacheCheckSucceeded = true := by
  native_decide

theorem familyCacheCheckSucceeded_eq :
    familyCacheCheckSucceeded = true :=
  familyCacheCheckSucceededNative

/-- The production post-commit cache checker takes its complete success path. -/
theorem familyCacheCheckRun :
    (RecM.checkGeneratedRecursorFromCache recursorBlockId recursorId
        recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
        familyInstalledRecursors).run checkerMethods familyRuleCommitAfter =
      .ok () familyCacheCheckAfter := by
  have success := familyCacheCheckSucceeded_eq
  unfold familyCacheCheckSucceeded at success
  unfold familyCacheCheckAfter
  generalize houtcome : familyCacheCheckOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyCacheCheckOutcome]

/-- Successful execution exposes the exact stateful selection and every
subsequent type/rule comparison performed by production. -/
theorem familyCacheCheckTrace :
    GeneratedRecursorCacheTrace recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods familyRuleCommitAfter
      familyCacheCheckAfter :=
  RecM.checkGeneratedRecursorFromCache_success familyCacheCheckRun

/-! ## Exact selected cache entry -/

/-- Any successful lookup in the installed singleton identifies position zero
and the exact canonical entry at that position. -/
theorem familyInstalledRecursorLookupUnique
    {index : Nat} {selected : GeneratedRecursor .anon}
    (lookup : familyInstalledRecursors[index]? = some selected) :
    index = 0 ∧ selected = familyInstalledRecursors[0]! := by
  obtain ⟨bound, value⟩ := Array.getElem?_eq_some_iff.mp lookup
  have indexEq : index = 0 := by
    rw [familyInstalledRecursorsSize] at bound
    omega
  subst index
  refine ⟨rfl, ?_⟩
  have zeroBound : 0 < familyInstalledRecursors.size := by
    rw [familyInstalledRecursorsSize]
    omega
  rw [getElem!_pos familyInstalledRecursors 0 zeroBound, value]

/-- The actual selection phase reaches position zero, then production compares
exactly that canonical installed artifact. -/
theorem familyCacheCheckSelectedZero :
    ∃ afterSelection,
      (RecM.selectGeneratedRecursorIndex recursorBlockId recursorId
          recursorConcrete.ty 1 1 2 familyId familyInstalledRecursors).run
          checkerMethods familyRuleCommitAfter =
        .ok (some 0) afterSelection ∧
      (RecM.checkGeneratedRecursorCandidate recursorConcrete.ty 2 false
          1 1 2 1 recursorRules familyInstalledRecursors[0]!).run
          checkerMethods afterSelection = .ok () familyCacheCheckAfter := by
  obtain ⟨index, selected, afterSelection, selection, lookup, comparison⟩ :=
    familyCacheCheckTrace
  obtain ⟨rfl, selectedEq⟩ := familyInstalledRecursorLookupUnique lookup
  subst selected
  exact ⟨afterSelection, selection, comparison⟩

/-! ## Independent stored-artifact translations -/

/-- The separately ingressed stored type and every stored rule RHS translate
independently of the generated cache entry used by the checker. -/
theorem familyStoredArtifactTranslations :
    StoredArtifactTranslationPlan indexedVecFinalEnv
      transaction.certificate.generation.recursor.uvars nameOf RawProjRel.none
      recursorConcrete.ty recursorRules := by
  refine ⟨⟨transaction.certificate.generation.recType, ?_⟩, ?_⟩
  · simpa [Lean4Lean.VInductDecl.GenerationChecked.recursor] using
      recursorTypeTyped
  · intro index hindex
    have indexTwo : index < 2 := by
      simpa [recursorRulesSize] using hindex
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · have zeroBound : 0 < recursorRules.size := by
        rw [recursorRulesSize]
        omega
      have typed := nilRuleTyped
      unfold concreteRuleAt at typed
      rw [getElem!_pos recursorRules 0 zeroBound] at typed
      have ruleUvars :
          (transaction.certificate.generation.rule 0 nilNormalized).uvars =
            transaction.certificate.generation.recursor.uvars := rfl
      rw [ruleUvars] at typed
      exact ⟨(transaction.certificate.generation.rule 0 nilNormalized).rhs,
        typed⟩
    · have oneBound : 1 < recursorRules.size := by
        rw [recursorRulesSize]
        omega
      have typed := consRuleTyped
      unfold concreteRuleAt at typed
      rw [getElem!_pos recursorRules 1 oneBound] at typed
      have ruleUvars :
          (transaction.certificate.generation.rule 1 consNormalized).uvars =
            transaction.certificate.generation.recursor.uvars := rfl
      rw [ruleUvars] at typed
      exact ⟨(transaction.certificate.generation.rule 1 consNormalized).rhs,
        typed⟩

/-! ## Exact finite semantic comparison domain -/

/-- The finite DefEq domain contains only the selected type comparison and
the two same-index rule comparisons. -/
def familyArtifactCalls : Methods.CallDomain :=
  GeneratedArtifactCallDomain familyInstalledRecursors[0]!
    recursorConcrete.ty recursorRules

/-- Every call admitted by the concrete frozen-artifact domain compares
literally identical syntax.  The type and rule arrays installed by the
transactional commit are the immutable ingress artifacts, so this statement
does not identify merely DefEq-equivalent generated expressions. -/
theorem familyArtifactCall_eq
    {left right : KExpr .anon}
    (call : familyArtifactCalls.isDefEq left right) : left = right := by
  change
    (left = familyInstalledRecursors[0]!.ty ∧
        right = recursorConcrete.ty) ∨
      ∃ index, index < familyInstalledRecursors[0]!.rules.size ∧
        left = familyInstalledRecursors[0]!.rules[index]!.rhs ∧
        right = recursorRules[index]!.rhs at call
  rcases call with ⟨rfl, rfl⟩ | ⟨index, _bound, rfl, rfl⟩
  · exact familyInstalledRecursorType_eq
  · rw [familyInstalledRecursorRules_eq]

/-- Active finite-call contract for the exact three frozen-artifact
comparisons.  All non-DefEq fields are empty, while each DefEq call executes
the real production trace/statistics prefix and literal address-equality fast
path under coordinated recursor-block authority. -/
theorem familyArtifactMethodsActiveScopedWFAtOn
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (theory : WhnfTheory RawProjRel.none familyAcceptedWorld
      model.keys.uvars)
    (within : familyArtifactCalls.Within support) :
    Methods.ActiveScopedWFAtOn model layer semantics support recursorMembers
      familyArtifactCalls (Methods.next checkerMethods) where
  within := within
  whnf call _ := False.elim call
  whnfCore call _ := False.elim call
  whnfMode call _ := False.elim call
  whnfCoreFlags call _ := False.elim call
  infer call _ := False.elim call
  isDefEq call leftTranslation rightTranslation := by
    simp only [Methods.next]
    exact RecM.isDefEq_eq_activeScoped_wf theory
      (familyArtifactCall_eq call) leftTranslation rightTranslation
        checkerMethods

theorem familyInstalledRecursorCanonicalAt
    {index : Nat} {selected : GeneratedRecursor .anon}
    (lookup : familyInstalledRecursors[index]? = some selected) :
    CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation selected := by
  obtain ⟨rfl, selectedEq⟩ := familyInstalledRecursorLookupUnique lookup
  subst selected
  exact familyInstalledRecursorCanonical

theorem familyArtifactCallPlanAt
    {index : Nat} {selected : GeneratedRecursor .anon}
    (lookup : familyInstalledRecursors[index]? = some selected) :
    GeneratedArtifactCallPlan familyArtifactCalls selected
      recursorConcrete.ty recursorRules := by
  obtain ⟨rfl, selectedEq⟩ := familyInstalledRecursorLookupUnique lookup
  subst selected
  exact GeneratedArtifactCallDomain.callPlan familyInstalledRecursors[0]!
    recursorConcrete.ty recursorRules

/-! ## Selection callback closure -/

/-- Every possible selection call in the installed singleton is the same
complete-type call already admitted by the exact artifact domain. -/
theorem familySelectionCallPlan :
    GeneratedSelectionCallPlan familyArtifactCalls familyInstalledRecursors
      recursorConcrete.ty := by
  intro index selected lookup
  obtain ⟨rfl, selectedEq⟩ := familyInstalledRecursorLookupUnique lookup
  subst selected
  exact Or.inl ⟨rfl, rfl⟩

/-- Selection translates only complete closed recursor types.  The stored
translation is independent of the canonical installed entry. -/
theorem familySelectionTranslations :
    GeneratedSelectionTranslationPlan indexedVecFinalEnv
      transaction.certificate.generation.recursor.uvars nameOf
      RawProjRel.none familyInstalledRecursors recursorConcrete.ty := by
  refine ⟨familyStoredArtifactTranslations.type, ?_⟩
  intro index selected lookup
  exact ⟨transaction.certificate.generation.recType,
    (familyInstalledRecursorCanonicalAt lookup).type⟩

/-- Admitting the certified family transaction materializes exactly the
semantic environment used by the generated-artifact proofs. -/
theorem familyAcceptedWorld_venv_eq :
    familyAcceptedWorld.venv = indexedVecFinalEnv := rfl

theorem familyAcceptedWorld_nameOf_eq :
    familyAcceptedWorld.nameOf = nameOf := rfl

/-- Transport the concrete closed-type translations to the exact suffix-model
universe count selected by K2S. -/
theorem familySelectionTranslationsScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars) :
    GeneratedSelectionTranslationPlan familyAcceptedWorld.venv
      model.keys.uvars familyAcceptedWorld.nameOf RawProjRel.none
      familyInstalledRecursors recursorConcrete.ty := by
  simpa only [familyAcceptedWorld_venv_eq,
    familyAcceptedWorld_nameOf_eq, ← uvars] using
      familySelectionTranslations

/-- The concrete selection phase preserves the scoped K2 invariant under the
same finite successor layer later used for exhaustive artifact comparison. -/
theorem familySelectionInvariantScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ScopedWFAtOn model layer semantics support
      familyArtifactCalls (Methods.next checkerMethods))
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support []
        familyRuleCommitAfter) :
    ∀ {index : Nat} {selected : GeneratedRecursor .anon}
        {afterSelection : TcState .anon},
      (RecM.selectGeneratedRecursorIndex recursorBlockId recursorId
          recursorConcrete.ty 1 1 2 familyId familyInstalledRecursors).run
          checkerMethods familyRuleCommitAfter =
        .ok (some index) afterSelection →
      familyInstalledRecursors[index]? = some selected →
      ScopedWhnfStateInv model layer semantics support []
        afterSelection := by
  intro index selected afterSelection selection _lookup
  exact RecM.selectGeneratedRecursorIndex_preservesScoped
    familySelectionCallPlan (familySelectionTranslationsScoped uvars)
      successor initialInvariant selection

/-- All concrete production and representation premises are discharged.  The
remaining semantic inputs are selection-state preservation and the K2 meaning
of the exact three comparison calls. -/
theorem familyCacheCheckCanonical
    {invariant : TcState .anon → Prop}
    (selectionInvariant : ∀ {index : Nat}
        {selected : GeneratedRecursor .anon}
        {afterSelection : TcState .anon},
      (RecM.selectGeneratedRecursorIndex recursorBlockId recursorId
          recursorConcrete.ty 1 1 2 familyId familyInstalledRecursors).run
          checkerMethods familyRuleCommitAfter =
        .ok (some index) afterSelection →
      familyInstalledRecursors[index]? = some selected →
      invariant afterSelection)
    (defEq : ArtifactDefEqContract indexedVecFinalEnv
      transaction.certificate.generation.recursor.uvars nameOf RawProjRel.none
      familyArtifactCalls checkerMethods invariant) :
    CanonicalCacheAcceptance indexedVecFinalEnv nameOf
      RawProjRel.none transaction.certificate.generation
      recursorBlockId recursorId recursorConcrete.ty 2 false 1 1 2 1
      familyId recursorRules familyInstalledRecursors checkerMethods invariant
      familyRuleCommitAfter familyCacheCheckAfter := by
  exact RecM.checkGeneratedRecursorFromCache_canonical familyCacheCheckRun
    familyInstalledRecursorCanonicalAt familyStoredArtifactTranslations
    familyArtifactCallPlanAt selectionInvariant defEq

/-- Concrete E2c checker closure: one finite K2S successor-layer contract
accounts for the selection call, the repeated full-type comparison, and both
positional rule comparisons. -/
theorem familyCacheCheckCanonicalScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ScopedWFAtOn model layer semantics support
      familyArtifactCalls (Methods.next checkerMethods))
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support []
        familyRuleCommitAfter) :
    CanonicalCacheAcceptance indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods
      (ScopedWhnfStateInv model layer semantics support [])
      familyRuleCommitAfter familyCacheCheckAfter := by
  have defEq : ArtifactDefEqContract indexedVecFinalEnv
      transaction.certificate.generation.recursor.uvars nameOf RawProjRel.none
      familyArtifactCalls checkerMethods
        (ScopedWhnfStateInv model layer semantics support []) := by
    have closed : ArtifactDefEqContract familyAcceptedWorld.venv
        model.keys.uvars familyAcceptedWorld.nameOf RawProjRel.none
        familyArtifactCalls checkerMethods
          (ScopedWhnfStateInv model layer semantics support []) :=
      successor.artifactDefEqContract
    intro state final generated stored target storedV call initial
      generatedTr storedTr run
    have generatedTr' : TrKExprS familyAcceptedWorld.venv model.keys.uvars
        familyAcceptedWorld.nameOf RawProjRel.none [] generated target := by
      simpa only [familyAcceptedWorld_venv_eq,
        familyAcceptedWorld_nameOf_eq, ← uvars] using generatedTr
    have storedTr' : TrKExprS familyAcceptedWorld.venv model.keys.uvars
        familyAcceptedWorld.nameOf RawProjRel.none [] stored storedV := by
      simpa only [familyAcceptedWorld_venv_eq,
        familyAcceptedWorld_nameOf_eq, ← uvars] using storedTr
    obtain ⟨finalInvariant, storedCanonical⟩ :=
      closed call initial generatedTr' storedTr' run
    refine ⟨finalInvariant, ?_⟩
    simpa only [familyAcceptedWorld_venv_eq,
      familyAcceptedWorld_nameOf_eq, ← uvars] using storedCanonical
  exact familyCacheCheckCanonical
    (familySelectionInvariantScoped uvars successor initialInvariant) defEq

/-- Operational success, exact selected-entry identity, canonical generated
artifacts, and independent stored translations packaged for semantic closure. -/
theorem familyCacheCheckExecution :
    (RecM.checkGeneratedRecursorFromCache recursorBlockId recursorId
        recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
        familyInstalledRecursors).run checkerMethods familyRuleCommitAfter =
        .ok () familyCacheCheckAfter ∧
      CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
        transaction.certificate.generation familyInstalledRecursors[0]! ∧
      StoredArtifactTranslationPlan indexedVecFinalEnv
        transaction.certificate.generation.recursor.uvars nameOf
        RawProjRel.none recursorConcrete.ty recursorRules :=
  ⟨familyCacheCheckRun, familyInstalledRecursorCanonical,
    familyStoredArtifactTranslations⟩

end Ix.Tc.IndexedRecursiveFixture
