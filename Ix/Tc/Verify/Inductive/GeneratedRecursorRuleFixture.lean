import Ix.Tc.Verify.Inductive.GeneratedRecursorTypeFixture

/-!
# Production generated-recursor rule fixture

This module executes the complete production rule-population core for the
checked `IndexedVec` family.  The input is the exact immutable generated batch
left in `recursorCache` by the successful family checker.  The core scans the
separately ingressed recursor block, verifies canonical peer alignment, and
invokes `buildRuleRhs` for both constructors before returning its local batch.

As with the type fixture, total projections have unreachable fallbacks.  The
public run theorem proves the successful data-bearing branch, and the final
theorem identifies every returned rule position with Lean4Lean's canonical
normalized-constructor rule.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open GeneratedRecursorSemantics
open IndexedRecursiveCertificateFixture
open Lean4Lean.InductiveReplayFixtures

local instance generatedRuleKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance generatedRuleKExprDecidableEq : DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

local instance generatedRuleRecRuleDecidableEq :
    DecidableEq (RecRule .anon) :=
  AnonStructural.decidableEqOfRoundtrip AnonStructural.RecRule.ofKernel
    AnonStructural.RecRule.toKernel AnonStructural.RecRule.roundtrip

/-- Immutable generated batch installed by the successful family checker and
subsequently consumed by the recursor-block rule population path. -/
def familyGeneratedSnapshot : Array (GeneratedRecursor .anon) :=
  (familyKernelAfter.env.recursorCache[familyBlockId]?).getD #[]

private theorem familyGeneratedSnapshotSizeNative :
    familyGeneratedSnapshot.size = 1 := by
  native_decide

theorem familyGeneratedSnapshotSize : familyGeneratedSnapshot.size = 1 :=
  familyGeneratedSnapshotSizeNative

private theorem familyGeneratedSnapshotRulesNative :
    familyGeneratedSnapshot[0]!.rules = #[] := by
  native_decide

theorem familyGeneratedSnapshotRules :
    familyGeneratedSnapshot[0]!.rules = #[] :=
  familyGeneratedSnapshotRulesNative

/-! ## Actual complete rule-population execution -/

def familyRulePopulationOutcome :=
  (RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
      familyGeneratedSnapshot).run checkerMethods familyKernelAfter

def familyGeneratedWithRules : Array (GeneratedRecursor .anon) :=
  match familyRulePopulationOutcome with
  | .ok generated _ => generated
  | .error _ _ => #[]

def familyRulePopulationAfter : TcState .anon :=
  match familyRulePopulationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyRulePopulationSucceeded : Bool :=
  match familyRulePopulationOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyRulePopulationSucceededNative :
    familyRulePopulationSucceeded = true := by
  native_decide

theorem familyRulePopulationSucceeded_eq :
    familyRulePopulationSucceeded = true :=
  familyRulePopulationSucceededNative

/-- The real peer-alignment and complete-rule path returns the projected local
batch; no cache mutation is used as the proof result. -/
theorem familyRulePopulationRun :
    (RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
        familyGeneratedSnapshot).run checkerMethods familyKernelAfter =
      .ok familyGeneratedWithRules familyRulePopulationAfter := by
  have success := familyRulePopulationSucceeded_eq
  unfold familyRulePopulationSucceeded at success
  unfold familyGeneratedWithRules familyRulePopulationAfter
  generalize houtcome : familyRulePopulationOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyRulePopulationOutcome]

private theorem familyGeneratedWithRulesSizeNative :
    familyGeneratedWithRules.size = 1 := by
  native_decide

theorem familyGeneratedWithRulesSize : familyGeneratedWithRules.size = 1 :=
  familyGeneratedWithRulesSizeNative

def familyCompletedRecursor : GeneratedRecursor .anon :=
  familyGeneratedWithRules[0]!

def familyBuiltRules : Array (RecRule .anon) :=
  familyCompletedRecursor.rules

/-- Both production-built rules are structurally identical to the separately
ingressed recursor rules, including their field counts and recursive RHS. -/
private theorem familyBuiltRulesNative : familyBuiltRules = recursorRules := by
  native_decide

theorem familyBuiltRules_eq : familyBuiltRules = recursorRules :=
  familyBuiltRulesNative

private theorem recursorRulesLiteralNative :
    recursorRules = #[concreteRuleAt 0, concreteRuleAt 1] := by
  native_decide

theorem recursorRules_literal :
    recursorRules = #[concreteRuleAt 0, concreteRuleAt 1] :=
  recursorRulesLiteralNative

private theorem generationRuleCountNative :
    transaction.certificate.generation.block.ctorPairs.length = 2 := by
  native_decide

/-- The array returned by the actual complete-rule builder is positionally the
canonical Lean4Lean rule array for the certified IndexedVec generation. -/
theorem familyBuildRulesCanonical :
    CanonicalRulesS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyBuiltRules := by
  rw [familyBuiltRules_eq, recursorRules_literal]
  refine ⟨?_, ?_⟩
  · simpa using generationRuleCountNative.symm
  · intro index hindex
    change index < 2 at hindex
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · exact ⟨nilNormalized, nilNormalizedAt, nilRuleFields,
        nilRuleTyped⟩
    · exact ⟨consNormalized, consNormalizedAt, consRuleFields,
        consRuleTyped⟩

private theorem familyCompletedRecursorTypeNative :
    familyCompletedRecursor.ty = recursorConcrete.ty := by
  native_decide

theorem familyCompletedRecursorType_eq :
    familyCompletedRecursor.ty = recursorConcrete.ty :=
  familyCompletedRecursorTypeNative

/-- The complete-rule core preserves the canonical type installed by family
generation while replacing only the locally returned rule array. -/
theorem familyCompletedTypeCanonical :
    CanonicalTypeS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyCompletedRecursor := by
  unfold CanonicalTypeS
  rw [familyCompletedRecursorType_eq]
  simpa [Lean4Lean.VInductDecl.GenerationChecked.recursor] using
    recursorTypeTyped

/-- The actual local result of the rule-population core contains both the
canonical generated type and all positional canonical rules. -/
theorem familyCompletedArtifactsCanonical :
    CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyCompletedRecursor :=
  ⟨familyCompletedTypeCanonical, familyBuildRulesCanonical⟩

/-- One theorem packages the exact production rule-population execution and
the positional canonical semantic postcondition. -/
theorem familyBuildRulesExecution :
    (RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
        familyGeneratedSnapshot).run checkerMethods familyKernelAfter =
      .ok familyGeneratedWithRules familyRulePopulationAfter ∧
    CanonicalRulesS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyBuiltRules :=
  ⟨familyRulePopulationRun, familyBuildRulesCanonical⟩

/-- Stronger execution package consumed by the forthcoming transactional
commit and recursor-checker composition. -/
theorem familyBuildArtifactsExecution :
    (RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
        familyGeneratedSnapshot).run checkerMethods familyKernelAfter =
      .ok familyGeneratedWithRules familyRulePopulationAfter ∧
    CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyCompletedRecursor :=
  ⟨familyRulePopulationRun, familyCompletedArtifactsCanonical⟩

end Ix.Tc.IndexedRecursiveFixture
