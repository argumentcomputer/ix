import Ix.Tc.Verify.Inductive.GeneratedRecursorTypeClosure
import Ix.Tc.Verify.Inductive.IndexedRecursiveAcceptance
import Ix.Tc.Verify.Ingress.AnonStructural

/-!
# Production generated-recursor type fixture

This module executes the real generated-recursor preparation and type builder
for the certified `IndexedVec` fixture.  It deliberately starts from the
successful post-family checker state: all source constants have passed the
production family checks, while the call below still recomputes the exact
flat block, motives, open telescope, and closed recursor type through the
production helpers.

The fallback values only make the projections total.  The public run
theorems prove that neither fallback is taken, and the final theorem relates
the expression returned by that exact execution to Lean4Lean's canonical
mixed recursor type.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open GeneratedRecursorSemantics
open IndexedRecursiveCertificateFixture
open Lean4Lean.InductiveReplayFixtures

local instance generatedTypeKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance generatedTypeKExprDecidableEq : DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

/-- Unreachable totalization used to project data out of the preparation
outcome before its successful branch has been proved. -/
private def emptyBuildInputs : RecM.GeneratedRecursorBuildInputs .anon where
  flatIndInfos := #[]
  flatIds := #[]
  flat := #[]
  motiveTypes := #[]
  univOffset := 0
  recLvls := 0
  nParams := 0
  nMinors := 0
  blockIsUnsafe := false
  isLarge := false

/-- Exact production preparation run for the checked indexed family. -/
def familyPreparationOutcome :=
  (RecM.prepareGeneratedRecursorBuildInputs familyBlockId).run checkerMethods
    familyKernelAfter

def familyBuildInputs : RecM.GeneratedRecursorBuildInputs .anon :=
  match familyPreparationOutcome with
  | .ok (some inputs) _ => inputs
  | _ => emptyBuildInputs

def familyPreparationAfter : TcState .anon :=
  match familyPreparationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyPreparationSucceeded : Bool :=
  match familyPreparationOutcome with
  | .ok (some _) _ => true
  | _ => false

private theorem familyPreparationSucceededNative :
    familyPreparationSucceeded = true := by
  native_decide

theorem familyPreparationSucceeded_eq :
    familyPreparationSucceeded = true :=
  familyPreparationSucceededNative

/-- Preparation takes its data-bearing success branch, so every subsequent
projection denotes the values selected by production. -/
theorem familyPreparationRun :
    (RecM.prepareGeneratedRecursorBuildInputs familyBlockId).run
        checkerMethods familyKernelAfter =
      .ok (some familyBuildInputs) familyPreparationAfter := by
  have success := familyPreparationSucceeded_eq
  unfold familyPreparationSucceeded at success
  unfold familyBuildInputs familyPreparationAfter
  generalize houtcome : familyPreparationOutcome = outcome at success ⊢
  cases outcome with
  | error error failed =>
      simp_all [familyPreparationOutcome]
  | ok result after =>
      cases result <;> simp_all [familyPreparationOutcome]

private theorem familyFlatSizeNative : familyBuildInputs.flat.size = 1 := by
  native_decide

theorem familyFlatSize : familyBuildInputs.flat.size = 1 :=
  familyFlatSizeNative

private theorem familyFlatIdsNative :
    familyBuildInputs.flatIds = #[familyId] := by
  native_decide

theorem familyFlatIds : familyBuildInputs.flatIds = #[familyId] :=
  familyFlatIdsNative

/-! ## Actual recursor-type construction -/

def familyBuildTypeOutcome :=
  (RecM.buildRecType 0 familyBuildInputs.flatIndInfos
      familyBuildInputs.flatIds familyBuildInputs.flat
      familyBuildInputs.motiveTypes familyBuildInputs.univOffset).run
    checkerMethods familyPreparationAfter

def familyBuildTypeResult : KExpr .anon :=
  match familyBuildTypeOutcome with
  | .ok result _ => result
  | .error _ _ => .mkSort .mkZero

def familyBuildTypeAfter : TcState .anon :=
  match familyBuildTypeOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyBuildTypeSucceeded : Bool :=
  match familyBuildTypeOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyBuildTypeSucceededNative :
    familyBuildTypeSucceeded = true := by
  native_decide

theorem familyBuildTypeSucceeded_eq : familyBuildTypeSucceeded = true :=
  familyBuildTypeSucceededNative

/-- The real builder succeeds and returns the projected concrete result. -/
theorem familyBuildTypeRun :
    (RecM.buildRecType 0 familyBuildInputs.flatIndInfos
        familyBuildInputs.flatIds familyBuildInputs.flat
        familyBuildInputs.motiveTypes familyBuildInputs.univOffset).run
      checkerMethods familyPreparationAfter =
        .ok familyBuildTypeResult familyBuildTypeAfter := by
  have success := familyBuildTypeSucceeded_eq
  unfold familyBuildTypeSucceeded at success
  unfold familyBuildTypeResult familyBuildTypeAfter
  generalize houtcome : familyBuildTypeOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyBuildTypeOutcome]

/-- The production result is exactly the independently ingressed canonical
recursor type, including every forall binder and de Bruijn index. -/
private theorem familyBuildTypeResultNative :
    familyBuildTypeResult = recursorConcrete.ty := by
  native_decide

theorem familyBuildTypeResult_eq :
    familyBuildTypeResult = recursorConcrete.ty :=
  familyBuildTypeResultNative

/-- Header obtained from the actual type result and the exact metadata chosen
by production preparation. -/
def familyBuiltRecursor : GeneratedRecursor .anon :=
  RecM.initialGeneratedRecursor familyBuildInputs.flat[0]!
    familyBuildInputs.flat familyBuildInputs.recLvls familyBuildInputs.nParams
    familyBuildInputs.nMinors familyBuildInputs.blockIsUnsafe
    familyBuildTypeResult

/-- The type produced by the concrete `buildRecType` execution is the exact
structural translation of Lean4Lean's canonical `IndexedVec` recursor type. -/
theorem familyBuildTypeCanonical :
    CanonicalTypeS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyBuiltRecursor := by
  unfold CanonicalTypeS familyBuiltRecursor
  change TrKExprS indexedVecFinalEnv
    transaction.certificate.generation.recursor.uvars nameOf RawProjRel.none
    [] familyBuildTypeResult transaction.certificate.generation.recType
  rw [familyBuildTypeResult_eq]
  simpa [Lean4Lean.VInductDecl.GenerationChecked.recursor] using
    recursorTypeTyped

/-- One data-bearing theorem packages the production execution and its exact
semantic postcondition. -/
theorem familyBuildTypeExecution :
    (RecM.prepareGeneratedRecursorBuildInputs familyBlockId).run
        checkerMethods familyKernelAfter =
      .ok (some familyBuildInputs) familyPreparationAfter ∧
    (RecM.buildRecType 0 familyBuildInputs.flatIndInfos
          familyBuildInputs.flatIds familyBuildInputs.flat
          familyBuildInputs.motiveTypes familyBuildInputs.univOffset).run
        checkerMethods familyPreparationAfter =
      .ok familyBuiltRecursor.ty familyBuildTypeAfter ∧
    CanonicalTypeS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyBuiltRecursor := by
  refine ⟨familyPreparationRun, ?_, familyBuildTypeCanonical⟩
  simpa [familyBuiltRecursor, RecM.initialGeneratedRecursor] using
    familyBuildTypeRun

end Ix.Tc.IndexedRecursiveFixture
