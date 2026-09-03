import Ix.Tc.Verify.Inductive.IndexedPositivityTransport

/-!
# IndexedVec constructor-validation trace

This module places the three production-derived positivity artifacts back into
Lean4Lean's complete retained constructor telescope.  The resulting trace
records the shared parameter check, all ordinary field type/universe checks,
the transported positivity evidence, and the terminal indexed-family
application.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean.InductiveReplayFixtures
open Lean4Lean.InductiveReplayFixtures.IndexedVecConsReplay

private abbrev ConsValidationTrace
    (context : Lean4Lean.AddInductive.Context) (source : Lean.Expr)
    (argIdx fuel : Nat) :=
  Lean4Lean.AddInductive.ConstructorTypeValidationTrace
    indexedVecConstructorStats false 0 indexedVecKernelCons.name
      context source argIdx fuel

/-! ## Exact proof-independent constructor observations -/

private theorem indexedVecConstructorGetTypeAlphaNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.AddInductive.getType indexedVecConstructorAlpha
        indexedVecConstructorContext)
      (.sort (.succ (.param `u))) = true := by
  native_decide

private theorem indexedVecConstructorGetTypeAlpha :
    Lean4Lean.AddInductive.getType indexedVecConstructorAlpha
        indexedVecConstructorContext =
      .ok (.sort (.succ (.param `u))) :=
  ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorGetTypeAlphaNative

private theorem indexedVecConstructorParamIsDefEqNative :
    ExactLeanSyntax.exceptBoolCheck
      (Lean4Lean.TypeChecker.M.run indexedVecConstructorContext.env
        indexedVecConstructorContext.safety
        indexedVecConstructorContext.lctx
        indexedVecConstructorContext.lparams
        indexedVecConstructorContext.fuel
        (Lean4Lean.TypeChecker.isDefEq
          (.sort (.succ (.param `u)))
          (.sort (.succ (.param `u))))) true = true := by
  native_decide

private theorem indexedVecConstructorParamIsDefEq :
    Lean4Lean.AddInductive.CandidateIsDefEqStep.Valid
      ⟨indexedVecConstructorContext,
        .sort (.succ (.param `u)), .sort (.succ (.param `u))⟩ := by
  unfold Lean4Lean.AddInductive.CandidateIsDefEqStep.Valid
  exact ExactLeanSyntax.exceptBool_eq_ok_of_check
    indexedVecConstructorParamIsDefEqNative

private theorem indexedVecConstructorNatEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run indexedVecConstructorContext.env
        indexedVecConstructorContext.safety
        indexedVecConstructorContext.lctx
        indexedVecConstructorContext.lparams
        indexedVecConstructorContext.fuel
        (Lean4Lean.TypeChecker.ensureType (.const ``Nat [])))
      (.sort (.succ .zero)) = true := by
  native_decide

private theorem indexedVecConstructorNatEnsureType :
    Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨indexedVecConstructorContext, .const ``Nat [],
        .sort (.succ .zero)⟩ := by
  unfold Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorNatEnsureTypeNative

private theorem indexedVecConstructorAlphaEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run indexedVecConstructorNContext.env
        indexedVecConstructorNContext.safety
        indexedVecConstructorNContext.lctx
        indexedVecConstructorNContext.lparams
        indexedVecConstructorNContext.fuel
        (Lean4Lean.TypeChecker.ensureType indexedVecConstructorAlpha))
      (.sort (.succ (.param `u))) = true := by
  native_decide

private theorem indexedVecConstructorAlphaEnsureType :
    Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨indexedVecConstructorNContext, indexedVecConstructorAlpha,
        .sort (.succ (.param `u))⟩ := by
  unfold Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorAlphaEnsureTypeNative

private theorem indexedVecConstructorTailEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run indexedVecConstructorHeadContext.env
        indexedVecConstructorHeadContext.safety
        indexedVecConstructorHeadContext.lctx
        indexedVecConstructorHeadContext.lparams
        indexedVecConstructorHeadContext.fuel
        (Lean4Lean.TypeChecker.ensureType
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)))
      (.sort (.succ (.param `u))) = true := by
  native_decide

private theorem indexedVecConstructorTailEnsureType :
    Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨indexedVecConstructorHeadContext,
        ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr,
        .sort (.succ (.param `u))⟩ := by
  unfold Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorTailEnsureTypeNative

private theorem indexedVecConstructorResultIsValidNative :
    Lean4Lean.AddInductive.isValidIndAppIdx indexedVecConstructorStats
      indexedVecConstructorResult 0 = true := by
  native_decide

private theorem indexedVecConstructorConsumeNatNative :
    ExactLeanSyntax.exprCheck
      (Lean4Lean.AddInductive.consumeTypeAnnotations (.const ``Nat []))
      (.const ``Nat []) = true := by
  native_decide

private theorem indexedVecConstructorConsumeNat :
    Lean4Lean.AddInductive.consumeTypeAnnotations (.const ``Nat []) =
      .const ``Nat [] :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorConsumeNatNative

private theorem indexedVecConstructorConsumeAlphaNative :
    ExactLeanSyntax.exprCheck
      (Lean4Lean.AddInductive.consumeTypeAnnotations
        indexedVecConstructorAlpha)
      indexedVecConstructorAlpha = true := by
  native_decide

private theorem indexedVecConstructorConsumeAlpha :
    Lean4Lean.AddInductive.consumeTypeAnnotations
        indexedVecConstructorAlpha = indexedVecConstructorAlpha :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorConsumeAlphaNative

private theorem indexedVecConstructorConsumeTailNative :
    ExactLeanSyntax.exprCheck
      (Lean4Lean.AddInductive.consumeTypeAnnotations
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr))
      (ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr) = true := by
  native_decide

private theorem indexedVecConstructorConsumeTail :
    Lean4Lean.AddInductive.consumeTypeAnnotations
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) =
      ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorConsumeTailNative

private theorem indexedVecConstructorTypeShapeNative :
    ExactLeanSyntax.exprCheck indexedVecKernelCons.type consCtorTypeRaw =
      true := by
  native_decide

private theorem indexedVecConstructorTypeShape :
    indexedVecKernelCons.type = consCtorTypeRaw :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorTypeShapeNative

private theorem indexedVecConstructorAfterParamShapeNative :
    ExactLeanSyntax.exprCheck indexedVecConstructorAfterParam
      (.forallE consNName (.const ``Nat [])
        (.forallE consHeadName indexedVecConstructorAlpha
          (.forallE consTailName
            (ctorIndexedVecApp indexedVecConstructorAlpha (.bvar 1))
            (ctorIndexedVecApp indexedVecConstructorAlpha
              (replaySuccApp (.bvar 2)))
            .default)
          .default)
        .implicit) = true := by
  native_decide

private theorem indexedVecConstructorAfterParamShape :
    indexedVecConstructorAfterParam =
      .forallE consNName (.const ``Nat [])
        (.forallE consHeadName indexedVecConstructorAlpha
          (.forallE consTailName
            (ctorIndexedVecApp indexedVecConstructorAlpha (.bvar 1))
            (ctorIndexedVecApp indexedVecConstructorAlpha
              (replaySuccApp (.bvar 2)))
            .default)
          .default)
        .implicit :=
  ExactLeanSyntax.expr_eq_of_check
    indexedVecConstructorAfterParamShapeNative

private theorem indexedVecConstructorInstantiateNNative :
    ExactLeanSyntax.exprCheck
      ((.forallE consHeadName indexedVecConstructorAlpha
        (.forallE consTailName
          (ctorIndexedVecApp indexedVecConstructorAlpha (.bvar 1))
          (ctorIndexedVecApp indexedVecConstructorAlpha
            (replaySuccApp (.bvar 2)))
          .default)
        .default : Lean.Expr).instantiate1
          indexedVecConstructorContext.freshExpr)
      indexedVecConstructorAfterN = true := by
  native_decide

private theorem indexedVecConstructorInstantiateN :
    ((.forallE consHeadName indexedVecConstructorAlpha
      (.forallE consTailName
        (ctorIndexedVecApp indexedVecConstructorAlpha (.bvar 1))
        (ctorIndexedVecApp indexedVecConstructorAlpha
          (replaySuccApp (.bvar 2)))
        .default)
      .default : Lean.Expr).instantiate1
        indexedVecConstructorContext.freshExpr) =
      indexedVecConstructorAfterN :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorInstantiateNNative

private theorem indexedVecConstructorInstantiateHeadNative :
    ExactLeanSyntax.exprCheck
      ((.forallE consTailName
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr)
        (ctorIndexedVecApp indexedVecConstructorAlpha
          (replaySuccApp indexedVecConstructorNExpr))
        .default : Lean.Expr).instantiate1
          indexedVecConstructorNContext.freshExpr)
      indexedVecConstructorAfterHead = true := by
  native_decide

private theorem indexedVecConstructorInstantiateHead :
    ((.forallE consTailName
      (ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr)
      (ctorIndexedVecApp indexedVecConstructorAlpha
        (replaySuccApp indexedVecConstructorNExpr))
      .default : Lean.Expr).instantiate1
        indexedVecConstructorNContext.freshExpr) =
      indexedVecConstructorAfterHead :=
  ExactLeanSyntax.expr_eq_of_check
    indexedVecConstructorInstantiateHeadNative

private theorem indexedVecConstructorInstantiateTailNative :
    ExactLeanSyntax.exprCheck
      ((ctorIndexedVecApp indexedVecConstructorAlpha
        (replaySuccApp indexedVecConstructorNExpr)).instantiate1
          indexedVecConstructorHeadContext.freshExpr)
      indexedVecConstructorResult = true := by
  native_decide

private theorem indexedVecConstructorInstantiateTail :
    (ctorIndexedVecApp indexedVecConstructorAlpha
      (replaySuccApp indexedVecConstructorNExpr)).instantiate1
        indexedVecConstructorHeadContext.freshExpr =
      indexedVecConstructorResult :=
  ExactLeanSyntax.expr_eq_of_check
    indexedVecConstructorInstantiateTailNative

private theorem indexedVecConstructorNatUniverse :
    Lean4Lean.AddInductive.levelStructGe
      indexedVecConstructorStats.resultLevel (.succ .zero) = true := by
  native_decide

private theorem indexedVecConstructorParamUniverse :
    Lean4Lean.AddInductive.levelStructGe
      indexedVecConstructorStats.resultLevel (.succ (.param `u)) = true := by
  native_decide

/-- Complete retained validation of the real `IndexedVec.cons` candidate.

Unlike applying `ConstructorTypeValidationTrace.exists_of_run` to the
already-known Lean4Lean replay, this construction explicitly installs the
three traces transported from the production Ix positivity calls. -/
theorem indexedVecConsConstructorTypeValidationTrace :
    Nonempty (ConsValidationTrace indexedVecConstructorContext
      indexedVecKernelCons.type 0
        indexedVecConstructorContext.fuel.inductiveFuel) := by
  obtain ⟨natPositivity⟩ :=
    indexedVecProductionNatConstructorPositivityTraceAt 999
  obtain ⟨headPositivity⟩ :=
    indexedVecProductionHeadConstructorPositivityTraceAt 999
  obtain ⟨tailPositivity⟩ :=
    indexedVecProductionTailConstructorPositivityTraceAt 999

  have terminalTrace :
      ConsValidationTrace indexedVecConstructorTailContext
        indexedVecConstructorResult 4 996 := by
    exact .terminal indexedVecConstructorTailContext
      indexedVecConstructorResult 995 4 rfl
        indexedVecConstructorResultIsValidNative

  have tailTrace :
      ConsValidationTrace indexedVecConstructorHeadContext
        indexedVecConstructorAfterHead 3 997 := by
    unfold indexedVecConstructorAfterHead
    refine .ordinary
      (context := indexedVecConstructorHeadContext)
      (fuel := 996) (argIdx := 3)
      (name := consTailName)
      (domain := ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr)
      (body := ctorIndexedVecApp indexedVecConstructorAlpha
        (replaySuccApp indexedVecConstructorNExpr))
      (binderInfo := .default)
      (sortResult := .sort (.succ (.param `u)))
      (noParameter := by rfl)
      (ensureType := indexedVecConstructorTailEnsureType)
      (universeTrace := .structural
        indexedVecConstructorParamUniverse)
      (positivity := .safe rfl tailPositivity)
      (tail := ?_)
    rw [indexedVecConstructorConsumeTail]
    rw [indexedVecConstructorInstantiateTail]
    exact terminalTrace

  have headTrace :
      ConsValidationTrace indexedVecConstructorNContext
        indexedVecConstructorAfterN 2 998 := by
    unfold indexedVecConstructorAfterN
    refine .ordinary
      (context := indexedVecConstructorNContext)
      (fuel := 997) (argIdx := 2)
      (name := consHeadName)
      (domain := indexedVecConstructorAlpha)
      (body := .forallE consTailName
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr)
        (ctorIndexedVecApp indexedVecConstructorAlpha
          (replaySuccApp indexedVecConstructorNExpr)) .default)
      (binderInfo := .default)
      (sortResult := .sort (.succ (.param `u)))
      (noParameter := by rfl)
      (ensureType := indexedVecConstructorAlphaEnsureType)
      (universeTrace := .structural
        indexedVecConstructorParamUniverse)
      (positivity := .safe rfl headPositivity)
      (tail := ?_)
    rw [indexedVecConstructorConsumeAlpha]
    rw [indexedVecConstructorInstantiateHead]
    exact tailTrace

  have natTrace :
      ConsValidationTrace indexedVecConstructorContext
        indexedVecConstructorAfterParam 1 999 := by
    rw [indexedVecConstructorAfterParamShape]
    refine .ordinary
      (context := indexedVecConstructorContext)
      (fuel := 998) (argIdx := 1)
      (name := consNName) (domain := .const ``Nat [])
      (body := .forallE consHeadName indexedVecConstructorAlpha
        (.forallE consTailName
          (ctorIndexedVecApp indexedVecConstructorAlpha (.bvar 1))
          (ctorIndexedVecApp indexedVecConstructorAlpha
            (replaySuccApp (.bvar 2))) .default) .default)
      (binderInfo := .implicit)
      (sortResult := .sort (.succ .zero))
      (noParameter := by rfl)
      (ensureType := indexedVecConstructorNatEnsureType)
      (universeTrace := .structural indexedVecConstructorNatUniverse)
      (positivity := .safe rfl natPositivity)
      (tail := ?_)
    rw [indexedVecConstructorConsumeNat]
    rw [indexedVecConstructorInstantiateN]
    exact headTrace

  rw [indexedVecConstructorTypeShape]
  unfold consCtorTypeRaw
  refine ⟨.parameter
    (context := indexedVecConstructorContext)
    (fuel := 999) (argIdx := 0)
    (name := consAlphaName)
    (domain := .sort (.succ (.param `u)))
    (body := consNTypeRaw) (binderInfo := .implicit)
    (param := indexedVecConstructorAlpha)
    (parameterType := .sort (.succ (.param `u)))
    (parameterAt := by rfl)
    (parameterTypeRun := indexedVecConstructorGetTypeAlpha)
    (defeq := indexedVecConstructorParamIsDefEq)
    (tail := ?_)⟩
  simpa only [indexedVecConstructorAfterParam] using natTrace

/-- The assembled retained trace replays the pinned public constructor
validator, so the vertical slice reaches the complete method rather than only
its positivity helper. -/
theorem indexedVecConsConstructorValidationRun :
    Lean4Lean.AddInductive.checkConstructorType
      indexedVecConstructorStats false 0 indexedVecKernelCons.name
        indexedVecKernelCons.type indexedVecConstructorContext = .ok () := by
  obtain ⟨trace⟩ := indexedVecConsConstructorTypeValidationTrace
  exact trace.check_run

end Ix.Tc.IndexedRecursiveFixture
