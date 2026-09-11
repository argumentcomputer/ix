import Ix.Kernel.Verify.Inductive.IndexedPositivityTransport

/-!
# IndexedVec constructor-validation trace

This module places the three production-derived positivity artifacts back into
Ix.Theory.Named's complete retained constructor telescope.  The resulting trace
records the shared parameter check, all ordinary field type/universe checks,
the transported positivity evidence, and the terminal indexed-family
application.
-/

namespace Ix.Kernel.IndexedRecursiveFixture

open Ix.Theory.Named.InductiveReplayFixtures
open Ix.Theory.Named.InductiveReplayFixtures.IndexedVecConsReplay

private abbrev ConsValidationTrace
    (context : Ix.Theory.Named.AddInductive.Context) (source : Lean.Expr)
    (argIdx fuel : Nat) :=
  Ix.Theory.Named.AddInductive.ConstructorTypeValidationTrace
    indexedVecConstructorStats false 0 indexedVecKernelCons.name
      context source argIdx fuel

/-! ## Exact proof-independent constructor observations -/

private theorem indexedVecConstructorGetTypeAlphaNative :
    ExactLeanSyntax.exceptExprCheck
      (Ix.Theory.Named.AddInductive.getType indexedVecConstructorAlpha
        indexedVecConstructorContext)
      (.sort (.succ (.param `u))) = true := by
  native_decide

private theorem indexedVecConstructorGetTypeAlpha :
    Ix.Theory.Named.AddInductive.getType indexedVecConstructorAlpha
        indexedVecConstructorContext =
      .ok (.sort (.succ (.param `u))) :=
  ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorGetTypeAlphaNative

private theorem indexedVecConstructorParamIsDefEqNative :
    ExactLeanSyntax.exceptBoolCheck
      (Ix.Theory.Named.TypeChecker.M.run indexedVecConstructorContext.env
        indexedVecConstructorContext.safety
        indexedVecConstructorContext.lctx
        indexedVecConstructorContext.lparams
        indexedVecConstructorContext.fuel
        (Ix.Theory.Named.TypeChecker.isDefEq
          (.sort (.succ (.param `u)))
          (.sort (.succ (.param `u))))) true = true := by
  native_decide

private theorem indexedVecConstructorParamIsDefEq :
    Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.Valid
      ⟨indexedVecConstructorContext,
        .sort (.succ (.param `u)), .sort (.succ (.param `u))⟩ := by
  unfold Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.Valid
  exact ExactLeanSyntax.exceptBool_eq_ok_of_check
    indexedVecConstructorParamIsDefEqNative

private theorem indexedVecConstructorNatEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Ix.Theory.Named.TypeChecker.M.run indexedVecConstructorContext.env
        indexedVecConstructorContext.safety
        indexedVecConstructorContext.lctx
        indexedVecConstructorContext.lparams
        indexedVecConstructorContext.fuel
        (Ix.Theory.Named.TypeChecker.ensureType (.const ``Nat [])))
      (.sort (.succ .zero)) = true := by
  native_decide

private theorem indexedVecConstructorNatEnsureType :
    Ix.Theory.Named.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨indexedVecConstructorContext, .const ``Nat [],
        .sort (.succ .zero)⟩ := by
  unfold Ix.Theory.Named.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorNatEnsureTypeNative

private theorem indexedVecConstructorAlphaEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Ix.Theory.Named.TypeChecker.M.run indexedVecConstructorNContext.env
        indexedVecConstructorNContext.safety
        indexedVecConstructorNContext.lctx
        indexedVecConstructorNContext.lparams
        indexedVecConstructorNContext.fuel
        (Ix.Theory.Named.TypeChecker.ensureType indexedVecConstructorAlpha))
      (.sort (.succ (.param `u))) = true := by
  native_decide

private theorem indexedVecConstructorAlphaEnsureType :
    Ix.Theory.Named.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨indexedVecConstructorNContext, indexedVecConstructorAlpha,
        .sort (.succ (.param `u))⟩ := by
  unfold Ix.Theory.Named.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorAlphaEnsureTypeNative

private theorem indexedVecConstructorTailEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Ix.Theory.Named.TypeChecker.M.run indexedVecConstructorHeadContext.env
        indexedVecConstructorHeadContext.safety
        indexedVecConstructorHeadContext.lctx
        indexedVecConstructorHeadContext.lparams
        indexedVecConstructorHeadContext.fuel
        (Ix.Theory.Named.TypeChecker.ensureType
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)))
      (.sort (.succ (.param `u))) = true := by
  native_decide

private theorem indexedVecConstructorTailEnsureType :
    Ix.Theory.Named.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨indexedVecConstructorHeadContext,
        ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr,
        .sort (.succ (.param `u))⟩ := by
  unfold Ix.Theory.Named.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecConstructorTailEnsureTypeNative

private theorem indexedVecConstructorResultIsValidNative :
    Ix.Theory.Named.AddInductive.isValidIndAppIdx indexedVecConstructorStats
      indexedVecConstructorResult 0 = true := by
  native_decide

private theorem indexedVecConstructorConsumeNatNative :
    ExactLeanSyntax.exprCheck
      (Ix.Theory.Named.AddInductive.consumeTypeAnnotations (.const ``Nat []))
      (.const ``Nat []) = true := by
  native_decide

private theorem indexedVecConstructorConsumeNat :
    Ix.Theory.Named.AddInductive.consumeTypeAnnotations (.const ``Nat []) =
      .const ``Nat [] :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorConsumeNatNative

private theorem indexedVecConstructorConsumeAlphaNative :
    ExactLeanSyntax.exprCheck
      (Ix.Theory.Named.AddInductive.consumeTypeAnnotations
        indexedVecConstructorAlpha)
      indexedVecConstructorAlpha = true := by
  native_decide

private theorem indexedVecConstructorConsumeAlpha :
    Ix.Theory.Named.AddInductive.consumeTypeAnnotations
        indexedVecConstructorAlpha = indexedVecConstructorAlpha :=
  ExactLeanSyntax.expr_eq_of_check indexedVecConstructorConsumeAlphaNative

private theorem indexedVecConstructorConsumeTailNative :
    ExactLeanSyntax.exprCheck
      (Ix.Theory.Named.AddInductive.consumeTypeAnnotations
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr))
      (ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr) = true := by
  native_decide

private theorem indexedVecConstructorConsumeTail :
    Ix.Theory.Named.AddInductive.consumeTypeAnnotations
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
    Ix.Theory.Named.AddInductive.levelStructGe
      indexedVecConstructorStats.resultLevel (.succ .zero) = true := by
  native_decide

private theorem indexedVecConstructorParamUniverse :
    Ix.Theory.Named.AddInductive.levelStructGe
      indexedVecConstructorStats.resultLevel (.succ (.param `u)) = true := by
  native_decide

/-- Complete retained validation of the real `IndexedVec.cons` candidate.

Unlike applying `ConstructorTypeValidationTrace.exists_of_run` to the
already-known Ix.Theory.Named replay, this construction explicitly installs the
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
    Ix.Theory.Named.AddInductive.checkConstructorType
      indexedVecConstructorStats false 0 indexedVecKernelCons.name
        indexedVecKernelCons.type indexedVecConstructorContext = .ok () := by
  obtain ⟨trace⟩ := indexedVecConsConstructorTypeValidationTrace
  exact trace.check_run

end Ix.Kernel.IndexedRecursiveFixture
