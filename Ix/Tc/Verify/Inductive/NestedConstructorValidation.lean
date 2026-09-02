import Ix.Tc.Verify.Inductive.NestedAuxiliaryPositivity

/-!
# Constructor validation for the flattened nested fixture

This module places both production-derived positivity traces into
Lean4Lean's exact constructor validator.  The outer `Tree.node` field uses the
nested-production transport, while the generated `Box.wrap` field uses the
retained copied-constructor traversal.  Both are checked in the same
two-family environment produced by the real nested eliminator.
-/

namespace Ix.Tc.NestedRecursiveFixture

private abbrev NodeValidationTrace
    (context : Lean4Lean.AddInductive.Context) (source : Lean.Expr)
    (argIdx fuel : Nat) :=
  Lean4Lean.AddInductive.ConstructorTypeValidationTrace leanFlatStats false
    0 leanFlatNode.name context source argIdx fuel

private abbrev WrapValidationTrace
    (context : Lean4Lean.AddInductive.Context) (source : Lean.Expr)
    (argIdx fuel : Nat) :=
  Lean4Lean.AddInductive.ConstructorTypeValidationTrace leanFlatStats false
    1 leanFlatWrap.name context source argIdx fuel

def leanFlatNodeFieldContext : Lean4Lean.AddInductive.Context :=
  leanFlatConstructorContext.pushLocalDecl `value .default leanAuxiliaryExpr

def leanFlatWrapFieldContext : Lean4Lean.AddInductive.Context :=
  leanFlatConstructorContext.pushLocalDecl leanFlatWrapBinderName .default
    leanTreeExpr

/-! ## Exact constructor-checker operations -/

private theorem leanAuxiliaryEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run leanFlatConstructorContext.env
        leanFlatConstructorContext.safety leanFlatConstructorContext.lctx
        leanFlatConstructorContext.lparams leanFlatConstructorContext.fuel
        (Lean4Lean.TypeChecker.ensureType leanAuxiliaryExpr))
      (.sort (.succ .zero)) = true := by
  native_decide

private theorem leanAuxiliaryEnsureType :
    Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨leanFlatConstructorContext, leanAuxiliaryExpr,
        .sort (.succ .zero)⟩ := by
  unfold Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    leanAuxiliaryEnsureTypeNative

private theorem leanTreeEnsureTypeNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run leanFlatConstructorContext.env
        leanFlatConstructorContext.safety leanFlatConstructorContext.lctx
        leanFlatConstructorContext.lparams leanFlatConstructorContext.fuel
        (Lean4Lean.TypeChecker.ensureType leanTreeExpr))
      (.sort (.succ .zero)) = true := by
  native_decide

private theorem leanTreeEnsureType :
    Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨leanFlatConstructorContext, leanTreeExpr,
        .sort (.succ .zero)⟩ := by
  unfold Lean4Lean.AddInductive.ConstructorEnsureTypeStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check leanTreeEnsureTypeNative

private theorem leanFlatFieldUniverse :
    Lean4Lean.AddInductive.levelStructGe leanFlatStats.resultLevel
      (.succ .zero) = true := by
  native_decide

private theorem leanTreeTerminalNative :
    Lean4Lean.AddInductive.isValidIndAppIdx leanFlatStats leanTreeExpr 0 =
      true := by
  native_decide

private theorem leanAuxiliaryTerminalNative :
    Lean4Lean.AddInductive.isValidIndAppIdx leanFlatStats
      leanAuxiliaryExpr 1 = true := by
  native_decide

private theorem consumeLeanAuxiliaryNative :
    ExactLeanSyntax.exprCheck
      (Lean4Lean.AddInductive.consumeTypeAnnotations leanAuxiliaryExpr)
      leanAuxiliaryExpr = true := by
  native_decide

private theorem consumeLeanAuxiliary :
    Lean4Lean.AddInductive.consumeTypeAnnotations leanAuxiliaryExpr =
      leanAuxiliaryExpr :=
  ExactLeanSyntax.expr_eq_of_check consumeLeanAuxiliaryNative

private theorem consumeLeanTreeNative :
    ExactLeanSyntax.exprCheck
      (Lean4Lean.AddInductive.consumeTypeAnnotations leanTreeExpr)
      leanTreeExpr = true := by
  native_decide

private theorem consumeLeanTree :
    Lean4Lean.AddInductive.consumeTypeAnnotations leanTreeExpr =
      leanTreeExpr :=
  ExactLeanSyntax.expr_eq_of_check consumeLeanTreeNative

private theorem instantiateLeanTreeNative :
    ExactLeanSyntax.exprCheck
      (leanTreeExpr.instantiate1 leanFlatConstructorContext.freshExpr)
      leanTreeExpr = true := by
  native_decide

private theorem instantiateLeanTree :
    leanTreeExpr.instantiate1 leanFlatConstructorContext.freshExpr =
      leanTreeExpr :=
  ExactLeanSyntax.expr_eq_of_check instantiateLeanTreeNative

private theorem instantiateLeanAuxiliaryNative :
    ExactLeanSyntax.exprCheck
      (leanAuxiliaryExpr.instantiate1 leanFlatConstructorContext.freshExpr)
      leanAuxiliaryExpr = true := by
  native_decide

private theorem instantiateLeanAuxiliary :
    leanAuxiliaryExpr.instantiate1 leanFlatConstructorContext.freshExpr =
      leanAuxiliaryExpr :=
  ExactLeanSyntax.expr_eq_of_check instantiateLeanAuxiliaryNative

private theorem leanFlatInductiveFuel :
    leanFlatConstructorContext.fuel.inductiveFuel = positivityFuel := by
  rfl

/-! ## Outer constructor -/

/-- Complete validation trace for the rewritten outer constructor.  Its
positivity member is the trace transported from Ix's actual nested
`Box Tree` traversal. -/
theorem leanFlatNodeConstructorTypeValidationTrace :
    Nonempty (NodeValidationTrace leanFlatConstructorContext leanFlatNode.type
      0 leanFlatConstructorContext.fuel.inductiveFuel) := by
  change Nonempty (NodeValidationTrace leanFlatConstructorContext
    leanFlatNode.type 0 positivityFuel)
  obtain ⟨positivity⟩ := nestedOuterConstructorPositivityTrace
  have terminalTrace :
      NodeValidationTrace leanFlatNodeFieldContext leanTreeExpr 1
        (positivityFuel - 1) := by
    exact .terminal leanFlatNodeFieldContext leanTreeExpr
      (positivityFuel - 2) 1 rfl leanTreeTerminalNative
  rw [leanFlatNodeType]
  refine ⟨.ordinary
    (context := leanFlatConstructorContext)
    (fuel := positivityFuel - 1) (argIdx := 0)
    (name := `value) (domain := leanAuxiliaryExpr)
    (body := leanTreeExpr) (binderInfo := .default)
    (sortResult := .sort (.succ .zero))
    (noParameter := by rfl)
    (ensureType := leanAuxiliaryEnsureType)
    (universeTrace := .structural leanFlatFieldUniverse)
    (positivity := .safe rfl positivity)
    (tail := ?_)⟩
  rw [consumeLeanAuxiliary, instantiateLeanTree]
  simpa [leanFlatNodeFieldContext, positivityFuel] using terminalTrace

/-- The assembled outer trace replays Lean4Lean's public constructor
validator. -/
theorem leanFlatNodeConstructorValidationRun :
    Lean4Lean.AddInductive.checkConstructorType leanFlatStats false 0
      leanFlatNode.name leanFlatNode.type leanFlatConstructorContext =
        .ok () := by
  obtain ⟨trace⟩ := leanFlatNodeConstructorTypeValidationTrace
  exact trace.check_run

/-! ## Generated auxiliary constructor -/

/-- Complete validation trace for the copied and specialized `Box.wrap`
constructor.  Its positivity member is extracted from the copied-constructor
field execution nested inside Ix's outer positivity run. -/
theorem leanFlatWrapConstructorTypeValidationTrace :
    Nonempty (WrapValidationTrace leanFlatConstructorContext leanFlatWrap.type
      0 leanFlatConstructorContext.fuel.inductiveFuel) := by
  change Nonempty (WrapValidationTrace leanFlatConstructorContext
    leanFlatWrap.type 0 positivityFuel)
  obtain ⟨positivity⟩ :=
    nestedAuxiliaryConstructorPositivityTraceAt (positivityFuel - 1)
  have terminalTrace :
      WrapValidationTrace leanFlatWrapFieldContext leanAuxiliaryExpr 1
        (positivityFuel - 1) := by
    exact .terminal leanFlatWrapFieldContext leanAuxiliaryExpr
      (positivityFuel - 2) 1 rfl leanAuxiliaryTerminalNative
  rw [leanFlatWrapType]
  refine ⟨.ordinary
    (context := leanFlatConstructorContext)
    (fuel := positivityFuel - 1) (argIdx := 0)
    (name := leanFlatWrapBinderName) (domain := leanTreeExpr)
    (body := leanAuxiliaryExpr) (binderInfo := .default)
    (sortResult := .sort (.succ .zero))
    (noParameter := by rfl)
    (ensureType := leanTreeEnsureType)
    (universeTrace := .structural leanFlatFieldUniverse)
    (positivity := .safe rfl (by
      rw [leanFlatInductiveFuel]
      simpa [positivityFuel] using positivity))
    (tail := ?_)⟩
  rw [consumeLeanTree, instantiateLeanAuxiliary]
  simpa [leanFlatWrapFieldContext, positivityFuel] using terminalTrace

/-- The generated auxiliary also passes the public constructor validator from
the production-derived positivity evidence. -/
theorem leanFlatWrapConstructorValidationRun :
    Lean4Lean.AddInductive.checkConstructorType leanFlatStats false 1
      leanFlatWrap.name leanFlatWrap.type leanFlatConstructorContext =
        .ok () := by
  obtain ⟨trace⟩ := leanFlatWrapConstructorTypeValidationTrace
  exact trace.check_run

end Ix.Tc.NestedRecursiveFixture
