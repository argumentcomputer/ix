/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.EliminationFixturesCommon

/-! Exact Spec-06B source-universe small-elimination differential fixture. -/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

def smallSourceInfo06 : ConstantInfo := kernelInductInfo% Spec06SmallSource
def smallSourceLeftInfo06 : ConstantInfo :=
  kernelCtorInfo% Spec06SmallSource.left
def smallSourceRightInfo06 : ConstantInfo :=
  kernelCtorInfo% Spec06SmallSource.right
def smallSourceRecInfo06 : ConstantInfo :=
  kernelRecInfo% Spec06SmallSource.rec
def smallSourceLeftRuleRhs06 : VExpr :=
  kernelRecRuleRhs% Spec06SmallSource.rec 0
def smallSourceRightRuleRhs06 : VExpr :=
  kernelRecRuleRhs% Spec06SmallSource.rec 1

def smallSourceType06 : VInductiveType where
  name := ``Spec06SmallSource
  uvars := 1
  type := vconst(type_of% @Spec06SmallSource).type
  ctors := [
    ⟨vconst(type_of% @Spec06SmallSource.left), ``Spec06SmallSource.left⟩,
    ⟨vconst(type_of% @Spec06SmallSource.right), ``Spec06SmallSource.right⟩]

def smallSourceDecl06 : VInductDecl := ⟨1, 1, [smallSourceType06]⟩

def smallSourceChecked06 : smallSourceDecl06.Checked :=
  smallSourceDecl06.checked?.get (by decide)

def smallSourceGeneration06 :
    VInductDecl.GenerationChecked smallSourceDecl06 :=
  (VInductDecl.identityGeneration? smallSourceDecl06).get (by decide)

def smallSourceKernelType06 : InductiveType where
  name := smallSourceInfo06.name
  type := smallSourceInfo06.type
  ctors := [
    { name := smallSourceLeftInfo06.name, type := smallSourceLeftInfo06.type },
    { name := smallSourceRightInfo06.name, type := smallSourceRightInfo06.type }]

def smallSourceEliminationResult06 :=
  AddInductive.NormalizationEliminationExecution.buildExecution 1
    [smallSourceKernelType06] 0 false
      (spec06Context smallSourceInfo06.levelParams)

theorem smallSourceEliminationResult06_isOk :
    smallSourceEliminationResult06.isOk = true := by
  native_decide

def smallSourceProducedExecution06 :
    { execution // smallSourceEliminationResult06 = .ok execution } :=
  match h : smallSourceEliminationResult06 with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := smallSourceEliminationResult06_isOk
      rw [h] at hOk
      contradiction

def smallSourceExecution06 := smallSourceProducedExecution06.val

def smallSourceAlignment06 : AddInductive.CheckerEliminationRun
    smallSourceGeneration06 smallSourceExecution06 :=
  (AddInductive.CheckerEliminationRun.build? smallSourceGeneration06
    smallSourceExecution06).get (by native_decide)

example : smallSourceInfo06.levelParams = [`u] := rfl
example : smallSourceExecution06.elimination.large.result = false := by
  native_decide
example : smallSourceExecution06.kTarget.result = false := by native_decide
example : smallSourceExecution06.kTarget.singleton = none := by native_decide
example : smallSourceExecution06.elimination.level = .zero :=
  Level.isStructEq_eq (by native_decide)
example : smallSourceExecution06.recLevelParams = [`u] := by native_decide
example : smallSourceExecution06.recLevels = [.param `u] :=
  levelListStructEq06_eq (by native_decide)
example : recursorShape06 smallSourceRecInfo06 =
    ([`u], 1, 0, 1, 2, false,
      [(``Spec06SmallSource.left, 0), (``Spec06SmallSource.right, 0)]) := rfl
example : smallSourceChecked06.elimination = .small :=
  smallSourceAlignment06.small_result_iff.mp (by native_decide)
example : smallSourceGeneration06.kTarget = false :=
  smallSourceAlignment06.kTarget_result_false_iff.mp (by native_decide)
example : smallSourceGeneration06.recursor =
    vconst(type_of% @Spec06SmallSource.rec) := rfl
example : smallSourceLeftRuleRhs06 =
    smallSourceGeneration06.generatedRules[0].rhs := rfl
example : smallSourceRightRuleRhs06 =
    smallSourceGeneration06.generatedRules[1].rhs := rfl

end Ix.Theory.Named.InductiveReplayFixtures
