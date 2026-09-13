/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.EliminationFixturesCommon

/-! Exact Or/And elimination differential fixtures. -/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

/-! ## Or: Prop-only elimination -/

def orInfo06 : ConstantInfo := kernelInductInfo% Or
def orInlInfo06 : ConstantInfo := kernelCtorInfo% Or.inl
def orInrInfo06 : ConstantInfo := kernelCtorInfo% Or.inr
def orRecInfo06 : ConstantInfo := kernelRecInfo% Or.rec
def orInlKernelRuleRhs06 : VExpr := kernelRecRuleRhs% Or.rec 0
def orInrKernelRuleRhs06 : VExpr := kernelRecRuleRhs% Or.rec 1

def orKernelType06 : InductiveType where
  name := orInfo06.name
  type := orInfo06.type
  ctors := [
    { name := orInlInfo06.name, type := orInlInfo06.type },
    { name := orInrInfo06.name, type := orInrInfo06.type }]

def orEliminationResult06 :=
  AddInductive.NormalizationEliminationExecution.buildExecution 2
    [orKernelType06] 0 false (spec06Context orInfo06.levelParams)

theorem orEliminationResult06_isOk : orEliminationResult06.isOk = true := by
  native_decide

def orProducedExecution06 :
    { execution // orEliminationResult06 = .ok execution } :=
  match h : orEliminationResult06 with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := orEliminationResult06_isOk
      rw [h] at hOk
      contradiction

def orExecution06 := orProducedExecution06.val

def orGeneration06 : VInductDecl.GenerationChecked orDecl :=
  (VInductDecl.identityGeneration? orDecl).get (by decide)

def orAlignment06 :
    AddInductive.CheckerEliminationRun orGeneration06 orExecution06 :=
  (AddInductive.CheckerEliminationRun.build? orGeneration06 orExecution06).get
    (by native_decide)

example : orExecution06.elimination.large.result = false := by native_decide
example : orExecution06.kTarget.result = false := by native_decide
example : orExecution06.kTarget.singleton = none := by native_decide
example : orExecution06.elimination.level = .zero :=
  Level.isStructEq_eq (by native_decide)
example : orExecution06.recLevelParams = [] := by native_decide
example : orExecution06.recLevels = [] := by native_decide
example : recursorShape06 orRecInfo06 =
    ([], 2, 0, 1, 2, false, [(``Or.inl, 1), (``Or.inr, 1)]) := rfl
example : orInlKernelRuleRhs06 = orChecked.generatedRules[0].rhs := rfl
example : orInrKernelRuleRhs06 = orChecked.generatedRules[1].rhs := rfl
example : orGeneration06.elimination = .small :=
  orAlignment06.small_result_iff.mp (by native_decide)
example : orGeneration06.kTarget = false :=
  orAlignment06.kTarget_result_false_iff.mp (by native_decide)

/-! ## And: singleton proof fields permit large elimination -/

def andInfo06 : ConstantInfo := kernelInductInfo% And
def andIntroInfo06 : ConstantInfo := kernelCtorInfo% And.intro
def andRecInfo06 : ConstantInfo := kernelRecInfo% And.rec
def andKernelRuleRhs06 : VExpr := kernelRecRuleRhs% And.rec 0

def andKernelType06 : InductiveType where
  name := andInfo06.name
  type := andInfo06.type
  ctors := [{ name := andIntroInfo06.name, type := andIntroInfo06.type }]

def andEliminationResult06 :=
  AddInductive.NormalizationEliminationExecution.buildExecution 2
    [andKernelType06] 0 false (spec06Context andInfo06.levelParams)

theorem andEliminationResult06_isOk : andEliminationResult06.isOk = true := by
  native_decide

def andProducedExecution06 :
    { execution // andEliminationResult06 = .ok execution } :=
  match h : andEliminationResult06 with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := andEliminationResult06_isOk
      rw [h] at hOk
      contradiction

def andExecution06 := andProducedExecution06.val

def andGeneration06 : VInductDecl.GenerationChecked andDecl :=
  (VInductDecl.identityGeneration? andDecl).get (by decide)

def andAlignment06 :
    AddInductive.CheckerEliminationRun andGeneration06 andExecution06 :=
  (AddInductive.CheckerEliminationRun.build? andGeneration06 andExecution06).get
    (by native_decide)

def andSingletonExecution06 :=
  andExecution06.elimination.large.singleton.get (by native_decide)

def andKTargetSingleton06 :=
  andExecution06.kTarget.singleton.get (by native_decide)

example : andExecution06.elimination.large.result = true := by native_decide
example : andExecution06.kTarget.result = false := by native_decide
example : andKTargetSingleton06.trace.parameterCount = 2 := by native_decide
example : andKTargetSingleton06.trace.fieldCount = 1 := by native_decide
example : andExecution06.elimination.level = .param `u :=
  Level.isStructEq_eq (by native_decide)
example : andExecution06.recLevelParams = [`u] := by native_decide
example : andExecution06.recLevels = [.param `u] :=
  levelListStructEq06_eq (by native_decide)
example : recursorShape06 andRecInfo06 =
    ([`u], 2, 0, 1, 1, false, [(``And.intro, 2)]) := rfl
example : andSingletonExecution06.trace.parameterCount = 2 := by native_decide
example : andSingletonExecution06.trace.proofFieldCount = 2 := by native_decide
example : andSingletonExecution06.trace.dataFieldCount = 0 := by native_decide
example : andKernelRuleRhs06 = andChecked.generatedRules[0].rhs := rfl
example : andGeneration06.elimination = .large :=
  andAlignment06.large_result_iff.mp (by native_decide)
example : andGeneration06.kTarget = false :=
  andAlignment06.kTarget_result_false_iff.mp (by native_decide)

end Ix.Theory.Named.InductiveReplayFixtures
