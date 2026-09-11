/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.EliminationFixturesCommon

/-! Exact Spec-06B Nat never-zero elimination and non-K fixture. -/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

/-! Nat's nonzero result universe takes the immediate large-elimination
branch. The exact singleton statistics and source levels are pinned directly
so this replay tests that branch without compiling the unrelated full
normalization trace a second time. -/

def natKernelType06 : InductiveType where
  name := natInfo.name
  type := natInfo.type
  ctors := [
    { name := natZeroInfo.name, type := natZeroInfo.type },
    { name := natSuccInfo.name, type := natSuccInfo.type }]

def natNeverZeroStats06 : AddInductive.InductiveStats :=
  AddInductive.singletonInductiveStats (spec06Context []) natKernelType06
    (.succ .zero)

def natElimLevelResult06 :=
  AddInductive.ElimLevelExecution.buildExecution natNeverZeroStats06
    #[natKernelType06] (spec06Context [])

theorem natElimLevelResult06_isOk : natElimLevelResult06.isOk = true := by
  native_decide

def natProducedElimLevel06 :
    { execution // natElimLevelResult06 = .ok execution } :=
  match h : natElimLevelResult06 with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := natElimLevelResult06_isOk
      rw [h] at hOk
      contradiction

def natElimLevelExecution06 := natProducedElimLevel06.val

def natElimAlignmentResult06 :=
  AddInductive.CheckerElimLevelRun.build? natGenerationChecked
    natElimLevelExecution06

theorem natElimAlignmentResult06_isSome :
    natElimAlignmentResult06.isSome = true := by
  native_decide

def natElimAlignment06 : AddInductive.CheckerElimLevelRun
    natGenerationChecked natElimLevelExecution06 :=
  natElimAlignmentResult06.get natElimAlignmentResult06_isSome

def natKTargetResult06 :=
  AddInductive.KTargetExecution.buildExecution natNeverZeroStats06
    #[natKernelType06] (spec06Context [])

theorem natKTargetResult06_isOk : natKTargetResult06.isOk = true := by
  native_decide

def natProducedKTarget06 :
    { execution // natKTargetResult06 = .ok execution } :=
  match h : natKTargetResult06 with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := natKTargetResult06_isOk
      rw [h] at hOk
      contradiction

def natKTargetExecution06 := natProducedKTarget06.val

def natKTargetAlignmentResult06 :=
  AddInductive.CheckerKTargetRun.build? natGenerationChecked
    natKTargetExecution06

theorem natKTargetAlignmentResult06_isSome :
    natKTargetAlignmentResult06.isSome = true := by
  native_decide

def natKTargetAlignment06 : AddInductive.CheckerKTargetRun
    natGenerationChecked natKTargetExecution06 :=
  natKTargetAlignmentResult06.get natKTargetAlignmentResult06_isSome

example : natNeverZeroStats06.isNotZero = true := rfl
example : natNeverZeroStats06.resultLevel = .succ .zero := rfl
example : natKernelType06.type = .sort (.succ .zero) := rfl
example : natChecked.resultLevel = .succ .zero := rfl
example : natElimLevelExecution06.large.result = true := by native_decide
example : natKTargetExecution06.result = false := by native_decide
example : natKTargetExecution06.singleton = none := by native_decide
example : natElimLevelExecution06.level = .param `u :=
  Level.isStructEq_eq (by native_decide)
example : AddInductive.getRecLevelParams natElimLevelExecution06.level [] =
    [`u] := by native_decide
example : AddInductive.getRecLevels natElimLevelExecution06.level [] =
    [.param `u] := levelListStructEq06_eq (by native_decide)
example : recursorShape06 natRecInfo =
    ([`u], 0, 0, 1, 2, false,
      [(``Nat.zero, 0), (``Nat.succ, 1)]) := rfl
example : natZeroKernelRuleRhs = natChecked.generatedRules[0].rhs := rfl
example : natSuccKernelRuleRhs = natChecked.generatedRules[1].rhs := rfl
example : natGenerationChecked.elimination = .large :=
  natElimAlignment06.large_result_iff.mp (by native_decide)
example : natGenerationChecked.kTarget = false :=
  natKTargetAlignment06.result_false_iff.mp (by native_decide)

end Ix.Theory.Named.InductiveReplayFixtures
