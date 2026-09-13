/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.EliminationFixturesCommon

/-! Exact Eq elimination differential fixture. -/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

/-! Eq: indexed singleton large elimination and fresh-first order. -/

def eqKernelType06 : InductiveType where
  name := eqInfo.name
  type := eqInfo.type
  ctors := [{ name := eqReflInfo.name, type := eqReflInfo.type }]

def eqEliminationResult06 :=
  AddInductive.NormalizationEliminationExecution.buildExecution 2
    [eqKernelType06] 0 false (spec06Context eqInfo.levelParams)

theorem eqEliminationResult06_isOk : eqEliminationResult06.isOk = true := by
  native_decide

def eqProducedExecution06 :
    { execution // eqEliminationResult06 = .ok execution } :=
  match h : eqEliminationResult06 with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := eqEliminationResult06_isOk
      rw [h] at hOk
      contradiction

def eqExecution06 := eqProducedExecution06.val

def eqAlignment06 :
    AddInductive.CheckerEliminationRun eqGenerationChecked eqExecution06 :=
  (AddInductive.CheckerEliminationRun.build? eqGenerationChecked eqExecution06).get
    (by native_decide)

def eqKTargetSingleton06 :=
  eqExecution06.kTarget.singleton.get (by native_decide)

example : eqExecution06.elimination.large.result = true := by native_decide
example : eqExecution06.kTarget.result = true := by native_decide
example : eqKTargetSingleton06.trace.parameterCount = 2 := by native_decide
example : eqKTargetSingleton06.trace.fieldCount = 0 := by native_decide
example : eqExecution06.elimination.level = .param `u :=
  Level.isStructEq_eq (by native_decide)
example : eqExecution06.recLevelParams = [`u, `u_1] := by native_decide
example : eqExecution06.recLevels = [.param `u, .param `u_1] :=
  levelListStructEq06_eq (by native_decide)
example : recursorShape06 eqRecInfo =
    ([`u, `u_1], 2, 1, 1, 1, true, [(``Eq.refl, 0)]) := rfl
example : eqReflKernelRuleRhs = eqChecked.generatedRules[0].rhs := rfl
example : eqGenerationChecked.elimination = .large :=
  eqAlignment06.large_result_iff.mp (by native_decide)
example : eqGenerationChecked.kTarget = true :=
  eqAlignment06.kTarget_result_true_iff.mp (by native_decide)

end Ix.Theory.Named.InductiveReplayFixtures
