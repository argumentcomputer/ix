/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationAllocation
import Ix.Aiur.Proofs.LookupLayout

/-! The allocation projection describes the actual compiler layout step. -/

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode

theorem getDegree_list (indices : List ValIdx) (initial : LayoutMState) :
    (indices.mapM getDegree).run initial = (indices.map (fun i => initial.degrees[i]?.getD 0), initial) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    rw [List.mapM_cons]
    change (let (values, final) := (indices.mapM getDegree).run initial;
      (initial.degrees[index]?.getD 0 :: values, final)) =
      (initial.degrees[index]?.getD 0 :: indices.map (fun i => initial.degrees[i]?.getD 0), initial)
    rw [ih]

theorem getDegree_array (indices : Array ValIdx) :
    indices.mapM getDegree = (fun initial => pure (indices.map (fun i => initial.degrees[i]?.getD 0), initial)) := by
  rw [Array.mapM_eq_mapM_toList]
  funext initial
  change (let (values, final) := (indices.toList.mapM getDegree).run initial;
      (values.toArray, final)) = (indices.map (fun i => initial.degrees[i]?.getD 0), initial)
  rw [getDegree_list]
  simp only [← List.map_toArray, Array.toArray_toList]

theorem opLayout_allocation (op : Op) (initial : LayoutMState) :
    ((opLayout op).run initial).2.degrees = initial.degrees ++ (op.allocation initial.degrees).degrees ∧
    ((opLayout op).run initial).2.functionLayout.auxiliaries =
      initial.functionLayout.auxiliaries + (op.allocation initial.degrees).auxiliaries := by
  cases op <;>
    simp only [opLayout, getDegree_array, bumpLookups, bumpAuxiliaries, getDegree,
      pushDegree, pushDegrees, addMemSize, Op.allocation, OpAllocation.advice]
  all_goals dsimp [StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
    instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad,
    bind, pure]
  all_goals try simp [selectedDegree]
  all_goals try split
  all_goals try simp_all
  all_goals first | rfl | exact ⟨rfl, rfl⟩

end Aiur.Concrete.Bytecode
