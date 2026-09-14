/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Compiler.Layout

/-! State fields that every operation layout preserves, for all three
component rank modes and the generic ordered fallback. -/

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

theorem opLayout_fixed (op : Op) (initial : LayoutMState) :
    ((opLayout op).run initial).2.functionLayout.inputSize = initial.functionLayout.inputSize ∧
    ((opLayout op).run initial).2.functionLayout.selectors = initial.functionLayout.selectors := by
  cases op
  case call function args outputSize unconstrained =>
    cases unconstrained <;> cases rank : initial.callRanks[function]?.getD .ordered <;>
      simp [opLayout, bumpLookups, bumpAuxiliaries, pushDegrees,
        StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
        get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
        bind, pure, rank]
  all_goals
    simp only [opLayout, getDegree_array, bumpLookups, bumpAuxiliaries, getDegree,
      pushDegree, pushDegrees, addMemSize]
  all_goals dsimp [StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
    instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad, bind, pure]
  all_goals try split
  all_goals exact ⟨rfl, rfl⟩

theorem opLayout_callRanks (op : Op) (initial : LayoutMState) :
    ((opLayout op).run initial).2.callRanks = initial.callRanks := by
  cases op
  case call function args outputSize unconstrained =>
    cases unconstrained <;> cases rank : initial.callRanks[function]?.getD .ordered <;>
      simp [opLayout, bumpLookups, bumpAuxiliaries, pushDegrees,
        StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
        get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
        bind, pure, rank]
  all_goals
    simp only [opLayout, getDegree_array, bumpLookups, bumpAuxiliaries, getDegree,
      pushDegree, pushDegrees, addMemSize]
  all_goals dsimp [StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
    instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad, bind, pure]
  all_goals try split
  all_goals rfl

private theorem ops_fold_inputSize (ops : List Op) (initial : LayoutMState) :
    ((ops.foldlM (fun _ op => opLayout op) ()).run initial).2.functionLayout.inputSize =
      initial.functionLayout.inputSize := by
  induction ops generalizing initial with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldlM_cons]
    exact (ih ((opLayout op).run initial).2).trans (opLayout_fixed op initial).1

theorem opsLayout_inputSize (ops : Array Op) (initial : LayoutMState) :
    ((ops.forM opLayout).run initial).2.functionLayout.inputSize =
      initial.functionLayout.inputSize := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact ops_fold_inputSize ops.toList initial

/-- The input arity and the selected call modes stay fixed throughout layout. -/
def LayoutMState.context (state : LayoutMState) : Nat × Array CallRank :=
  (state.functionLayout.inputSize, state.callRanks)

theorem opLayout_context (op : Op) (initial : LayoutMState) :
    ((opLayout op).run initial).2.context = initial.context :=
  Prod.ext (opLayout_fixed op initial).1 (opLayout_callRanks op initial)

private theorem ops_fold_context (ops : List Op) (initial : LayoutMState) :
    ((ops.foldlM (fun _ op => opLayout op) ()).run initial).2.context = initial.context := by
  induction ops generalizing initial with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldlM_cons]
    exact (ih ((opLayout op).run initial).2).trans (opLayout_context op initial)

theorem opsLayout_context (ops : Array Op) (initial : LayoutMState) :
    ((ops.forM opLayout).run initial).2.context = initial.context := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact ops_fold_context ops.toList initial

end Aiur.Concrete.Bytecode
