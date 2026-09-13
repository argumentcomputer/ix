/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationAllocation
import Ix.Aiur.Proofs.LookupLayout
import Ix.Aiur.Proofs.LayoutState

/-! The allocation projection describes the actual compiler layout step. -/

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode

theorem opLayout_allocation (op : Op) (initial : LayoutMState) :
    ((opLayout op).run initial).2.degrees = initial.degrees ++ (op.allocationFor initial.callRanks initial.degrees).degrees ∧
    ((opLayout op).run initial).2.functionLayout.auxiliaries =
      initial.functionLayout.auxiliaries + (op.allocationFor initial.callRanks initial.degrees).auxiliaries := by
  cases op
  case call function args outputSize unconstrained =>
    cases unconstrained <;> cases rank : initial.callRanks[function]?.getD .ordered <;>
      simp [opLayout, Op.allocationFor, bumpLookups, bumpAuxiliaries, pushDegrees,
        StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
        get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
        bind, pure, rank, Nat.add_assoc]
  all_goals
    simp only [opLayout, getDegree_array, bumpLookups, bumpAuxiliaries, getDegree,
      pushDegree, pushDegrees, addMemSize, Op.allocationFor, Op.allocation, OpAllocation.advice]
  all_goals dsimp [StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
    instMonadStateOfMonadStateOf, instMonadStateOfStateTOfMonad,
    bind, pure]
  all_goals try simp [selectedDegree]
  all_goals try split
  all_goals try simp_all
  all_goals first | rfl | exact ⟨rfl, rfl⟩

theorem opLayout_genericAllocation (op : Op) (initial : LayoutMState)
    (generic : initial.callRanks = #[]) :
    ((opLayout op).run initial).2.degrees = initial.degrees ++ (op.allocation initial.degrees).degrees ∧
    ((opLayout op).run initial).2.functionLayout.auxiliaries =
      initial.functionLayout.auxiliaries + (op.allocation initial.degrees).auxiliaries := by
  simpa only [generic, Op.allocationFor_empty] using opLayout_allocation op initial

end Aiur.Concrete.Bytecode
