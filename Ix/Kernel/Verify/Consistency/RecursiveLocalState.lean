/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.DefEqLocalState
import Ix.Kernel.Verify.Consistency.ProjectionLocalState

/-!
# Structural local-state preservation for the complete recursive knot

Induction on the actual production method-table depth closes the six mutually
dependent state contracts. Public entries select that table from the current
recursive fuel, exactly as `TcM.runRec` does. There are no recursive-method or
loader-effect premises beyond the maintained initial local-state invariant.

The result preserves local declarations, monotone fresh allocation and the
installed loader on both outcomes. Reduction, conversion and inference still
need their separate semantic correctness proofs for general consistency.
-/

namespace Ix.Kernel.Consistency

/-- Every finite production table satisfies the complete structural contract.
The successor case uses only the strictly smaller table's callbacks. -/
theorem MethodsLocalState.methodsN (depth : Nat) :
    MethodsLocalState (_root_.Ix.Kernel.methodsN (m := .anon) depth) := by
  induction depth with
  | zero =>
      exact {
        whnf := fun _ => FramesLocalState.throw _
        whnfCore := fun _ => FramesLocalState.throw _
        whnfMode := fun _ _ => FramesLocalState.throw _
        whnfCoreFlags := fun _ _ => FramesLocalState.throw _
        infer := fun _ => FramesLocalState.throw _
        isDefEq := fun _ _ => FramesLocalState.throw _ }
  | succ depth recursive =>
      exact {
        whnf := FramesLocalState.whnf recursive
        whnfCore := FramesLocalState.whnfCore recursive
        whnfMode := FramesLocalState.whnfWithNatSuccMode recursive
        whnfCoreFlags := FramesLocalState.whnfCoreWithFlags recursive
        infer := infer_framesLocalState_of_whnf recursive.infer
          (FramesLocalState.whnf recursive) recursive.isDefEq
        isDefEq := FramesLocalState.isDefEq recursive }

/-- Running from arbitrary current fuel uses a proved finite table, including
the exhausted-depth table and every error-side partial state. -/
theorem FramesLocalState.runRec {action : RecM .anon α}
    (framed : ∀ methods, MethodsLocalState methods → FramesLocalState (action.run methods)) :
    FramesLocalState (TcM.runRec action) := by
  intro before valid
  exact framed (_root_.Ix.Kernel.methodsN before.recFuel.toNat)
    (MethodsLocalState.methodsN before.recFuel.toNat) before valid

end Ix.Kernel.Consistency

namespace Ix.Kernel.TcM

open Consistency

theorem whnf_framesLocalState (term : KExpr .anon) : FramesLocalState (whnf term) :=
  FramesLocalState.runRec fun _ recursive => FramesLocalState.whnf recursive term

theorem whnfCore_framesLocalState (term : KExpr .anon) : FramesLocalState (whnfCore term) :=
  FramesLocalState.runRec fun _ recursive => FramesLocalState.whnfCore recursive term

theorem whnfNoDelta_framesLocalState (term : KExpr .anon) : FramesLocalState (whnfNoDelta term) :=
  FramesLocalState.runRec fun _ recursive => FramesLocalState.whnfNoDelta recursive term

theorem infer_framesLocalState (term : KExpr .anon) : FramesLocalState (infer term) :=
  FramesLocalState.runRec fun _ recursive =>
    infer_framesLocalState_of_whnf recursive.infer
      (FramesLocalState.whnf recursive) recursive.isDefEq term

theorem isDefEq_framesLocalState (left right : KExpr .anon) :
    FramesLocalState (isDefEq left right) :=
  FramesLocalState.runRec fun _ recursive => FramesLocalState.isDefEq recursive left right

theorem ensureSort_framesLocalState (term : KExpr .anon) : FramesLocalState (ensureSort term) :=
  FramesLocalState.runRec fun _ recursive =>
    FramesLocalState.ensureSortDirect (FramesLocalState.whnf recursive) term

theorem ensureForall_framesLocalState (term : KExpr .anon) : FramesLocalState (ensureForall term) :=
  FramesLocalState.runRec fun _ recursive =>
    FramesLocalState.ensureForallDirect (FramesLocalState.whnf recursive) term

end Ix.Kernel.TcM
