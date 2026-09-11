/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Semantics.BytecodeEval

/-! Circuit metadata does not change reference bytecode execution. The
theorem preserves errors and state as well as successful outputs, and works
in both directions. It does not interpret satisfying AIR witnesses as
executions of the reference evaluator. -/

namespace Aiur.Bytecode.Eval

structure SameCode (a b : Toplevel) : Prop where
  size : a.functions.size = b.functions.size
  body : ∀ i (ha : i < a.functions.size) (hb : i < b.functions.size),
    a.functions[i].body = b.functions[i].body
  inputSize : ∀ i (ha : i < a.functions.size) (hb : i < b.functions.size),
    a.functions[i].layout.inputSize = b.functions[i].layout.inputSize

private theorem ops_lt (b : Block) : sizeOf b.ops < sizeOf b := by
  cases b; simp; omega

private theorem ctrl_lt (b : Block) : sizeOf b.ctrl < sizeOf b := by
  cases b; simp; omega

private theorem case_lt (cases : Array (G × Block)) (defaultBlock : Option Block)
    (i : Nat) (h : i < cases.size) :
    sizeOf cases[i].2 < sizeOf cases + sizeOf defaultBlock := by
  have h1 := Array.sizeOf_get cases i h
  have h2 : sizeOf cases[i].2 < sizeOf cases[i] := by
    cases cases[i]; simp; omega
  omega

mutual

theorem evalOp_sameCode {a b : Toplevel} (code : SameCode a b)
    (fuel : Nat) (op : Op) (st : EvalState) :
    evalOp a fuel op st = evalOp b fuel op st := by
  cases op <;> simp only [evalOp]
  case call fi args outputSize unconstrained =>
    cases hg : readIdxs st args with
    | error e => rfl
    | ok gs =>
      simp only [bind, Except.bind]
      by_cases ha : fi < a.functions.size
      · have hb : fi < b.functions.size := by rwa [← code.size]
        simp only [dif_pos ha, dif_pos hb, code.inputSize fi ha hb]
        split
        · rfl
        · cases fuel with
          | zero => rfl
          | succ fuel =>
            simp only
            rw [code.body fi ha hb, evalBlock_sameCode code]
      · have hb : ¬ fi < b.functions.size := by rwa [← code.size]
        simp only [dif_neg ha, dif_neg hb]
termination_by (fuel, sizeOf op, 0)
decreasing_by all_goals first | decreasing_tactic | omega

theorem runOps_sameCode {a b : Toplevel} (code : SameCode a b)
    (fuel : Nat) (ops : Array Op) (st : EvalState) (i : Nat) :
    runOps a fuel ops st i = runOps b fuel ops st i := by
  rw [runOps.eq_1 a, runOps.eq_1 b]
  by_cases h : i < ops.size
  · simp only [dif_pos h, evalOp_sameCode code fuel ops[i] st]
    cases evalOp b fuel ops[i] st with
    | error e => rfl
    | ok st' => exact runOps_sameCode code fuel ops st' (i + 1)
  · simp only [dif_neg h]
termination_by (fuel, sizeOf ops, 1 + (ops.size - i))
decreasing_by all_goals first | decreasing_tactic | omega

theorem evalBlock_sameCode {a b : Toplevel} (code : SameCode a b)
    (fuel : Nat) (block : Block) (st : EvalState) :
    evalBlock a fuel block st = evalBlock b fuel block st := by
  rw [evalBlock.eq_1 a, evalBlock.eq_1 b, runOps_sameCode code]
  cases runOps b fuel block.ops st 0 with
  | error e => rfl
  | ok st' => exact evalCtrl_sameCode code fuel block.ctrl st'
termination_by (fuel, sizeOf block, 4)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact ops_lt _)
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact ctrl_lt _)
    | omega

theorem evalCtrl_sameCode {a b : Toplevel} (code : SameCode a b)
    (fuel : Nat) (ctrl : Ctrl) (st : EvalState) :
    evalCtrl a fuel ctrl st = evalCtrl b fuel ctrl st := by
  cases ctrl with
  | «return» sel outs => simp only [evalCtrl]
  | «yield» sel outs => simp only [evalCtrl]
  | «match» idx cases fallback =>
    simp only [evalCtrl]
    cases readIdx st idx with
    | error e => rfl
    | ok scrut => exact evalMatchArm_sameCode code fuel cases fallback scrut st 0
  | matchContinue idx cases fallback out aux lookups cont =>
    simp only [evalCtrl]
    cases readIdx st idx with
    | error e => rfl
    | ok scrut =>
      simp only
      rw [evalMatchArm_sameCode code]
      cases evalMatchArm b fuel cases fallback scrut st with
      | error e => rfl
      | ok result => exact evalBlock_sameCode code fuel cont _
termination_by (fuel, sizeOf ctrl, 3)
decreasing_by all_goals first | decreasing_tactic | omega

theorem evalMatchArm_sameCode {a b : Toplevel} (code : SameCode a b)
    (fuel : Nat) (cases : Array (G × Block)) (fallback : Option Block)
    (scrut : G) (st : EvalState) (i : Nat) :
    evalMatchArm a fuel cases fallback scrut st i = evalMatchArm b fuel cases fallback scrut st i := by
  rw [evalMatchArm.eq_1 a, evalMatchArm.eq_1 b]
  by_cases h : i < cases.size
  · simp only [dif_pos h]
    split
    · exact evalBlock_sameCode code fuel cases[i].2 st
    · exact evalMatchArm_sameCode code fuel cases fallback scrut st (i + 1)
  · simp only [dif_neg h]
    exact evalDefaultBlock_sameCode code fuel fallback st
termination_by (fuel, sizeOf cases + sizeOf fallback, 2 + (cases.size - i))
decreasing_by
  all_goals
    clean_wf
    first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact case_lt cases fallback i ‹_›)
    | (apply Prod.Lex.right; apply Prod.Lex.left
       cases cases; simp; omega)
    | omega

theorem evalDefaultBlock_sameCode {a b : Toplevel} (code : SameCode a b)
    (fuel : Nat) (fallback : Option Block) (st : EvalState) :
    evalDefaultBlock a fuel fallback st = evalDefaultBlock b fuel fallback st := by
  cases fallback with
  | none => simp only [evalDefaultBlock]
  | some block => simpa only [evalDefaultBlock] using evalBlock_sameCode code fuel block st
termination_by (fuel, sizeOf fallback, 1)
decreasing_by all_goals first | decreasing_tactic | (simp_wf; omega)

end

theorem runFunction_sameCode {a b : Toplevel} (code : SameCode a b)
    (function : FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) :
    runFunction a function args io fuel = runFunction b function args io fuel := by
  rw [runFunction.eq_1 a, runFunction.eq_1 b]
  by_cases ha : function < a.functions.size
  · have hb : function < b.functions.size := by rwa [← code.size]
    simp only [dif_pos ha, dif_pos hb, code.inputSize function ha hb,
      code.body function ha hb, evalBlock_sameCode code]
  · have hb : ¬ function < b.functions.size := by rwa [← code.size]
    simp only [dif_neg ha, dif_neg hb]

end Aiur.Bytecode.Eval
