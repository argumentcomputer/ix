/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Compiler.Dedup
import Ix.Aiur.Semantics.BytecodeEval

/-! Exact successful-execution equivalence under checked function renaming.
The relation retains memory, I/O and the early-return escape channel. -/

namespace Aiur.Bytecode.Eval

/-- Function renaming preserves the call domain, every rewritten body and
the input arity. It may merge multiple old functions into one target. -/
structure RenamedCode (a b : Toplevel) (rename : FunIdx → FunIdx) : Prop where
  domain : ∀ i, i < a.functions.size ↔ rename i < b.functions.size
  body : ∀ i (ha : i < a.functions.size) (hb : rename i < b.functions.size),
    rewriteBlock rename a.functions[i].body = b.functions[rename i].body
  inputSize : ∀ i (ha : i < a.functions.size) (hb : rename i < b.functions.size),
    a.functions[i].layout.inputSize = b.functions[rename i].layout.inputSize

/-- Errors may contain function indices changed by renaming. Successful
results and the evaluator's early-return channel retain their full values. -/
def returnObservation : BytecodeError → Option (Array G × EvalState)
  | .earlyReturn outs st => some (outs, st)
  | _ => none

def observe (result : Except BytecodeError α) : Except (Option (Array G × EvalState)) α :=
  result.mapError returnObservation

theorem observe_ok_iff {result : Except BytecodeError α} {value : α} :
    observe result = .ok value ↔ result = .ok value := by
  cases result <;> simp [observe, Except.mapError]

theorem observe_bind {x y : Except BytecodeError α}
    (h : observe x = observe y) {f g : α → Except BytecodeError β}
    (hf : ∀ value, observe (f value) = observe (g value)) :
    observe (match x with | .error e => .error e | .ok value => f value) =
      observe (match y with | .error e => .error e | .ok value => g value) := by
  cases x <;> cases y <;> simp_all [observe, Except.mapError]

theorem observe_pairBind {x y : Except BytecodeError (Array G × EvalState)}
    (h : observe x = observe y) {f g : Array G → EvalState → Except BytecodeError β}
    (hf : ∀ outs st, observe (f outs st) = observe (g outs st)) :
    observe (match x with | .error e => .error e | .ok (outs, st) => f outs st) =
      observe (match y with | .error e => .error e | .ok (outs, st) => g outs st) := by
  cases x <;> cases y <;> simp_all [observe, Except.mapError]

private def finishCall (st : EvalState) (outputSize : Nat)
    (result : Except BytecodeError (Array G × EvalState)) : Except BytecodeError EvalState :=
  match result with
  | .error (.earlyReturn outs innerSt) | .ok (outs, innerSt) =>
    if outs.size != outputSize then .error .callOutputSizeMismatch
    else .ok (appendMap (setIoBuffer { st with memory := innerSt.memory } innerSt.ioBuffer) outs)
  | .error e => .error e

private def finishObservedCall (st : EvalState) (outputSize : Nat)
    (result : Except (Option (Array G × EvalState)) (Array G × EvalState)) :
    Except (Option (Array G × EvalState)) EvalState :=
  match result with
  | .error (some (outs, innerSt)) | .ok (outs, innerSt) =>
    if outs.size != outputSize then .error none
    else .ok (appendMap (setIoBuffer { st with memory := innerSt.memory } innerSt.ioBuffer) outs)
  | .error none => .error none

private theorem observe_finishCall (st : EvalState) (outputSize : Nat)
    (result : Except BytecodeError (Array G × EvalState)) :
    observe (finishCall st outputSize result) =
      finishObservedCall st outputSize (observe result) := by
  cases result with
  | ok value =>
    rcases value with ⟨outs, innerSt⟩
    by_cases h : outs.size != outputSize <;>
      simp [finishCall, finishObservedCall, observe, Except.mapError, returnObservation, h]
  | error error =>
    cases error <;> try rfl
    case earlyReturn outs innerSt =>
      by_cases h : outs.size != outputSize <;>
        simp [finishCall, finishObservedCall, observe, Except.mapError, returnObservation, h]

private theorem ops_lt (b : Block) : sizeOf b.ops < sizeOf b := by
  cases b; simp; omega

private theorem ctrl_lt (b : Block) : sizeOf b.ctrl < sizeOf b := by
  cases b; simp; omega

private theorem case_lt (cases : Array (G × Block)) (fallback : Option Block)
    (i : Nat) (h : i < cases.size) :
    sizeOf cases[i].2 < sizeOf cases + sizeOf fallback := by
  have h1 := Array.sizeOf_get cases i h
  have h2 : sizeOf cases[i].2 < sizeOf cases[i] := by
    cases cases[i]; simp; omega
  omega

mutual

theorem evalOp_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (fuel : Nat) (op : Op) (st : EvalState) :
    observe (evalOp a fuel op st) = observe (evalOp b fuel (rewriteOp rename op) st) := by
  cases op <;> simp only [rewriteOp, evalOp]
  all_goals try rfl
  case call fi args outputSize unconstrained =>
    cases hg : readIdxs st args with
    | error e => rfl
    | ok gs =>
      simp only [bind, Except.bind]
      by_cases ha : fi < a.functions.size
      · have hb := (code.domain fi).mp ha
        simp only [dif_pos ha, dif_pos hb, code.inputSize fi ha hb]
        split
        · rfl
        · cases fuel with
          | zero => rfl
          | succ fuel =>
            change observe (finishCall st outputSize (evalBlock a fuel a.functions[fi].body _)) =
              observe (finishCall st outputSize (evalBlock b fuel b.functions[rename fi].body _))
            rw [observe_finishCall, observe_finishCall,
              ← code.body fi ha hb, evalBlock_renamed code]
      · have hb : ¬ rename fi < b.functions.size := by simpa [← code.domain fi] using ha
        simp only [dif_neg ha, dif_neg hb]
        rfl
termination_by (fuel, sizeOf op, 0)
decreasing_by all_goals first | decreasing_tactic | omega

theorem runOps_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (fuel : Nat) (ops : Array Op) (st : EvalState) (i : Nat) :
    observe (runOps a fuel ops st i) =
      observe (runOps b fuel (ops.map (rewriteOp rename)) st i) := by
  rw [runOps.eq_1 a, runOps.eq_1 b]
  simp only [Array.size_map]
  by_cases h : i < ops.size
  · simp only [dif_pos h, Array.getElem_map]
    have related := observe_bind (f := fun st' => runOps a fuel ops st' (i + 1))
      (g := fun st' => runOps b fuel (ops.map (rewriteOp rename)) st' (i + 1))
      (evalOp_renamed code fuel ops[i] st) (fun st' => runOps_renamed code fuel ops st' (i + 1))
    cases hleft : evalOp a fuel ops[i] st <;>
      cases hright : evalOp b fuel (rewriteOp rename ops[i]) st <;>
      simpa only [hleft, hright] using related
  · simp only [dif_neg h]
termination_by (fuel, sizeOf ops, 1 + (ops.size - i))
decreasing_by all_goals first | decreasing_tactic | omega

theorem evalBlock_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (fuel : Nat) (block : Block) (st : EvalState) :
    observe (evalBlock a fuel block st) =
      observe (evalBlock b fuel (rewriteBlock rename block) st) := by
  rw [evalBlock.eq_1 a, evalBlock.eq_1 b]
  simp only [rewriteBlock]
  have related := observe_bind (f := fun st' => evalCtrl a fuel block.ctrl st')
    (g := fun st' => evalCtrl b fuel (rewriteCtrl rename block.ctrl) st')
    (runOps_renamed code fuel block.ops st 0) (fun st' => evalCtrl_renamed code fuel block.ctrl st')
  cases hleft : runOps a fuel block.ops st 0 <;>
    cases hright : runOps b fuel (block.ops.map (rewriteOp rename)) st 0 <;>
    simpa only [hleft, hright] using related
termination_by (fuel, sizeOf block, 4)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact ops_lt _)
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact ctrl_lt _)
    | omega

theorem evalCtrl_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (fuel : Nat) (ctrl : Ctrl) (st : EvalState) :
    observe (evalCtrl a fuel ctrl st) =
      observe (evalCtrl b fuel (rewriteCtrl rename ctrl) st) := by
  cases ctrl with
  | «return» sel outs => simp only [rewriteCtrl, evalCtrl]
  | «yield» sel outs => simp only [rewriteCtrl, evalCtrl]
  | «match» idx cases fallback =>
    rw [rewriteCtrl.eq_def]
    simp only [evalCtrl]
    cases readIdx st idx with
    | error e => rfl
    | ok scrut =>
      cases fallback <;>
        simpa only [Option.map] using evalMatchArm_renamed code fuel cases _ scrut st 0
  | matchContinue idx cases fallback out aux lookups cont =>
    rw [rewriteCtrl.eq_def]
    simp only [evalCtrl]
    cases readIdx st idx with
    | error e => rfl
    | ok scrut =>
      cases fallback
      all_goals
        with_unfolding_all
          apply observe_pairBind
            (f := fun outs st' => evalBlock a fuel cont { st' with map := st.map ++ outs })
            (g := fun outs st' => evalBlock b fuel (rewriteBlock rename cont)
              { st' with map := st.map ++ outs })
            (evalMatchArm_renamed code fuel cases _ scrut st 0)
      all_goals intro outs st'
      all_goals exact evalBlock_renamed code fuel cont _
termination_by (fuel, sizeOf ctrl, 3)
decreasing_by all_goals first | decreasing_tactic | omega

theorem evalMatchArm_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (fuel : Nat) (cases : Array (G × Block))
    (fallback : Option Block) (scrut : G) (st : EvalState) (i : Nat) :
    observe (evalMatchArm a fuel cases fallback scrut st i) =
      observe (evalMatchArm b fuel
        (cases.attach.map fun pair => (pair.val.1, rewriteBlock rename pair.val.2))
        (fallback.map (rewriteBlock rename)) scrut st i) := by
  rw [evalMatchArm.eq_1 a, evalMatchArm.eq_1 b]
  simp only [Array.size_map, Array.size_attach]
  by_cases h : i < cases.size
  · simp only [dif_pos h, Array.getElem_map, Array.getElem_attach]
    split
    · exact evalBlock_renamed code fuel cases[i].2 st
    · exact evalMatchArm_renamed code fuel cases fallback scrut st (i + 1)
  · simp only [dif_neg h]
    exact evalDefaultBlock_renamed code fuel fallback st
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

theorem evalDefaultBlock_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (fuel : Nat) (fallback : Option Block) (st : EvalState) :
    observe (evalDefaultBlock a fuel fallback st) =
      observe (evalDefaultBlock b fuel (fallback.map (rewriteBlock rename)) st) := by
  cases fallback with
  | none => simp only [Option.map, evalDefaultBlock]
  | some block => simpa only [Option.map, evalDefaultBlock] using evalBlock_renamed code fuel block st
termination_by (fuel, sizeOf fallback, 1)
decreasing_by all_goals first | decreasing_tactic | (simp_wf; omega)

end

private def finishFunction (result : Except BytecodeError (Array G × EvalState)) :
    Except BytecodeError (Array G × IOBuffer) :=
  match result with
  | .error (.earlyReturn outs st) | .ok (outs, st) => .ok (outs, st.ioBuffer)
  | .error error => .error error

private def finishObservedFunction
    (result : Except (Option (Array G × EvalState)) (Array G × EvalState)) :
    Except (Option (Array G × EvalState)) (Array G × IOBuffer) :=
  match result with
  | .error (some (outs, st)) | .ok (outs, st) => .ok (outs, st.ioBuffer)
  | .error none => .error none

private theorem observe_finishFunction (result : Except BytecodeError (Array G × EvalState)) :
    observe (finishFunction result) = finishObservedFunction (observe result) := by
  cases result with
  | ok value => cases value; rfl
  | error error => cases error <;> rfl

theorem runFunction_renamed {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (function : FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) :
    observe (runFunction a function args io fuel) =
      observe (runFunction b (rename function) args io fuel) := by
  rw [runFunction.eq_1 a, runFunction.eq_1 b]
  by_cases ha : function < a.functions.size
  · have hb := (code.domain function).mp ha
    simp only [dif_pos ha, dif_pos hb, code.inputSize function ha hb]
    split
    · rfl
    · change observe (finishFunction (evalBlock a fuel a.functions[function].body _)) =
        observe (finishFunction (evalBlock b fuel b.functions[rename function].body _))
      rw [observe_finishFunction, observe_finishFunction, ← code.body function ha hb,
        evalBlock_renamed code]
  · have hb : ¬ rename function < b.functions.size := by
      simpa [← code.domain function] using ha
    simp only [dif_neg ha, dif_neg hb]
    rfl

/-- Renaming preserves and reflects every successful result and final I/O
state at the same fuel. Failures may report different function indices. -/
theorem runFunction_renamed_iff {a b : Toplevel} {rename : FunIdx → FunIdx}
    (code : RenamedCode a b rename) (function : FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat)
    (result : Array G × IOBuffer) :
    runFunction a function args io fuel = .ok result ↔
      runFunction b (rename function) args io fuel = .ok result := by
  rw [← observe_ok_iff, ← observe_ok_iff, runFunction_renamed code]

end Aiur.Bytecode.Eval
