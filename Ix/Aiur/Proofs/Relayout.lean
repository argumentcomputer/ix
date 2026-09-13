/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Compiler.CallOrder
import Ix.Aiur.Proofs.Metadata
import Ix.Aiur.Proofs.LayoutProjection

/-! Component selection recomputes continuation column counts. These counts
do not affect reference execution, including errors, early returns, memory,
I/O or fuel. The proof follows the actual stateful layout pass. -/

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode Aiur.Bytecode.Eval

private def blockCode (block : Block) :=
  fun (t : Toplevel) fuel st => evalBlock t fuel block st

private def branchCode (branch : G × Block) := (branch.1, blockCode branch.2)

private theorem evalMatchArm_congr (t : Toplevel) (fuel : Nat)
    (before after : Array (G × Block)) (fallback fallback' : Option Block)
    (same : before.map branchCode = after.map branchCode)
    (default : ∀ st, evalDefaultBlock t fuel fallback st =
      evalDefaultBlock t fuel fallback' st) (scrut : G) (st : EvalState) (i : Nat) :
    evalMatchArm t fuel before fallback scrut st i =
      evalMatchArm t fuel after fallback' scrut st i := by
  have size : before.size = after.size := by
    simpa only [Array.size_map] using congrArg Array.size same
  rw [evalMatchArm.eq_1 t fuel before, evalMatchArm.eq_1 t fuel after]
  by_cases ha : i < before.size
  · have hb : i < after.size := by omega
    have item : branchCode before[i] = branchCode after[i] := by
      have eq := congrArg (fun xs => xs[i]?) same
      simpa only [Array.getElem?_map, Array.getElem?_eq_getElem ha,
        Array.getElem?_eq_getElem hb, Option.map_some, Option.some.injEq] using eq
    have tag : before[i].1 = after[i].1 :=
      congrArg (fun value => value.1) item
    simp only [dif_pos ha, dif_pos hb, tag]
    split
    · exact congrFun (congrFun (congrFun (congrArg Prod.snd item) t) fuel) st
    · exact evalMatchArm_congr t fuel before after fallback fallback' same default scrut st (i + 1)
  · have hb : ¬ i < after.size := by omega
    simp only [dif_neg ha, dif_neg hb]
    exact default st
termination_by before.size - i

private def branchStep (shared : SharedData) (degrees : Array Nat)
    (acc : Array (G × Block) × SharedData) (pair : G × Block) :
    LayoutM (Array (G × Block) × SharedData) := do
  setSharedData shared
  let block ← relayoutBlock pair.2
  let used ← getSharedData
  setDegrees degrees
  pure (acc.1.push (pair.1, block), acc.2.maximals used)

private theorem branchFold_code (items : List (G × Block))
    (shared : SharedData) (degrees : Array Nat)
    (acc : Array (G × Block) × SharedData) (initial : LayoutMState)
    (effect : ∀ pair ∈ items, ∀ state,
      blockCode ((relayoutBlock pair.2).run state).1 = blockCode pair.2) :
    (((items.foldlM (branchStep shared degrees) acc).run initial).1.1.map branchCode).toList =
      (acc.1.map branchCode).toList ++ items.map branchCode := by
  induction items generalizing acc initial with
  | nil => simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
  | cons pair items ih =>
    rw [List.foldlM_cons]
    have first := effect pair List.mem_cons_self
      ((setSharedData shared).run initial).2
    have rest := ih ((branchStep shared degrees acc pair).run initial).1
      ((branchStep shared degrees acc pair).run initial).2
      (fun pair member => effect pair (List.mem_cons_of_mem _ member))
    change _ = _ at rest
    change (((items.foldlM (branchStep shared degrees)
      ((branchStep shared degrees acc pair).run initial).1).run
      ((branchStep shared degrees acc pair).run initial).2).1.1.map branchCode).toList = _
    rw [rest]
    change ((acc.1.push (pair.1, ((relayoutBlock pair.2).run
      ((setSharedData shared).run initial).2).1)).map branchCode).toList ++ _ = _
    simp only [Array.map_push, Array.toList_push, branchCode, first,
      List.map_cons, List.append_assoc, List.cons_append, List.nil_append]

private theorem branchLoop_code (branches : Array (G × Block))
    (shared : SharedData) (degrees : Array Nat) (initial : LayoutMState)
    (effect : ∀ pair ∈ branches.toList, ∀ state,
      blockCode ((relayoutBlock pair.2).run state).1 = blockCode pair.2) :
    ((branches.attach.foldlM (fun acc pair => branchStep shared degrees acc pair.val)
      (#[], shared)).run initial).1.1.map branchCode = branches.map branchCode := by
  rw [← Array.foldlM_toList, Array.toList_attach, ← List.foldlM_map,
    List.attachWith_map_subtype_val]
  apply Array.toList_inj.mp
  simpa only [Array.map_empty, Array.toList_empty, List.nil_append, Array.toList_map] using
    branchFold_code branches.toList shared degrees (#[], shared) initial effect

private theorem branch_smaller {branches : Array (G × Block)} {pair : G × Block}
    (member : pair ∈ branches.toList) : sizeOf pair.2 < sizeOf branches := by
  have bound := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp member)
  cases pair
  simp at bound ⊢
  omega

mutual

private theorem relayoutCtrl_code (ctrl : Ctrl) (initial : LayoutMState)
    (t : Toplevel) (fuel : Nat) (st : EvalState) :
    evalCtrl t fuel ((relayoutCtrl ctrl).run initial).1 st = evalCtrl t fuel ctrl st := by
  cases ctrl with
  | «return» sel outs => rw [relayoutCtrl.eq_def]; rfl
  | «yield» sel outs => rw [relayoutCtrl.eq_def]; rfl
  | «match» index branches fallback =>
    let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
    let loop := branches.attach.foldlM
      (fun acc pair => branchStep shared initial.degrees acc pair.val) (#[], shared)
    have same := branchLoop_code branches shared initial.degrees initial
      (fun pair member state => relayoutBlock_code pair.2 state)
    rw [relayoutCtrl.eq_def]
    cases fallback with
    | none =>
      change evalCtrl t fuel (.match index (loop.run initial).1.1 none) st = _
      simp only [evalCtrl]
      cases readIdx st index with
      | error e => rfl
      | ok scrut => exact evalMatchArm_congr t fuel _ _ none none same (fun _ => rfl) scrut st 0
    | some block =>
      let before := ((bumpAuxiliaries (loop.run initial).1.1.size).run
        ((setSharedData shared).run (loop.run initial).2).2).2
      change evalCtrl t fuel (.match index (loop.run initial).1.1
        (some ((relayoutBlock block).run before).1)) st = _
      simp only [evalCtrl]
      cases readIdx st index with
      | error e => rfl
      | ok scrut =>
        apply evalMatchArm_congr t fuel _ _ (some ((relayoutBlock block).run before).1)
          (some block) same ?_ scrut st 0
        intro state
        simpa only [evalDefaultBlock, blockCode] using
          congrFun (congrFun (congrFun (relayoutBlock_code block before) t) fuel) state
  | matchContinue index branches fallback size aux slots cont =>
    let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
    let loop := branches.attach.foldlM
      (fun acc pair => branchStep shared initial.degrees acc pair.val) (#[], shared)
    have same := branchLoop_code branches shared initial.degrees initial
      (fun pair member state => relayoutBlock_code pair.2 state)
    rw [relayoutCtrl.eq_def]
    cases fallback with
    | none =>
      change evalCtrl t fuel (.matchContinue index (loop.run initial).1.1 none size _ _
        ((relayoutBlock cont).run _).1) st = _
      simp only [evalCtrl]
      cases readIdx st index with
      | error e => rfl
      | ok scrut =>
        dsimp only
        rw [evalMatchArm_congr t fuel _ _ none none same (fun _ => rfl) scrut st 0]
        cases evalMatchArm t fuel branches none scrut st with
        | error e => rfl
        | ok result => exact congrFun (congrFun (congrFun (relayoutBlock_code cont _) t) fuel) _
    | some block =>
      let before := ((bumpAuxiliaries (loop.run initial).1.1.size).run
        ((setSharedData shared).run (loop.run initial).2).2).2
      have default : ∀ st, evalDefaultBlock t fuel
          (some ((relayoutBlock block).run before).1) st =
          evalDefaultBlock t fuel (some block) st := fun st => by
        simpa only [evalDefaultBlock, blockCode] using congrFun
          (congrFun (congrFun (relayoutBlock_code block before) t) fuel) st
      change evalCtrl t fuel (.matchContinue index (loop.run initial).1.1
        (some ((relayoutBlock block).run before).1) size _ _
        ((relayoutBlock cont).run _).1) st = _
      simp only [evalCtrl]
      cases readIdx st index with
      | error e => rfl
      | ok scrut =>
        dsimp only
        rw [evalMatchArm_congr t fuel _ _ (some ((relayoutBlock block).run before).1)
          (some block) same default scrut st 0]
        cases evalMatchArm t fuel branches (some block) scrut st with
        | error e => rfl
        | ok result => exact congrFun (congrFun (congrFun (relayoutBlock_code cont _) t) fuel) _
termination_by (sizeOf ctrl, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := branch_smaller member; grind)
    | grind

private theorem relayoutBlock_code (block : Block) (initial : LayoutMState) :
    blockCode ((relayoutBlock block).run initial).1 = blockCode block := by
  funext t fuel st
  rw [relayoutBlock.eq_def]
  change evalBlock t fuel { ops := block.ops, ctrl := ((relayoutCtrl block.ctrl).run
    ((block.ops.forM opLayout).run initial).2).1 } st = evalBlock t fuel block st
  simp only [evalBlock]
  cases runOps t fuel block.ops st 0 with
  | error e => rfl
  | ok st' => exact relayoutCtrl_code block.ctrl _ t fuel st'
termination_by (sizeOf block, 1)
decreasing_by
  cases block
  simp_wf
  omega

end

/-- Recomputing continuation allocations preserves the complete evaluator result. -/
theorem relayoutBlock_preserves_execution (block : Block) (initial : LayoutMState)
    (t : Toplevel) (fuel : Nat) (st : EvalState) :
    evalBlock t fuel ((relayoutBlock block).run initial).1 st = evalBlock t fuel block st :=
  congrFun (congrFun (congrFun (relayoutBlock_code block initial) t) fuel) st

private theorem branchFold_context (items : List (G × Block))
    (shared : SharedData) (degrees : Array Nat)
    (acc : Array (G × Block) × SharedData) (initial : LayoutMState)
    (effect : ∀ pair ∈ items, ∀ state,
      ((relayoutBlock pair.2).run state).2.context =
        state.context) :
    ((items.foldlM (branchStep shared degrees) acc).run initial).2.context =
      initial.context := by
  induction items generalizing acc initial with
  | nil => rfl
  | cons pair items ih =>
    rw [List.foldlM_cons]
    have first := effect pair List.mem_cons_self
      ((setSharedData shared).run initial).2
    have rest := ih ((branchStep shared degrees acc pair).run initial).1
      ((branchStep shared degrees acc pair).run initial).2
      (fun pair member => effect pair (List.mem_cons_of_mem _ member))
    exact rest.trans first

private theorem branchLoop_context (branches : Array (G × Block))
    (shared : SharedData) (degrees : Array Nat) (initial : LayoutMState)
    (effect : ∀ pair ∈ branches.toList, ∀ state,
      ((relayoutBlock pair.2).run state).2.context =
        state.context) :
    ((branches.attach.foldlM (fun acc pair => branchStep shared degrees acc pair.val)
      (#[], shared)).run initial).2.context = initial.context := by
  rw [← Array.foldlM_toList, Array.toList_attach, ← List.foldlM_map,
    List.attachWith_map_subtype_val]
  exact branchFold_context branches.toList shared degrees (#[], shared) initial effect

mutual

theorem relayoutCtrl_context (ctrl : Ctrl) (initial : LayoutMState) :
    ((relayoutCtrl ctrl).run initial).2.context =
      initial.context := by
  cases ctrl with
  | «return» sel outs => rw [relayoutCtrl.eq_def]; rfl
  | «yield» sel outs => rw [relayoutCtrl.eq_def]; rfl
  | «match» index branches fallback =>
    let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
    let loop := branches.attach.foldlM
      (fun acc pair => branchStep shared initial.degrees acc pair.val) (#[], shared)
    have fixed := branchLoop_context branches shared initial.degrees initial
      (fun pair member state => relayoutBlock_context pair.2 state)
    rw [relayoutCtrl.eq_def]
    cases fallback with
    | none => exact fixed
    | some block =>
      let before := ((bumpAuxiliaries (loop.run initial).1.1.size).run
        ((setSharedData shared).run (loop.run initial).2).2).2
      exact (relayoutBlock_context block before).trans fixed
  | matchContinue index branches fallback size aux slots cont =>
    let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
    let loop := branches.attach.foldlM
      (fun acc pair => branchStep shared initial.degrees acc pair.val) (#[], shared)
    have fixed := branchLoop_context branches shared initial.degrees initial
      (fun pair member state => relayoutBlock_context pair.2 state)
    rw [relayoutCtrl.eq_def]
    cases fallback with
    | none =>
      change ((relayoutBlock cont).run _).2.context = _
      exact (relayoutBlock_context cont _).trans fixed
    | some block =>
      let before := ((bumpAuxiliaries (loop.run initial).1.1.size).run
        ((setSharedData shared).run (loop.run initial).2).2).2
      have default := (relayoutBlock_context block before).trans fixed
      change ((relayoutBlock cont).run _).2.context = _
      exact (relayoutBlock_context cont _).trans default
termination_by (sizeOf ctrl, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := branch_smaller member; grind)
    | grind

theorem relayoutBlock_context (block : Block) (initial : LayoutMState) :
    ((relayoutBlock block).run initial).2.context =
      initial.context := by
  rw [relayoutBlock.eq_def]
  exact (relayoutCtrl_context block.ctrl _).trans (opsLayout_context block.ops initial)
termination_by (sizeOf block, 1)
decreasing_by
  cases block
  simp_wf
  omega

end

theorem relayoutCtrl_inputSize (ctrl : Ctrl) (initial : LayoutMState) :
    ((relayoutCtrl ctrl).run initial).2.functionLayout.inputSize = initial.functionLayout.inputSize :=
  congrArg Prod.fst (relayoutCtrl_context ctrl initial)

theorem relayoutBlock_inputSize (block : Block) (initial : LayoutMState) :
    ((relayoutBlock block).run initial).2.functionLayout.inputSize = initial.functionLayout.inputSize :=
  congrArg Prod.fst (relayoutBlock_context block initial)

theorem relayoutCtrl_callRanks (ctrl : Ctrl) (initial : LayoutMState) :
    ((relayoutCtrl ctrl).run initial).2.callRanks = initial.callRanks :=
  congrArg Prod.snd (relayoutCtrl_context ctrl initial)

theorem relayoutBlock_callRanks (block : Block) (initial : LayoutMState) :
    ((relayoutBlock block).run initial).2.callRanks = initial.callRanks :=
  congrArg Prod.snd (relayoutBlock_context block initial)

theorem blockLayout_callRanks (block : Block) (initial : LayoutMState) :
    ((blockLayout block).run initial).2.callRanks = initial.callRanks := by
  rw [blockLayout_eq_discard_relayout]
  exact relayoutBlock_callRanks block initial

theorem ctrlLayout_callRanks (ctrl : Ctrl) (initial : LayoutMState) :
    ((ctrlLayout ctrl).run initial).2.callRanks = initial.callRanks :=
  relayoutCtrl_callRanks ctrl initial

end Aiur.Concrete.Bytecode

namespace Aiur.Bytecode
open Concrete.Bytecode

/-- The checked component pass preserves instruction behavior and input arity.
Its continuation metadata and other circuit layout fields may change. -/
theorem Toplevel.withCallComponents_sameCode (top : Toplevel) :
    Eval.SameCode top.withCallComponents top := by
  unfold Toplevel.withCallComponents
  dsimp only
  split
  · exact ⟨rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · constructor
    · simp only [Array.size_mapIdx]
    · intro i ha hb t fuel st
      simp only [Array.getElem_mapIdx]
      exact relayoutBlock_preserves_execution _ _ t fuel st
    · intro i ha hb
      simp only [Array.getElem_mapIdx]
      exact relayoutBlock_inputSize _ _

end Aiur.Bytecode
