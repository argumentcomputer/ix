/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CompilerBranches

/-! The compiler preserves input width, counts every leaf selector, and
retains the reserved auxiliary columns through branches and continuations. -/

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode

private theorem ops_fold_fields (ops : List Op) (initial : LayoutMState) :
    let final := ((ops.foldlM (fun _ op => opLayout op) ()).run initial).2.functionLayout
    final.inputSize = initial.functionLayout.inputSize ∧
    final.selectors = initial.functionLayout.selectors ∧
    initial.functionLayout.auxiliaries ≤ final.auxiliaries := by
  induction ops generalizing initial with
  | nil => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | cons op ops ih =>
    rw [List.foldlM_cons]
    have fixed := opLayout_fixed op initial
    have allocated := (opLayout_allocation op initial).2
    have rest := ih ((opLayout op).run initial).2
    exact ⟨rest.1.trans fixed.1, rest.2.1.trans fixed.2,
      Nat.le_trans (by rw [allocated]; exact Nat.le_add_right _ _) rest.2.2⟩

theorem opsLayout_fields (ops : Array Op) (initial : LayoutMState) :
    let final := ((ops.forM opLayout).run initial).2.functionLayout
    final.inputSize = initial.functionLayout.inputSize ∧
    final.selectors = initial.functionLayout.selectors ∧
    initial.functionLayout.auxiliaries ≤ final.auxiliaries := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact ops_fold_fields ops.toList initial

theorem allocationBranchStep_fields (shared : SharedData) (degrees : Array Nat) (acc : SharedData)
    (block : Block) (initial : LayoutMState)
    (effect : ∀ state : LayoutMState,
      ((blockLayout block).run state).2.functionLayout.inputSize = state.functionLayout.inputSize ∧
      ((blockLayout block).run state).2.functionLayout.selectors =
        state.functionLayout.selectors + block.controlCounts.leaves) :
    let final := (allocationBranchStep shared degrees acc block).run initial
    final.2.functionLayout.inputSize = initial.functionLayout.inputSize ∧
    final.2.functionLayout.selectors = initial.functionLayout.selectors + block.controlCounts.leaves ∧
    acc.auxiliaries ≤ final.1.auxiliaries := by
  have body := effect ((setSharedData shared).run initial).2
  exact ⟨body.1, body.2, Nat.le_max_left _ _⟩

theorem allocationBranchFold_fields {α : Type} (items : List α) (blockOf : α → Block)
    (shared : SharedData) (degrees : Array Nat) (acc : SharedData) (initial : LayoutMState)
    (effect : ∀ item ∈ items, ∀ state : LayoutMState,
      ((blockLayout (blockOf item)).run state).2.functionLayout.inputSize = state.functionLayout.inputSize ∧
      ((blockLayout (blockOf item)).run state).2.functionLayout.selectors =
        state.functionLayout.selectors + (blockOf item).controlCounts.leaves) :
    let final := (items.foldlM (fun acc item => allocationBranchStep shared degrees acc (blockOf item)) acc).run initial
    final.2.functionLayout.inputSize = initial.functionLayout.inputSize ∧
    final.2.functionLayout.selectors = initial.functionLayout.selectors +
      (items.map (fun item => (blockOf item).controlCounts.leaves)).sum ∧
    acc.auxiliaries ≤ final.1.auxiliaries := by
  induction items generalizing acc initial with
  | nil => exact ⟨rfl, (Nat.add_zero _).symm, Nat.le_refl _⟩
  | cons item items ih =>
    rw [List.foldlM_cons]
    have first := allocationBranchStep_fields shared degrees acc (blockOf item) initial
      (effect item List.mem_cons_self)
    have rest := ih ((allocationBranchStep shared degrees acc (blockOf item)).run initial).1
      ((allocationBranchStep shared degrees acc (blockOf item)).run initial).2
      (fun item member => effect item (List.mem_cons_of_mem _ member))
    refine ⟨rest.1.trans first.1, ?_, Nat.le_trans first.2.2 rest.2.2⟩
    exact rest.2.1.trans (by rw [first.2.1]; simp only [List.map_cons, List.sum_cons, Nat.add_assoc])

theorem matchLayout_fields (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (initial : LayoutMState)
    (caseEffect : ∀ pair ∈ branches.toList, ∀ state : LayoutMState,
      ((blockLayout pair.2).run state).2.functionLayout.inputSize = state.functionLayout.inputSize ∧
      ((blockLayout pair.2).run state).2.functionLayout.selectors =
        state.functionLayout.selectors + pair.2.controlCounts.leaves)
    (defaultEffect : ∀ block, fallback = some block → ∀ state : LayoutMState,
      ((blockLayout block).run state).2.functionLayout.inputSize = state.functionLayout.inputSize ∧
      ((blockLayout block).run state).2.functionLayout.selectors =
        state.functionLayout.selectors + block.controlCounts.leaves) :
    let final := ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout
    final.inputSize = initial.functionLayout.inputSize ∧
    final.selectors = initial.functionLayout.selectors +
      (ControlCounts.sum (branchControlCounts branches fallback)).leaves ∧
    initial.functionLayout.auxiliaries ≤ final.auxiliaries := by
  let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
  let loop : LayoutM SharedData := branches.attach.foldlM
    (fun acc pair => allocationBranchStep shared initial.degrees acc pair.val.2) shared
  have loopResult : (loop.run initial).2.functionLayout.inputSize = initial.functionLayout.inputSize ∧
      (loop.run initial).2.functionLayout.selectors = initial.functionLayout.selectors +
        (branches.toList.map (fun pair => pair.2.controlCounts.leaves)).sum ∧
      initial.functionLayout.auxiliaries ≤ (loop.run initial).1.auxiliaries := by
    dsimp only [loop]
    rw [allocationBranchLoop]
    exact allocationBranchFold_fields branches.toList Prod.snd shared initial.degrees shared initial caseEffect
  rw [ctrlLayout_eq_def]
  cases present : fallback with
  | none =>
    change (loop.run initial).2.functionLayout.inputSize = _ ∧
      (loop.run initial).2.functionLayout.selectors = _ ∧
      initial.functionLayout.auxiliaries ≤ (loop.run initial).1.auxiliaries
    simpa only [branchControlCounts, ControlCounts.sum, Option.toList_none, List.map_nil,
      List.append_nil, List.map_map, Function.comp_def] using loopResult
  | some block =>
    let before := ((bumpAuxiliaries branches.size).run ((setSharedData shared).run (loop.run initial).2).2).2
    have body := defaultEffect block present before
    change ((blockLayout block).run before).2.functionLayout.inputSize = _ ∧
      ((blockLayout block).run before).2.functionLayout.selectors = _ ∧
      initial.functionLayout.auxiliaries ≤ max (loop.run initial).1.auxiliaries _
    refine ⟨body.1.trans loopResult.1, ?_, Nat.le_trans loopResult.2.2 (Nat.le_max_left _ _)⟩
    rw [body.2]
    change (loop.run initial).2.functionLayout.selectors + block.controlCounts.leaves = _
    rw [loopResult.2.1]
    simp only [branchControlCounts, ControlCounts.sum, Option.toList_some, List.map_cons,
      List.map_nil, List.map_append, List.map_map, Function.comp_def, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]

private theorem layout_case_smaller {branches : Array (G × Block)} {pair : G × Block}
    (member : pair ∈ branches.toList) : sizeOf pair.2 < sizeOf branches := by
  have bound := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp member)
  cases pair
  simp at bound ⊢
  omega

private theorem layout_default_smaller {fallback : Option Block} {block : Block}
    (present : fallback = some block) : sizeOf block < sizeOf fallback := by
  rw [present]
  simp

mutual

theorem ctrlLayout_fields (ctrl : Ctrl) (initial : LayoutMState) :
    let final := ((ctrlLayout ctrl).run initial).2.functionLayout
    final.inputSize = initial.functionLayout.inputSize ∧
    final.selectors = initial.functionLayout.selectors + ctrl.controlCounts.leaves ∧
    initial.functionLayout.auxiliaries ≤ final.auxiliaries := by
  cases ctrl with
  | «return» index indices | yield index indices =>
    rw [ctrlLayout_eq_def, Ctrl.controlCounts.eq_def]
    exact ⟨rfl, rfl, Nat.le_refl _⟩
  | «match» index branches fallback =>
    rw [Ctrl.controlCounts_match]
    exact matchLayout_fields index branches fallback initial
      (fun pair member state => ⟨(blockLayout_fields pair.2 state).1, (blockLayout_fields pair.2 state).2.1⟩)
      (fun block present state => ⟨(blockLayout_fields block state).1, (blockLayout_fields block state).2.1⟩)
  | matchContinue index branches fallback size aux slots continuation =>
    have first := matchLayout_fields index branches fallback initial
      (fun pair member state => ⟨(blockLayout_fields pair.2 state).1, (blockLayout_fields pair.2 state).2.1⟩)
      (fun block present state => ⟨(blockLayout_fields block state).1, (blockLayout_fields block state).2.1⟩)
    let before := ((pushDegrees (.replicate size 1)).run ((bumpAuxiliaries size).run
      ((ctrlLayout (.match index branches fallback)).run initial).2).2).2
    have rest := blockLayout_fields continuation before
    rw [ctrlLayout_continue, Ctrl.controlCounts_matchContinue]
    refine ⟨rest.1.trans first.1, ?_, ?_⟩
    · change ((blockLayout continuation).run before).2.functionLayout.selectors = _
      rw [rest.2.1]
      change ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.selectors + _ = _
      rw [first.2.1, Nat.add_assoc]
      rfl
    · have monotone := rest.2.2
      change ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.auxiliaries + size ≤ _ at monotone
      exact Nat.le_trans first.2.2 (Nat.le_trans (Nat.le_add_right _ _) monotone)
termination_by sizeOf ctrl
decreasing_by
  all_goals subst ctrl
  all_goals first
    | (have bound := layout_case_smaller ‹_ ∈ _›; simp; omega)
    | (have bound := layout_default_smaller ‹_ = some _›; simp; omega)
    | decreasing_tactic

theorem blockLayout_fields (block : Block) (initial : LayoutMState) :
    let final := ((blockLayout block).run initial).2.functionLayout
    final.inputSize = initial.functionLayout.inputSize ∧
    final.selectors = initial.functionLayout.selectors + block.controlCounts.leaves ∧
    initial.functionLayout.auxiliaries ≤ final.auxiliaries := by
  rw [blockLayout, Block.controlCounts]
  have first := opsLayout_fields block.ops initial
  have rest := ctrlLayout_fields block.ctrl ((block.ops.forM opLayout).run initial).2
  exact ⟨rest.1.trans first.1, rest.2.1.trans (congrArg (· + block.ctrl.controlCounts.leaves) first.2.1),
    Nat.le_trans first.2.2 rest.2.2⟩
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

theorem ctrlLayout_match_list (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    ctrlLayout (.match index branches fallback) = (do
      let shared ← getSharedData
      let degrees ← getDegrees
      let acc ← branches.toList.foldlM (fun acc pair => allocationBranchStep shared degrees acc pair.2) shared
      let final ← match fallback with
        | none => pure acc
        | some block => do
          setSharedData shared
          bumpAuxiliaries branches.size
          blockLayout block
          let used ← getSharedData
          setDegrees degrees
          pure (acc.maximals used)
      setSharedData final) := by
  rw [ctrlLayout_eq_def]
  change (do
    let shared ← getSharedData
    let degrees ← getDegrees
    let acc ← branches.attach.foldlM
      (fun acc (pair : {pair // pair ∈ branches}) => allocationBranchStep shared degrees acc pair.val.2) shared
    let final ← match fallback with
      | none => pure acc
      | some block => do
        setSharedData shared
        bumpAuxiliaries branches.size
        blockLayout block
        let used ← getSharedData
        setDegrees degrees
        pure (acc.maximals used)
    setSharedData final) = _
  simp only [allocationBranchLoop]

/-- Renaming preserves physical layout when it preserves the selected call
mode. The empty table used before component analysis satisfies this property. -/
def LayoutRenaming (rename : FunIdx → FunIdx) (ranks : Array CallRank) : Prop :=
  ∀ function, ranks[rename function]?.getD .ordered = ranks[function]?.getD .ordered

theorem layoutRenaming_empty (rename : FunIdx → FunIdx) : LayoutRenaming rename #[] := by
  intro function
  simp

theorem rewriteOp_layout (rename : FunIdx → FunIdx) (op : Op) (initial : LayoutMState)
    (compatible : LayoutRenaming rename initial.callRanks) :
    (opLayout (rewriteOp rename op)).run initial = (opLayout op).run initial := by
  cases op
  case call function args outputSize unconstrained =>
    cases unconstrained <;>
      simp [rewriteOp, opLayout, bumpLookups, bumpAuxiliaries, pushDegrees,
        StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
        get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
        bind, pure, compatible function]
  all_goals rfl

private theorem rewrite_branches_list (rename : FunIdx → FunIdx) (branches : Array (G × Block)) :
    (branches.attach.map fun ⟨(tag, block), _⟩ => (tag, rewriteBlock rename block)).toList =
      branches.toList.map (fun pair => (pair.1, rewriteBlock rename pair.2)) := by
  simp only [Array.toList_map, Array.toList_attach]
  exact List.attachWith_map_val (f := fun pair : G × Block => (pair.1, rewriteBlock rename pair.2)) _

private theorem foldlM_layout_equal {α β : Type} (items : List α)
    (first second : β → α → LayoutM β) (ranks : Array CallRank)
    (equal : ∀ item ∈ items, ∀ acc state, state.callRanks = ranks →
      (first acc item).run state = (second acc item).run state)
    (preserved : ∀ item ∈ items, ∀ acc state,
      ((second acc item).run state).2.callRanks = state.callRanks)
    (acc : β) (initial : LayoutMState) (aligned : initial.callRanks = ranks) :
    (items.foldlM first acc).run initial = (items.foldlM second acc).run initial := by
  induction items generalizing acc initial with
  | nil => rfl
  | cons item items ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    change (let next := (first acc item).run initial;
      (items.foldlM first next.1).run next.2) =
      (let next := (second acc item).run initial;
        (items.foldlM second next.1).run next.2)
    rw [equal item List.mem_cons_self acc initial aligned]
    exact ih (fun item member => equal item (List.mem_cons_of_mem _ member))
      (fun item member => preserved item (List.mem_cons_of_mem _ member))
      ((second acc item).run initial).1 ((second acc item).run initial).2
      ((preserved item List.mem_cons_self acc initial).trans aligned)

theorem matchLayout_rewrite (rename : FunIdx → FunIdx) (index : ValIdx)
    (branches : Array (G × Block)) (fallback : Option Block)
    (ranks : Array CallRank) (initial : LayoutMState) (aligned : initial.callRanks = ranks)
    (caseEqual : ∀ pair ∈ branches.toList, ∀ state, state.callRanks = ranks →
      (blockLayout (rewriteBlock rename pair.2)).run state = (blockLayout pair.2).run state)
    (defaultEqual : ∀ block, fallback = some block → ∀ state, state.callRanks = ranks →
      (blockLayout (rewriteBlock rename block)).run state = (blockLayout block).run state) :
    (ctrlLayout (.match index
      (branches.attach.map fun ⟨(tag, block), _⟩ => (tag, rewriteBlock rename block))
      (fallback.map (rewriteBlock rename)))).run initial = (ctrlLayout (.match index branches fallback)).run initial := by
  rw [ctrlLayout_match_list, ctrlLayout_match_list, rewrite_branches_list]
  simp only [List.foldlM_map]
  let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
  let loop := branches.toList.foldlM
    (fun acc pair => allocationBranchStep shared initial.degrees acc pair.2) shared
  have loops :
      (branches.toList.foldlM
        (fun acc pair => allocationBranchStep shared initial.degrees acc (rewriteBlock rename pair.2)) shared).run initial =
        loop.run initial := by
    apply foldlM_layout_equal _ _ _ ranks ?_ ?_ shared initial aligned
    · intro pair member acc state stateRanks
      change (let result := (blockLayout (rewriteBlock rename pair.2)).run ((setSharedData shared).run state).2;
        (acc.maximals ⟨result.2.functionLayout.auxiliaries, result.2.functionLayout.lookups⟩,
          ((setDegrees initial.degrees).run result.2).2)) = _
      rw [caseEqual pair member ((setSharedData shared).run state).2 stateRanks]
      rfl
    · intro pair _ acc state
      exact allocationBranchStep_callRanks shared initial.degrees acc pair.2 state
  simp only [Array.size_map, Array.size_attach]
  cases present : fallback with
  | none =>
    change (let result := (branches.toList.foldlM
      (fun acc pair => allocationBranchStep shared initial.degrees acc (rewriteBlock rename pair.2)) shared).run initial;
      (setSharedData result.1).run result.2) = _
    rw [loops]
    rfl
  | some block =>
    let before := ((bumpAuxiliaries branches.size).run
      ((setSharedData shared).run (loop.run initial).2).2).2
    have beforeRanks : before.callRanks = ranks :=
      (allocationBranchFold_callRanks branches.toList Prod.snd shared initial.degrees shared initial).trans aligned
    change (let branchResult := (branches.toList.foldlM
        (fun acc pair => allocationBranchStep shared initial.degrees acc (rewriteBlock rename pair.2)) shared).run initial;
      let result := (blockLayout (rewriteBlock rename block)).run
        ((bumpAuxiliaries branches.size).run ((setSharedData shared).run branchResult.2).2).2;
      (setSharedData (branchResult.1.maximals
        ⟨result.2.functionLayout.auxiliaries, result.2.functionLayout.lookups⟩)).run
        ((setDegrees initial.degrees).run result.2).2) = _
    rw [loops]
    dsimp only
    rw [defaultEqual block present before beforeRanks]
    rfl

mutual

theorem rewriteCtrl_layout (rename : FunIdx → FunIdx) (ctrl : Ctrl) (initial : LayoutMState)
    (compatible : LayoutRenaming rename initial.callRanks) :
    (ctrlLayout (rewriteCtrl rename ctrl)).run initial = (ctrlLayout ctrl).run initial := by
  cases ctrl with
  | «return» index indices | yield index indices => rw [rewriteCtrl.eq_def]
  | «match» index branches fallback =>
    rw [rewriteCtrl.eq_def]
    have equal := matchLayout_rewrite rename index branches fallback
      initial.callRanks initial rfl
      (fun pair member state aligned => rewriteBlock_layout rename pair.2 state (aligned ▸ compatible))
      (fun block present state aligned => rewriteBlock_layout rename block state (aligned ▸ compatible))
    cases fallback <;> exact equal
  | matchContinue index branches fallback size aux slots continuation =>
    rw [rewriteCtrl.eq_def, ctrlLayout_continue, ctrlLayout_continue]
    have equal := matchLayout_rewrite rename index branches fallback
      initial.callRanks initial rfl
      (fun pair member state aligned => rewriteBlock_layout rename pair.2 state (aligned ▸ compatible))
      (fun block present state aligned => rewriteBlock_layout rename block state (aligned ▸ compatible))
    cases fallback <;> simp only [Option.map_none, Option.map_some] at equal ⊢
    all_goals
      change (blockLayout (rewriteBlock rename continuation)).run
        ((pushDegrees (.replicate size 1)).run ((bumpAuxiliaries size).run
          ((ctrlLayout _).run initial).2).2).2 = _
      rw [equal]
      apply rewriteBlock_layout
      change LayoutRenaming rename ((ctrlLayout _).run initial).2.callRanks
      rw [ctrlLayout_callRanks]
      exact compatible
termination_by sizeOf ctrl
decreasing_by
  all_goals subst ctrl
  all_goals first
    | (have bound := layout_case_smaller ‹_ ∈ _›; simp; omega)
    | (have bound := layout_default_smaller ‹_ = some _›; simp; omega)
    | decreasing_tactic

theorem rewriteBlock_layout (rename : FunIdx → FunIdx) (block : Block) (initial : LayoutMState)
    (compatible : LayoutRenaming rename initial.callRanks) :
    (blockLayout (rewriteBlock rename block)).run initial = (blockLayout block).run initial := by
  have operations : ((block.ops.map (rewriteOp rename)).forM opLayout).run initial =
      (block.ops.forM opLayout).run initial := by
    simp only [Array.forM, ← Array.foldlM_toList, Array.toList_map, List.foldlM_map]
    apply foldlM_layout_equal _ _ _ initial.callRanks ?_ ?_ () initial rfl
    · intro op _ _ state aligned
      exact rewriteOp_layout rename op state (aligned ▸ compatible)
    · intro op _ _ state
      exact opLayout_callRanks op state
  rw [rewriteBlock, blockLayout, blockLayout]
  change (ctrlLayout (rewriteCtrl rename block.ctrl)).run
    (((block.ops.map (rewriteOp rename)).forM opLayout).run initial).2 = _
  rw [operations]
  exact rewriteCtrl_layout rename block.ctrl ((block.ops.forM opLayout).run initial).2
    (by
      change LayoutRenaming rename ((block.ops.forM opLayout).run initial).2.context.2
      rw [opsLayout_context]
      exact compatible)
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

end Aiur.Concrete.Bytecode
