/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitMembership
import Ix.Aiur.Proofs.Relayout

/-!
For the generic rank layout, the compiler's lookup allocation equals the valued emitter's physical extent.
The equality is preserved by function renaming and deduplication; final
compilation and grouping bound every member by its selected circuit layout.
Canonical trace execution therefore needs no independent per-witness lookup
limit or shape hypothesis. Native extraction, memory validity and the complete
compiler and certified semantic/cryptographic endpoint remain obligations.
-/

namespace Aiur.Bytecode

def Op.lookupUsage : Op → Nat
  | .call _ _ _ unconstrained => if unconstrained then 0 else 4
  | .store _ | .load _ _ | .u8BitDecomposition _ | .u8ShiftLeft _ | .u8ShiftRight _
  | .u8Xor .. | .u8And .. | .u8Or .. | .u8Add .. | .u8Sub .. | .u8Mul ..
  | .u8XorSplit7 .. | .u8XorSplit4 .. | .u8LessThan .. | .u8RangeCheck .. => 1
  | .u32LessThan .. => 6
  | _ => 0

private theorem lookup_block_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def Ctrl.lookupUsage : Ctrl → Nat
  | .return .. | .yield .. => 0
  | .match _ branches fallback => (
      (branches.attach.toList.map fun ⟨pair, _⟩ => pair.2.lookupUsage) ++
      (match fallback with | none => [] | some block => [block.lookupUsage])).foldl Nat.max 0
  | .matchContinue _ branches fallback _ _ _ continuation => (
      (branches.attach.toList.map fun ⟨pair, _⟩ => pair.2.lookupUsage) ++
      (match fallback with | none => [] | some block => [block.lookupUsage])).foldl Nat.max 0 +
        continuation.lookupUsage
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.lookupUsage (block : Block) : Nat :=
  (block.ops.toList.map Op.lookupUsage).sum + block.ctrl.lookupUsage
termination_by sizeOf block
decreasing_by exact lookup_block_smaller block

end

def branchLookupUsage (branches : Array (G × Block)) (fallback : Option Block) : Nat :=
  (branches.toList.map (fun pair => pair.2.lookupUsage) ++
    fallback.toList.map (fun block => block.lookupUsage)).foldl Nat.max 0

theorem Ctrl.lookupUsage_match (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).lookupUsage = branchLookupUsage branches fallback := by
  rw [Ctrl.lookupUsage.eq_def]
  simp only [branchLookupUsage, Array.toList_attach]
  rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.lookupUsage)]
  cases fallback <;> rfl

theorem Ctrl.lookupUsage_matchContinue (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (outputs aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback outputs aux lookups continuation).lookupUsage =
      branchLookupUsage branches fallback + continuation.lookupUsage := by
  rw [Ctrl.lookupUsage.eq_def]
  simp only [branchLookupUsage, Array.toList_attach]
  rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.lookupUsage)]
  cases fallback <;> rfl

end Aiur.Bytecode

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode Std.Do

private theorem list_getDegree (indices : List ValIdx) (initial : LayoutMState) :
    (indices.mapM getDegree).run initial = (indices.map (fun i => initial.degrees[i]?.getD 0), initial) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    rw [List.mapM_cons]
    change (let (values, final) := (indices.mapM getDegree).run initial;
      (initial.degrees[index]?.getD 0 :: values, final)) =
      (initial.degrees[index]?.getD 0 :: indices.map (fun i => initial.degrees[i]?.getD 0), initial)
    rw [ih]

private theorem array_getDegree (indices : Array ValIdx) :
    indices.mapM getDegree = (fun initial => pure (indices.map (fun i => initial.degrees[i]?.getD 0), initial)) := by
  rw [Array.mapM_eq_mapM_toList]
  funext initial
  change (let (values, final) := (indices.toList.mapM getDegree).run initial;
      (values.toArray, final)) = (indices.map (fun i => initial.degrees[i]?.getD 0), initial)
  rw [list_getDegree]
  simp only [← List.map_toArray, Array.toArray_toList]

set_option mvcgen.warning false in
theorem opLayout_lookupUsage (op : Op) (initial : LayoutMState)
    (generic : initial.callRanks = #[]) :
    ((opLayout op).run initial).2.functionLayout.lookups = initial.functionLayout.lookups + op.lookupUsage := by
  cases op
  case call function args outputSize unconstrained =>
    cases unconstrained <;>
      simp [opLayout, Op.lookupUsage, bumpLookups, bumpAuxiliaries, pushDegrees,
        StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
        get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
        bind, pure, generic, Nat.add_assoc]
  all_goals
    simp only [opLayout, array_getDegree] <;>
    apply StateM.of_wp_run_eq rfl (fun result : Unit × LayoutMState =>
      result.2.functionLayout.lookups = _)
  all_goals
    mvcgen [opLayout, array_getDegree, bumpLookups, bumpAuxiliaries, getDegree, getDegrees,
      pushDegree, pushDegrees, addMemSize]
  all_goals simp_all [Op.lookupUsage]
  all_goals try rfl

private theorem ops_fold_lookupUsage (ops : List Op) (initial : LayoutMState)
    (generic : initial.callRanks = #[]) :
    ((ops.foldlM (fun _ op => opLayout op) ()).run initial).2.functionLayout.lookups =
      initial.functionLayout.lookups + (ops.map Op.lookupUsage).sum := by
  induction ops generalizing initial with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldlM_cons]
    change ((ops.foldlM (fun _ op => opLayout op) ()).run ((opLayout op).run initial).2).2.functionLayout.lookups = _
    rw [ih _ ((opLayout_callRanks op initial).trans generic), opLayout_lookupUsage op initial generic,
      List.map_cons, List.sum_cons, Nat.add_assoc]

theorem opsLayout_lookupUsage (ops : Array Op) (initial : LayoutMState)
    (generic : initial.callRanks = #[]) :
    ((ops.forM opLayout).run initial).2.functionLayout.lookups =
      initial.functionLayout.lookups + (ops.toList.map Op.lookupUsage).sum := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact ops_fold_lookupUsage ops.toList initial generic

private def branchLayoutStep (shared : SharedData) (degrees : Array Nat) (acc : SharedData)
    (block : Block) : LayoutM SharedData := do
  setSharedData shared
  blockLayout block
  let used ← getSharedData
  setDegrees degrees
  return acc.maximals used

private theorem branchLayoutStep_callRanks (shared : SharedData) (degrees : Array Nat)
    (acc : SharedData) (block : Block) (initial : LayoutMState) :
    ((branchLayoutStep shared degrees acc block).run initial).2.callRanks = initial.callRanks :=
  blockLayout_callRanks block ((setSharedData shared).run initial).2

private theorem branchFold_callRanks {α : Type} (items : List α) (blockOf : α → Block)
    (shared : SharedData) (degrees : Array Nat) (acc : SharedData) (initial : LayoutMState) :
    ((items.foldlM (fun acc item => branchLayoutStep shared degrees acc (blockOf item)) acc).run initial).2.callRanks =
      initial.callRanks := by
  induction items generalizing acc initial with
  | nil => rfl
  | cons item items ih =>
    rw [List.foldlM_cons]
    exact (ih ((branchLayoutStep shared degrees acc (blockOf item)).run initial).1
      ((branchLayoutStep shared degrees acc (blockOf item)).run initial).2).trans
      (branchLayoutStep_callRanks shared degrees acc (blockOf item) initial)

private theorem branchLayoutStep_lookupUsage (shared : SharedData) (degrees : Array Nat) (acc : SharedData)
    (block : Block) (initial : LayoutMState)
    (generic : initial.callRanks = #[])
    (effect : ∀ state, state.callRanks = #[] → ((blockLayout block).run state).2.functionLayout.lookups =
      state.functionLayout.lookups + block.lookupUsage) :
    ((branchLayoutStep shared degrees acc block).run initial).1.lookups =
      max acc.lookups (shared.lookups + block.lookupUsage) := by
  change max acc.lookups ((blockLayout block).run ((setSharedData shared).run initial).2).2.functionLayout.lookups = _
  rw [effect ((setSharedData shared).run initial).2 generic]
  rfl

private theorem branchFold_lookupUsage {α : Type} (items : List α) (blockOf : α → Block)
    (shared : SharedData) (degrees : Array Nat) (acc : SharedData) (initial : LayoutMState)
    (start : Nat) (aligned : acc.lookups = shared.lookups + start)
    (generic : initial.callRanks = #[])
    (effect : ∀ item ∈ items, ∀ state, state.callRanks = #[] →
      ((blockLayout (blockOf item)).run state).2.functionLayout.lookups =
      state.functionLayout.lookups + (blockOf item).lookupUsage) :
    ((items.foldlM (fun acc item => branchLayoutStep shared degrees acc (blockOf item)) acc).run initial).1.lookups =
      shared.lookups + (items.map (fun item => (blockOf item).lookupUsage)).foldl Nat.max start := by
  induction items generalizing acc initial start with
  | nil => exact aligned
  | cons item items ih =>
    rw [List.foldlM_cons]
    change ((items.foldlM (fun acc item => branchLayoutStep shared degrees acc (blockOf item))
        ((branchLayoutStep shared degrees acc (blockOf item)).run initial).1).run
        ((branchLayoutStep shared degrees acc (blockOf item)).run initial).2).1.lookups = _
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ _ _
      ((branchLayoutStep_callRanks shared degrees acc (blockOf item) initial).trans generic)
      (fun item member => effect item (List.mem_cons_of_mem _ member))
    rw [branchLayoutStep_lookupUsage shared degrees acc (blockOf item) initial generic
      (effect item List.mem_cons_self), aligned, Nat.add_max_add_left]

private theorem matchLayout_lookupUsage (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (initial : LayoutMState)
    (generic : initial.callRanks = #[])
    (caseEffect : ∀ pair ∈ branches.toList, ∀ state, state.callRanks = #[] →
      ((blockLayout pair.2).run state).2.functionLayout.lookups =
      state.functionLayout.lookups + pair.2.lookupUsage)
    (defaultEffect : ∀ block, fallback = some block → ∀ state, state.callRanks = #[] →
      ((blockLayout block).run state).2.functionLayout.lookups =
        state.functionLayout.lookups + block.lookupUsage) :
    ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.lookups =
      initial.functionLayout.lookups + branchLookupUsage branches fallback := by
  let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
  let loop : LayoutM SharedData := branches.attach.foldlM (init := shared)
    fun acc pair => branchLayoutStep shared initial.degrees acc pair.val.2
  have loopCount : (loop.run initial).1.lookups = initial.functionLayout.lookups +
      (branches.toList.map (fun pair => pair.2.lookupUsage)).foldl Nat.max 0 := by
    dsimp only [loop]
    rw [← Array.foldlM_toList]
    have count := branchFold_lookupUsage branches.attach.toList (fun pair => pair.val.2)
      shared initial.degrees shared initial 0 (Nat.add_zero _).symm
      generic
      (fun pair _ => caseEffect pair.val (Array.mem_def.mp pair.property))
    simp only [Array.toList_attach] at count ⊢
    rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.lookupUsage)] at count
    exact count
  have loopGeneric : (loop.run initial).2.callRanks = #[] := by
    dsimp only [loop]
    rw [← Array.foldlM_toList]
    exact (branchFold_callRanks branches.attach.toList (fun pair => pair.val.2)
      shared initial.degrees shared initial).trans generic
  rw [ctrlLayout_eq_def]
  cases fallbackEq : fallback with
  | none =>
    change (loop.run initial).1.lookups = _
    simpa only [branchLookupUsage, fallbackEq, Option.toList_none, List.map_nil, List.append_nil] using loopCount
  | some block =>
    change max (loop.run initial).1.lookups
      ((blockLayout block).run ((bumpAuxiliaries branches.size).run
        ((setSharedData shared).run (loop.run initial).2).2).2).2.functionLayout.lookups = _
    rw [defaultEffect block fallbackEq ((bumpAuxiliaries branches.size).run
      ((setSharedData shared).run (loop.run initial).2).2).2 loopGeneric]
    change max (loop.run initial).1.lookups (initial.functionLayout.lookups + block.lookupUsage) = _
    rw [loopCount, Nat.add_max_add_left]
    simp only [branchLookupUsage, Option.toList_some, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]

end Aiur.Concrete.Bytecode

namespace Aiur.Bytecode

def Function.LookupLayout (function : Function) : Prop :=
  function.layout.lookups = 4 + function.body.lookupUsage

def FunctionsLookupLayout (functions : Array Function) : Prop :=
  ∀ function ∈ functions, function.LookupLayout

private theorem functionsLookupLayout_empty : FunctionsLookupLayout #[] := by
  simp [FunctionsLookupLayout]

private theorem functionsLookupLayout_push {functions : Array Function} {function : Function}
    (before : FunctionsLookupLayout functions) (valid : function.LookupLayout) :
    FunctionsLookupLayout (functions.push function) := by
  intro fn member
  rcases Array.mem_push.mp member with prior | equal
  · exact before fn prior
  · subst fn; exact valid

end Aiur.Bytecode

namespace Aiur.AIR
open Bytecode

theorem emitOp_lookupUsage {row : Nat → G} {selector rank : G} {op : Op}
    {values : Array RowValue} {emission : OpEmission}
    (emitted : emitOp row selector rank op values = some emission) :
    emission.queries.length = op.lookupUsage := by
  cases op <;> simp only [emitOp, emitByte1, emitByte2, emitU32LessThan, emitU32Add,
    emitAdvice, bind, Option.bind, Option.map, pure] at emitted
  all_goals
    repeat' first
      | split at emitted
      | (dsimp only at emitted; split at emitted)
  all_goals cases emitted
  all_goals simp_all [Op.lookupUsage, rankByteQueries, range4Queries]

theorem emitOps_lookupUsage {row : Nat → G} {selector rank : G} {ops : List Op}
    {values : Array RowValue} {column : Nat} {emission : OpsEmission}
    (emitted : emitOps row selector rank ops values column = some emission) :
    emission.queries.length = (ops.map Op.lookupUsage).sum := by
  induction ops generalizing values column emission with
  | nil =>
    have equal := Option.some.inj emitted
    subst emission
    rfl
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i first firstEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i rest restEmitted
        have equal := Option.some.inj emitted
        subst emission
        simp only [List.length_append, List.map_cons, List.sum_cons,
          emitOp_lookupUsage firstEmitted, ih restEmitted]

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

private theorem lookup_fold_related {blocks : List Block} {emissions : List BlockEmission} {lookup : Nat}
    (related : List.Forall₂ (fun block emission => emission.lookup = lookup + block.lookupUsage) blocks emissions)
    (acc : Nat) :
    emissions.foldl (fun value emission => max value emission.lookup) (lookup + acc) =
      lookup + (blocks.map Block.lookupUsage).foldl Nat.max acc := by
  induction related generalizing acc with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldl_cons, List.map_cons, first, Nat.add_max_add_left]
    exact ih _

theorem branchRows_lookupUsage (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (caseSound : ∀ pair ∈ branches.toList, ∀ emission,
      pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup = some emission →
      emission.lookup = lookup + pair.2.lookupUsage)
    (defaultSound : ∀ block, fallback = some block → ∀ emission,
      block.emitRow row selector context (block.selectorFlow selector).entry values
        (column + branches.size) lookup = some emission →
      emission.lookup = lookup + block.lookupUsage) :
    emission.lookup = lookup + branchLookupUsage branches fallback := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i cases casesEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i default defaultEmitted
      have equal := Option.some.inj emitted
      subst emission
      have casesRelated : List.Forall₂ (fun block emission => emission.lookup = lookup + block.lookupUsage)
          (branches.toList.map Prod.snd) cases := by
        apply forall₂_map_left
        apply mapM_forall₂ casesEmitted
        intro pair member emission emitted
        simp only [caseRow, bind, Option.bind] at emitted
        split at emitted
        · cases emitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj emitted
          subst emission
          exact caseSound pair member body bodyEmitted
      have defaultRelated : List.Forall₂ (fun block emission => emission.lookup = lookup + block.lookupUsage)
          fallback.toList default := by
        cases fallbackEq : fallback with
        | none =>
          simp only [defaultRow, fallbackEq, Option.some.injEq] at defaultEmitted
          subst default
          exact .nil
        | some block =>
          simp only [defaultRow, fallbackEq, bind, Option.bind] at defaultEmitted
          split at defaultEmitted
          · cases defaultEmitted
          · rename_i body bodyEmitted
            have equal := Option.some.inj defaultEmitted
            subst default
            exact .cons (defaultSound block fallbackEq body bodyEmitted) .nil
      have joined := lookup_fold_related (forall₂_append casesRelated defaultRelated) 0
      simpa only [Nat.add_zero, joinBlockEmissions, branchLookupUsage, List.map_append,
        List.map_map, Function.comp_def] using joined

private theorem lookup_pair_smaller (pair : G × Block) : sizeOf pair.2 < sizeOf pair := by
  cases pair
  simp
  omega

private theorem lookup_option_smaller {fallback : Option Block} {block : Block}
    (present : fallback = some block) : sizeOf block < sizeOf fallback := by
  rw [present]
  simp

mutual

theorem Ctrl.emitRow_lookupUsage (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (ctrl : Ctrl)
    {emission : BlockEmission}
    (emitted : ctrl.emitRow row selector context incoming values column lookup = some emission) :
    emission.lookup = lookup + ctrl.lookupUsage := by
  cases ctrlEq : ctrl with
  | «return» index indices =>
    rw [ctrlEq] at emitted
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · dsimp only at emitted
      split at emitted
      · cases emitted
      · have equal := Option.some.inj emitted
        subst emission
        simp only [Ctrl.lookupUsage, Nat.add_zero]
  | yield index indices =>
    rw [ctrlEq] at emitted
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · have equal := Option.some.inj emitted
      subst emission
      simp only [Ctrl.lookupUsage, Nat.add_zero]
  | «match» index branches fallback =>
    rw [ctrlEq] at emitted
    rw [Ctrl.lookupUsage_match]
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      apply branchRows_lookupUsage row selector context matched.value values column lookup branches fallback emitted
      · intro pair member body bodyEmitted
        exact Block.emitRow_lookupUsage row selector context _ values column lookup pair.2 bodyEmitted
      · intro block present body bodyEmitted
        exact Block.emitRow_lookupUsage row selector context _ values _ lookup block bodyEmitted
  | matchContinue index branches fallback size aux slots continuation =>
    rw [ctrlEq] at emitted
    rw [Ctrl.lookupUsage_matchContinue]
    rw [Ctrl.emitRow_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i joined branchesEmitted
        simp only [continueRow] at emitted
        split at emitted
        · simp only [bind, Option.bind] at emitted
          split at emitted
          · cases emitted
          · rename_i continued contEmitted
            have equal := Option.some.inj emitted
            subst emission
            have joinedLookup := branchRows_lookupUsage row selector context matched.value values column lookup
              branches fallback branchesEmitted
              (fun pair member body bodyEmitted =>
                Block.emitRow_lookupUsage row selector context _ values column lookup pair.2 bodyEmitted)
              (fun block present body bodyEmitted =>
                Block.emitRow_lookupUsage row selector context _ values _ lookup block bodyEmitted)
            have contLookup := Block.emitRow_lookupUsage row selector context _ _ _ _ continuation contEmitted
            simpa only [BlockEmission.continued, joinedLookup, Nat.add_assoc] using contLookup
        · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals
    try rw [ctrlEq]
    first
    | (have bound := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member)
       have pairBound := lookup_pair_smaller pair
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (have optionBound := lookup_option_smaller present
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (simp only [Ctrl.matchContinue.sizeOf_spec]; omega)

theorem Block.emitRow_lookupUsage (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission) :
    emission.lookup = lookup + block.lookupUsage := by
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i operations opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control ctrlEmitted
      have controlLookup := Ctrl.emitRow_lookupUsage row selector context incoming _ _ _ block.ctrl ctrlEmitted
      have equal := Option.some.inj emitted
      subst emission
      simpa only [BlockEmission.prefix, BlockEmission.afterOps, Block.lookupUsage,
        emitOps_lookupUsage opsEmitted, Nat.add_assoc] using controlLookup
termination_by sizeOf block
decreasing_by exact lookup_block_smaller block

end

end Aiur.Bytecode

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode

private theorem ctrlLayout_matchContinue (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (size aux slots : Nat) (continuation : Block) :
    ctrlLayout (.matchContinue index branches fallback size aux slots continuation) = (do
      ctrlLayout (.match index branches fallback)
      bumpAuxiliaries size
      pushDegrees (.replicate size 1)
      blockLayout continuation) := by
  exact ctrlLayout_eq_def _

mutual

theorem ctrlLayout_lookupUsage (ctrl : Ctrl) (initial : LayoutMState)
    (generic : initial.callRanks = #[]) :
    ((ctrlLayout ctrl).run initial).2.functionLayout.lookups =
      initial.functionLayout.lookups + ctrl.lookupUsage := by
  cases ctrlEq : ctrl with
  | «return» index indices =>
    rw [ctrlLayout_eq_def, Ctrl.lookupUsage.eq_def]
    rfl
  | yield index indices =>
    rw [ctrlLayout_eq_def, Ctrl.lookupUsage.eq_def]
    rfl
  | «match» index branches fallback =>
    rw [Ctrl.lookupUsage_match]
    apply matchLayout_lookupUsage index branches fallback initial generic
    · intro pair member state stateGeneric
      exact blockLayout_lookupUsage pair.2 state stateGeneric
    · intro block present state stateGeneric
      exact blockLayout_lookupUsage block state stateGeneric
  | matchContinue index branches fallback size aux slots continuation =>
    rw [ctrlLayout_matchContinue, Ctrl.lookupUsage_matchContinue]
    change ((blockLayout continuation).run ((pushDegrees (.replicate size 1)).run
      ((bumpAuxiliaries size).run ((ctrlLayout (.match index branches fallback)).run initial).2).2).2).2.functionLayout.lookups = _
    rw [blockLayout_lookupUsage continuation ((pushDegrees (.replicate size 1)).run
      ((bumpAuxiliaries size).run ((ctrlLayout (.match index branches fallback)).run initial).2).2).2
      ((ctrlLayout_callRanks _ initial).trans generic)]
    change ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.lookups +
      continuation.lookupUsage = _
    have first := matchLayout_lookupUsage index branches fallback initial generic
      (fun pair member state stateGeneric => blockLayout_lookupUsage pair.2 state stateGeneric)
      (fun block present state stateGeneric => blockLayout_lookupUsage block state stateGeneric)
    rw [first, Nat.add_assoc]
termination_by sizeOf ctrl
decreasing_by
  all_goals
    try rw [ctrlEq]
    first
    | (have bound := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member)
       have pairBound := lookup_pair_smaller pair
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (have optionBound := lookup_option_smaller present
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (simp only [Ctrl.matchContinue.sizeOf_spec]; omega)

theorem blockLayout_lookupUsage (block : Block) (initial : LayoutMState)
    (generic : initial.callRanks = #[]) :
    ((blockLayout block).run initial).2.functionLayout.lookups =
      initial.functionLayout.lookups + block.lookupUsage := by
  rw [blockLayout]
  change ((ctrlLayout block.ctrl).run ((block.ops.forM opLayout).run initial).2).2.functionLayout.lookups = _
  rw [ctrlLayout_lookupUsage _ _ ((congrArg Prod.snd (opsLayout_context block.ops initial)).trans generic),
    opsLayout_lookupUsage _ initial generic, Block.lookupUsage, Nat.add_assoc]
termination_by sizeOf block
decreasing_by exact lookup_block_smaller block

end

end Aiur.Concrete.Bytecode

namespace Aiur.Concrete
open Aiur.Bytecode

private theorem layout_result_lookupUsage {body : Block} {size : Nat} {state : Bytecode.LayoutMState}
    {resultUnit : Unit} (computed : (Bytecode.blockLayout body).run (.new size) = (resultUnit, state)) :
    state.functionLayout.lookups + 1 = 4 + body.lookupUsage := by
  have count := Bytecode.blockLayout_lookupUsage body (.new size) rfl
  rw [computed] at count
  simp only [Bytecode.LayoutMState.new] at count
  omega

theorem Function.compile_lookupLayout {layoutMap : LayoutMap} {function : Function}
    {body : Block} {state : Bytecode.LayoutMState}
    (compiled : function.compile layoutMap = .ok (body, state)) :
    state.functionLayout.lookups = 4 + body.lookupUsage := by
  unfold Function.compile at compiled
  simp only [bind, Except.bind, pure, Except.pure] at compiled
  repeat' first
    | split at compiled
    | (dsimp only at compiled; split at compiled)
  all_goals cases compiled
  all_goals
    change _ + 1 = 4 + _
    exact layout_result_lookupUsage (by assumption)

open Std.Do

private theorem except_post {ε α : Type} (action : Except ε α) (property : α → Prop)
    (valid : ∀ value, action = .ok value → property value) :
    ⦃⌜True⌝⦄ action ⦃post⟨fun value => ⌜property value⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases computed : action with
  | error error =>
    change ⦃⌜True⌝⦄ (throw error : Except ε α) ⦃post⟨fun value => ⌜property value⌝, fun _ => ⌜True⌝⟩⦄
    simp [Triple.iff]
  | ok value =>
    change ⦃⌜True⌝⦄ (pure value : Except ε α) ⦃post⟨fun value => ⌜property value⌝, fun _ => ⌜True⌝⟩⦄
    simpa [Triple.iff] using valid value computed

private theorem lookup_throw {ε α : Type} {error : ε} {post : PostCond α (.except ε .pure)} :
    Triple (ps := .except ε .pure) (throw error : Except ε α) (spred(post.2.1 error)) post := by
  simp [Triple.iff]

private theorem layoutMap_spec (decls : Decls) :
    ⦃⌜True⌝⦄ decls.layoutMap ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ :=
  except_post decls.layoutMap (fun _ => True) (fun _ _ => trivial)

set_option mvcgen.warning false in
theorem Decls.toBytecode_lookupLayout {decls : Decls} {program : Toplevel}
    {names : Std.HashMap Global FunIdx} (compiled : decls.toBytecode = .ok (program, names)) :
    FunctionsLookupLayout program.functions := by
  have spec : ⦃⌜True⌝⦄ decls.toBytecode
      ⦃post⟨fun result => ⌜FunctionsLookupLayout result.1.functions⌝, fun _ => ⌜True⌝⟩⦄ := by
    mvcgen [Decls.toBytecode, IndexMap.foldlM, ← Array.foldlM_toList,
      layoutMap_spec, -Spec.throw_Except, lookup_throw] invariants
    · post⟨fun ⟨_, functions, _⟩ => ⌜FunctionsLookupLayout functions⌝, fun _ => ⌜True⌝⟩
    case vc2.step.h_1.h_2 =>
      apply functionsLookupLayout_push (by assumption)
      exact Function.compile_lookupLayout (by assumption)
    case vc4.success.pre => exact functionsLookupLayout_empty
  exact Except.of_wp_eq compiled (fun result => match result with
    | .error _ => True
    | .ok result => FunctionsLookupLayout result.1.functions) spec

end Aiur.Concrete

namespace Aiur.Bytecode

theorem rewriteOp_lookupUsage (rename : FunIdx → FunIdx) (op : Op) :
    (rewriteOp rename op).lookupUsage = op.lookupUsage := by
  cases op <;> rfl

private theorem branchLookupUsage_rewrite (rename : FunIdx → FunIdx)
    (branches : Array (G × Block)) (fallback : Option Block)
    (caseEqual : ∀ pair ∈ branches.toList, (rewriteBlock rename pair.2).lookupUsage = pair.2.lookupUsage)
    (defaultEqual : ∀ block, fallback = some block → (rewriteBlock rename block).lookupUsage = block.lookupUsage) :
  branchLookupUsage (branches.attach.map fun ⟨(tag, block), _⟩ => (tag, rewriteBlock rename block))
      (fallback.map (rewriteBlock rename)) =
      branchLookupUsage branches fallback := by
  unfold branchLookupUsage
  apply congrArg (fun values : List Nat => values.foldl Nat.max 0)
  congr 1
  · simp only [Array.toList_map, Array.toList_attach, List.map_map, Function.comp_def]
    rw [← List.attachWith_map_val (p := fun pair => pair ∈ branches)
      (f := fun pair : G × Block => pair.2.lookupUsage) (fun _ member => Array.mem_def.mpr member)]
    apply List.map_congr_left
    intro pair member
    rcases pair with ⟨⟨tag, block⟩, present⟩
    exact caseEqual (tag, block) (Array.mem_def.mp present)
  · cases fallbackEq : fallback with
    | none => rfl
    | some block =>
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil]
      rw [defaultEqual block fallbackEq]

mutual

theorem rewriteCtrl_lookupUsage (rename : FunIdx → FunIdx) (ctrl : Ctrl) :
    (rewriteCtrl rename ctrl).lookupUsage = ctrl.lookupUsage := by
  cases ctrlEq : ctrl with
  | «return» index indices => rw [rewriteCtrl.eq_def]
  | yield index indices => rw [rewriteCtrl.eq_def]
  | «match» index branches fallback =>
    rw [rewriteCtrl.eq_def, Ctrl.lookupUsage_match, Ctrl.lookupUsage_match]
    have equal := branchLookupUsage_rewrite rename branches fallback
      (fun pair member => rewriteBlock_lookupUsage rename pair.2)
      (fun block present => rewriteBlock_lookupUsage rename block)
    cases fallback <;> exact equal
  | matchContinue index branches fallback size aux slots continuation =>
    rw [rewriteCtrl.eq_def, Ctrl.lookupUsage_matchContinue, Ctrl.lookupUsage_matchContinue,
      rewriteBlock_lookupUsage rename continuation]
    congr 1
    have equal := branchLookupUsage_rewrite rename branches fallback
      (fun pair member => rewriteBlock_lookupUsage rename pair.2)
      (fun block present => rewriteBlock_lookupUsage rename block)
    cases fallback <;> exact equal
termination_by sizeOf ctrl
decreasing_by
  all_goals
    try rw [ctrlEq]
    first
    | (have bound := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member)
       have pairBound := lookup_pair_smaller pair
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (have optionBound := lookup_option_smaller present
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (simp only [Ctrl.matchContinue.sizeOf_spec]; omega)

theorem rewriteBlock_lookupUsage (rename : FunIdx → FunIdx) (block : Block) :
    (rewriteBlock rename block).lookupUsage = block.lookupUsage := by
  rw [rewriteBlock, Block.lookupUsage, Block.lookupUsage, rewriteCtrl_lookupUsage]
  simp only [Array.toList_map, List.map_map, Function.comp_def, rewriteOp_lookupUsage]
termination_by sizeOf block
decreasing_by exact lookup_block_smaller block

end

theorem deduplicate_newFunctions_lookupLayout (functions : Array Function)
    (classes : Array Nat) (canonical : Array Bool) (rename : FunIdx → FunIdx)
    (valid : FunctionsLookupLayout functions) :
    FunctionsLookupLayout (deduplicate_newFunctions functions classes canonical rename) := by
  unfold deduplicate_newFunctions
  apply Array.foldl_induction (fun _ result => FunctionsLookupLayout result) functionsLookupLayout_empty
  intro index accumulated before
  dsimp only
  split
  · apply functionsLookupLayout_push before
    change (((classes.zip canonical).zip functions)[index]).2.layout.lookups =
      4 + (rewriteBlock rename (((classes.zip canonical).zip functions)[index]).2.body).lookupUsage
    rw [rewriteBlock_lookupUsage]
    apply valid
    exact (Array.of_mem_zip (Array.getElem_mem index.isLt)).2
  · exact before

theorem Toplevel.deduplicateCandidate_lookupLayout (program : Toplevel)
    (valid : FunctionsLookupLayout program.functions) :
    FunctionsLookupLayout program.deduplicateCandidate.1.functions := by
  unfold Toplevel.deduplicateCandidate
  dsimp only
  split
  · exact valid
  · exact deduplicate_newFunctions_lookupLayout _ _ _ _ valid

theorem Toplevel.deduplicate_lookupLayout (program : Toplevel)
    (valid : FunctionsLookupLayout program.functions) :
    FunctionsLookupLayout program.deduplicate.1.functions := by
  unfold Toplevel.deduplicate checkedRenaming
  dsimp only
  split
  · exact program.deduplicateCandidate_lookupLayout valid
  · exact valid

end Aiur.Bytecode

namespace Aiur
open Bytecode

theorem finishCompilation_lookupLayout (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) (valid : FunctionsLookupLayout raw.functions)
    (generic : source.componentRanks = false) :
    FunctionsLookupLayout (finishCompilation source raw names).bytecode.functions := by
  unfold finishCompilation
  simp only [generic, Bool.false_eq_true, if_false]
  intro function member
  obtain ⟨index, bound, equal⟩ := Array.exists_of_mem_mapIdx member
  subst function
  change raw.deduplicate.1.functions[index].LookupLayout
  exact raw.deduplicate_lookupLayout valid _ (Array.getElem_mem bound)

theorem Source.Toplevel.compile_lookupLayout {source : Source.Toplevel} {compiled : CompiledToplevel}
    (accepted : source.compile = .ok compiled) (generic : source.componentRanks = false) :
    FunctionsLookupLayout compiled.bytecode.functions := by
  obtain ⟨inlined, typed, concrete, raw, names, inlinedOk, _, _, lowered, artifact⟩ :=
    source.compile_artifact_of_ok accepted
  rw [artifact]
  exact finishCompilation_lookupLayout inlined raw names (Concrete.Decls.toBytecode_lookupLayout lowered)
    ((Source.Toplevel.inlineCalls_componentRanks inlinedOk).trans generic)

theorem BoundVerifier.Backend.functions_lookupLayout {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) (generic : selection.source.componentRanks = false) :
    FunctionsLookupLayout backend.compiled.bytecode.functions := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  have valid := Source.Toplevel.compile_lookupLayout compiled generic
  split at grouped
  · cases grouped
    exact valid
  · rw [(CompiledToplevel.groupFunctions_preserves_code grouped).2.2.1]
    exact valid

end Aiur

namespace Aiur.Bytecode

def MembersLookupBound (functions : Array Function) (members : Array FunIdx) (slots : Nat) : Prop :=
  4 ≤ slots ∧ ∀ index ∈ members, functions[index]!.layout.lookups ≤ slots

def CircuitsLookupBound (functions : Array Function) (circuits : Array Circuit) : Prop :=
  ∀ circuit ∈ circuits, MembersLookupBound functions circuit.members circuit.layout.lookups

private theorem lookup_circuits_empty (functions : Array Function) : CircuitsLookupBound functions #[] := by
  simp [CircuitsLookupBound]

private theorem lookup_circuits_push {functions : Array Function} {circuits : Array Circuit} {circuit : Circuit}
    (before : CircuitsLookupBound functions circuits)
    (member : MembersLookupBound functions circuit.members circuit.layout.lookups) :
    CircuitsLookupBound functions (circuits.push circuit) := by
  intro c present
  rcases Array.mem_push.mp present with prior | equal
  · exact before c prior
  · subst c; exact member

private theorem lookup_member_singleton {functions : Array Function} {index : FunIdx} {function : Function}
    (present : functions[index]? = some function) (valid : function.LookupLayout) :
    MembersLookupBound functions #[index] function.layout.lookups := by
  constructor
  · change function.layout.lookups = 4 + function.body.lookupUsage at valid
    omega
  · intro i member
    have equal : i = index := by simpa using member
    subst i
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, present]
    exact Nat.le_refl _

open Std.Do

set_option mvcgen.warning false in
theorem singletonCircuits_lookupBound (program : Toplevel) (nameOf : FunIdx → String)
    (valid : FunctionsLookupLayout program.functions) :
    CircuitsLookupBound program.functions (program.singletonCircuits nameOf) := by
  have spec : Triple (m := Id) (program.singletonCircuits nameOf) ⌜True⌝
      (⇓ circuits => ⌜CircuitsLookupBound program.functions circuits⌝) := by
    mvcgen [Toplevel.singletonCircuits, Id.run] invariants
    · ⇓⟨_, circuits⟩ => ⌜CircuitsLookupBound program.functions circuits⌝
    case vc1.step.isTrue =>
      apply lookup_circuits_push (by assumption)
      exact lookup_member_singleton (Array.getElem?_eq_getElem _) (valid _ (Array.getElem_mem _))
    case vc3.pre => exact lookup_circuits_empty _
  exact Id.of_wp_run_eq rfl _ spec

private theorem lookup_bang_of_present {functions : Array Function} {index : Nat} {function : Function}
    (present : functions[index]? = some function) : functions[index]! = function := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, present]
  rfl

private theorem lookup_array_bang {α : Type} [Inhabited α] (property : α → Prop)
    {array : Array α} (valid : ∀ value ∈ array, property value) (fallback : property default) (index : Nat) :
    property array[index]! := by
  by_cases bound : index < array.size
  · rw [getElem!_pos array index bound]
    exact valid _ (Array.getElem_mem bound)
  · rw [getElem!_neg array index bound]
    exact fallback

private theorem lookup_first_reserved {functions : Array Function} {members : Array FunIdx}
    (valid : FunctionsLookupLayout functions) (nonempty : 0 < functions.size)
    (constrained : MembersConstrained functions members) :
    4 ≤ functions[members[0]!]!.layout.lookups := by
  refine lookup_array_bang (fun index : FunIdx => 4 ≤ functions[index]!.layout.lookups)
    (array := members) ?_ ?_ 0
  · intro index member
    obtain ⟨function, present, _⟩ := constrained index member
    rw [lookup_bang_of_present present]
    have bound := valid function (Array.mem_of_getElem? present)
    change function.layout.lookups = 4 + function.body.lookupUsage at bound
    omega
  · change 4 ≤ functions[0]!.layout.lookups
    rw [getElem!_pos functions 0 nonempty]
    have bound := valid _ (Array.getElem_mem nonempty)
    change functions[0].layout.lookups = 4 + functions[0].body.lookupUsage at bound
    omega

private theorem lookup_merge_fold (functions : Array Function) (first : FunIdx) (members : List FunIdx)
    (initial : FunctionLayout) (firstBound : functions[first]!.layout.lookups ≤ initial.lookups) :
    let final := members.foldl (fun acc index => if index == first then acc else acc.merge functions[index]!.layout) initial
    initial.lookups ≤ final.lookups ∧ ∀ index ∈ members, functions[index]!.layout.lookups ≤ final.lookups := by
  induction members generalizing initial with
  | nil => exact ⟨Nat.le_refl _, by simp⟩
  | cons index members ih =>
    let next := if index == first then initial else initial.merge functions[index]!.layout
    have before : initial.lookups ≤ next.lookups := by
      dsimp only [next]
      split
      · exact Nat.le_refl _
      · exact Nat.le_max_left _ _
    have here : functions[index]!.layout.lookups ≤ next.lookups := by
      dsimp only [next]
      split
      · rename_i equal
        have eq : index = first := beq_iff_eq.mp equal
        subst index
        exact firstBound
      · exact Nat.le_max_right _ _
    have rest := ih next (Nat.le_trans firstBound before)
    refine ⟨Nat.le_trans before rest.1, ?_⟩
    intro chosen member
    rcases List.mem_cons.mp member with equal | later
    · subst chosen; exact Nat.le_trans here rest.1
    · exact rest.2 chosen later

theorem merged_lookupBound (functions : Array Function) (members : Array FunIdx)
    (valid : FunctionsLookupLayout functions) (nonempty : 0 < functions.size)
    (constrained : MembersConstrained functions members) :
    MembersLookupBound functions members
      (members.foldl (init := functions[members[0]!]!.layout)
        fun acc index => if index == members[0]! then acc else acc.merge functions[index]!.layout).lookups := by
  rw [← Array.foldl_toList]
  have folded := lookup_merge_fold functions members[0]! members.toList functions[members[0]!]!.layout
    (Nat.le_refl _)
  exact ⟨Nat.le_trans (lookup_first_reserved valid nonempty constrained) folded.1,
    fun index member => folded.2 index (Array.mem_def.mp member)⟩

end Aiur.Bytecode

namespace Aiur
open Bytecode Std.Do

private theorem lookup_throw_except {ε α : Type} {error : ε} {post : PostCond α (.except ε .pure)} :
    Triple (ps := .except ε .pure) (throw error : Except ε α) (spred(post.2.1 error)) post := by
  simp [Triple.iff]

private theorem lookup_members_empty (functions : Array Function) : MembersConstrained functions #[] := by
  simp [MembersConstrained]

private theorem lookup_members_push {functions : Array Function} {members : Array FunIdx} {index : FunIdx}
    (before : MembersConstrained functions members) (constrained : functions[index]!.constrained = true) :
    MembersConstrained functions (members.push index) := by
  intro i member
  rcases Array.mem_push.mp member with prior | equal
  · exact before i prior
  · subst i
    by_cases bound : index < functions.size
    · exact ⟨functions[index], Array.getElem?_eq_getElem bound,
        by simpa only [getElem!_pos functions index bound] using constrained⟩
    · rw [getElem!_neg functions index bound] at constrained
      contradiction

private theorem lookup_split_member {α : Type} {array : Array α} {pref suff : List α} {value : α}
    (split : array.toList = pref ++ value :: suff) : value ∈ array := by
  apply Array.mem_toList_iff.mp
  rw [split]
  simp

set_option mvcgen.warning false in
theorem CompiledToplevel.groupFunctions_lookupBound {before after : CompiledToplevel}
    {groups : Array (String × Array String)}
    (functions : FunctionsLookupLayout before.bytecode.functions)
    (nonempty : 0 < before.bytecode.functions.size)
    (valid : CircuitsLookupBound before.bytecode.functions before.bytecode.circuits)
    (accepted : before.groupFunctions groups = .ok after) :
    CircuitsLookupBound after.bytecode.functions after.bytecode.circuits := by
  have spec : ⦃⌜True⌝⦄ before.groupFunctions groups
      ⦃post⟨fun compiled => ⌜CircuitsLookupBound compiled.bytecode.functions compiled.bytecode.circuits⌝,
        fun _ => ⌜True⌝⟩⦄ := by
    mvcgen [CompiledToplevel.groupFunctions, -Spec.throw_Except, lookup_throw_except] invariants
    · post⟨fun ⟨_, _, resolved⟩ => ⌜∀ pair ∈ resolved,
        MembersConstrained before.bytecode.functions pair.2⌝, fun _ => ⌜True⌝⟩
    · post⟨fun ⟨_, _, members⟩ => ⌜MembersConstrained before.bytecode.functions members⌝,
        fun _ => ⌜True⌝⟩
    · post⟨fun ⟨_, circuits, _⟩ => ⌜CircuitsLookupBound before.bytecode.functions circuits⌝,
        fun _ => ⌜True⌝⟩
    case vc4.step.h_1.isTrue.isFalse.isFalse => exact lookup_members_push (by assumption) (by assumption)
    case vc7.step.isFalse.pre => exact lookup_members_empty _
    case vc8.step.isFalse.post.success =>
      intro pair member
      rcases Array.mem_push.mp member with prior | equal
      · apply_assumption; exact prior
      · subst pair; assumption
    case vc10.pre =>
      change ∀ pair ∈ (#[] : Array (String × Array FunIdx)), _
      simp
    case vc11.step.isTrue.h_1 =>
      apply lookup_circuits_push (by assumption)
      apply valid
      exact lookup_split_member (by assumption)
    case vc13.step.isTrue.h_2.isFalse =>
      apply lookup_circuits_push (by assumption)
      apply merged_lookupBound _ _ functions nonempty
      exact lookup_array_bang (fun pair : String × Array FunIdx =>
        MembersConstrained before.bytecode.functions pair.2) (by assumption) (lookup_members_empty _) _
    case vc15.post.success.pre => exact lookup_circuits_empty _
  exact Except.of_wp_eq accepted (fun result => match result with
    | .error _ => True
    | .ok compiled => CircuitsLookupBound compiled.bytecode.functions compiled.bytecode.circuits) spec

theorem finishCompilation_lookupBound (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) (valid : FunctionsLookupLayout raw.functions)
    (generic : source.componentRanks = false) :
    CircuitsLookupBound (finishCompilation source raw names).bytecode.functions
      (finishCompilation source raw names).bytecode.circuits := by
  unfold finishCompilation
  apply singletonCircuits_lookupBound
  exact finishCompilation_lookupLayout source raw names valid generic

theorem Source.Toplevel.compile_lookupBound {source : Source.Toplevel} {compiled : CompiledToplevel}
    (accepted : source.compile = .ok compiled) (generic : source.componentRanks = false) :
    CircuitsLookupBound compiled.bytecode.functions compiled.bytecode.circuits := by
  obtain ⟨inlined, typed, concrete, raw, names, inlinedOk, _, _, lowered, artifact⟩ :=
    source.compile_artifact_of_ok accepted
  rw [artifact]
  exact finishCompilation_lookupBound inlined raw names (Concrete.Decls.toBytecode_lookupLayout lowered)
    ((Source.Toplevel.inlineCalls_componentRanks inlinedOk).trans generic)

theorem BoundVerifier.Backend.circuits_lookupBound {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) (generic : selection.source.componentRanks = false) :
    CircuitsLookupBound backend.compiled.bytecode.functions backend.compiled.bytecode.circuits := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  have valid := Source.Toplevel.compile_lookupBound compiled generic
  split at grouped
  · cases grouped
    exact valid
  · have same := (CompiledToplevel.groupFunctions_preserves_code grouped).2.2.1
    have bound := (Array.getElem?_eq_some_iff.mp backend.present).choose
    rw [same] at bound
    exact CompiledToplevel.groupFunctions_lookupBound
      (Source.Toplevel.compile_lookupLayout compiled generic) (by omega) valid grouped

end Aiur

namespace Aiur.AIR
open Bytecode

theorem CircuitWitness.lookupBounds_of_compiled {program : Toplevel}
    (functions : FunctionsLookupLayout program.functions)
    (layouts : CircuitsLookupBound program.functions program.circuits)
    (witness : CircuitWitness) (circuit : witness.circuit ∈ program.circuits)
    (emitted : witness.Emitted program) : witness.LookupBounds := by
  obtain ⟨_, indices, source⟩ := witness.circuit.emitRow_spec witness.values program emitted
  have bounds := layouts witness.circuit circuit
  refine ⟨bounds.1, ?_⟩
  intro part member
  have index : part.functionIndex ∈ witness.circuit.members := by
    apply Array.mem_toList_iff.mp
    rw [← indices]
    exact List.mem_map.mpr ⟨part, member, rfl⟩
  have present := (source part member).present
  have count := Block.emitRow_lookupUsage witness.values (part.selector witness.values) _ _ _ _ _
    part.function.body (source part member).emitted
  have layout := functions part.function (Array.mem_of_getElem? present)
  change part.function.layout.lookups = 4 + part.function.body.lookupUsage at layout
  have limit := bounds.2 part.functionIndex index
  rw [lookup_bang_of_present present] at limit
  rw [count, ← layout]
  exact limit

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem Backend.witness_lookupBounds {selection : Selection} (backend : Backend selection)
    (generic : selection.source.componentRanks = false)
    (witness : CircuitWitness) (circuit : witness.circuit ∈ backend.compiled.bytecode.circuits)
    (emitted : witness.Emitted backend.compiled.bytecode) : witness.LookupBounds :=
  witness.lookupBounds_of_compiled (backend.functions_lookupLayout generic)
    (backend.circuits_lookupBound generic) circuit emitted

theorem Backend.bounded_trace_execution {selection : Selection} (backend : Backend selection)
    (generic : selection.source.componentRanks = false)
    (tables : AuxiliaryTables) (traces : CircuitTraces backend.compiled.bytecode.circuits.toList)
    {witnesses : List CircuitWitness}
    (emitted : traces.emitWitnesses backend.compiled.bytecode = some witnesses)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (budget : lookupQueryBound
      (backend.compiled.bytecode.circuits.toList.map (·.layout.lookups) ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        encodedCircuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory)
      ⟨selection.function, input, selection.success, 0⟩ := by
  have valid := (traces.emitWitnesses_spec emitted).1
  apply backend.compiled_trace_execution tables traces emitted budget width input arity balanced
    publicWidth queryWidths memoryValid canonical satisfied
  intro witness member
  exact backend.witness_lookupBounds generic witness
    (by simpa using (valid witness member).1) (valid witness member).2

end Aiur.BoundVerifier
