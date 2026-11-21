import Aiur.Optimized.LookupCalls
import Aiur.Optimized.LookupMemory
import Aiur.Optimized.BranchOutputs

namespace Aiur.Optimized.LookupMerging

variable {F : Type} [Field F] [DecidableEq F]

def Context.CallsBounded (ctx : Context F) : Prop :=
  ∀ call ∈ ctx.logical.calls.toList, call.scope < ctx.logical.scopes.size

def Context.CellsBounded (ctx : Context F) : Prop :=
  ∀ cell ∈ ctx.logical.cells.toList, cell.scope < ctx.logical.scopes.size

instance (ctx : Context F) : Decidable ctx.CallsBounded := by unfold Context.CallsBounded; infer_instance
instance (ctx : Context F) : Decidable ctx.CellsBounded := by unfold Context.CellsBounded; infer_instance

def Context.calls (ctx : Context F) (bounded : ctx.CallsBounded) : List (CallSlot ctx) :=
  ctx.logical.calls.toList.attach.map fun call =>
    ⟨call.val.channel, call.val.result.map ctx.layout.column,
      .single (.ofScope ctx call.val.scope (bounded call.val call.property))
        (call.val.args.map (WireValue.map ctx.layout.expression))⟩

def Context.cells (ctx : Context F) (bounded : ctx.CellsBounded) : List (Payload ctx) :=
  ctx.logical.cells.toList.attach.map fun cell =>
    .single (.ofScope ctx cell.val.scope (bounded cell.val cell.property))
      (memoryWords (ctx.layout.expression cell.val.address) (cell.val.value.map ctx.layout.expression))

theorem Context.calls_emit (ctx : Context F) (bounded : ctx.CallsBounded) :
    (ctx.calls bounded).map CallSlot.emit = (emitChip ctx.logical ctx.layout).sends := by
  simp [Context.calls, CallSlot.emit, Payload.single, Guard.ofScope, Context.guard,
    emitChip, List.map_map, Function.comp_def]

theorem Context.cells_emit (ctx : Context F) (bounded : ctx.CellsBounded) :
    (ctx.cells bounded).map Payload.emitMemory = (emitChip ctx.logical ctx.layout).memory := by
  simp [Context.cells, Payload.emitMemory, Payload.single, Guard.ofScope, Context.guard,
    memoryWords, unpackMemory, WireValue.field, WireValue.map,
    emitChip, List.map_map, Function.comp_def]

def mergedChip (ctx : Context F) (calls : ctx.CallsBounded) (cells : ctx.CellsBounded) : Circuit.Chip F :=
  { emitChip ctx.logical ctx.layout with
    sends := (mergeCalls (ctx.calls calls)).map CallSlot.emit
    memory := (mergeMemory (ctx.cells cells)).map Payload.emitMemory }

theorem mergedChip_valid (ctx : Context F) (calls : ctx.CallsBounded) (cells : ctx.CellsBounded)
    (rom : WireROM F) (a : Witness → F) :
    (mergedChip ctx calls cells).ValidAssignment rom a ↔
      (emitChip ctx.logical ctx.layout).ValidAssignment rom a := by
  unfold Circuit.Chip.ValidAssignment
  apply and_congr_right
  intro valid
  change ctx.Valid a at valid
  simp only [mergedChip, List.forall_mem_map]
  change memoryValid rom a (mergeMemory (ctx.cells cells)) ↔ _
  rw [mergeMemory_valid _ valid]
  rw [← ctx.cells_emit cells]
  simp only [memoryValid, List.forall_mem_map]

theorem mergedChip_claims (ctx : Context F) (calls : ctx.CallsBounded) (cells : ctx.CellsBounded)
    {a : Witness → F} (valid : ctx.Valid a) :
    (mergedChip ctx calls cells).requirements a = (emitChip ctx.logical ctx.layout).requirements a := by
  unfold Circuit.Chip.requirements
  change (List.map CallSlot.emit (mergeCalls (ctx.calls calls))).filterMap _ = _
  rw [emitCalls_claims, mergeCalls_claims _ valid]
  rw [← ctx.calls_emit calls, emitCalls_claims]

def merge (ctx : Context F) (calls : ctx.CallsBounded) (cells : ctx.CellsBounded) :
    Propagation.Checked (emitChip ctx.logical ctx.layout) where
  chip := mergedChip ctx calls cells
  equivalent := by
    constructor
    · intro rom a valid
      exact ⟨a, (mergedChip_valid ctx calls cells rom a).mpr valid, rfl,
        mergedChip_claims ctx calls cells valid.1⟩
    · intro rom a valid
      have original := (mergedChip_valid ctx calls cells rom a).mp valid
      exact ⟨a, original, rfl, (mergedChip_claims ctx calls cells original.1).symm⟩
  name_eq := rfl
  inputTypes := rfl
  outputType := rfl

/-- Rejecting an optimization certificate leaves the already certified emitted
chip alone. In particular branchless chips retain affine lookup payloads. -/
def run (config : Config) (logical : ScopedChip F) (layout : ColumnLayout) :
    Propagation.Checked (emitChip logical layout) :=
  let original := emitChip logical layout
  if !config.mergeLookups || logical.choices.isEmpty then .identity original else
  if control : Control.Certificate logical then
    if boolean : ∀ scope ∈ List.range logical.scopes.size,
        Control.ZeroEquation logical (.mul (logical.activation scope) (.sub (logical.activation scope) (.const 1))) then
      let ctx : Context F := ⟨logical, layout, control, boolean⟩
      if calls : ctx.CallsBounded then
        if cells : ctx.CellsBounded then
          let merged := merge ctx calls cells
          let outputs := replaceOutputs merged.chip (outputFacts ctx merged.chip rfl)
          if outputs.chip.stats.maxConstraintDegree ≤ config.maxDegree && outputs.chip.stats.maxLookupDegree ≤ 2 && outputs.chip.maxLookupGuardDegree ≤ 1 then
            { chip := outputs.chip
              equivalent := merged.equivalent.trans outputs.equivalent
              name_eq := outputs.name_eq.trans merged.name_eq
              inputTypes := outputs.inputTypes.trans merged.inputTypes
              outputType := outputs.outputType.trans merged.outputType }
          else if merged.chip.stats.maxLookupDegree ≤ 2 then merged
          else .identity original
        else .identity original
      else .identity original
    else .identity original
  else .identity original

end Aiur.Optimized.LookupMerging
