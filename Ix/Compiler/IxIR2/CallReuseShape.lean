import Ix.Compiler.IxIR2.CallReuseTerminators

/-! Exact instruction coordinates of the recognized source and generated block. -/

namespace Ix.Compiler.IxIR2.CallReuse

@[simp] theorem Shape.fetches_size (shape : Shape) : shape.fetches.size = shape.fieldCount := by
  simp [Shape.fetches]

@[simp] theorem Shape.retains_size (shape : Shape) : shape.retains.size = shape.fieldCount := by
  simp [Shape.retains]

@[simp] theorem Shape.moves_size (shape : Shape) : shape.moves.size = shape.fieldCount := by
  simp [Shape.moves]

@[simp] theorem Shape.baseline_size (shape : Shape) :
    shape.baseline.instructions.size = 2 * shape.fieldCount + shape.calls.size + 2 := by
  simp [Shape.baseline]; omega

@[simp] theorem Shape.target_size (shape : Shape) :
    shape.target.instructions.size = shape.fieldCount + shape.calls.size + 2 := by
  simp [Shape.target]; omega

theorem Shape.fetch_at (shape : Shape) {field : Nat} (within : field < shape.fieldCount) :
    shape.baseline.instructions[field]? =
      some (.fetch (.reg shape.source) shape.sourceConstructor field) := by
  simp (discharger := omega) [Shape.baseline, Array.getElem?_append, Shape.fetches,
    Shape.retains, Array.getElem?_range, within]

theorem Shape.retain_at (shape : Shape) {field : Nat} (within : field < shape.fieldCount) :
    shape.baseline.instructions[shape.fieldCount + field]? =
      some (.retainShared (.reg (shape.valueParams.size + field))) := by
  simp (discharger := omega) [Shape.baseline, Array.getElem?_append, Shape.fetches,
    Shape.retains, Array.getElem?_push, Array.getElem?_range, within,
    show ¬shape.fieldCount + field < shape.fieldCount by omega,
    show field < shape.fieldCount + 1 by omega, show field ≠ shape.fieldCount by omega]

theorem Shape.release_at (shape : Shape) :
    shape.baseline.instructions[2 * shape.fieldCount]? = some (.releaseShared (.reg shape.source)) := by
  simp (discharger := omega) [Shape.baseline, Array.getElem?_append, Shape.fetches,
    Shape.retains, Array.getElem?_push, Nat.two_mul]

theorem Shape.call_at (shape : Shape) {offset : Nat} (within : offset < shape.calls.size) :
    shape.baseline.instructions[2 * shape.fieldCount + 1 + offset]? = shape.calls[offset]? := by
  simp (discharger := omega) [Shape.baseline, Array.getElem?_append, Array.getElem?_push,
    Nat.two_mul, Nat.add_assoc,
    show ¬shape.fieldCount + (shape.fieldCount + (1 + offset)) < shape.fieldCount by omega,
    show shape.fieldCount + (1 + offset) - (shape.fieldCount + 1) = offset by omega,
    show offset ≠ shape.calls.size by omega]

theorem Shape.alloc_at (shape : Shape) :
    shape.baseline.instructions[2 * shape.fieldCount + 1 + shape.calls.size]? =
      some (.alloc .shared shape.allocationConstructor shape.allocationArguments) := by
  simp (discharger := omega) [Shape.baseline, Array.getElem?_append, Array.getElem?_push,
    Nat.two_mul, Nat.add_assoc,
    show ¬shape.fieldCount + (shape.fieldCount + (1 + shape.calls.size)) < shape.fieldCount by omega,
    show shape.fieldCount + (1 + shape.calls.size) - (shape.fieldCount + 1) = shape.calls.size by omega]

theorem Shape.reset_at (shape : Shape) :
    shape.target.instructions[0]? = some (.resetShared (.reg shape.source) shape.sourceConstructor) := by
  simp [Shape.target, Array.getElem?_append]

theorem Shape.move_at (shape : Shape) {field : Nat} (within : field < shape.fieldCount) :
    shape.target.instructions[1 + field]? = some (.move (.reg (shape.valueParams.size + field))) := by
  simp (discharger := omega) [Shape.target, Array.getElem?_append, Shape.moves, within,
    Nat.add_comm 1 field, Array.getElem?_range]

theorem Shape.target_call_at (shape : Shape) {offset : Nat} (within : offset < shape.calls.size) :
    shape.target.instructions[shape.fieldCount + 1 + offset]? = shape.calls[offset]? := by
  simp (discharger := omega) [Shape.target, Array.getElem?_append, Array.getElem?_push,
    Nat.add_assoc, Nat.add_sub_assoc,
    show ¬shape.fieldCount + offset < shape.fieldCount by omega,
    show offset ≠ shape.calls.size by omega]

theorem Shape.target_alloc_at (shape : Shape) :
    shape.target.instructions[shape.fieldCount + 1 + shape.calls.size]? =
      some (.allocWith 0 .shared shape.allocationConstructor shape.allocationArguments) := by
  simp (discharger := omega) [Shape.target, Array.getElem?_append, Array.getElem?_push,
    Nat.add_assoc, Nat.add_sub_assoc,
    show ¬shape.fieldCount + shape.calls.size < shape.fieldCount by omega]

theorem Site.sourceBound {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    (site : Site limits validation block) : site.shape.source < site.shape.valueParams.size :=
  (Array.getElem?_eq_some_iff.mp site.sourceOwned).1

theorem Site.schemas {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    (site : Site limits validation block) :
    ∃ sourceSchema allocationSchema,
      validation.schemas .shared site.shape.sourceConstructor = some sourceSchema ∧
      validation.schemas .shared site.shape.allocationConstructor = some allocationSchema ∧
      sourceSchema.fields = Array.replicate site.shape.fieldCount .shared ∧
      allocationSchema.fields = sourceSchema.fields ∧
      site.representation.layout = sourceSchema.layout ∧
      site.representation.layout = allocationSchema.layout := by
  obtain ⟨source, allocation, sourceAt, allocationAt, fields, allocationFields, layouts, represented⟩ :=
    Reuse.representation?_sound site.representationProduced
  exact ⟨source, allocation, sourceAt, allocationAt, fields, allocationFields,
    represented, represented.trans layouts⟩

theorem Site.call_exists {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    (site : Site limits validation block) {offset : Nat} (within : offset < site.shape.calls.size) :
    ∃ call : Eval.Policy.DirectCall, site.shape.calls[offset] = call.instruction := by
  have checked := Array.all_eq_true.mp site.directCalls offset within
  cases found : site.shape.calls[offset] <;>
    simp only [found, Eval.Policy.DirectCall.ofInstruction?, Option.isSome_none, Bool.false_eq_true] at checked
  case call address arguments => exact ⟨.function address arguments, rfl⟩
  case callSelf arguments => exact ⟨.self arguments, rfl⟩

namespace Sim

open Eval

theorem FrameRel.advanceBody {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right : Frame}
    (frames : FrameRel limits validation mapping block left right)
    {site : Site limits validation block} (produced : inspect limits validation block = some site)
    {offset : Nat} (within : offset < site.shape.calls.size) {credit : Credit}
    (leftPC : left.pc = 2 * site.shape.fieldCount + 1 + offset)
    (rightPC : right.pc = site.shape.fieldCount + 1 + offset)
    (credits : right.credits = #[some credit]) (layout : credit.layout = site.representation.layout)
    (physical : PhysicalCredit credit) :
    FrameRel limits validation mapping block
      { left with pc := left.pc + 1 } { right with pc := right.pc + 1 } := by
  exact { frames with
    position := by
      simp only
      rw [leftPC, rightPC, credits]
      simpa only [Nat.add_assoc] using Position.body site produced (offset + 1) (by omega) credit layout physical
    entryCount := by intro zero; simp only at zero; omega }

theorem TransferRel.machineRel {limits : Validate.Limits} {validation : Validate.Context}
    {context : Context} {before after : Array Nat} {leftBefore rightBefore : Store}
    {leftAfter rightAfter : Machine}
    (related : TransferRel limits validation context before after leftBefore rightBefore leftAfter rightAfter)
    (reservations : rightAfter.ReservationOwnership) :
    MachineRel limits validation context after leftAfter rightAfter :=
  ⟨related.transition.state.heap, related.transition.state.ordered, related.transition.state.shaped,
    related.fuel, related.control, reservations⟩

theorem FrameRel.finishBody {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right : Frame}
    (frames : FrameRel limits validation mapping block left right)
    {site : Site limits validation block} (produced : inspect limits validation block = some site)
    (leftPC : left.pc = 2 * site.shape.fieldCount + 1 + site.shape.calls.size)
    (rightPC : right.pc = site.shape.fieldCount + 1 + site.shape.calls.size) :
    FrameRel limits validation mapping block
      { left with pc := left.pc + 1 } { right with pc := right.pc + 1, credits := #[none] } := by
  exact { frames with
    position := by
      simp only
      rw [show left.pc + 1 = 2 * site.shape.fieldCount + site.shape.calls.size + 2 by omega,
        show right.pc + 1 = site.shape.fieldCount + site.shape.calls.size + 2 by omega]
      exact Position.finished site produced
    entryCount := by intro zero; simp only at zero; omega }

end Sim

end Ix.Compiler.IxIR2.CallReuse
