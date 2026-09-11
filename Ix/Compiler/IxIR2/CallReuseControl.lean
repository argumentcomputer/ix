import Ix.Compiler.IxIR2.CallReuse
import Ix.Compiler.IxIR2.CallReuseHeapShape
import Ix.Compiler.IxIR2.ReservationSteps

/-!
# Compiler control correspondence for suspended reuse

The pass preserves declaration addresses, block identities, and all register
numbers after its consuming prefix. A saved caller records its exact position
and optional credit until the matching allocation. Allocation history extends
all saved value correspondences without changing this control evidence.
-/

namespace Ix.Compiler.IxIR2.CallReuse

theorem rewriteBlock_valueParams (limits : Validate.Limits) (context : Validate.Context)
    (block : Block) : (rewriteBlock limits context block).valueParams = block.valueParams := by
  unfold rewriteBlock
  cases decideBlock limits context block with
  | unchanged => rfl
  | accepted site produced => simp only [Decision.target, Shape.target, site.exact, Shape.baseline]

theorem rewriteBlock_creditParams (limits : Validate.Limits) (context : Validate.Context)
    (block : Block) : (rewriteBlock limits context block).creditParams = block.creditParams := by
  unfold rewriteBlock
  cases decideBlock limits context block with
  | unchanged => rfl
  | accepted site produced => simp only [Decision.target, Shape.target, site.exact, Shape.baseline]

theorem rewriteBlock_rejected {limits : Validate.Limits} {context : Validate.Context} {block : Block}
    (rejected : inspect limits context block = none) : rewriteBlock limits context block = block := by
  unfold rewriteBlock decideBlock
  split
  · rfl
  · rename_i site found
    rw [rejected] at found
    cases found

theorem rewriteBlock_accepted {limits : Validate.Limits} {context : Validate.Context} {block : Block}
    {site : Site limits context block} (produced : inspect limits context block = some site) :
    rewriteBlock limits context block = site.shape.target := by
  unfold rewriteBlock decideBlock
  split
  · rename_i missing
    rw [produced] at missing
    cases missing
  · rename_i foundSite found
    have same := Option.some.inj (found.symm.trans produced)
    subst foundSite
    rfl

theorem rewriteFunction_block {limits : Validate.Limits} {context : Validate.Context}
    {definition : Function} {block : Block} {blockId : Nat}
    (found : definition.blocks[blockId]? = some block) :
    (rewriteFunction limits context definition).blocks[blockId]? =
      some (rewriteBlock limits context block) := by
  simp [rewriteFunction, Array.getElem?_map, found]

theorem rewriteFunction_nonempty {limits : Validate.Limits} {context : Validate.Context}
    {definition : Function} (nonempty : definition.blocks.isEmpty = false) :
    (rewriteFunction limits context definition).blocks.isEmpty = false := by
  simpa [rewriteFunction] using nonempty

namespace Sim

open Eval
open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)

def rewriteDecl (limits : Validate.Limits) (validation : Validate.Context) : Decl → Decl
  | .fn definition => .fn (rewriteFunction limits validation definition)
  | .extern arity => .extern arity

structure ContextRel (limits : Validate.Limits) (validation : Validate.Context)
    (left right : Context) : Prop where
  schemas : left.schemas = right.schemas
  oracle : left.oracle = right.oracle
  declarations : ∀ address, right.declarations address =
    (left.declarations address).map (rewriteDecl limits validation)

theorem ContextRel.ofProgram (limits : Validate.Limits) (validation : Validate.Context)
    (source : Program) (oracle : Address → List RVal → Option RVal := fun _ _ => none) :
    ContextRel limits validation (Context.ofProgram source validation.schemas oracle)
      (Context.ofProgram (rewriteProgram limits validation source) validation.schemas oracle) := by
  refine ⟨rfl, rfl, ?_⟩
  intro address
  simp only [Context.ofProgram, rewriteProgram, List.find?_map, Option.map_map,
    Function.comp_def]
  rfl

theorem ContextRel.function {limits : Validate.Limits} {validation : Validate.Context}
    {left right : Context} (contexts : ContextRel limits validation left right)
    {address : Address} {definition : Function} (found : left.declarations address = some (.fn definition)) :
    right.declarations address = some (.fn (rewriteFunction limits validation definition)) := by
  rw [contexts.declarations, found]
  rfl

theorem ContextRel.extern {limits : Validate.Limits} {validation : Validate.Context}
    {left right : Context} (contexts : ContextRel limits validation left right)
    {address : Address} {arity : Nat} (found : left.declarations address = some (.extern arity)) :
    right.declarations address = some (.extern arity) := by
  rw [contexts.declarations, found]
  rfl

def ContextReady (context : Context) : Prop :=
  ∀ {address definition}, context.declarations address = some (.fn definition) →
    functionReady definition = true

theorem programReady_context {source : Program} {schemas oracle}
    (ready : programReady source = true) : ContextReady (Context.ofProgram source schemas oracle) := by
  intro address definition found
  simp only [programReady, Bool.and_eq_true] at ready
  simp only [Context.ofProgram] at found
  cases lookup : source.declarations.find? (fun entry => entry.1 == address) with
  | none => simp [lookup] at found
  | some entry =>
      simp only [lookup, Option.map_some, Option.some.injEq] at found
      have member := List.mem_of_find?_eq_some lookup
      have checked := List.all_eq_true.mp ready.2 entry member
      simpa only [found] using checked

def PhysicalCredit (credit : Credit) : Prop :=
  credit.presence = .absent ∨ ∃ location, credit.presence = .present (some location)

/-- Stable points before a consuming prefix and after its release. Calls in
the body retain the same one-element credit file in their saved caller. -/
inductive Position (limits : Validate.Limits) (validation : Validate.Context) (block : Block) :
    Nat → Nat → Array (Option Credit) → Prop where
  | unchanged {pc : Nat} {credits : Array (Option Credit)}
      (rejected : inspect limits validation block = none)
      (cleared : credits.any Option.isSome = false) : Position limits validation block pc pc credits
  | entry (site : Site limits validation block)
      (produced : inspect limits validation block = some site) :
      Position limits validation block 0 0 #[]
  | body (site : Site limits validation block)
      (produced : inspect limits validation block = some site)
      (offset : Nat) (within : offset ≤ site.shape.calls.size) (credit : Credit)
      (layout : credit.layout = site.representation.layout) (physical : PhysicalCredit credit) :
      Position limits validation block (2 * site.shape.fieldCount + 1 + offset)
        (site.shape.fieldCount + 1 + offset) #[some credit]
  | finished (site : Site limits validation block)
      (produced : inspect limits validation block = some site) :
      Position limits validation block (2 * site.shape.fieldCount + site.shape.calls.size + 2)
        (site.shape.fieldCount + site.shape.calls.size + 2) #[none]

structure FrameRel (limits : Validate.Limits) (validation : Validate.Context) (mapping : Array Nat)
    (sourceBlock : Block) (left right : Frame) : Prop where
  definition : right.definition = rewriteFunction limits validation left.definition
  ready : functionReady left.definition = true
  blockId : right.block = left.block
  sourceAt : left.definition.blocks[left.block]? = some sourceBlock
  values : RValsIso (MapRel mapping) left.values.toList right.values.toList
  leftCredits : left.credits = #[]
  position : Position limits validation sourceBlock left.pc right.pc right.credits
  entryCount : left.pc = 0 → left.values.size = sourceBlock.valueParams.size

theorem FrameRel.targetAt {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {sourceBlock : Block} {left right : Frame}
    (frames : FrameRel limits validation mapping sourceBlock left right) :
    right.definition.blocks[right.block]? = some (rewriteBlock limits validation sourceBlock) := by
  rw [frames.definition, frames.blockId]
  exact rewriteFunction_block frames.sourceAt

theorem FrameRel.mono {limits : Validate.Limits} {validation : Validate.Context}
    {before after : Array Nat} {sourceBlock : Block} {left right : Frame}
    (frames : FrameRel limits validation before sourceBlock left right)
    (lift : ∀ {l r}, MapRel before l r → MapRel after l r) :
    FrameRel limits validation after sourceBlock left right :=
  { frames with values := frames.values.mono lift }

theorem Position.atEntry (limits : Validate.Limits) (validation : Validate.Context) (block : Block) :
    Position limits validation block 0 0 #[] := by
  cases decideBlock limits validation block with
  | unchanged rejected => exact .unchanged rejected (by simp)
  | accepted site produced => exact .entry site produced

theorem FrameRel.atEntry {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {definition : Function} {block : Block} {blockId : Nat}
    {leftValues rightValues : Array RVal} (ready : functionReady definition = true)
    (found : definition.blocks[blockId]? = some block)
    (values : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (arity : leftValues.size = block.valueParams.size) :
    FrameRel limits validation mapping block
      { definition, block := blockId, values := leftValues }
      { definition := rewriteFunction limits validation definition, block := blockId, values := rightValues } :=
  ⟨rfl, ready, rfl, found, values, rfl, Position.atEntry .., fun _ => arity⟩

theorem FrameRel.functionEntry {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {definition : Function} {leftValues rightValues : Array RVal}
    (ready : functionReady definition = true)
    (values : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (arity : leftValues.size = definition.signature.params.size) :
    ∃ block, FrameRel limits validation mapping block
      { definition, values := leftValues }
      { definition := rewriteFunction limits validation definition, values := rightValues } := by
  cases found : definition.blocks[0]? with
  | none => simp [functionReady, found] at ready
  | some block =>
      exact ⟨block, FrameRel.atEntry ready found values
        (arity.trans (functionReady_entry ready found).symm)⟩

theorem FrameRel.pushResult {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right : Frame} {leftValue rightValue : RVal}
    (frames : FrameRel limits validation mapping block left right) (positive : 0 < left.pc)
    (value : RValIso (MapRel mapping) leftValue rightValue) :
    FrameRel limits validation mapping block
      { left with values := left.values.push leftValue }
      { right with values := right.values.push rightValue } :=
  { frames with
    values := by simpa only [Array.toList_push] using frames.values.append (.cons value .nil)
    entryCount := by intro zero; simp only at zero; omega }

theorem Position.unchanged_parts {limits : Validate.Limits} {validation : Validate.Context}
    {block : Block} {leftPC rightPC : Nat} {credits : Array (Option Credit)}
    (position : Position limits validation block leftPC rightPC credits)
    (rejected : inspect limits validation block = none) :
    leftPC = rightPC ∧ credits.any Option.isSome = false := by
  cases position with
  | unchanged missing cleared => exact ⟨rfl, cleared⟩
  | entry site produced => rw [rejected] at produced; cases produced
  | body site produced offset within credit layout physical => rw [rejected] at produced; cases produced
  | finished site produced => rw [rejected] at produced; cases produced

theorem FrameRel.unchanged {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right : Frame}
    (frames : FrameRel limits validation mapping block left right)
    (rejected : inspect limits validation block = none) : left.pc = right.pc ∧ NoLiveCredits right :=
  frames.position.unchanged_parts rejected

theorem FrameRel.advanceUnchanged {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right : Frame}
    (frames : FrameRel limits validation mapping block left right)
    (rejected : inspect limits validation block = none) :
    FrameRel limits validation mapping block { left with pc := left.pc + 1 } { right with pc := right.pc + 1 } := by
  obtain ⟨pc, cleared⟩ := frames.unchanged rejected
  exact { frames with
    position := by rw [pc]; exact .unchanged rejected cleared
    entryCount := by intro zero; simp only at zero; omega }

inductive ContinuationRel (limits : Validate.Limits) (validation : Validate.Context) (mapping : Array Nat) :
    Continuation → Continuation → Prop where
  | resume {sourceBlock : Block} {left right : Frame}
      (frames : FrameRel limits validation mapping sourceBlock left right)
      (afterInstruction : 0 < left.pc) :
      ContinuationRel limits validation mapping (.resume left) (.resume right)
  | applyMore {sourceBlock : Block} {left right : Frame} {leftArguments rightArguments : Array RVal}
      (frames : FrameRel limits validation mapping sourceBlock left right) (afterInstruction : 0 < left.pc)
      (arguments : RValsIso (MapRel mapping) leftArguments.toList rightArguments.toList) :
      ContinuationRel limits validation mapping (.applyMore leftArguments left) (.applyMore rightArguments right)

inductive StackRel (limits : Validate.Limits) (validation : Validate.Context) (mapping : Array Nat) :
    List Continuation → List Continuation → Prop where
  | nil : StackRel limits validation mapping [] []
  | cons {left right : Continuation} {lefts rights : List Continuation}
      (head : ContinuationRel limits validation mapping left right)
      (tail : StackRel limits validation mapping lefts rights) :
      StackRel limits validation mapping (left :: lefts) (right :: rights)

theorem ContinuationRel.mono {limits : Validate.Limits} {validation : Validate.Context}
    {before after : Array Nat} {left right : Continuation}
    (related : ContinuationRel limits validation before left right)
    (lift : ∀ {l r}, MapRel before l r → MapRel after l r) :
    ContinuationRel limits validation after left right := by
  cases related with
  | resume frames positive => exact .resume (frames.mono lift) positive
  | applyMore frames positive arguments => exact .applyMore (frames.mono lift) positive (arguments.mono lift)

theorem StackRel.mono {limits : Validate.Limits} {validation : Validate.Context}
    {before after : Array Nat} {left right : List Continuation}
    (related : StackRel limits validation before left right)
    (lift : ∀ {l r}, MapRel before l r → MapRel after l r) : StackRel limits validation after left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.mono lift) ih

inductive ControlRel (limits : Validate.Limits) (validation : Validate.Context) (mapping : Array Nat) :
    Control → Control → Prop where
  | halted {left right : RVal} (values : RValIso (MapRel mapping) left right) :
      ControlRel limits validation mapping (.halted left) (.halted right)
  | running {sourceBlock : Block} {left right : Frame} {leftStack rightStack : List Continuation}
      (frames : FrameRel limits validation mapping sourceBlock left right)
      (stack : StackRel limits validation mapping leftStack rightStack) :
      ControlRel limits validation mapping (.running left leftStack) (.running right rightStack)

structure MachineRel (limits : Validate.Limits) (validation : Validate.Context) (sourceContext : Context)
    (mapping : Array Nat) (left right : Machine) : Prop where
  heap : HeapMap left.store right.store mapping
  ordered : Ordered left.store
  shaped : Shaped sourceContext left.store
  fuel : left.heapFuel ≤ right.heapFuel
  control : ControlRel limits validation mapping left.control right.control
  reservations : right.ReservationOwnership

theorem initialMachine_related {limits : Validate.Limits} {validation : Validate.Context}
    {sourceContext : Context} {definition : Function} {heapFuel : Nat}
    (ready : functionReady definition = true) (arity : definition.signature.params.size = 0) :
    MachineRel limits validation sourceContext #[]
      (initialMachine definition #[] heapFuel)
      (initialMachine (rewriteFunction limits validation definition) #[] heapFuel) := by
  obtain ⟨block, frames⟩ := FrameRel.functionEntry (limits := limits) (validation := validation)
    (mapping := #[]) ready (RValsIso.nil) arity.symm
  exact ⟨HeapMap.empty, Ordered.empty, NodeProperty.empty _, Nat.le_refl _,
    .running frames .nil, Policy.initialMachine_reservationOwnership ..⟩

theorem directCall_definition {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat} {block : Block}
    {left right : Frame} (contexts : ContextRel limits validation leftContext rightContext)
    (frames : FrameRel limits validation mapping block left right)
    {call : Policy.DirectCall} {definition : Function}
    (found : call.definition leftContext left = .ok definition) :
    call.definition rightContext right = .ok (rewriteFunction limits validation definition) := by
  cases call with
  | self arguments =>
      simp only [Policy.DirectCall.definition, Except.ok.injEq] at found
      subst definition
      simp only [Policy.DirectCall.definition, frames.definition]
  | function address arguments =>
      cases declared : leftContext.declarations address with
      | none => simp [Policy.DirectCall.definition, declared] at found
      | some declaration =>
          cases declaration with
          | extern arity => simp [Policy.DirectCall.definition, declared] at found
          | fn callee =>
              simp only [Policy.DirectCall.definition, declared, Except.ok.injEq] at found
              subst callee
              simp only [Policy.DirectCall.definition, contexts.function declared]

theorem directCall_ready {context : Context} (readyContext : ContextReady context)
    {frame : Frame} (ready : functionReady frame.definition = true)
    {call : Policy.DirectCall} {definition : Function}
    (found : call.definition context frame = .ok definition) : functionReady definition = true := by
  cases call with
  | self arguments =>
      simp only [Policy.DirectCall.definition, Except.ok.injEq] at found
      exact found ▸ ready
  | function address arguments =>
      cases declared : context.declarations address with
      | none => simp [Policy.DirectCall.definition, declared] at found
      | some declaration =>
          cases declaration with
          | extern arity => simp [Policy.DirectCall.definition, declared] at found
          | fn callee =>
              simp only [Policy.DirectCall.definition, declared, Except.ok.injEq] at found
              subst callee
              exact readyContext declared

theorem directCall_step {context : Context} {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block} {call : Policy.DirectCall}
    {values : Array RVal} {definition : Function}
    (running : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = call.instruction)
    (resolved : resolveAtoms frame.values call.arguments = .ok values)
    (found : call.definition context frame = .ok definition)
    (arity : values.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    Policy.Step .suspendedCallsV1 context interpretation machine
      { machine with
        control := .running { definition, values }
          (.resume { frame with pc := frame.pc + 1 } :: stack) } := by
  have atCall : Policy.directCall? frame = some call := by
    rw [Policy.directCall?_atInstruction blockAt pc instruction]
    cases call <;> rfl
  simp only [Policy.Step, Policy.step, running, atCall]
  exact Policy.suspendCall_iff.mpr ⟨values, definition, resolved, found, arity, nonempty, rfl⟩

end Sim

end Ix.Compiler.IxIR2.CallReuse
