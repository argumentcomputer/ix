import Ix.Compiler.IxIR2.CallReuseShape

/-! Suspended calls and the allocation that consumes the caller's optional credit. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)

theorem callInstruction_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {block targetBlock : Block} {leftFrame rightFrame : Frame}
    {leftStack rightStack : List Continuation} {call : Policy.DirectCall} {leftAfter : Machine}
    (contexts : ContextRel limits validation leftContext rightContext)
    (readyContext : ContextReady leftContext)
    (machines : MachineRel limits validation leftContext mapping
      { store := leftStore, heapFuel := leftFuel, control := .running leftFrame leftStack }
      { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack })
    (frames : FrameRel limits validation mapping block leftFrame rightFrame)
    (advanced : FrameRel limits validation mapping block
      { leftFrame with pc := leftFrame.pc + 1 } { rightFrame with pc := rightFrame.pc + 1 })
    (stack : StackRel limits validation mapping leftStack rightStack)
    (targetAt : rightFrame.definition.blocks[rightFrame.block]? = some targetBlock)
    (targetPC : rightFrame.pc < targetBlock.instructions.size)
    (targetInstruction : targetBlock.instructions[rightFrame.pc] = call.instruction)
    (classified : InstructionTransferCase leftContext .physical leftStore leftFuel
      leftFrame leftStack call.instruction leftAfter) :
    ∃ rightAfter,
      Policy.Step .suspendedCallsV1 rightContext .physical
        { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } rightAfter ∧
      TransferRel limits validation leftContext mapping mapping leftStore rightStore leftAfter rightAfter := by
  cases call with
  | function address arguments =>
      cases classified with
      | callFn noCredits resolved declaration arity nonempty =>
          obtain ⟨target, stepped, related, _, targetStore⟩ := directCall_related contexts readyContext machines
            frames advanced stack targetAt targetPC targetInstruction resolved
            (by simp [Policy.DirectCall.definition, declaration]) arity nonempty
          exact ⟨target, stepped, ⟨by simpa only [targetStore] using HeapTransition.refl machines.heapState,
            related.fuel, related.control⟩⟩
  | self arguments =>
      cases classified with
      | callSelf noCredits resolved arity nonempty =>
          obtain ⟨target, stepped, related, _, targetStore⟩ := directCall_related contexts readyContext machines
            frames advanced stack targetAt targetPC targetInstruction resolved rfl arity nonempty
          exact ⟨target, stepped, ⟨by simpa only [targetStore] using HeapTransition.refl machines.heapState,
            related.fuel, related.control⟩⟩

theorem bodyAllocation_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {block : Block} {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {site : Site limits validation block} {credit : Credit} {leftAfter : Machine}
    (contexts : ContextRel limits validation leftContext rightContext)
    (schemas : leftContext.schemas = validation.schemas)
    (machines : MachineRel limits validation leftContext mapping
      { store := leftStore, heapFuel := leftFuel, control := .running leftFrame leftStack }
      { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack })
    (frames : FrameRel limits validation mapping block leftFrame rightFrame)
    (stack : StackRel limits validation mapping leftStack rightStack)
    (produced : inspect limits validation block = some site)
    (leftPC : leftFrame.pc = 2 * site.shape.fieldCount + 1 + site.shape.calls.size)
    (rightPC : rightFrame.pc = site.shape.fieldCount + 1 + site.shape.calls.size)
    (credits : rightFrame.credits = #[some credit])
    (layout : credit.layout = site.representation.layout) (physical : PhysicalCredit credit)
    (classified : InstructionTransferCase leftContext .physical leftStore leftFuel leftFrame leftStack
      (.alloc .shared site.shape.allocationConstructor site.shape.allocationArguments) leftAfter) :
    ∃ after rightAfter,
      Policy.Step .suspendedCallsV1 rightContext .physical
        { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } rightAfter ∧
      TransferRel limits validation leftContext mapping after leftStore rightStore leftAfter rightAfter := by
  cases classified with
  | @alloc _ _ _ schema values schemaAt resolved fields =>
      obtain ⟨sourceSchema, allocationSchema, _, allocationAt, _, _, _, allocationLayout⟩ := site.schemas
      have schemaSame : schema = allocationSchema := by
        rw [← schemas, schemaAt] at allocationAt
        exact Option.some.inj allocationAt
      subst allocationSchema
      have creditLayout := layout.trans allocationLayout
      have targetSchema : rightContext.schemas .shared site.shape.allocationConstructor = some schema := by
        rw [← contexts.schemas]
        exact schemaAt
      obtain ⟨targetValues, targetResolved, valuesRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
      have targetFields := machines.heap.fieldWorlds valuesRel fields
      have taken : CreditTake { rightFrame with pc := rightFrame.pc + 1 } 0
          { rightFrame with pc := rightFrame.pc + 1, credits := #[none] } credit := by
        have atCredit : ({ rightFrame with pc := rightFrame.pc + 1 } : Frame).credits[0]? =
            some (some credit) := by simp [credits]
        simpa [credits, Array.setIfInBounds] using CreditTake.of_lookup (CreditLookup.of_getElem atCredit)
      have finished := frames.finishBody produced leftPC rightPC
      have positive : 0 < ({ leftFrame with pc := leftFrame.pc + 1 } : Frame).pc := by simp
      have targetAt : rightFrame.definition.blocks[rightFrame.block]? = some site.shape.target := by
        simpa only [rewriteBlock_accepted produced] using frames.targetAt
      have targetFound : site.shape.target.instructions[rightFrame.pc]? =
          some (.allocWith 0 .shared site.shape.allocationConstructor site.shape.allocationArguments) := by
        rw [rightPC]
        exact site.shape.target_alloc_at
      obtain ⟨targetPC, targetInstruction⟩ := Array.getElem?_eq_some_iff.mp targetFound
      rcases physical with absent | ⟨location, present⟩
      · have allocating := machines.heapState.alloc (world := .shared)
          (leftNode := .ctorN site.shape.allocationConstructor values) (.ctor valuesRel)
          ⟨schema, schemaAt, fields.size⟩
        have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
            (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
          .loc (by rw [← machines.heap.size]; exact MapRel.fresh ..)
        have targetCase := InstructionTransferCase.allocWithAbsent
          (context := rightContext) (interpretation := .physical) (heapFuel := rightFuel)
          (stack := rightStack) targetSchema targetResolved targetFields taken creditLayout absent
        exact ⟨_, _, Policy.of_originalStep (targetCase.step targetAt targetPC targetInstruction),
          ⟨allocating, machines.fuel,
            .running ((finished.mono allocating.extension).pushResult positive valueRel)
              (stack.mono allocating.extension)⟩⟩
      · have empty : rightStore.EmptySlot location := machines.reservations.empty location (by
          simp [Machine.reservations, Frame.reservations, Frame.liveCredits, credits,
            Credit.reservation?, present])
        have succeeds : ∃ output, rightStore.reuseReservation location .shared
            (.ctorN site.shape.allocationConstructor targetValues) schema.fields.size = .ok output := by
          change rightStore.heap.nodes[location]? = some none at empty
          simp only [Store.reuseReservation, empty]
          exact ⟨_, rfl⟩
        obtain ⟨output, reused⟩ := succeeds
        have allocating := machines.heapState.reuse
          (leftNode := .ctorN site.shape.allocationConstructor values) (.ctor valuesRel)
          ⟨schema, schemaAt, fields.size⟩ reused
        have valueRel : RValIso (MapRel (mapping.push location))
            (.loc leftStore.heap.nodes.size) (.loc location) :=
          .loc (by rw [← machines.heap.size]; exact MapRel.fresh ..)
        have targetCase := InstructionTransferCase.allocWithPhysical
          (context := rightContext) (heapFuel := rightFuel) (stack := rightStack) rfl
          targetSchema targetResolved targetFields taken creditLayout present reused
        exact ⟨_, _, Policy.of_originalStep (targetCase.step targetAt targetPC targetInstruction),
          ⟨allocating, machines.fuel,
            .running ((finished.mono allocating.extension).pushResult positive valueRel)
              (stack.mono allocating.extension)⟩⟩

end Ix.Compiler.IxIR2.CallReuse.Sim
