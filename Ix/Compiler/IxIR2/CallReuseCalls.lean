import Ix.Compiler.IxIR2.CallReuseControl

/-!
# Corresponding calls with suspended caller credits

The callee receives related ordinary arguments and an empty credit file.
The complete caller relation, including its pending credit and next program
counter, is stored once in the continuation. Heap and cost state is unchanged.
-/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValsIso)

theorem directCall_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {block targetBlock : Block} {leftFrame rightFrame : Frame}
    {leftStack rightStack : List Continuation} {call : Policy.DirectCall}
    {arguments : Array RVal} {definition : Function}
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
    (resolved : resolveAtoms leftFrame.values call.arguments = .ok arguments)
    (found : call.definition leftContext leftFrame = .ok definition)
    (arity : arguments.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    ∃ target,
      Policy.Step .suspendedCallsV1 rightContext .physical
        { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } target ∧
      MachineRel limits validation leftContext mapping
        { store := leftStore, heapFuel := leftFuel
          control := .running { definition, values := arguments }
            (.resume { leftFrame with pc := leftFrame.pc + 1 } :: leftStack) } target ∧
      CostDelta leftStore leftStore rightStore target.store ∧ target.store = rightStore := by
  obtain ⟨targetArguments, targetResolved, argumentsRelated⟩ :=
    ReuseSim.resolveAtoms_iso frames.values resolved
  have targetDefinition := directCall_definition contexts frames found
  have definitionReady := directCall_ready readyContext frames.ready found
  have sizes : arguments.size = targetArguments.size := by simpa using argumentsRelated.lengths
  have targetArity : targetArguments.size =
      (rewriteFunction limits validation definition).signature.params.size := by
    simpa only [rewriteFunction_signature] using sizes.symm.trans arity
  have targetNonempty := rewriteFunction_nonempty (limits := limits) (context := validation) nonempty
  obtain ⟨entryBlock, entryFrames⟩ := FrameRel.functionEntry
    (limits := limits) (validation := validation) definitionReady argumentsRelated arity
  let target : Machine :=
    { store := rightStore, heapFuel := rightFuel
      control := .running
        { definition := rewriteFunction limits validation definition, values := targetArguments }
        (.resume { rightFrame with pc := rightFrame.pc + 1 } :: rightStack) }
  have stepped : Policy.Step .suspendedCallsV1 rightContext .physical
      { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } target :=
    directCall_step rfl targetAt targetPC targetInstruction targetResolved
      targetDefinition targetArity targetNonempty
  refine ⟨target, stepped, ?_, .refl leftStore rightStore, rfl⟩
  exact ⟨machines.heap, machines.ordered, machines.shaped, machines.fuel,
    .running entryFrames (.cons (.resume advanced (by simp)) stack),
    stepped.reservationOwnership machines.reservations⟩

end Ix.Compiler.IxIR2.CallReuse.Sim
