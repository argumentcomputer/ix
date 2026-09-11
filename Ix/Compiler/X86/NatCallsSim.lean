import Ix.Compiler.X86.NatCallsCheck
import Ix.Compiler.IxIR2.SourcePipelineSim

namespace Ix.Compiler.X86.NatCalls
open Ix.Compiler Ix.Compiler.Pipeline Ix.Compiler.IxIR1.LowerSim

/-- Source erasure/lowering and the closed representation certificate meet
at the actual constructor-valued physical run. The complete object endpoint
additionally requires the explicit execution/stack certificate for its initial
state; no ISA, runtime-body, or hash-injectivity axiom is added here. -/
theorem sourceObjectRefines
    {constants : List (Ixon.Address × Ixon.Constant)}
    {mainAddress : Ixon.Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (attached : IxIR2.Pipeline.Attached constants mainAddress config .shared eraseFuel lowerFuel)
    {schema : Schema}
    (object : Object attached.target.artifact.program attached.target.artifact.validationContext schema)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (hctx : (validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (validatedEvalCtx constants config) sourceFuel
      (validatedMainFrame mainAddress) [] validatedMainSource = .ok sourceValue)
    {core : Core} {fuel : Nat} (execution : Execution object core fuel)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ rawValue ir1Fuel ir1Store ir1Value controlFuel heapFuel physicalResult count holes finalState,
      @Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
        sourceValue rawValue attached.source.memberScope ∧
      MutualAddressedValueGraph
        (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap)
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw)
        attached.source.functionRel ir1Store rawValue ir1Value ∧
      IxIR1.runOwnedMain attached.compiled.simulationSourceContext .shared
        attached.target.artifact.source.main ir1Fuel = .ok (ir1Store, ir1Value) ∧
      IxIR2.Eval.runMain attached.compiled.simulationTargetContext .physical
        attached.target.artifact.program controlFuel heapFuel = .ok physicalResult ∧
      IxIR2.Lower.Sim.OutcomeRel (ir1Store, ir1Value) physicalResult ∧
      heapNat schema 10000 physicalResult.store.heap physicalResult.value = some object.selected.word.toNat ∧
      0 < count ∧ count ≤ 3 * fuel ∧
      ObjectEval.run object.object.bytes object.input.exportName base count core flags = .ok finalState ∧
      finalState.rip = execution.returnAddress ∧
      Stream.CoreRelated object.selected.target.program base holes []
        (execution.after.core.setReg .rsp (execution.after.core.readReg .rsp + 8)) finalState.core := by
  obtain ⟨rawValue, ir1Fuel, ir1Store, ir1Value, controlFuel, heapFuel, physicalResult,
    relatedSource, graph, owned, physical, relatedPhysical⟩ := attached.sourcePhysical horacles hctx hsource
  obtain ⟨observed, _, _⟩ := object.selected.refinesSuccessfulRun physical
  obtain ⟨count, holes, finalState, positive, bounded, executed, returned, relatedTarget⟩ := execution.objectRun base flags
  exact ⟨rawValue, ir1Fuel, ir1Store, ir1Value, controlFuel, heapFuel, physicalResult, count, holes, finalState,
    relatedSource, graph, owned, physical, relatedPhysical, observed, positive, bounded, executed, returned, relatedTarget⟩

/-- The source-to-object endpoint also exposes complete baseline reclamation
and the actual serialized object's RAX value. Static capture selection retains
the same source oracle/sharing and supplied-state execution hypotheses. -/
theorem sourceObjectReclaims
    {constants : List (Ixon.Address × Ixon.Constant)}
    {mainAddress : Ixon.Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (attached : IxIR2.Pipeline.Attached constants mainAddress config .shared eraseFuel lowerFuel)
    {schema : Schema}
    (object : Object attached.target.artifact.program attached.target.artifact.validationContext schema)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (hctx : (validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (validatedEvalCtx constants config) sourceFuel
      (validatedMainFrame mainAddress) [] validatedMainSource = .ok sourceValue)
    {core : Core} {fuel : Nat} (execution : Execution object core fuel)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ rawValue ir1Fuel ir1Store ir1Value controlFuel heapFuel physicalResult count finalState,
      @Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
        sourceValue rawValue attached.source.memberScope ∧
      MutualAddressedValueGraph
        (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap)
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw)
        attached.source.functionRel ir1Store rawValue ir1Value ∧
      IxIR1.runOwnedMain attached.compiled.simulationSourceContext .shared
        attached.target.artifact.source.main ir1Fuel = .ok (ir1Store, ir1Value) ∧
      IxIR2.Eval.runMain attached.compiled.simulationTargetContext .physical
        attached.target.artifact.program controlFuel heapFuel = .ok physicalResult ∧
      IxIR2.Lower.Sim.OutcomeRel (ir1Store, ir1Value) physicalResult ∧
      heapNat schema 10000 physicalResult.store.heap physicalResult.value = some object.selected.word.toNat ∧
      IxIR2.Eval.releaseShared 10000 physicalResult.store physicalResult.value =
        .ok (object.selected.reclaimed, object.selected.remaining) ∧
      object.selected.reclaimed.heap.live = 0 ∧
      object.selected.reclaimed.heap.allocs = object.selected.reclaimed.heap.frees ∧
      0 < count ∧ count ≤ 3 * fuel ∧
      ObjectEval.run object.object.bytes object.input.exportName base count core flags = .ok finalState ∧
      finalState.rip = execution.returnAddress ∧ finalState.core.readReg .rax = object.selected.word := by
  obtain ⟨rawValue, ir1Fuel, ir1Store, ir1Value, controlFuel, heapFuel, physicalResult,
    relatedSource, graph, owned, physical, relatedPhysical⟩ := attached.sourcePhysical horacles hctx hsource
  obtain ⟨observed, _, _⟩ := object.selected.refinesSuccessfulRun physical
  obtain ⟨released, empty, balanced⟩ := object.selected.reclaimsSuccessfulRun physical
  obtain ⟨count, finalState, positive, bounded, executed, returned, result⟩ := execution.objectReturns base flags
  exact ⟨rawValue, ir1Fuel, ir1Store, ir1Value, controlFuel, heapFuel, physicalResult, count, finalState,
    relatedSource, graph, owned, physical, relatedPhysical, observed, released, empty, balanced,
    positive, bounded, executed, returned, result⟩

end Ix.Compiler.X86.NatCalls
