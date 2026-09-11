import Ix.Compiler.X86.PhysicalScalarCapturedExport
import Ix.Compiler.IxIR2.SourcePipelineSim

namespace Ix.Compiler.X86.PhysicalScalar.Captured
open Ix.Compiler.Pipeline (validatedEvalCtx validatedMainFrame validatedMainSource)

variable {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
  {config : Ix.Compiler.Pipeline.Config} {eraseFuel lowerFuel : Nat} {limits : Limits}

/-- The closed initializer identifies the source function's actual value
graph and heap image through both compiler address passes. -/
theorem Compiled.sourceFunction
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (compiled : Compiled attached.target.artifact.program attached.target.artifact.validationContext.schemas
      limits (sourceProvenance attached))
    {fuel : Nat} {function : Ixon.Eval.Value}
    (oracles : @Ix.Compiler.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) fuel
      (validatedMainFrame root) [] validatedMainSource = .ok function) :
    ∃ rawFunction rawStore,
      @Ix.Compiler.Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
        function rawFunction attached.source.memberScope ∧
      IxIR1.Sim.ValueGraph attached.source.functionRel rawStore
        (IxIR0.Readdress.Value.mapAddresses
          (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap) rawFunction)
        (.loc compiled.source.heap.location) ∧
      IxIR1.Readdress.Store.mapAddresses
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) rawStore =
        compiled.source.result.store.heap := by
  obtain ⟨rawFunction, _, store, value, _, _, result, related, graph, _, physical, heaps⟩ :=
    attached.sourcePhysical oracles contextWF entry
  have same := IxIR2.Eval.runMain_success_unique compiled.source.nullary compiled.source.nonempty
    physical compiled.source.run
  have valueEq : value = .loc compiled.source.heap.location :=
    heaps.value.symm.trans (same.2.trans compiled.source.value)
  have storeEq : store = compiled.source.result.store.heap :=
    heaps.heap.symm.trans (congrArg IxIR2.Eval.Store.heap same.1)
  obtain ⟨rawStore, renamed, graph⟩ := graph
  exact ⟨rawFunction, rawStore, related, valueEq ▸ graph, renamed.symm.trans storeEq⟩

structure SourceRun
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (compiled : Compiled attached.target.artifact.program attached.target.artifact.validationContext.schemas
      limits (sourceProvenance attached)) (argument : Word) (result : Ixon.Eval.Value) where
  rawResult : IxIR0.Value
  rawStore : IxIR1.Store
  store : IxIR1.Store
  value : IxIR1.RVal
  applyFuel : Nat
  invokeFuel : Nat
  controlFuel : Nat
  heapFuel : Nat
  physicalResult : IxIR2.Eval.Result
  sourceRelated : @Ix.Compiler.Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
    result rawResult attached.source.memberScope
  valueRelated : IxIR1.Sim.ValueGraph attached.source.functionRel rawStore
    (IxIR0.Readdress.Value.mapAddresses
      (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap) rawResult) value
  storeRenamed : store = IxIR1.Readdress.Store.mapAddresses
    (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) rawStore
  applied : IxIR1.applyGo attached.compiled.simulationSourceContext applyFuel
    compiled.source.result.store.heap (.loc compiled.source.heap.location) [rval argument] = .ok (store, value)
  invoked : IxIR1.invoke attached.compiled.simulationSourceContext invokeFuel compiled.source.address
    [rval compiled.source.capture, rval argument] compiled.source.heap.spent = .ok (store, value)
  physical : IxIR2.Eval.runFunction attached.compiled.simulationTargetContext .physical
    compiled.source.target (#[compiled.source.capture, argument].map rval) controlFuel heapFuel
    { heap := compiled.source.heap.spent } = .ok physicalResult
  agrees : IxIR2.Lower.Sim.OutcomeRel (store, value) physicalResult

/-- Source application reaches the selected binary physical function with
the checked capture followed by the runtime argument. Lower-stage dispatch,
invocation and execution are conclusions, including closure reclamation. -/
theorem Compiled.sourceRun
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (compiled : Compiled attached.target.artifact.program attached.target.artifact.validationContext.schemas
      limits (sourceProvenance attached)) (argument : Word)
    {entryFuel applyFuel : Nat} {function result : Ixon.Eval.Value}
    (oracles : @Ix.Compiler.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (sourceArguments #[argument]) = .ok result) :
    Nonempty (SourceRun attached compiled argument result) := by
  letI : Ix.Compiler.Sim.MemberScope := attached.source.memberScope
  obtain ⟨rawFunction, rawStore, functionRel, functionGraph, storeRenamed⟩ :=
    compiled.sourceFunction attached oracles contextWF entry
  have frameWF : (validatedMainFrame root).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [validatedMainFrame] at found
  have functionWF := (Ixon.Eval.eval_inlineSharing contextWF frameWF .nil (by rfl) entry).2
  obtain ⟨limit, rawResult, rawTrace, resultRel⟩ := Ix.Compiler.Sim.applyMany_sim_projectionSafe_inlineSharing
    attached.source.members oracles contextWF functionWF (sourceArguments.wf #[argument]) applied functionRel
    (sourceArguments.related _ _ #[argument])
  have trace := IxIR0.Readdress.ProjectionSafe.AppliesBelow.mapAddresses attached.source.runtimeTraceRenames rawTrace
  rw [rawArguments.renamed] at trace
  have rawOwned : IxIR1.Sim.RootOwnership rawStore [⟨.shared, .loc compiled.source.heap.location⟩] := by
    apply (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) rawStore _).mp
    rw [storeRenamed]
    exact compiled.source.heap.owned
  have ownership : IxIR1.Sim.RootOwnership rawStore
      (⟨.shared, .loc compiled.source.heap.location⟩ :: IxIR1.Sim.rootsFor .shared (#[argument].map rval).toList) := by
    simpa using (scalarArguments_owned rawOwned #[argument]).perm List.perm_append_comm
  obtain ⟨targetFuel, outputStore, outputValue, targetRun, outputGraph, _⟩ :=
    attached.source.runtimeApply functionGraph (rawArguments.graph _ _ #[argument]) trace (by simp [rawArguments]) ownership
  let store := IxIR1.Readdress.Store.mapAddresses
    (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) outputStore
  have targetApplied : IxIR1.applyGo attached.compiled.simulationSourceContext targetFuel
      compiled.source.result.store.heap (.loc compiled.source.heap.location) [rval argument] = .ok (store, outputValue) := by
    have renames : IxIR1.Readdress.Ctx.Renames
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw)
        (attached.source.exactTargetCtx (fun _ _ => none)) attached.compiled.simulationSourceContext :=
      attached.compiled.sourceContextRenames
    conv => lhs; arg 3; rw [← storeRenamed]
    rw [IxIR1.Readdress.applyGo_mapAddresses renames]
    have targetRun : IxIR1.applyGo (attached.source.exactTargetCtx (fun _ _ => none)) targetFuel rawStore
        (.loc compiled.source.heap.location) [rval argument] = .ok (outputStore, outputValue) := by
      simpa using targetRun
    rw [targetRun]
    rfl
  have declared : attached.compiled.simulationTargetContext.declarations compiled.source.address =
      some (.fn compiled.source.target) := compiled.source.declared
  obtain ⟨definition, functionTrace, _, matched, sourceDeclared⟩ :=
    attached.compiled.functionTrace_of_target_declaration
      (sourceContext := attached.compiled.simulationSourceContext) rfl rfl declared
  have safe : IxIR1.declPapSafe (.fn definition) = true := by
    change definition.papSafe = true
    rw [← matched.source, ← functionTrace.sourcePapSafe, matched.generated]
    exact compiled.source.safe
  obtain ⟨invokeFuel, invoked⟩ := compiled.source.heap.applied sourceDeclared safe argument targetApplied
  obtain ⟨controlFuel, heapFuel, physicalResult, physical, agrees⟩ :=
    attached.compiled.successfulFunctionSimulation declared compiled.source.safe
      (#[compiled.source.capture, argument].map rval) (by simpa using invoked)
      (compiled.source.heap.spent_empty.owned _) (compiled.source.heap.spent_empty.runtime _)
      (compiled.source.heap.spent_empty.image attached.compiled)
  exact ⟨{
    rawResult, rawStore := outputStore, store, value := outputValue
    applyFuel := targetFuel, invokeFuel, controlFuel, heapFuel, physicalResult
    sourceRelated := resultRel, valueRelated := outputGraph, storeRenamed := rfl
    applied := targetApplied, invoked, physical, agrees }⟩

end Ix.Compiler.X86.PhysicalScalar.Captured
