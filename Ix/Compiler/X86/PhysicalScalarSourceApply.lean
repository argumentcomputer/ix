import Ix.Compiler.X86.PhysicalScalarSourceHeap
import Ix.Compiler.IxIR2.SourcePipelineSim

namespace Ix.Compiler.X86.PhysicalScalar
open Ix.Compiler.Pipeline (ValidatedCompilation validatedEvalCtx validatedMainFrame validatedMainSource)

variable {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
  {config : Ix.Compiler.Pipeline.Config} {eraseFuel lowerFuel : Nat}

/-- The actual compiled module identifies the source-related uncaptured
function and its exact heap image, including both compiler address passes. -/
theorem Exported.sourceFunction
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
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
          (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap) rawFunction) (.loc 0) ∧
      IxIR1.Readdress.Store.mapAddresses
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) rawStore =
        (closureStore exported.source.address exported.source.target).heap := by
  obtain ⟨rawFunction, _, store, value, _, _, result, related, graph, _, physical, heaps⟩ :=
    attached.sourcePhysical oracles contextWF entry
  obtain ⟨count, canonical⟩ := exported.source.path.runMain attached.target.artifact.validationContext.schemas (fun _ _ => none)
  have same := IxIR2.Eval.runMain_success_unique exported.source.path.nullary exported.source.path.nonempty physical canonical
  have valueEq : value = .loc 0 := heaps.value.symm.trans same.2
  have storeEq : store = (closureStore exported.source.address exported.source.target).heap :=
    heaps.heap.symm.trans (congrArg IxIR2.Eval.Store.heap same.1)
  obtain ⟨rawStore, renamed, graph⟩ := graph
  exact ⟨rawFunction, rawStore, related, valueEq ▸ graph, renamed.symm.trans storeEq⟩

/-- A composed source application keeps the actual PAP dispatch, addressed
function invocation, physical execution, and source value graph together. -/
structure SourceRun
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (result : Ixon.Eval.Value) where
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
    (closureStore exported.source.address exported.source.target).heap (.loc 0) (values.map rval).toList = .ok (store, value)
  invoked : IxIR1.invoke attached.compiled.simulationSourceContext invokeFuel exported.source.address
    (values.map rval).toList invocationHeap = .ok (store, value)
  physical : IxIR2.Eval.runFunction attached.compiled.simulationTargetContext .physical
    exported.source.target (values.map rval) controlFuel heapFuel { heap := invocationHeap } = .ok physicalResult
  agrees : IxIR2.Lower.Sim.OutcomeRel (store, value) physicalResult

/-- Runtime Ixon application reaches the selected physical function through
the ordinary compiler. Only source execution, sharing/oracle assumptions,
and the scalar ABI arity are supplied by the caller. -/
theorem Exported.sourceRun
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (arity : values.size = exported.source.target.signature.params.size)
    {entryFuel applyFuel : Nat} {function result : Ixon.Eval.Value}
    (oracles : @Ix.Compiler.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (sourceArguments values) = .ok result) :
    Nonempty (SourceRun attached exported values result) := by
  letI : Ix.Compiler.Sim.MemberScope := attached.source.memberScope
  obtain ⟨rawFunction, rawStore, functionRel, functionGraph, storeRenamed⟩ :=
    exported.sourceFunction attached oracles contextWF entry
  have frameWF : (validatedMainFrame root).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [validatedMainFrame] at found
  have functionWF := (Ixon.Eval.eval_inlineSharing contextWF frameWF .nil (by rfl) entry).2
  obtain ⟨limit, rawResult, rawTrace, resultRel⟩ := Ix.Compiler.Sim.applyMany_sim_projectionSafe_inlineSharing
    attached.source.members oracles contextWF functionWF (sourceArguments.wf values) applied functionRel
    (sourceArguments.related _ _ values)
  have trace := IxIR0.Readdress.ProjectionSafe.AppliesBelow.mapAddresses attached.source.runtimeTraceRenames rawTrace
  rw [rawArguments.renamed] at trace
  have rawOwned : IxIR1.Sim.RootOwnership rawStore [⟨.shared, .loc 0⟩] := by
    apply (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) rawStore _).mp
    rw [storeRenamed]
    exact closureStore.owned _ _
  have ownership : IxIR1.Sim.RootOwnership rawStore
      (⟨.shared, .loc 0⟩ :: IxIR1.Sim.rootsFor .shared (values.map rval).toList) := by
    simpa using (scalarArguments_owned rawOwned values).perm List.perm_append_comm
  have nonempty : rawArguments values ≠ [] := by
    intro empty
    have length : values.size = 0 := by
      simpa only [rawArguments, List.length_map, Array.length_toList, List.length_nil] using congrArg List.length empty
    have positive := exported.source.path.positive
    omega
  obtain ⟨targetFuel, outputStore, outputValue, targetRun, outputGraph, _⟩ :=
    attached.source.runtimeApply functionGraph (rawArguments.graph _ _ values) trace nonempty ownership
  let store := IxIR1.Readdress.Store.mapAddresses
    (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) outputStore
  have targetApplied : IxIR1.applyGo attached.compiled.simulationSourceContext targetFuel
      (closureStore exported.source.address exported.source.target).heap (.loc 0) (values.map rval).toList =
      .ok (store, outputValue) := by
    have renames : IxIR1.Readdress.Ctx.Renames
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw)
        (attached.source.exactTargetCtx (fun _ _ => none)) attached.compiled.simulationSourceContext :=
      attached.compiled.sourceContextRenames
    rw [← storeRenamed, IxIR1.Readdress.applyGo_mapAddresses renames, targetRun]
    rfl
  have declared : attached.compiled.simulationTargetContext.declarations exported.source.address =
      some (.fn exported.source.target) := exported.source.path.declared
  obtain ⟨definition, functionTrace, _, matched, sourceDeclared⟩ :=
    attached.compiled.functionTrace_of_target_declaration
      (sourceContext := attached.compiled.simulationSourceContext) rfl rfl declared
  have safe : IxIR1.declPapSafe (.fn definition) = true := by
    change definition.papSafe = true
    rw [← matched.source, ← functionTrace.sourcePapSafe, matched.generated]
    exact exported.source.path.papSafe
  obtain ⟨invokeFuel, invoked⟩ := closureStore.applied sourceDeclared safe arity targetApplied
  obtain ⟨controlFuel, heapFuel, physicalResult, physical, agrees⟩ :=
    attached.compiled.successfulFunctionSimulation declared exported.source.path.papSafe
      (values.map rval) invoked (invocationHeap.owned values) (invocationHeap.runtime values)
      (invocationHeap.image attached.compiled)
  exact ⟨{
    rawResult, rawStore := outputStore, store, value := outputValue
    applyFuel := targetFuel, invokeFuel, controlFuel, heapFuel, physicalResult
    sourceRelated := resultRel, valueRelated := outputGraph, storeRenamed := rfl
    applied := targetApplied, invoked, physical, agrees }⟩

end Ix.Compiler.X86.PhysicalScalar
