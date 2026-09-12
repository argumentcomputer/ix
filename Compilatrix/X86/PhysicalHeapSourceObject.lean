import Compilatrix.X86.PhysicalHeapExport

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open Compilatrix.Pipeline (validatedEvalCtx validatedMainFrame validatedMainSource)

variable {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
  {config : Compilatrix.Pipeline.Config} {eraseFuel lowerFuel : Nat}

structure SourceResult
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.validationContext.schemas attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (result : Ixon.Eval.Value) (store : IxIR2.Eval.Store) (word : Word) (words : Words) : Prop where
  related : @Compilatrix.Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
    result (PhysicalScalar.rawArgument word) attached.source.memberScope
  applied : ∃ fuel, IxIR1.applyGo attached.compiled.simulationSourceContext fuel
    (PhysicalScalar.closureStore exported.source.address exported.source.target).heap (.loc 0)
      (values.map PhysicalScalar.rval).toList = .ok (store.heap, PhysicalScalar.rval word)
  invoked : ∃ fuel, IxIR1.invoke attached.compiled.simulationSourceContext fuel exported.source.address
    (values.map PhysicalScalar.rval).toList PhysicalScalar.invocationHeap = .ok (store.heap, PhysicalScalar.rval word)
  resources : HeapObservation 1 exported.compiled.selected.entryInterface.allocations store words

/-- Successful source application, ordinary checked compilation, physical
selection, finite native memory, and execution of the emitted ELF compose.
Every lower execution and the full reclamation result are conclusions. -/
theorem Exported.sourceReturns
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.validationContext.schemas attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (arity : values.size = exported.source.target.signature.params.size)
    {entryFuel applyFuel : Nat} {function result : Ixon.Eval.Value}
    (oracles : @Compilatrix.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (PhysicalScalar.sourceArguments values) = .ok result)
    (workspace : Workspace) (depth : exported.compiled.selected.entry < workspace.depth) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (arena : core.readReg .rdx = workspace.layout.region.base)
    (arguments : Scalar.ArgumentsAt values (HeapEntry.stateOf workspace core))
    (enough : exported.compiled.selected.entryInterface.allocations ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word store words, SourceResult attached exported values result store word words ∧
      Nonempty (HeapEntry.ObjectResult exported.compiled.object.bytes exported.compiled.input.exportName base flags core workspace word 0 words) := by
  obtain ⟨run⟩ := exported.source.sourceRun attached values arity oracles contextWF entry applied
  obtain ⟨word, words, valueEq, resources, native⟩ := exported.compiled.physicalReturns values
    (by simpa only [exported.same] using arity) (fun _ _ => none)
    (by simpa only [exported.same, initialStore, IxIR2.Pipeline.CompiledAttachment.simulationTargetContext,
      IxIR2.Pipeline.Attached.compiled] using run.physical)
    workspace depth core stack arena arguments enough bound readable writable base flags
  have value : run.value = PhysicalScalar.rval word := run.agrees.value.symm.trans valueEq
  have heap : run.store = run.physicalResult.store.heap := run.agrees.heap.symm
  have raw : run.rawResult = PhysicalScalar.rawArgument word := by
    have graph := run.valueRelated
    rw [value] at graph
    cases selected : run.rawResult <;>
      simp only [selected, IxIR0.Readdress.Value.mapAddresses] at graph <;> cases graph <;> rfl
  refine ⟨word, run.physicalResult.store, words, ⟨?_, ?_, ?_, resources⟩, native⟩
  · simpa [raw] using run.sourceRelated
  · exact ⟨run.applyFuel, by simpa only [heap, value] using run.applied⟩
  · exact ⟨run.invokeFuel, by simpa only [heap, value] using run.invoked⟩

/-- An observed source Nat equals the returned native Word without truncation. -/
theorem Exported.sourceNatReturns
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.validationContext.schemas attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (arity : values.size = exported.source.target.signature.params.size)
    {entryFuel applyFuel number : Nat} {function : Ixon.Eval.Value}
    (oracles : @Compilatrix.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (PhysicalScalar.sourceArguments values) = .ok (.litV (.natL number)))
    (workspace : Workspace) (depth : exported.compiled.selected.entry < workspace.depth) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (arena : core.readReg .rdx = workspace.layout.region.base)
    (arguments : Scalar.ArgumentsAt values (HeapEntry.stateOf workspace core))
    (enough : exported.compiled.selected.entryInterface.allocations ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word store words, word.toNat = number ∧ SourceResult attached exported values (.litV (.natL number)) store word words ∧
      Nonempty (HeapEntry.ObjectResult exported.compiled.object.bytes exported.compiled.input.exportName base flags core workspace word 0 words) := by
  obtain ⟨word, store, words, source, native⟩ := exported.sourceReturns attached values arity oracles contextWF entry applied
    workspace depth core stack arena arguments enough bound readable writable base flags
  have numberEq : word.toNat = number := by
    have related := source.related
    simp only [Compilatrix.Sim.InlinedValRel, Ixon.Eval.Value.inlineSharing, PhysicalScalar.rawArgument] at related
    cases related
    rfl
  exact ⟨word, store, words, numberEq, source, native⟩

end Compilatrix.X86.PhysicalHeap
