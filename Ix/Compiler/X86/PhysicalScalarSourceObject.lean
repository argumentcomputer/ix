import Ix.Compiler.X86.PhysicalScalarSourceApply

namespace Ix.Compiler.X86.PhysicalScalar
open Ix.Compiler.Pipeline (validatedEvalCtx validatedMainFrame validatedMainSource)

variable {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
  {config : Ix.Compiler.Pipeline.Config} {eraseFuel lowerFuel : Nat}

/-- Source value agreement and complete reclamation of the module's exported
PAP. The scalar body preserves the resulting dead slot and exact counters. -/
structure SourceResult
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (result : Ixon.Eval.Value) (word : Word) : Prop where
  related : @Ix.Compiler.Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
    result (rawArgument word) attached.source.memberScope
  applied : ∃ fuel, IxIR1.applyGo attached.compiled.simulationSourceContext fuel
    (closureStore exported.source.address exported.source.target).heap (.loc 0) (values.map rval).toList =
      .ok (invocationHeap, rval word)
  invoked : ∃ fuel, IxIR1.invoke attached.compiled.simulationSourceContext fuel exported.source.address
    (values.map rval).toList invocationHeap = .ok (invocationHeap, rval word)

/-- The ordinary source compiler, actual physical CFG selector, complete ELF,
and finite native stack compose for every admitted runtime Word vector.
The caller supplies source execution and the declared ABI/environment facts;
all lower-stage applications and native executions are conclusions. -/
theorem Exported.sourceReturns
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
      function (sourceArguments values) = .ok result)
    (stack : Scalar.Stack) (depth : exported.compiled.selected.scalar.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt values ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, SourceResult attached exported values result word ∧
      Nonempty (Scalar.ObjectResult exported.compiled.object.bytes exported.compiled.input.exportName base flags core stack (some word)) := by
  obtain ⟨run⟩ := exported.sourceRun attached values arity oracles contextWF entry applied
  obtain ⟨word, valueEq, heapEq, native⟩ := exported.compiled.physicalReturns values
    (by simpa [exported.same] using arity) attached.target.artifact.validationContext.schemas (fun _ _ => none)
    (by simpa only [exported.same, IxIR2.Pipeline.CompiledAttachment.simulationTargetContext,
      IxIR2.Pipeline.Attached.compiled] using run.physical)
    stack depth core stackPointer arguments readable writable base flags
  have value : run.value = rval word := run.agrees.value.symm.trans valueEq
  have heap : run.store = invocationHeap := run.agrees.heap.symm.trans (congrArg IxIR2.Eval.Store.heap heapEq)
  have raw : run.rawResult = rawArgument word := by
    have graph := run.valueRelated
    rw [value] at graph
    cases selected : run.rawResult <;>
      simp only [selected, IxIR0.Readdress.Value.mapAddresses] at graph <;> cases graph <;> rfl
  refine ⟨word, ⟨?_, ?_, ?_⟩, native⟩
  · simpa [raw] using run.sourceRelated
  · exact ⟨run.applyFuel, by simpa [heap, value] using run.applied⟩
  · exact ⟨run.invokeFuel, by simpa [heap, value] using run.invoked⟩

/-- Exact numeric observation of the source-to-object endpoint. A returned
source Nat is representable and equals RAX's Word value without truncation. -/
theorem Exported.sourceNatReturns
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (arity : values.size = exported.source.target.signature.params.size)
    {entryFuel applyFuel number : Nat} {function : Ixon.Eval.Value}
    (oracles : @Ix.Compiler.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (sourceArguments values) = .ok (.litV (.natL number)))
    (stack : Scalar.Stack) (depth : exported.compiled.selected.scalar.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt values ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, word.toNat = number ∧ SourceResult attached exported values (.litV (.natL number)) word ∧
      Nonempty (Scalar.ObjectResult exported.compiled.object.bytes exported.compiled.input.exportName base flags core stack (some word)) := by
  obtain ⟨word, source, native⟩ := exported.sourceReturns attached values arity oracles contextWF entry applied
    stack depth core stackPointer arguments readable writable base flags
  have numberEq : word.toNat = number := by
    have related := source.related
    simp only [Ix.Compiler.Sim.InlinedValRel, Ixon.Eval.Value.inlineSharing, rawArgument] at related
    cases related
    rfl
  exact ⟨word, numberEq, source, native⟩

end Ix.Compiler.X86.PhysicalScalar
