import Ix.Compiler.X86.PhysicalScalarCapturedSourceApply

namespace Ix.Compiler.X86.PhysicalScalar.Captured
open Ix.Compiler.Pipeline (validatedEvalCtx validatedMainFrame validatedMainSource)

variable {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
  {config : Ix.Compiler.Pipeline.Config} {eraseFuel lowerFuel : Nat} {limits : Limits}

/-- Exact source application and invocation, with the initializer's heap
fully reclaimed and every allocation accounted for. -/
structure SourceResult
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (compiled : Compiled attached.target.artifact.program attached.target.artifact.validationContext.schemas
      limits (sourceProvenance attached)) (argument : Word) (result : Ixon.Eval.Value) (word : Word) : Prop where
  related : @Ix.Compiler.Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
    result (rawArgument word) attached.source.memberScope
  applied : ∃ fuel, IxIR1.applyGo attached.compiled.simulationSourceContext fuel
    compiled.source.result.store.heap (.loc compiled.source.heap.location) [rval argument] =
      .ok (compiled.source.heap.spent, rval word)
  invoked : ∃ fuel, IxIR1.invoke attached.compiled.simulationSourceContext fuel compiled.source.address
    [rval compiled.source.capture, rval argument] compiled.source.heap.spent =
      .ok (compiled.source.heap.spent, rval word)
  empty : emptyHeap compiled.source.heap.spent
  accounted : compiled.source.heap.spent.frees = compiled.source.heap.spent.allocs

/-- For every runtime Word, ordinary source application composes with actual
captured PAP dispatch, physical CFG selection and execution of the complete
unary ELF. Finite stack, saved registers and outside memory are covered by
the native object result. No lower-stage execution is a caller premise. -/
theorem Compiled.sourceReturns
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
      function (sourceArguments #[argument]) = .ok result)
    (stack : Scalar.Stack) (depth : compiled.bound.checked.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt #[argument] ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, SourceResult attached compiled argument result word ∧
      Nonempty (Scalar.ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack (some word)) := by
  obtain ⟨run⟩ := compiled.sourceRun attached argument oracles contextWF entry applied
  obtain ⟨word, valueEq, heapEq, native⟩ := compiled.physicalReturns argument (fun _ _ => none)
    (by simpa only [IxIR2.Pipeline.CompiledAttachment.simulationTargetContext,
      IxIR2.Pipeline.Attached.compiled] using run.physical)
    stack depth core stackPointer arguments readable writable base flags
  have value : run.value = rval word := run.agrees.value.symm.trans valueEq
  have heap : run.store = compiled.source.heap.spent :=
    run.agrees.heap.symm.trans (congrArg IxIR2.Eval.Store.heap heapEq)
  have raw : run.rawResult = rawArgument word := by
    have graph := run.valueRelated
    rw [value] at graph
    cases selected : run.rawResult <;>
      simp only [selected, IxIR0.Readdress.Value.mapAddresses] at graph <;> cases graph <;> rfl
  refine ⟨word, ⟨?_, ?_, ?_, compiled.source.reclaimed.1, compiled.source.reclaimed.2.1⟩, native⟩
  · simpa [raw] using run.sourceRelated
  · exact ⟨run.applyFuel, by simpa [heap, value] using run.applied⟩
  · exact ⟨run.invokeFuel, by simpa [heap, value] using run.invoked⟩

theorem Compiled.sourceNatReturns
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (compiled : Compiled attached.target.artifact.program attached.target.artifact.validationContext.schemas
      limits (sourceProvenance attached)) (argument : Word)
    {entryFuel applyFuel number : Nat} {function : Ixon.Eval.Value}
    (oracles : @Ix.Compiler.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (sourceArguments #[argument]) = .ok (.litV (.natL number)))
    (stack : Scalar.Stack) (depth : compiled.bound.checked.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt #[argument] ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, word.toNat = number ∧ SourceResult attached compiled argument (.litV (.natL number)) word ∧
      Nonempty (Scalar.ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack (some word)) := by
  obtain ⟨word, source, native⟩ := compiled.sourceReturns attached argument oracles contextWF entry applied
    stack depth core stackPointer arguments readable writable base flags
  have numberEq : word.toNat = number := by
    have related := source.related
    simp only [Ix.Compiler.Sim.InlinedValRel, Ixon.Eval.Value.inlineSharing, rawArgument] at related
    cases related
    rfl
  exact ⟨word, numberEq, source, native⟩

end Ix.Compiler.X86.PhysicalScalar.Captured
