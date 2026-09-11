import Ix.Compiler.X86.PhysicalScalarCapturedInit
import Ix.Compiler.X86.ScalarBind

namespace Ix.Compiler.X86.PhysicalScalar.Captured

def policy : String := "physical-scalar-capture/1"

structure Compiled (program : IxIR2.Program)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (limits : Limits) (provenance : ELF.Provenance) where
  source : Initialized program schemas limits
  selected : Selected program source.address
  definitionFound : selected.entries[selected.scalar.program.entry]? = some (source.address, source.target)
  bound : Scalar.Bound selected.scalar source.capture
  native : Scalar.Output bound.checked
  stream : Stream.Certified native.target
  input : ELF.Input
  encoded : input.encoded = stream.output
  entry : input.entryBlock = native.target.program.entry
  provenanceBound : input.provenance = provenance
  object : ELF.Certified input

def compile (program : IxIR2.Program)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema) (provenance : ELF.Provenance)
    (name : String := "compilatrix_captured_scalar") (limits : Limits := {}) :
    Except String (Compiled program schemas limits provenance) := do
  let source ← checkInitializer program schemas limits
  let selected ← select program source.address
  if definitionFound : selected.entries[selected.scalar.program.entry]? = some (source.address, source.target) then
    let bound ← Scalar.bind selected.scalar source.capture
    let native ← Scalar.compile bound.checked
    let stream ← (Stream.encode native.target).mapError reprStr
    let input : ELF.Input := { encoded := stream.output, entryBlock := native.target.program.entry, exportName := name, provenance }
    let object ← (ELF.writeChecked input).mapError reprStr
    return {
      source, selected, definitionFound, bound, native, stream, input, encoded := rfl, entry := rfl
      provenanceBound := rfl, object }
  else throw "captured scalar selected entry differs from the initialized closure target"

/-- Every runtime Word executes the captured physical function with arguments
in capture-first order and returns through the complete unary ELF entry. -/
theorem Compiled.nativeReturns {program schemas limits provenance}
    (compiled : Compiled program schemas limits provenance) (argument : Word)
    (oracle : Ixon.Address → List IxIR2.Eval.RVal → Option IxIR2.Eval.RVal)
    (stack : Scalar.Stack) (depth : compiled.bound.checked.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt #[argument] ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, Runs (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical
      (frame compiled.source.target 0 0 #[compiled.source.capture, argument]) word ∧
      Nonempty (Scalar.ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack (some word)) := by
  have arity : #[compiled.source.capture, argument].size = compiled.bound.function.parameters := by
    simp [compiled.bound.binary]
  obtain ⟨result, evaluated⟩ := compiled.selected.scalar.function_total _ _ compiled.bound.found _ arity
  have contract := compiled.selected.contract (mode := .physical) (compiled.selected.declarations schemas oracle)
    compiled.definitionFound compiled.bound.found
  obtain ⟨word, success, physical⟩ := contract.evaluates _ result arity evaluated
  subst result
  obtain ⟨executed⟩ := compiled.native.root_run compiled.bound.entry (by rfl)
    (compiled.bound.evaluates argument evaluated) stack depth core stackPointer arguments readable writable
  have stream : Stream.Valid compiled.native.target.program compiled.input.encoded := by
    rw [compiled.encoded]
    exact compiled.stream.valid
  exact ⟨word, physical, executed.objectResult stream compiled.object.valid compiled.entry base flags⟩

theorem Compiled.physicalReturns {program schemas limits provenance}
    (compiled : Compiled program schemas limits provenance) (argument : Word)
    (oracle : Ixon.Address → List IxIR2.Eval.RVal → Option IxIR2.Eval.RVal)
    {controlFuel heapFuel : Nat} {store : IxIR2.Eval.Store} {result : IxIR2.Eval.Result}
    (physical : IxIR2.Eval.runFunction (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical
      compiled.source.target (#[compiled.source.capture, argument].map rval) controlFuel heapFuel store = .ok result)
    (stack : Scalar.Stack) (depth : compiled.bound.checked.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt #[argument] ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, result.value = rval word ∧
      result.store = (IxIR2.Eval.initialMachine compiled.source.target (#[compiled.source.capture, argument].map rval) 0 store).store ∧
      Nonempty (Scalar.ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack (some word)) := by
  obtain ⟨word, executed, native⟩ := compiled.nativeReturns argument oracle stack depth core stackPointer arguments readable writable base flags
  have contract := compiled.selected.contract (mode := .physical) (compiled.selected.declarations schemas oracle)
    compiled.definitionFound compiled.bound.found
  obtain ⟨value, heap⟩ := executed.agrees (by simp [compiled.source.binary]) contract.nonempty physical
  exact ⟨word, value, heap, native⟩

def sourceProvenance {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel) : ELF.Provenance :=
  .ixir1Policy (IxIR1.Optimizer.graphRoot attached.source.artifact.targetArtifacts attached.source.artifact.main) 7 1

def compileSource {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (name : String := "compilatrix_captured_scalar") (limits : Limits := {}) :
    Except String (Compiled attached.target.artifact.program attached.target.artifact.validationContext.schemas
      limits (sourceProvenance attached)) :=
  compile attached.target.artifact.program attached.target.artifact.validationContext.schemas
    (sourceProvenance attached) name limits

end Ix.Compiler.X86.PhysicalScalar.Captured
