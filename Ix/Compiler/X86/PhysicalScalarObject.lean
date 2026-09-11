import Ix.Compiler.X86.PhysicalScalarContracts
import Ix.Compiler.X86.ScalarObject
import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR1.Optimizer

namespace Ix.Compiler.X86.PhysicalScalar

def policy : String := "physical-scalar-cfg/1"

structure Compiled (program : IxIR2.Program) (root : Ixon.Address) (provenance : ELF.Provenance) where
  selected : Selected program root
  definition : IxIR2.Function
  definitionFound : selected.entries[selected.scalar.program.entry]? = some (root, definition)
  target : Scalar.Function
  targetFound : selected.scalar.program.functions[selected.scalar.program.entry]? = some target
  native : Scalar.Output selected.scalar
  stream : Stream.Certified native.target
  input : ELF.Input
  encoded : input.encoded = stream.output
  entry : input.entryBlock = native.target.program.entry
  provenanceBound : input.provenance = provenance
  object : ELF.Certified input

def compile (program : IxIR2.Program) (root : Ixon.Address) (provenance : ELF.Provenance)
    (name : String := "compilatrix_physical_scalar") : Except String (Compiled program root provenance) := do
  let selected ← select program root
  match definitionFound : selected.entries[selected.scalar.program.entry]? with
  | none => throw "physical scalar selected entry is missing"
  | some (address, definition) =>
    if same : address = root then
      match targetFound : selected.scalar.program.functions[selected.scalar.program.entry]? with
      | none => throw "physical scalar native entry is missing"
      | some target =>
        let native ← Scalar.compile selected.scalar
        let stream ← (Stream.encode native.target).mapError reprStr
        let input : ELF.Input := { encoded := stream.output, entryBlock := native.target.program.entry, exportName := name, provenance }
        let object ← (ELF.writeChecked input).mapError reprStr
        return {
          selected, definition, definitionFound := by simpa [same] using definitionFound
          target, targetFound, native, stream, input, encoded := rfl, entry := rfl, provenanceBound := rfl, object }
    else throw "physical scalar entry does not match the requested function"

theorem Compiled.arity {program root provenance} (compiled : Compiled program root provenance) :
    compiled.target.parameters = compiled.definition.signature.params.size :=
  (compiled.selected.contract (mode := .physical) (compiled.selected.declarations (fun _ _ => none) (fun _ _ => none))
    compiled.definitionFound compiled.targetFound).arity

/-- Universal execution of the actual exported ELF, with finite stack
capacity and complete register, return-address, and outside-memory behavior.
The same Word result has a physical CFG execution under every caller/heap. -/
theorem Compiled.nativeReturns {program root provenance} (compiled : Compiled program root provenance)
    (values : Array Word) (arity : values.size = compiled.definition.signature.params.size)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (oracle : Ixon.Address → List IxIR2.Eval.RVal → Option IxIR2.Eval.RVal)
    (stack : Scalar.Stack) (depth : compiled.selected.scalar.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt values ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, Runs (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical (frame compiled.definition 0 0 values) word ∧
      Nonempty (Scalar.ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack (some word)) := by
  have argumentArity := arity.trans compiled.arity.symm
  obtain ⟨result, evaluated⟩ := compiled.selected.scalar.function_total _ _ compiled.targetFound values argumentArity
  have contract := compiled.selected.contract (mode := .physical) (compiled.selected.declarations schemas oracle)
    compiled.definitionFound compiled.targetFound
  obtain ⟨word, success, physical⟩ := contract.evaluates values result argumentArity evaluated
  subst result
  obtain ⟨executed⟩ := compiled.native.root_run compiled.targetFound argumentArity evaluated stack depth core
    stackPointer arguments readable writable
  have stream : Stream.Valid compiled.native.target.program compiled.input.encoded := by
    rw [compiled.encoded]
    exact compiled.stream.valid
  exact ⟨word, physical, executed.objectResult stream compiled.object.valid compiled.entry base flags⟩

/-- Successful-run preservation for every selected physical CFG. The premise
is an execution of that exact input function; byte execution of the exact
emitted ELF and finite stack safety are conclusions. -/
theorem Compiled.physicalReturns {program root provenance} (compiled : Compiled program root provenance)
    (values : Array Word) (arity : values.size = compiled.definition.signature.params.size)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (oracle : Ixon.Address → List IxIR2.Eval.RVal → Option IxIR2.Eval.RVal)
    {controlFuel heapFuel : Nat} {store : IxIR2.Eval.Store} {result : IxIR2.Eval.Result}
    (physical : IxIR2.Eval.runFunction (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical
      compiled.definition (values.map rval) controlFuel heapFuel store = .ok result)
    (stack : Scalar.Stack) (depth : compiled.selected.scalar.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : Scalar.ArgumentsAt values ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word, result.value = rval word ∧
      result.store = (IxIR2.Eval.initialMachine compiled.definition (values.map rval) 0 store).store ∧
      Nonempty (Scalar.ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack (some word)) := by
  obtain ⟨word, executed, native⟩ := compiled.nativeReturns values arity schemas oracle stack depth core stackPointer arguments readable writable base flags
  have contract := compiled.selected.contract (mode := .physical) (compiled.selected.declarations schemas oracle)
    compiled.definitionFound compiled.targetFound
  obtain ⟨value, heap⟩ := executed.agrees arity contract.nonempty physical
  exact ⟨word, value, heap, native⟩

def sourceProvenance {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel) : ELF.Provenance :=
  .ixir1Policy (IxIR1.Optimizer.graphRoot attached.source.artifact.targetArtifacts attached.source.artifact.main) 6 1

/-- This attachment selects the physical IxIR₂ produced by the full validated
source compiler. Its object provenance pins the actual IxIR₁ root and this
physical selection policy; it does not re-read erased source to select code. -/
def compileSource {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (entry : Ixon.Address) (name : String := "compilatrix_physical_scalar") :
    Except String (Compiled attached.target.artifact.program entry (sourceProvenance attached)) :=
  compile attached.target.artifact.program entry (sourceProvenance attached) name

end Ix.Compiler.X86.PhysicalScalar
