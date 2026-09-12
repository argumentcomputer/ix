import Compilatrix.X86.PhysicalHeapRoot
import Compilatrix.IxIR2.WirePipeline

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (RVal Result)

def policy : String := "physical-leaf-cfg/1"

structure Compiled (schemas : Schemas) (program : IxIR2.Program) (root : Ixon.Address)
    (baseline : Bool) (provenance : ELF.Provenance) where
  selected : Selected schemas program root
  native : HeapTarget.Output selected baseline
  stream : Stream.Certified native.target
  input : ELF.Input
  encoded : input.encoded = stream.output
  entry : input.entryBlock = native.target.program.entry
  provenanceBound : input.provenance = provenance
  object : ELF.Certified input

def compile (schemas : Schemas) (program : IxIR2.Program) (root : Ixon.Address)
    (baseline : Bool) (provenance : ELF.Provenance) (name : String := "compilatrix_heap_cfg") :
    Except String (Compiled schemas program root baseline provenance) := do
  let selected ← select schemas program root
  let native ← HeapTarget.compile selected baseline
  let stream ← (Stream.encode native.target).mapError reprStr
  let input : ELF.Input := { encoded := stream.output, entryBlock := native.target.program.entry, exportName := name, provenance }
  let object ← (ELF.writeChecked input).mapError reprStr
  return { selected, native, stream, input, encoded := rfl, entry := rfl, provenanceBound := rfl, object }

/-- The object pins the complete physical snapshot, including its schema and
layout preimages and the versioned source ownership policy. -/
def compileSnapshot (artifact : IxIR2.Wire.Artifact) {limits : IxIR2.Validate.Limits}
    (_checked : IxIR2.Wire.Checked limits artifact) (root : Ixon.Address) (baseline : Bool := false)
    (name : String := "compilatrix_heap_cfg") :
    Except String (Compiled artifact.context.schemas artifact.program root baseline (.ixir2 artifact.address)) :=
  compile artifact.context.schemas artifact.program root baseline (.ixir2 artifact.address) name

/-- Execution of the exact parsed ELF with finite heap and stack capacity,
exact counters, complete reclamation, and preserved caller state. -/
theorem Compiled.policyReturns {schemas program root baseline provenance}
    (compiled : Compiled schemas program root baseline provenance)
    (values : Array Word) (arity : values.size = compiled.selected.entryInterface.definition.signature.params.size)
    (oracle : Ixon.Address → List RVal → Option RVal) {controlFuel heapFuel : Nat} {result : Result}
    (physical : IxIR2.Eval.Policy.runFunction .suspendedCallsV1
      (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical compiled.selected.entryInterface.definition
      (values.map PhysicalScalar.rval) controlFuel heapFuel (initialStore baseline) = .ok result)
    (workspace : Workspace) (depth : compiled.selected.entry < workspace.depth) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (arena : core.readReg .rdx = workspace.layout.region.base)
    (arguments : Scalar.ArgumentsAt values (HeapEntry.stateOf workspace core))
    (enough : compiled.selected.entryInterface.allocations ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word words, result.value = PhysicalScalar.rval word ∧
      HeapObservation (initialOffset baseline) compiled.selected.entryInterface.allocations result.store words ∧
      Nonempty (HeapEntry.ObjectResult compiled.object.bytes compiled.input.exportName base flags core workspace word 0 words) := by
  obtain ⟨word, words, value, resources, ⟨native⟩⟩ := Output.physicalReturns compiled.native values arity oracle physical
    workspace depth core stack arena arguments enough bound readable writable
  have stream : Stream.Valid compiled.native.target.program compiled.input.encoded := by
    rw [compiled.encoded]
    exact compiled.stream.valid
  exact ⟨word, words, value, resources, native.object stream compiled.object.valid compiled.entry base flags⟩

/-- Every successful baseline run is also a successful suspended-call run.
The ordinary source compiler therefore uses the same object endpoint. -/
theorem Compiled.physicalReturns {schemas program root baseline provenance}
    (compiled : Compiled schemas program root baseline provenance)
    (values : Array Word) (arity : values.size = compiled.selected.entryInterface.definition.signature.params.size)
    (oracle : Ixon.Address → List RVal → Option RVal) {controlFuel heapFuel : Nat} {result : Result}
    (physical : IxIR2.Eval.runFunction (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical
      compiled.selected.entryInterface.definition (values.map PhysicalScalar.rval) controlFuel heapFuel (initialStore baseline) = .ok result)
    (workspace : Workspace) (depth : compiled.selected.entry < workspace.depth) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (arena : core.readReg .rdx = workspace.layout.region.base)
    (arguments : Scalar.ArgumentsAt values (HeapEntry.stateOf workspace core))
    (enough : compiled.selected.entryInterface.allocations ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ word words, result.value = PhysicalScalar.rval word ∧
      HeapObservation (initialOffset baseline) compiled.selected.entryInterface.allocations result.store words ∧
      Nonempty (HeapEntry.ObjectResult compiled.object.bytes compiled.input.exportName base flags core workspace word 0 words) := by
  obtain ⟨summary⟩ := Output.summaries compiled.native (compiled.selected.declarations oracle)
    compiled.selected.entry compiled.selected.entryInterface compiled.selected.entryFound
  dsimp only [IxIR2.Eval.Context.ofProgram] at summary
  rw [IxIR2.Eval.runFunction_eq_runMachine (by simpa using arity) summary.nonempty] at physical
  have run := IxIR2.Eval.Policy.of_originalRun physical
  rw [← IxIR2.Eval.Policy.runFunction_eq_runMachine (by simpa using arity) summary.nonempty] at run
  exact compiled.policyReturns values arity oracle run workspace depth core stack arena arguments enough bound readable writable base flags

def sourceProvenance {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel) : ELF.Provenance :=
  .ixir2 (IxIR2.Wire.ofCompiled attached.compiled).address

end Compilatrix.X86.PhysicalHeap
