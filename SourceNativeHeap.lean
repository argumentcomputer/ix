import Compilatrix.X86.PhysicalHeapSources
import Compilatrix.X86.PhysicalHeapRejections
import Compilatrix.X86.PhysicalHeapSourceObject
import Compilatrix.X86.HeapReject
import Compilatrix.Coverage.Snapshot
import Compilatrix.IxIR2.WireJson
import Compilatrix.Tools.Check

open Lean Compilatrix Compilatrix.X86 Compilatrix.Tools.Check
namespace HeapGate

def inputs : List (Nat × Nat) :=
  let m := UInt64.size - 1
  [(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]

def workspaceWords (depth : Nat) : Nat := 272 + 34 * depth + 2

def core (depth a b capacity : Nat) : Core :=
  let low : Word := 0x10000
  let top := low + (8 * (workspaceWords depth - 1)).toUInt64
  let allowed := fun address : Word => decide (low ≤ address ∧ address < top + 8)
  let memory : Memory := { bytes := fun address => (address ^^^ 0xa7).toUInt8, readable := allowed, writable := allowed }
  let registers : Registers := fun register => 0x1020304050607080 + (SysV.calleeSaved.toList.idxOf register + 1).toUInt64
  { registers := (((registers.set .rsp top).set .rdi a.toUInt64).set .rsi b.toUInt64).set .rdx low
    memory := (memory.write64 (low + 8) capacity.toUInt64).write64 top 0x12345678 }

def wordAt (core : Core) (index : Nat) : Word := core.memory.read64 (0x10000 + (8 * index).toUInt64)

def heapNumbers (store : IxIR1.Store) : Array Nat :=
  #[store.allocs, store.frees, store.reuses, store.rcops, store.nodes.size, store.live]

def rejectExcept (name : String) (value : Except String α) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"heap CFG unexpectedly accepted {name}")

def byteRun (bytes : ByteArray) (name : String) (initial : Core) (wanted status : Nat) : IO (Nat × ByteEval.State) := do
  let text ← present (ELFRead.text? bytes) "heap ELF text is missing"
  let entry ← present (ELF.entry? bytes name) "heap ELF export is missing"
  let mut state : ByteEval.State := ⟨initial, 0x400000 + entry.toUInt64, {}⟩
  let mut count := 0
  for _ in [:20000] do
    if state.rip == 0x12345678 then break
    state ← checked ((ByteEval.step text 0x400000 state).mapError reprStr)
    count := count + 1
  need (state.rip == 0x12345678 && state.core.readReg .rax == wanted.toUInt64 && state.core.readReg .rdx == status.toUInt64)
    "heap ELF returned the wrong value/status/address"
  need (state.core.readReg .rsp == initial.readReg .rsp + 8 && state.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "heap ELF failed to restore the stack or saved registers"
  let parsed ← checked ((ObjectEval.run bytes name 0x400000 count initial).mapError reprStr)
  need (parsed.rip == state.rip && parsed.core.readReg .rax == state.core.readReg .rax && parsed.core.readReg .rdx == state.core.readReg .rdx)
    "complete parsed heap object disagrees with byte execution"
  for address in [(0xffff : Word), 0xfff8, initial.readReg .rsp + 8, initial.readReg .rsp + 16] do
    need (state.core.memory.bytes address == initial.memory.bytes address) "heap object changed an outside canary"
  return (count, state)

def observeNative {schemas program root baseline provenance}
    (compiled : PhysicalHeap.Compiled schemas program root baseline provenance) (name : String)
    (depth a b : Nat) (result : IxIR2.Eval.Result) : IO Nat := do
  let demand := compiled.selected.entryInterface.allocations
  let initial := core depth a b (if a % 2 == 0 then demand else 64)
  let .lit (.nat wanted) := result.value | throw (IO.userError "heap physical result is not a Nat")
  let typed := X86.runFrom Runtime.rejecting compiled.native.target 20000 initial
  need (typed.status == .halted wanted.toUInt64 && typed.core.readReg .rax == wanted.toUInt64 && typed.core.readReg .rdx == 0)
    "heap typed native result disagrees"
  need (typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "heap typed native caller restoration failed"
  let (count, native) ← byteRun compiled.object.bytes compiled.input.exportName initial wanted 0
  let used := result.store.heap.nodes.size - PhysicalHeap.initialOffset baseline
  need (used ≤ demand && result.store.live == 0 && result.store.heap.allocs == result.store.heap.frees &&
    result.store.heap.nodes.all Option.isNone) "heap physical execution did not reclaim all allocations"
  need (wordAt native.core 0 == (32 * used).toUInt64 && wordAt native.core 1 == wordAt initial 1 && wordAt native.core 9 == 0)
    "heap cursor, capacity, or outstanding reservation count disagrees"
  for field in [2:9] do
    need ((wordAt native.core field).toNat == PhysicalHeap.counters result.store field) s!"heap native counter {field} disagrees"
  for index in [:272] do
    need (wordAt typed.core index == wordAt native.core index) "typed and ELF heap words disagree"
    if 10 ≤ index && index < 16 || 16 + 4 * used ≤ index then
      need (wordAt native.core index == wordAt initial index) "heap execution touched an unused header/cell word"
  for index in [:used] do
    need (wordAt native.core (16 + 4 * index) == 0) "native cell remained live or reserved"
  if name == "unique-diamond" then
    need (wordAt native.core 17 == 23 && wordAt native.core 18 == 19) "parallel edge copies changed reused fields"
  if name == "hot-credit" then need (wordAt native.core 17 == a.toUInt64) "hot credit lost its runtime field"
  if name == "shared-pair" then
    need (wordAt native.core 17 == a.toUInt64 && wordAt native.core 18 == b.toUInt64) "shared pair fields changed"
  return count

def capacityRejections {schemas program root baseline provenance}
    (compiled : PhysicalHeap.Compiled schemas program root baseline provenance) : IO Nat := do
  let depth := compiled.selected.entry + 1
  let demand := compiled.selected.entryInterface.allocations
  need (demand > 0) "heap fixture unexpectedly allocates no cells"
  for limit in [demand - 1, 65, UInt64.size - 1] do
    let initial := core depth 2 3 limit
    let typed := X86.runFrom Runtime.rejecting compiled.native.target 20 initial
    need (typed.status == .halted 0 && typed.core.readReg .rdx == 1 &&
      typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
      "heap capacity rejection did not preserve caller state"
    let (_, native) ← byteRun compiled.object.bytes compiled.input.exportName initial 0 1
    for index in [:workspaceWords depth] do
      need (wordAt typed.core index == wordAt initial index && wordAt native.core index == wordAt initial index)
        "heap capacity rejection wrote a workspace word"
  let initial := core depth 2 3 64
  let unwritable := { initial with memory := { initial.memory with writable := fun _ => false } }
  match (X86.runFrom Runtime.rejecting compiled.native.target 20000 unwritable).status with
  | .trapped (.memoryFault _) => pure ()
  | _ => throw (IO.userError "heap unwritable workspace did not trap")
  let definition := compiled.selected.entryInterface.definition
  let calls := definition.blocks.any fun block =>
    block.instructions.any (fun | .call .. => true | _ => false) ||
      match block.terminator with | .tailCall .. => true | _ => false
  if calls then
    let allowed := fun address : Word => initial.memory.readable address &&
      decide (address < 0x10000 + 2176 || initial.readReg .rsp - 280 ≤ address)
    let short := { initial with memory := { initial.memory with readable := allowed, writable := allowed } }
    match (X86.runFrom Runtime.rejecting compiled.native.target 20000 short).status with
    | .trapped (.memoryFault _) => return 5
    | _ => throw (IO.userError "heap callee entered an unmapped activation record")
  return 4

def certificateRejections {schemas program root baseline provenance}
    (compiled : PhysicalHeap.Compiled schemas program root baseline provenance)
    (emission : HeapTarget.Emission := .tree) : IO Nat := do
  let target := compiled.native.target.program
  let plan ← present compiled.native.plans[compiled.selected.entry]? "heap entry plan is missing"
  let original ← present target.blocks[plan.entry.toNat]? "heap prologue block is missing"
  let changed := { target with
    blocks := target.blocks.setIfInBounds plan.entry.toNat { original with instructions := #[.mov .w64 .rax (.imm 0)] } }
  need (!(plan.matches changed (compiled.native.plans.map (·.entry))
    compiled.selected.entryInterface.parameters.size plan.body.tree)) "heap frame certificate accepted a changed prologue"
  let entry ← present target.blocks[compiled.native.entry.entry.toNat]? "heap guard block is missing"
  let changed := { target with
    blocks := target.blocks.setIfInBounds compiled.native.entry.entry.toNat { entry with terminator := .jump compiled.native.entry.adapter } }
  need (!(compiled.native.entry.matches changed baseline plan.entry compiled.selected.entryInterface.allocations))
    "heap entry certificate accepted a bypassed capacity guard"
  let stream := compiled.stream.output
  need (!(Stream.check target { stream with text := stream.text.set! 0 0 })) "heap stream certificate accepted corrupted code"
  if emission == .tree then return 3
  let candidate : HeapTarget.Candidate := {
    blocks := target.blocks, plans := compiled.native.plans, entry := compiled.native.entry }
  let _ ← checked (HeapTarget.checkCandidate compiled.selected baseline candidate)
  let mut count := 3
  for index in [:target.blocks.size] do
    let block := target.blocks[index]!
    let instruction := { block with instructions := block.instructions.push (.mov .w64 .rax (.imm 0)) }
    let control := { block with terminator := if block.terminator == .ret then .jump index.toUInt32 else .ret }
    for changed in [instruction, control] do
      rejectExcept "shared block instruction/control" (HeapTarget.checkCandidate compiled.selected baseline
        { candidate with blocks := target.blocks.set! index changed })
      count := count + 1
  rejectExcept "shared function coverage" (HeapTarget.checkCandidate compiled.selected baseline
    { candidate with plans := #[] })
  return count + 1

def admission : IO (Array String) := do
  let mut rejected := #[]
  for (name, artifact) in PhysicalHeap.Examples.rejections do
    rejectExcept name (PhysicalHeap.select artifact.context.schemas artifact.program PhysicalHeap.Examples.root)
    rejected := rejected.push name
  for name in ["unique-diamond", "hot-credit"] do
    let artifact := PhysicalHeap.Examples.artifact name
    let legacy := { artifact with policy := { artifact.policy with credits := .callLocalV0 } }
    rejectExcept s!"{name}/call-local-policy" (legacy.check IxIR2.Validate.defaultLimits)
  return rejected

def sourceObservation (source : Coverage.Source) (attached : source.Attached)
    (function : Ixon.Eval.Value) (rawFunction : IxIR0.Value) (moduleStore : IxIR1.Store) (moduleValue : IxIR1.RVal)
    (values : Array Word) (wanted : Nat) (physical : IxIR2.Eval.Result) : IO Json := do
  let context := Pipeline.validatedEvalCtx source.constants source.config
  let result ← checked ((Ixon.Eval.applyMany context 20000 function (PhysicalScalar.sourceArguments values)).mapError reprStr)
  need (match result with | .litV (.natL number) => number == wanted | _ => false) "heap source application returned the wrong Nat"
  let rawContext : IxIR0.Ctx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
  let mut raw := rawFunction
  for argument in PhysicalScalar.rawArguments values do
    raw ← checked ((IxIR0.apply rawContext 20000 raw argument).mapError reprStr)
  need (match raw with | .lit (.nat number) => number == wanted | _ => false) "heap erased source application disagrees"
  let (heap, value) ← checked ((IxIR1.applyGo attached.compiled.simulationSourceContext 2000 moduleStore moduleValue
    (values.map PhysicalScalar.rval).toList).mapError reprStr)
  need (value == physical.value && heapNumbers heap == heapNumbers physical.store.heap && heap.nodes.all Option.isNone)
    "heap source application disagrees with physical value/counters/reclamation"
  return Json.mkObj [("evaluated", toJson true), ("arguments", toJson (values.map UInt64.toNat)),
    ("heap", toJson (heapNumbers heap))]

def emit {schemas program root baseline provenance}
    (directory : System.FilePath) (name origin : String) (source : Json) (artifact : IxIR2.Wire.Artifact)
    (compiled : PhysicalHeap.Compiled schemas program root baseline provenance)
    (sourceObserve : Array Word → Nat → IxIR2.Eval.Result → IO Json)
    (emission : HeapTarget.Emission := .tree) : IO Json := do
  let encoded ← checked (artifact.encodeChecked {})
  let loaded ← checked (IxIR2.Wire.Artifact.ingest {} IxIR2.Validate.defaultLimits encoded.bytes artifact.address)
  need (loaded.artifact == artifact) "heap snapshot roundtrip changed its program or sidecars"
  let recompiled ← if baseline then do
      let exported ← checked (PhysicalHeap.compileSnapshotExport loaded.artifact loaded.checked (emission := emission))
      need (exported.source.address == root) "loaded source export differs from the selected entry"
      pure exported.compiled.object.bytes
    else do
      let selected ← checked (PhysicalHeap.compileSnapshot loaded.artifact loaded.checked root (emission := emission))
      pure selected.object.bytes
  need (recompiled == compiled.object.bytes && compiled.input.provenance == .ixir2 artifact.address)
    "heap snapshot recompilation changed the ELF or its provenance"
  let depth := compiled.selected.entry + 1
  let arity := compiled.selected.entryInterface.definition.signature.params.size
  need (arity == 1 || arity == 2) "heap fixture runtime arity changed"
  let capacityChecks ← capacityRejections compiled
  let certificateChecks ← certificateRejections compiled emission
  let mut observations := #[]
  for (a, b) in inputs do
    let values : Array Word := if arity == 1 then #[a.toUInt64] else #[a.toUInt64, b.toUInt64]
    let wanted := if baseline then PhysicalHeap.Examples.expected name a b else PhysicalHeap.Examples.rawExpected name a b
    let result ← checked ((IxIR2.Eval.Policy.runFunction artifact.policy.credits
      (IxIR2.Eval.Context.ofProgram artifact.program artifact.context.schemas) .physical compiled.selected.entryInterface.definition
      (values.map PhysicalScalar.rval) 2000 2000 (PhysicalHeap.initialStore baseline)).mapError reprStr)
    need (result.value == .lit (.nat wanted)) "heap physical result disagrees with the fixture formula"
    let source ← sourceObserve values wanted result
    let count ← observeNative compiled name depth a b result
    observations := observations.push (Json.mkObj [("left", toJson a), ("right", toJson b), ("value", toJson wanted),
      ("status", toJson (0 : Nat)), ("byte_steps", toJson count), ("control_steps", toJson (2000 - result.controlRemaining)),
      ("heap_fuel", toJson (2000 - result.heapRemaining)), ("heap", toJson (heapNumbers result.store.heap)),
      ("counters", toJson ((List.range 7).map fun field => PhysicalHeap.counters result.store (field + 2))),
      ("source", source)])
  let text ← present (ELFRead.text? compiled.object.bytes) "heap ELF text missing"
  let offset ← present (ELF.entry? compiled.object.bytes compiled.input.exportName) "heap ELF export missing"
  let selected := compiled.selected.entries.map fun entry => Json.mkObj [("address", toJson entry.address),
    ("parameters", toJson (entry.parameters.map fun kind => match kind with | .scalar => "scalar" | .node => "node" | .erased => "erased")),
    ("blocks", toJson entry.definition.blocks.size), ("allocations", toJson entry.allocations), ("controls", toJson entry.controls)]
  let sourceRoot ← if baseline then field (← field source "source") "root" else pure Json.null
  let rowFields := [("name", toJson name), ("origin", toJson origin), ("root", toJson artifact.address), ("source_root", sourceRoot),
    ("entry", toJson root), ("runtime_parameters", toJson arity), ("functions", toJson compiled.selected.entries.size),
    ("entry_index", toJson compiled.selected.entry), ("stack_depth", toJson depth), ("workspace_words", toJson (workspaceWords depth)),
    ("allocation_demand", toJson compiled.selected.entryInterface.allocations), ("control_bound", toJson compiled.selected.entryInterface.controls),
    ("native_blocks", toJson compiled.native.target.program.blocks.size), ("text_bytes", toJson text.size),
    ("text_hash", toJson (Coverage.hex (Blake3.Rust.hash text).val)), ("object_bytes", toJson compiled.object.bytes.size),
    ("snapshot_bytes", toJson encoded.bytes.size), ("capacity_checks", toJson capacityChecks), ("certificate_checks", toJson certificateChecks)]
  let row := Json.mkObj (rowFields ++ if emission == .shared then [("emission", toJson emission.policy)] else [])
  let snapshot := Json.mkObj [("format", toJson "compilatrix/source-native-heap/1"), ("policy", toJson PhysicalHeap.policy),
    ("row", row), ("artifact", IxIR2.Wire.artifactJson artifact), ("text", toJson (Coverage.hex text)),
    ("entry_offset", toJson offset), ("provenance", toJson (Coverage.hex compiled.input.provenance.bytes)),
    ("selected", toJson selected), ("observations", toJson observations), ("source_compilation", source)]
  IO.FS.writeBinFile (directory / s!"{name}.ixir2") encoded.bytes
  IO.FS.writeBinFile (directory / s!"{name}.o") compiled.object.bytes
  IO.FS.writeFile (directory / s!"{name}.json") (snapshot.pretty 100 ++ "\n")
  return row

end HeapGate

def main (args : List String) : IO UInt32 := cli "source native heap failed" do
  let (directory, emission) ← match args with
    | [directory] => pure (directory, HeapTarget.Emission.tree)
    | [directory, "shared"] => pure (directory, HeapTarget.Emission.shared)
    | _ => throw (IO.userError "usage: source-native-heap NEW-OUTPUT-DIRECTORY [shared]")
  let directory : System.FilePath := directory
  need (!(← directory.pathExists)) "heap producer requires a fresh output directory"
  let rejected ← HeapGate.admission
  IO.FS.createDirAll directory
  let mut rows := #[]
  for name in PhysicalHeap.Examples.sourceNames do
    let source ← checked (PhysicalHeap.Examples.source name)
    let attached ← checked (source.compile.mapError reprStr)
    let exported ← checked (PhysicalHeap.compileSourceExport attached (emission := emission))
    let context := Pipeline.validatedEvalCtx source.constants source.config
    let function ← checked ((Ixon.Eval.eval context 2000 (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError reprStr)
    let rawContext : IxIR0.Ctx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
    let rawFunction ← checked ((IxIR0.eval rawContext 2000 [] (.ref source.root)).mapError reprStr)
    let (moduleStore, moduleValue) ← checked ((IxIR1.runMain attached.compiled.simulationSourceContext attached.source.artifact.main 2000).mapError reprStr)
    rows := rows.push (← HeapGate.emit directory name "source" (source.compilationSnapshot attached)
      (IxIR2.Wire.ofCompiled attached.compiled) exported.compiled
      (HeapGate.sourceObservation source attached function rawFunction moduleStore moduleValue) emission)
  for name in PhysicalHeap.Examples.cfgNames do
    let artifact := PhysicalHeap.Examples.artifact name
    let certificate ← checked (artifact.check IxIR2.Validate.defaultLimits)
    let compiled ← checked (PhysicalHeap.compileSnapshot artifact certificate PhysicalHeap.Examples.root (emission := emission))
    rows := rows.push (← HeapGate.emit directory name "physical" Json.null artifact compiled (fun _ _ _ => pure Json.null) emission)
  let report := Json.mkObj [("format", toJson "compilatrix/source-native-heap-report/1"), ("policy", toJson PhysicalHeap.policy),
    ("source_evaluations", toJson (PhysicalHeap.Examples.sourceNames.length * HeapGate.inputs.length)),
    ("object_executions", toJson (rows.size * HeapGate.inputs.length)), ("snapshot_roundtrips", toJson rows.size),
    ("admission_rejections", toJson rejected), ("legacy_policy_rejections", toJson (2 : Nat)), ("cases", toJson rows)]
  IO.FS.writeFile (directory / "report.json") (report.pretty 100 ++ "\n")
  IO.println s!"source native heap ok: {rows.size} source/CFG objects, {rows.size * HeapGate.inputs.length} ELF executions, snapshots and rejections"
