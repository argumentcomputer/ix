import Benchmark.ScalingJoins

namespace Benchmark.Scaling
open Lean System Compilatrix Compilatrix.Ixon Compilatrix.Tools.Check

def arguments : Array Nat := #[0, 1, 7, UInt64.size - 1]

def wanted (family : String) (size : Nat) (argument : Nat) : Nat :=
  if family == "branches" || family == "joins" then argument - size else argument

def core (depth argument : Nat) : X86.Core :=
  let low : X86.Word := 0x10000
  let count := 272 + 34 * depth + 2
  let top := low + (8 * (count - 1)).toUInt64
  let allowed := fun address : X86.Word => decide (low ≤ address ∧ address < top + 8)
  let memory : X86.Memory := { bytes := fun address => (address ^^^ 0xa7).toUInt8, readable := allowed, writable := allowed }
  let registers : X86.Registers := fun _ => 0x1020304050607080
  { registers := (((registers.set .rsp top).set .rdi argument.toUInt64).set .rsi 0).set .rdx low
    memory := (memory.write64 (low + 8) 64).write64 top 0x12345678 }

def scalar (value : IxIR2.Eval.RVal) : IO Nat :=
  match value with
  | .lit (.nat n) => pure n
  | _ => throw (IO.userError "scaling evaluation returned a non-Nat")

def verify (directory output : FilePath) : IO Unit := do
  need (!(← output.pathExists)) s!"verification output already exists: {output}"
  let outcome ← readJson (directory / "outcome.json")
  need ((← strField outcome "format") == "compilatrix/compiler-scaling-outcome/1") "wrong scaling outcome format"
  let family ← strField outcome "family"
  let size ← nat (← field outcome "size")
  if (← strField (← readJson (directory / "input.json")) "format") == "compilatrix/compiler-scaling-rejected-input/1" then
    let (actualFamily, actualSize, edited, reason) ← rejectedInput (directory / "input.json")
    need (family == actualFamily && size == actualSize && (← field outcome "edited") == toJson edited &&
      (← strField outcome "input_stage") == "source-construction" && (← strField outcome "status") == "rejected" &&
      (← field outcome "rejection") == Json.mkObj [("stage", toJson "source-construction"), ("reason", toJson reason)] &&
      !(← (directory / "ixir1.json").pathExists) && !(← (directory / "ixir2.bin").pathExists) &&
      !(← (directory / "main.o").pathExists)) "source construction rejection disagrees"
    writeJson output (Json.mkObj [("status", toJson "passed"), ("scope", toJson "source construction rejection; no canonical source or compilation claimed"),
      ("rejection", ← field outcome "rejection")])
    return
  let mut wire : Option IxIR2.Wire.Artifact := none
  let mut sourceValues := #[]
  if family == "joins" then
    let (count, artifact) ← readJoins (directory / "input.json")
    need (count == size) "join size disagrees"
    wire := some artifact
  else
    let input ← readInput (directory / "input.json")
    let source := input.source
    need (family == input.family && size == input.size && (← field outcome "edited") == toJson input.edited &&
      (← field outcome "source_work") == toJson (Ixon.Work.programStats source.constants)) "source outcome identity or work counters disagree"
    match Pipeline.preflightValidated source.config.limits source.constants source.policy.checkFuel
        source.policy.eraseFuel source.policy.validateFuel source.policy.lowerFuel with
    | .error error =>
      need ((← strField outcome "status") == "rejected" && (← field outcome "rejection") == Json.mkObj [
        ("stage", toJson "source-preflight"), ("reason", toJson (reprStr error))]) "preflight rejection changed"
      need (!(← (directory / "ixir2.bin").pathExists) && !(← (directory / "main.o").pathExists)) "preflight rejection emitted backend artifacts"
      writeJson output (Json.mkObj [("status", toJson "passed"), ("scope", toJson "preflight rejection"), ("rejection", ← field outcome "rejection")])
      return
    | .ok _ => pure ()
    if family == "candidates" then
      need ((← strField outcome "status") == "preflight-only" && (← field outcome "rejection") == Json.null) "candidate preflight changed"
      need (!(← (directory / "ixir2.bin").pathExists) && !(← (directory / "main.o").pathExists)) "preflight-only row emitted backend artifacts"
      writeJson output (Json.mkObj [("status", toJson "passed"), ("scope", toJson "preflight only; no source certificate claimed")])
      return
    -- This invokes the ordinary pipeline, independently of the worker's
    -- phased assembly and cached sidecar construction.
    let attached ← checked (source.compile.mapError reprStr)
    let artifact := IxIR2.Wire.ofCompiled attached.compiled
    wire := some artifact
    need ((← strField outcome "source_root") == source.root.toHex &&
      (← nat (← field outcome "source_bytes")) == source.constants.foldl (fun n entry => n + (ser entry.2).size) 0) "source root/size disagrees"
    need ((← IO.FS.readBinFile (directory / "hpt.store")) == IxIR1.HPT.Cache.encodeStore (IxIR1.HPT.Cache.Store.ofResult attached.hpt.result))
      "retained HPT evidence differs from ordinary checked production"
    need ((← readJson (directory / "hpt-certificate.json")) == toJson (attached.hpt.certificate.artifacts.map Coverage.hptCandidate))
      "retained HPT certificate differs from ordinary checked production"
    need ((← readJson (directory / "ixir1.json")) == Json.mkObj [
      ("artifacts", toJson (attached.source.artifact.targetArtifacts.map Coverage.ir1Artifact)),
      ("declarations", Coverage.ir1Entries attached.source.artifact.targetDecls),
      ("main", Coverage.byteJson attached.source.artifact.main.bytes)]) "phased IxIR1 differs from ordinary compilation"
    let coverage ← (← array (← readJson (directory / "source-coverage.json"))).mapM address
    let candidates := source.constants.filterMap fun entry => match entry.2.info with | .muts _ => none | _ => some entry.1
    need (coverage.size == candidates.length && coverage.toList.Nodup &&
      candidates.all coverage.contains && (← nat (← field outcome "source_coverage_entries")) == coverage.size) "source coverage inventory changed"
    let context := Pipeline.validatedEvalCtx source.constants source.config
    let function ← checked ((Ixon.Eval.eval context source.policy.evalFuel (Pipeline.validatedMainFrame source.root)
      [] Pipeline.validatedMainSource).mapError reprStr)
    for argument in arguments do
      let value ← checked ((Ixon.Eval.applyMany context source.policy.evalFuel function
        (X86.PhysicalScalar.sourceArguments #[argument.toUInt64])).mapError reprStr)
      let .litV (.natL actual) := value | throw (IO.userError "source application did not return Nat")
      need (actual == wanted family size argument) "source application disagrees with the workload oracle"
      sourceValues := sourceValues.push actual
  let artifact ← present wire "missing checked artifact"
  let bytes ← IO.FS.readBinFile (directory / "ixir2.bin")
  let root ← address (← field outcome "snapshot_root")
  let decoded ← checked (IxIR2.Wire.Artifact.ingest {} IxIR2.Validate.defaultLimits bytes root)
  need (decoded.artifact == artifact && (← readJson (directory / "ixir2.json")) == IxIR2.Wire.artifactJson artifact &&
    (← nat (← field outcome "snapshot_bytes")) == bytes.size && (← field outcome "ixir2_shape") == shape artifact.program)
    "retained snapshot differs from its checked origin"
  let exported ← checked (X86.PhysicalScalar.resolveExport artifact.program)
  let context := IxIR2.Eval.Context.ofProgram artifact.program artifact.context.schemas
  let mut results := #[]
  for argument in arguments do
    let result ← checked ((IxIR2.Eval.runFunction context .physical exported.target
      #[X86.PhysicalScalar.rval argument.toUInt64] 100000 100000 (X86.PhysicalHeap.initialStore true)).mapError reprStr)
    need ((← scalar result.value) == wanted family size argument && result.store.live == 0 &&
      result.store.heap.allocs == result.store.heap.frees && result.store.heap.nodes.all Option.isNone)
      "physical execution disagrees with the value/reclamation oracle"
    results := results.push result
  if family == "joins" && !joinEmitsObject size then
    need (!(← (directory / "main.o").pathExists) && (← strField outcome "requested_endpoint") == "native-lower") "join endpoint emitted an unrequested object"
    match X86.PhysicalHeap.select artifact.context.schemas artifact.program exported.address with
    | .error reason =>
      need ((← strField outcome "status") == "rejected" && (← strField (← field outcome "rejection") "reason") == reason) "join selection rejection changed"
    | .ok selected =>
      let native ← checked (X86.HeapTarget.compile selected true)
      need ((← strField outcome "status") == "lowered" && (← field outcome "rejection") == Json.null &&
        (← nat (← field outcome "x86_blocks")) == native.target.program.blocks.size) "join lowering changed"
      for argument in arguments do
        let initial := core (selected.entry + 1) argument
        let result := X86.runFrom X86.Runtime.rejecting native.target 100000 initial
        need (result.status == .halted (wanted family size argument).toUInt64 && result.core.readReg .rdx == 0 &&
          result.core.calleeSavedMatch initial.calleeSavedSnapshot && result.core.readReg .rsp == initial.readReg .rsp)
          "typed join execution disagrees with physical execution"
    writeJson output (Json.mkObj [("status", toJson "passed"), ("scope", toJson "checked IxIR2 through native lowering"),
      ("arguments", toJson arguments), ("native_status", ← field outcome "status")])
    return
  let native := X86.PhysicalHeap.compileSnapshotExport decoded.artifact decoded.checked "compilatrix_scaling"
  match native with
  | .error reason =>
    need ((← strField outcome "status") == "rejected" && (← strField (← field outcome "rejection") "reason") == reason &&
      !(← (directory / "main.o").pathExists)) "native rejection changed"
  | .ok native =>
    need ((← strField outcome "status") == "compiled" && (← field outcome "rejection") == Json.null) "native acceptance changed"
    let object ← IO.FS.readBinFile (directory / "main.o")
    need (object == native.compiled.object.bytes && object.size == (← nat (← field outcome "elf_bytes")) &&
      (← strField outcome "elf_root") == (Address.blake3 object).toHex) "retained ELF differs from checked replay"
    let text ← present (X86.ELFRead.text? object) "ELF text is missing"
    let entry ← present (X86.ELF.entry? object "compilatrix_scaling") "ELF entry is missing"
    for i in [:arguments.size] do
      let initial := core (native.compiled.selected.entry + 1) arguments[i]!
      let mut state : X86.ByteEval.State := ⟨initial, 0x400000 + entry.toUInt64, {}⟩
      let mut steps := 0
      for _ in [:100000] do
        if state.rip == 0x12345678 then break
        state ← checked ((X86.ByteEval.step text 0x400000 state).mapError reprStr)
        steps := steps + 1
      need (state.rip == 0x12345678) "ELF failed to return within the execution budget"
      let result ← checked ((X86.ObjectEval.run object "compilatrix_scaling" 0x400000 steps initial).mapError reprStr)
      need (result.rip == 0x12345678 && result.core.readReg .rax == (wanted family size arguments[i]!).toUInt64 &&
        result.core.readReg .rdx == 0 && result.core.readReg .rsp == initial.readReg .rsp + 8 &&
        result.core.calleeSavedMatch initial.calleeSavedSnapshot) "parsed ELF execution disagrees with physical execution or caller state"
      for field in [2:9] do
        need ((result.core.memory.read64 (0x10000 + (8 * field).toUInt64)).toNat == X86.PhysicalHeap.counters results[i]!.store field)
          "parsed ELF resource counters disagree with physical execution"
  writeJson output (Json.mkObj [
    ("status", toJson "passed"), ("family", toJson family), ("size", toJson size),
    ("source_values", toJson sourceValues), ("arguments", toJson arguments),
    ("physical_values", toJson (← results.mapM (scalar ∘ (·.value)))),
    ("ordinary_pipeline_exact", toJson (family != "joins")), ("snapshot_reloaded", toJson true),
    ("native_status", ← field outcome "status")])

end Benchmark.Scaling
