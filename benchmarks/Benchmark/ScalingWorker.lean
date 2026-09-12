import Benchmark.ScalingSources
import Compilatrix.Coverage.Snapshot
import Compilatrix.X86.PhysicalHeapExport
import Compilatrix.IxIR2.WireJson
import Compilatrix.Tools.Check

namespace Benchmark.Scaling
open Lean System Compilatrix Compilatrix.Ixon Compilatrix.Tools.Check

deriving instance ToJson for Ixon.Work.ProgramStats
deriving instance ToJson for IxIR1.HPT.Cache.Stats

def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty ++ "\n")

def fresh (path : FilePath) : IO Unit := do
  need (!(← path.pathExists)) s!"output already exists: {path}"
  IO.FS.createDirAll path

def address (value : Json) : IO Address := do
  let value ← string value
  need (isHex 64 value) "noncanonical address"
  present (Address.ofBytes? (← checked (unhex value))) "invalid address length"

structure Input where
  family : String
  size : Nat
  edited : Bool
  source : Coverage.Source

def generate (family : String) (size : Nat) (edited : Bool) (path : FilePath) : IO Unit := do
  need (!(← path.pathExists)) s!"input already exists: {path}"
  need (["declarations", "call-depth", "branches", "allocations", "candidates"].contains family &&
    size > 0 && size ≤ 1024 && (!edited || family == "call-depth")) "invalid scaling request"
  match source family size edited with
  | .ok input => writeJson path (Json.mkObj [
      ("format", toJson "compilatrix/compiler-scaling-input/1"), ("family", toJson family),
      ("size", toJson size), ("edited", toJson edited), ("source", input.inputSnapshot)])
  | .error reason => writeJson path (Json.mkObj [
      ("format", toJson "compilatrix/compiler-scaling-rejected-input/1"), ("family", toJson family),
      ("size", toJson size), ("edited", toJson edited), ("generation_error", toJson reason)])

/-- Replay decodes retained canonical source bytes, then checks the complete
input against the versioned generator. Limits come from this tool's policy. -/
def readInput (path : FilePath) : IO Input := do
  need ((← path.metadata).byteSize ≤ 16 * 1024 * 1024) "scaling input exceeds 16 MiB"
  let metadata ← readJson path
  need ((← strField metadata "format") == "compilatrix/compiler-scaling-input/1") "wrong scaling input format"
  let family ← strField metadata "family"
  let size ← nat (← field metadata "size")
  let edited ← checked ((← field metadata "edited").getBool?)
  let generated ← checked (source family size edited)
  let snapshot ← field metadata "source"
  need (snapshot == generated.inputSnapshot) "source bytes or fixed compiler policy differ from the workload definition"
  let mut constants := []
  for entry in ← arrField snapshot "constants" do
    let key ← address (← field entry "key")
    let bytes ← checked (unhex (← strField entry "bytes"))
    let constant ← checked (de bytes : Except String Constant)
    need (ser constant == bytes) "source constant is not canonically encoded"
    let actual ← checked (constant.addressChecked.mapError reprStr)
    need (actual == key) "source constant has the wrong content address"
    constants := (key, constant) :: constants
  let source := { generated with constants := constants.reverse, root := ← address (← field snapshot "root") }
  return { family, size, edited, source }

def memory : IO Json := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    let get := fun label =>
      ((status.splitOn "\n").find? (·.startsWith label)).bind fun line =>
        (words line)[1]?.bind String.toNat?
    return Json.mkObj [("rss_kib", toJson (get "VmRSS:")), ("process_peak_rss_kib", toJson (get "VmHWM:"))]
  catch _ => return Json.mkObj [("rss_kib", Json.null), ("process_peak_rss_kib", Json.null)]

structure Measurements where
  rows : IO.Ref (Array Json)
  rejection : IO.Ref (Option (String × String))
  directory : FilePath
  timerPairNs : Nat

def timerControl : IO Nat := do
  let mut minimum := 1000000000
  for _ in [:200] do
    let start ← IO.monoNanosNow
    minimum := min minimum ((← IO.monoNanosNow) - start)
  return minimum

/-- Keep the pure compiler call inside the IO action between the clocks. -/
@[noinline] def force (action : Unit → Except String α) : IO (Except String α) :=
  pure (action ())

@[noinline] def measure (measurements : Measurements) (name : String)
    (action : Unit → Except String α) : IO α := do
  writeJson (measurements.directory / "current-stage.json") (Json.mkObj [("stage", toJson name), ("status", toJson "running")])
  let before ← memory
  let start ← IO.monoNanosNow
  let result ← force action
  let elapsed := (← IO.monoNanosNow) - start
  let after ← memory
  let status := match result with | .ok _ => "accepted" | .error _ => "rejected"
  let reason := match result with | .ok _ => Json.null | .error message => toJson message
  let row := Json.mkObj [
    ("stage", toJson name), ("elapsed_ns", toJson elapsed), ("memory_before", before), ("memory_after", after),
    ("status", toJson status), ("reason", reason)]
  measurements.rows.modify (·.push row)
  let journal ← IO.FS.Handle.mk (measurements.directory / "stages.jsonl") .append
  journal.putStr (row.compress ++ "\n")
  journal.flush
  writeJson (measurements.directory / "current-stage.json") (Json.mkObj [("stage", toJson name), ("status", toJson status)])
  match result with
  | .ok value => return value
  | .error reason =>
    measurements.rejection.set (some (name, reason))
    throw (IO.userError reason)

/-- Assemble the ordinary finite sidecars with a separately checked cache
production. All analysis and attachment algorithms are the public compiler
APIs; the replay check also compares the ordinary end-to-end pipeline. -/
def sidecars (input : Coverage.Source)
    (compiled : Pipeline.ValidatedCompilation input.constants input.root input.config .shared
      input.policy.eraseFuel input.policy.lowerFuel)
    (cached : IxIR1.HPT.Cache.Production IxIR1.HPT.Cache.defaultLimits compiled.lowering.result.artifacts) :
    Except IxIR2.Pipeline.Error (IxIR2.Pipeline.BuiltCompiledSidecars compiled.lowered) := do
  let hpt : IxIR1.HPT.Production IxIR1.HPT.defaultProducerLimits.checker compiled.lowering.result.artifacts := {
    certificate := cached.certificate, result := cached.result
    stats := { rounds := cached.stats.rounds, widenedArtifacts := cached.stats.widenedArtifacts }, checked := cached.checked }
  let built ← IxIR2.Pipeline.buildSidecarsWithHPT compiled hpt
  return { sidecars := built.sidecars, hpt := built.hpt
           certificateProduced := built.certificateProduced, inputProduced := built.inputProduced }

def shape (program : IxIR2.Program) : Json := Id.run do
  let functions := program.main :: program.declarations.filterMap (fun | (_, .fn fn) => some fn | _ => none)
  let mut branches : Nat := 0
  let mut joins : Nat := 0
  let mut calls : Nat := 0
  let mut allocations : Nat := 0
  for fn in functions do
    let mut incoming : Array Nat := Array.replicate fn.blocks.size 0
    for block in fn.blocks do
      for instruction in block.instructions do
        match instruction with
        | .call .. => calls := calls + 1
        | .alloc .. | .allocWith .. => allocations := allocations + 1
        | _ => pure ()
      let edges ← match block.terminator with
        | .jump edge => pure [edge]
        | .switchValue _ alternatives peel => do
          branches := branches + 1
          pure ((alternatives.toList.map (·.edge)) ++ (peel.toList.flatMap fun p => [p.zero, p.succ]))
        | .branchCredit _ yes no => do branches := branches + 1; pure [yes, no]
        | .tailCall .. => do calls := calls + 1; pure []
        | _ => pure []
      -- Alternative constructor and Nat dispatch can name the same edge.
      for target in (edges.map (·.target)).eraseDups do
        if target < incoming.size then incoming := incoming.modify target (· + 1)
    joins := joins + (incoming.filter (· > 1)).size
  return Json.mkObj [("branch_blocks", toJson branches), ("join_blocks", toJson joins),
    ("call_sites", toJson calls), ("allocation_sites", toJson allocations)]

def add (data : IO.Ref (List (String × Json))) (key : String) (value : Json) : IO Unit :=
  data.modify (· ++ [(key, value)])

def backend (measurements : Measurements) (data : IO.Ref (List (String × Json)))
    (output : FilePath) (wire : IxIR2.Wire.Artifact) (emitObject : Bool := true) : IO Unit := do
  add data "requested_endpoint" (toJson (if emitObject then "elf" else "native-lower"))
  add data "ixir2_shape" (shape wire.program)
  let encoded ← measure measurements "snapshot-encode-check" fun _ => wire.encodeChecked {}
  IO.FS.writeBinFile (output / "ixir2.bin") encoded.bytes
  writeJson (output / "ixir2.json") (IxIR2.Wire.artifactJson wire)
  add data "snapshot_root" (toJson wire.address)
  add data "snapshot_bytes" (toJson encoded.bytes.size)
  let decoded ← measure measurements "snapshot-decode-check" fun _ =>
    IxIR2.Wire.Artifact.ingest {} IxIR2.Validate.defaultLimits encoded.bytes wire.address
  need (decoded.artifact == wire) "snapshot replay differs from the compiler artifact"
  let exported ← measure measurements "native-export" fun _ => X86.PhysicalScalar.resolveExport wire.program
  let selected ← measure measurements "native-select" fun _ => X86.PhysicalHeap.select wire.context.schemas wire.program exported.address
  add data "native_interfaces" (toJson selected.entries.size)
  add data "native_entry_index" (toJson selected.entry)
  add data "native_allocation_bound" (toJson selected.entryInterface.allocations)
  add data "native_control_bound" (toJson selected.entryInterface.controls)
  let native ← measure measurements "native-lower" fun _ => X86.HeapTarget.compile selected true
  add data "x86_blocks" (toJson native.target.program.blocks.size)
  add data "x86_instructions" (toJson (native.target.program.blocks.foldl (fun n block => n + block.instructions.size) 0))
  if !emitObject then return
  let stream ← measure measurements "x86-encode-check" fun _ => (X86.Stream.encode native.target).mapError reprStr
  let objectInput : X86.ELF.Input := {
    encoded := stream.output, entryBlock := native.target.program.entry
    exportName := "compilatrix_scaling", provenance := .ixir2 wire.address }
  let object ← measure measurements "elf-write-check" fun _ => (X86.ELF.writeChecked objectInput).mapError reprStr
  IO.FS.writeBinFile (output / "main.o") object.bytes
  add data "elf_bytes" (toJson object.bytes.size)
  add data "elf_root" (toJson (Address.blake3 object.bytes))
  add data "x86_text_bytes" (toJson stream.output.text.size)

def finish (output : FilePath) (measurements : Measurements)
    (data : IO.Ref (List (String × Json))) (acceptedStatus : String := "compiled") : IO Unit := do
  let rejection ← measurements.rejection.get
  add data "status" (toJson (if rejection.isSome then "rejected" else acceptedStatus))
  add data "rejection" (match rejection with
    | none => Json.null
    | some (stage, reason) => Json.mkObj [("stage", toJson stage), ("reason", toJson reason)])
  writeJson (output / "outcome.json") (Json.mkObj (← data.get))
  writeJson (output / "measurements.json") (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-measurements/1"),
    ("timer_pair_min_ns", toJson measurements.timerPairNs),
    ("clock", toJson "IO.monoNanosNow; one invocation per stage"),
    ("memory_scope", toJson "Linux process RSS and raw reported VmHWM at stage boundaries; includes prior phases, diagnostics, retained artifacts, and IO; GNU time records the final process peak"),
    ("diagnostic_scope", toJson "diagnostic stages rerun work already included in source-to-ixir1; do not add them to pipeline latency"),
    ("stages", Json.arr (← measurements.rows.get))])

def rejectedInput (path : FilePath) : IO (String × Nat × Bool × String) := do
  let input ← readJson path
  need ((← strField input "format") == "compilatrix/compiler-scaling-rejected-input/1") "wrong rejected input format"
  let family ← strField input "family"
  let size ← nat (← field input "size")
  let edited ← checked ((← field input "edited").getBool?)
  need (["declarations", "call-depth", "branches", "allocations", "candidates"].contains family &&
    size > 0 && size ≤ 1024 && (!edited || family == "call-depth")) "invalid rejected scaling request"
  let reason ← strField input "generation_error"
  match source family size edited with
  | .ok _ => throw (IO.userError "source construction now succeeds for a rejected request")
  | .error actual => need (actual == reason) "source construction rejection changed"
  return (family, size, edited, reason)

/-- A request rejected by canonical source construction has no invented source
bytes. Time and replay that earlier boundary separately from compilation. -/
def compileRejectedInput (input output : FilePath) : IO Unit := do
  let (family, size, edited, _) ← rejectedInput input
  fresh output
  IO.FS.writeFile (output / "input.json") (← IO.FS.readFile input)
  let measurements : Measurements := {
    rows := ← IO.mkRef #[], rejection := ← IO.mkRef none, directory := output, timerPairNs := ← timerControl }
  let data ← IO.mkRef [
    ("format", toJson "compilatrix/compiler-scaling-outcome/1"), ("family", toJson family),
    ("size", toJson size), ("edited", toJson edited), ("input_stage", toJson "source-construction")]
  try
    let _ ← measure measurements "source-construction" fun _ => source family size edited
    throw (IO.userError "source construction unexpectedly succeeded")
  catch error =>
    if (← measurements.rejection.get).isNone then throw error
  finish output measurements data

def compile (inputPath output : FilePath) (cachePath : Option FilePath) : IO Unit := do
  let input ← readInput inputPath
  let source := input.source
  let cacheBytes ← cachePath.mapM IO.FS.readBinFile
  fresh output
  IO.FS.writeFile (output / "input.json") (← IO.FS.readFile inputPath)
  let measurements : Measurements := {
    rows := ← IO.mkRef #[], rejection := ← IO.mkRef none, directory := output, timerPairNs := ← timerControl }
  let data ← IO.mkRef [
    ("format", toJson "compilatrix/compiler-scaling-outcome/1"), ("family", toJson input.family),
    ("size", toJson input.size), ("edited", toJson input.edited), ("source_root", toJson source.root),
    ("source_work", toJson (Ixon.Work.programStats source.constants)),
    ("source_bytes", toJson (source.constants.foldl (fun total entry => total + (ser entry.2).size) 0)),
    ("input_cache_bytes", toJson (cacheBytes.map ByteArray.size |>.getD 0))]
  try
    let _ ← measure measurements "source-preflight" fun _ =>
      (Pipeline.preflightValidated source.config.limits source.constants source.policy.checkFuel
        source.policy.eraseFuel source.policy.validateFuel source.policy.lowerFuel).mapError reprStr
    if input.family != "candidates" then
      let compiled ← measure measurements "source-to-ixir1" fun _ =>
        (Pipeline.compileValidatedWithTrace source.constants source.root source.config .shared source.policy.checkFuel
          source.policy.eraseFuel source.policy.validateFuel source.policy.lowerFuel).mapError reprStr
      add data "ixir1_root" (toJson (IxIR1.Optimizer.graphRoot compiled.artifact.targetArtifacts compiled.artifact.main))
      add data "ixir1_declarations" (toJson compiled.artifact.targetDecls.length)
      add data "ixir1_bytes" (toJson (compiled.artifact.targetDecls.foldl (fun n entry => n + entry.2.preimage.size) compiled.artifact.main.bytes.size))
      writeJson (output / "ixir1.json") (Json.mkObj [
        ("artifacts", toJson (compiled.artifact.targetArtifacts.map Coverage.ir1Artifact)),
        ("declarations", Coverage.ir1Entries compiled.artifact.targetDecls), ("main", Coverage.byteJson compiled.artifact.main.bytes)])
      let ectx := Pipeline.validatedEvalCtx source.constants source.config
      let ictx : IxIR0.Ctx := { env := (IxIR0.Env.Index.ofList compiled.erasure.result.raw).toEnv }
      let candidates := source.constants.filterMap fun entry => match entry.2.info with | .muts _ => none | _ => some entry.1
      let order ← measure measurements "diagnostic-coverage-discovery" fun _ =>
        letI : Sim.MemberScope := compiled.memberScope
        (Pipeline.coveragePlan ectx.inlineSharing ictx source.policy.validateFuel (candidates.length + 1) [] [] candidates).mapError
          (fun (address, message) => s!"{address}: {message}")
      let certificate ← measure measurements "diagnostic-source-certificate" fun _ =>
        letI : Sim.MemberScope := compiled.memberScope
        ((EraseValidator.certifySharedProgram ectx source.constants order source.policy.eraseFuel source.policy.validateFuel).map
          (fun certificate => (certificate.target, certificate.coverage.map (·.address)))).mapError reprStr
      need (certificate.1 == compiled.erasure.result.raw) "diagnostic source certificate targets different erasure"
      add data "source_coverage_entries" (toJson certificate.2.length)
      writeJson (output / "source-coverage.json") (toJson certificate.2)
      let store ← measure measurements "cache-decode" fun _ =>
        match cacheBytes with | none => .ok { entries := [] } | some bytes => IxIR1.HPT.Cache.decodeStore bytes
      let hpt ← measure measurements "hpt-cache-produce-check" fun _ => IxIR1.HPT.Cache.run compiled.lowering.result.artifacts store
      add data "hpt_cache" (toJson hpt.stats)
      let checkedHpt ← measure measurements "hpt-certificate-check" fun _ =>
        IxIR1.HPT.runWith IxIR1.HPT.defaultLimits compiled.lowering.result.artifacts hpt.certificate
      need (checkedHpt == hpt.result) "HPT certificate replay differs"
      let storeBytes := IxIR1.HPT.Cache.encodeStore hpt.completeStore
      IO.FS.writeBinFile (output / "hpt.store") storeBytes
      let evidence := toJson (hpt.certificate.artifacts.map Coverage.hptCandidate)
      writeJson (output / "hpt-certificate.json") evidence
      add data "hpt_store_bytes" (toJson storeBytes.size)
      add data "hpt_certificate_json_bytes" (toJson (evidence.pretty ++ "\n").utf8ByteSize)
      add data "hpt_certificate_artifacts" (toJson hpt.certificate.artifacts.length)
      add data "hpt_cache_keys" (toJson (hpt.completeStore.entries.map (·.1)))
      let built ← measure measurements "sidecars" fun _ => (sidecars source compiled hpt).mapError reprStr
      let attached ← measure measurements "ixir2-lower-check" fun _ =>
        (IxIR2.Pipeline.attachCompiled compiled.lowered built source.policy.maxDepth).mapError reprStr
      let wire := IxIR2.Wire.ofCompiled attached.val
      add data "ixir2_stats" (toJson attached.val.target.stats)
      backend measurements data output wire
  catch error =>
    if (← measurements.rejection.get).isNone then throw error
  finish output measurements data (if input.family == "candidates" then "preflight-only" else "compiled")
  IO.println s!"{input.family}/{input.size}: {if (← measurements.rejection.get).isSome then "rejected" else "accepted"}"

end Benchmark.Scaling
