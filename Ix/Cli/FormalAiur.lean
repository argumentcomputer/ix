module
public import Cli
public import Ix.Check
public import Ix.Shard.Check
public import Ix.Store
public import Ix.Aggr.Reference
public import Ix.Cli.ShardProofIndex
public import Ix.Cli.Compression
public import Ix.AiurArtifact
public import Ix.Aiur.Statistics
public import Ix.AiurInvocation
public import Ix.Benchmark.Results
public import Ix.TracingTexray
public import Ix.FormalProver

/-! Application bridge to the separate Aiur/IxVM packages. This module reuses
Ix's claim and witness construction, not the legacy evaluator or compiler.
Compilation runs in the standalone exporter, which embeds the program; the
artifact is cached by the exporter and the program's digest. Execution,
proving and verification run in this process through the prover library
(`Ix.FormalProver`). The generic Aiur Lean library does not acquire
application-specific FFI. -/
public section
namespace Ix.Cli.FormalAiur
open Lean IxVM.ClaimHarness

def commandStatus (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO UInt32 := do
  (← IO.getStdout).flush
  let child ← IO.Process.spawn { cmd, args, cwd, env, stdout := .inherit, stderr := .inherit }
  child.wait

def command (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO Unit := do
  let code ← commandStatus cmd args cwd env
  unless code == 0 do throw (IO.userError s!"{cmd} failed with status {code}")

/-- Run `act`; with `IX_PHASE_TIMES` set, report its wall time on stderr. The
work is a thunk so that pure computations run inside the measured interval. -/
def phase {α : Type} (label : String) (act : Unit → IO α) : IO α := do
  if (← IO.getEnv "IX_PHASE_TIMES").isNone then return ← act ()
  let start ← IO.monoNanosNow
  let result ← act ()
  let finish ← IO.monoNanosNow
  IO.eprintln s!"[phase] {label}: {(finish - start) / 1000000} ms (ended at {finish / 1000000} ms)"
  return result

/-- Whether `dir` is an Ix checkout: it holds the IxVM package. -/
private def isCheckout (dir : System.FilePath) : IO Bool :=
  (dir / "IxVM" / "lakefile.lean").pathExists

/-- The checkout this `ix` belongs to. The backend's exporters, Rust hosts and
artifact cache live there, so commands work from any directory. In order:
`IX_ROOT`, which must name a checkout; the checkout whose `.lake/build/bin`
holds this executable; the working directory, if it is a checkout. An
installed or packaged `ix` outside a checkout matches none of these and fails
here, before any `lake` or `cargo` runs. -/
def repoRoot : IO System.FilePath := do
  if let some root ← IO.getEnv "IX_ROOT" then
    unless ← isCheckout root do
      throw (IO.userError s!"IX_ROOT={root} is not an Ix checkout (it has no IxVM/lakefile.lean)")
    return root
  let app ← IO.appPath
  let root := do
    let bin ← app.parent
    let build ← bin.parent
    let lake ← build.parent
    lake.parent
  if let some root := root then
    if ← isCheckout root then return root
  let cwd ← IO.currentDir
  if ← isCheckout cwd then return cwd
  throw (IO.userError s!"cannot find the Ix checkout that builds the Aiur artifacts: {app} is \
    not in a checkout's .lake/build/bin, and the working directory is not a checkout. Set \
    IX_ROOT to an Ix checkout of the same revision as this ix, or pass the exported artifacts: \
    --aiur-artifact or IX_AIUR_ARTIFACT (and --aggr-artifact or IX_AGGR_ARTIFACT for \
    aggregation).")

/-- The digest of the program an exporter embeds (`IxVM.programDigest`,
`MultiStark.recursionDigest`, `MultiStark.aggregateDigest`), which it prints in
its `digest` mode. It identifies the deployed program. -/
def programDigest (root exporter : System.FilePath) (extra : Array String := #[]) : IO String := do
  let result ← IO.Process.output {
    cmd := "lake", args := #["env", exporter.toString, "digest"] ++ extra, cwd := root }
  let digest := result.stdout.trimAscii.toString
  unless result.exitCode == 0 && digest.length == 64 && digest.all Char.isHexDigit do
    throw (IO.userError s!"{exporter} digest failed ({result.exitCode}): {result.stderr}")
  return digest

/-- The artifact `exporter` compiles, built once and cached under
`.lake/aiur`. The key is BLAKE3 of the exporter's binary and the digest of the
program it embeds: the program alone determines the circuit only together with
the compiler that is linked into the exporter. -/
def compiledArtifact (p : Cli.Parsed) (flag env exporterPath target mode : String)
    (extra : Array String := #[]) : IO String := do
  let expected ← AiurArtifact.expected ((p.flag? s!"{flag}-digest").map (·.as! String)) env
  if let some path := (p.flag? flag).map (·.as! String) then
    let _ ← AiurArtifact.admit target path expected; return path
  if let some path ← IO.getEnv env then
    let _ ← AiurArtifact.admit target path expected; return path
  let root ← repoRoot
  let exporter := root / exporterPath
  let buildTarget := if target == "ixvm" then "ixvm/ixvm"
    else if target == "stark-export" then "multiStark/stark-export"
    else target
  command "lake" #["-q", "build", buildTarget] root
  let program ← programDigest root exporter extra
  let compiler ← IO.FS.readBinFile exporter
  let digest := Address.blake3 ((Address.blake3 compiler).hash ++ program.toUTF8)
  AiurArtifact.cached (root / ".lake" / "aiur") target digest expected fun tmp =>
    command "lake" (#["env", exporter.toString, mode, tmp.toString] ++ extra) root

def artifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "aiur-artifact" "IX_AIUR_ARTIFACT" "IxVM/.lake/build/bin/ixvm"
    "ixvm" "export-claim-trace"

/-- The certified aggregation program (`MultiStark::ix_aggr`) with its circuits. -/
def aggregationArtifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "aggr-artifact" "IX_AGGR_ARTIFACT"
    "MultiStark/.lake/build/bin/stark-export" "stark-export"
    "export-trace" #["--aggregate"]

/-- The certified recursive verifier (`MultiStark::verify_multi_stark_proof`)
with its circuits. -/
def verifierArtifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "verifier-artifact" "IX_VERIFIER_ARTIFACT"
    "MultiStark/.lake/build/bin/stark-export" "stark-export"
    "export-trace"

structure HostOptions where
  rows : Nat := 0
  retention : String := "auto"
  ram : Nat := 0
  device : Option Nat := none
  threads : Nat := 0

def HostOptions.json (o : HostOptions) : Json := Json.mkObj [
  ("max_rows", if o.rows == 0 then .null else toJson o.rows),
  ("retention", toJson o.retention),
  ("max_ram_bytes", if o.ram == 0 then .null else toJson o.ram),
  ("device", toJson o.device)]

def HostOptions.forWave (o : HostOptions) (jobs members : Nat) : HostOptions :=
  { o with ram := o.ram * max jobs 1 / max members 1
           threads := o.threads * max jobs 1 / max members 1 }

/-- Keep workers occupied as individual jobs finish. All admitted tasks are
joined on failure, so temporary files outlive their jobs. -/
def boundedMap {α β : Type} (jobs : Nat) (xs : Array α) (f : Nat → α → IO β) : IO (Array β) := do
  let mut out : Array (Option β) := Array.replicate xs.size none
  let mut running : Array (Nat × Task (Except IO.Error β)) := #[]
  let admitted ← IO.mkRef running
  let mut offset := 0
  let limit := max 1 (min jobs xs.size)
  try
    while offset < xs.size || !running.isEmpty do
      while offset < xs.size && running.size < limit do
        let some x := xs[offset]? | throw (IO.userError "missing scheduled input")
        let task ← IO.asTask (prio := .dedicated) (f limit x)
        running := running.push (offset, task)
        admitted.set running
        offset := offset + 1
      let mut waiting := #[]
      for (i, task) in running do
        if ← IO.hasFinished task then out := out.set! i (some (← IO.ofExcept task.get))
        else waiting := waiting.push (i, task)
      running := waiting
      admitted.set running
      unless running.isEmpty do IO.sleep 1
    out.mapM fun x => match x with
      | some x => pure x
      | none => throw (IO.userError "missing scheduled result")
  finally
    for (_, task) in (← admitted.get) do let _ ← IO.wait task; pure ()

def resources : IO Json := FormalProver.resources

def jobCount (p : Cli.Parsed) : IO Nat := do
  let n := ((p.flag? "jobs").map (·.as! Nat)).getD 1
  if n != 0 then return n
  return max 1 ((← resources).getObjValAs? Nat "cores" |>.toOption.getD 1)

def hostOptions (p : Cli.Parsed) (shares : Nat := 1) : IO HostOptions := do
  let rows := ((p.flag? "shard-rows").map (·.as! Nat)).getD 0
  unless rows == 0 || (rows &&& (rows - 1)) == 0 do
    throw (IO.userError "--shard-rows must be zero (automatic) or a power of two")
  let retention := ((p.flag? "retention").map (·.as! String)).getD "auto"
  unless #["auto", "retain", "regenerate"].contains retention do
    throw (IO.userError "--retention must be auto, retain or regenerate")
  let maxRam := (p.flag? "max-ram").map (·.as! Nat)
  if maxRam == some 0 then throw (IO.userError "RAM budget must be positive")
  let gib := maxRam.orElse fun _ => ((p.flag? "ram-budget").map (·.as! Nat)).filter (· != 0)
  let ram ← match gib with
    | some n => pure (n * 1024^3)
    | none => pure (((← resources).getObjValAs? Nat "available_bytes" |>.toOption.getD (8 * 1024^3)) * 85 / 100)
  let device ← match (p.flag? "gpu-device").map (·.as! Nat) with
    | some n => pure (some n)
    | none => do
      if p.hasFlag "lanes" || (← IO.getEnv "IX_CUDA") == some "1" then
        pure (some (((← IO.getEnv "MULTI_STARK_CUDA_DEVICE").bind String.toNat?).getD 0))
      else pure none
  let cores := ((← resources).getObjValAs? Nat "cores").toOption.getD 1
  return {
    rows, retention, ram := max 1 (ram / max shares 1), device
    threads := max 1 (cores / max shares 1) }

def executionJobs (p : Cli.Parsed) (jobs : Nat) : IO Nat := do
  let cores := ((← resources).getObjValAs? Nat "cores").toOption.getD 1
  let n := ((p.flag? "exec-jobs").map (·.as! Nat)).getD (if p.hasFlag "lanes" then 0 else jobs)
  if n == 0 then return cores
  return if p.hasFlag "lanes" then n * (((p.flag? "lanes").map (·.as! Nat)).getD 1) else n

/-- Run one request: prove it, or with `execute` and `plan` check it
without proving. Returns the status and report. -/
def runHost (artifactPath mode : String) (request : FormalProver.Request) (output : String)
    (options : HostOptions) : IO (UInt32 × Json) := do
  -- The library prints progress on the process's stdout.
  (← IO.getStdout).flush
  let (code, report) ← if mode == "prove" then
      phase "prover" fun _ =>
        FormalProver.prove artifactPath request output options.json.compress options.threads
    else if mode == "execute" || mode == "plan" then
      phase s!"check {mode}" fun _ =>
        FormalProver.check (mode == "plan") artifactPath request options.json.compress options.threads
    else throw (IO.userError s!"unknown prover mode {mode}")
  return (code, ← IO.ofExcept (Json.parse report))

/-- A host input, in Ixon (`Ix.AiurInvocation`). Stream metadata is small; each
byte payload is transported exactly once. The Rust host turns these into
immutable vectors captured by hint closures. -/
def invocation (input : Array Aiur.G) (buffer : Aiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : ByteArray :=
  AiurInvocation.ofBuffer input buffer entry

private def pushUInt64 (bytes : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut bytes := bytes
  for i in [0:8] do
    bytes := bytes.push (n >>> (8 * i).toUInt64).toUInt8
  return bytes

/-- An existing witness as compact advice, in the buffer's stream order. A
stream whose values are all below 256 travels as bytes, any other as
numeric words. -/
def bufferRequest (input : Array Aiur.G) (buffer : Aiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : IO FormalProver.Request := do
  let mut layout := ByteArray.empty
  let mut bytes := ByteArray.empty
  let mut words := ByteArray.empty
  for ((channel, key), info) in buffer.map.toArray do
    let values := (buffer.data.getD channel #[]).extract info.idx (info.idx + info.len)
    let byteStream := values.all (·.val < 256)
    layout := pushUInt64 layout channel.val
    layout := pushUInt64 layout (if byteStream then 0 else 1)
    layout := pushUInt64 layout key.size.toUInt64
    for k in key do layout := pushUInt64 layout k.val
    layout := pushUInt64 layout values.size.toUInt64
    if byteStream then
      for v in values do bytes := bytes.push v.val.toUInt8
    else
      for v in values do words := pushUInt64 words v.val
  FormalProver.Request.buffers entry (input.map (·.val)) layout bytes words

/-- Concatenated 32-byte addresses. -/
def addressBytes (xs : Array Address) : ByteArray :=
  xs.foldl (fun bytes a => bytes ++ a.hash) ByteArray.empty

/-- A shard `CheckEnv` leaf the prover prepares from `env`: the claim of
the constants `blocks` own, checked against `claim`. -/
def shardRequest (env : FormalProver.Env) (blocks : Array Address) (claim : Ix.Claim) :
    IO FormalProver.Request :=
  FormalProver.Request.shard env (addressBytes blocks) (Ix.Claim.ser claim)

/-- The request for a `forEachClaim` target. `Check` claims are prepared by
the prover from `env`; other claim forms submit their Lean witness. -/
def targetRequest (env : Option FormalProver.Env) (claim : Ix.Claim) :
    Ix.Check.Target → IO FormalProver.Request
  | .addr a => do
    let some env := env | throw (IO.userError "a Check request needs an environment")
    FormalProver.Request.check env a.hash (Ix.Claim.ser claim)
  | .shard _ => throw (IO.userError "submit shard leaves by their manifest blocks")
  | .leanW w => bufferRequest w.input w.inputIOBuffer

def rejectFlags (p : Cli.Parsed) (flags : Array String) : IO Unit := do
  for flag in flags do
    if p.hasFlag flag then
      throw (IO.userError s!"--{flag} is not supported")

def verifyWrapper (artifactPath : String) (wrapper : Ixon.Proof) : IO Unit := do
  let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let _ ← FormalProver.verify artifactPath "IxVM::verify_claim"
    ((packedDigestKey digest).map (·.val)) wrapper.proof

def readProofFileOrStore (pathOrHex : String) : IO Ixon.Proof := do
  let bytes ← if ← System.FilePath.pathExists pathOrHex then
      IO.FS.readBinFile pathOrHex
    else if let some addr := Address.fromString pathOrHex then
      StoreIO.toIO (Store.read addr)
    else
      throw (IO.userError s!"cannot find proof file or store address '{pathOrHex}'")
  IO.ofExcept (Ixon.Proof.de bytes)

def shardIndex : IO System.FilePath := ShardProofIndex.indexDir

structure JobResult where
  code : UInt32 := 0
  report : Json := .null
  address : Option Address := none

def JobResult.peak (r : JobResult) : Nat :=
  let plan := (r.report.getObjVal? "plan").toOption.getD .null
  max ((plan.getObjValAs? Nat "generation_peak_bytes").toOption.getD 0)
    ((plan.getObjValAs? Nat "proving_peak_bytes").toOption.getD 0)

def persistClaim (p : Cli.Parsed) (claim : Ix.Claim) (path : System.FilePath) : IO Address := do
  let keyAddr ← StoreIO.toIO (Store.write (← IO.FS.readBinFile (path.toString ++ ".vk")))
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let wrapper : Ixon.Proof := { claim, proof := ← IO.FS.readBinFile path }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  unless p.hasFlag "no-index" do
    ShardProofIndex.writeAddress (← shardIndex) (Address.blake3 (Ix.Claim.ser claim)) proofAddr
  IO.println s!"verifying-key {keyAddr}"
  return proofAddr

def one (p : Cli.Parsed) (artifactPath : String) (options : HostOptions)
    (mode : String) (claim : Ix.Claim) (request : Unit → IO FormalProver.Request) (label : String)
    (resume : Bool := false) : IO JobResult := do
  try
    let digest := Address.blake3 (Ix.Claim.ser claim)
    -- A verified proof of exactly this claim settles it: proving reuses it,
    -- and checking (`ix shard refine`) keeps its leaf rather than orphan it.
    let lookup := (resume && mode == "prove" || p.hasFlag "skip-proven") &&
      !p.hasFlag "no-index" && !p.hasFlag "fresh"
    if lookup then
      if let some addr ← ShardProofIndex.readAddress (← shardIndex) digest then
        try
          let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
          unless wrapper.claim == claim do throw (IO.userError "cached claim mismatch")
          verifyWrapper artifactPath wrapper
          IO.println s!"{label}: verified proof {addr} of this claim in the shard-proof index; reused"
          if mode == "prove" then IO.println (toString addr)
          return { address := some addr, report := Json.mkObj [("reused", toJson (toString addr))] }
        catch e => IO.eprintln s!"ignored cached proof {addr}: {e}"
    IO.println s!"[aiur] {mode} {label}"
    IO.FS.withTempDir fun dir => do
      let path := dir / "proof"
      let request ← phase "request" fun _ => request ()
      let (code, report) ← runHost artifactPath mode request path.toString options
      if code == 0 && (report.getObjVal? "execution_statistics").toOption.isNone then
        throw (IO.userError "successful execution returned no circuit statistics")
      let report ← IO.ofExcept (Aiur.enrichExecutionReport report)
      if let some flag := p.flag? "stats-out" then
        IO.FS.writeFile (flag.as! String) report.pretty
      else if (p.variableArgsAs! String).size == 1 || p.hasFlag "claim" || p.hasFlag "shard" then
        if let .ok raw := report.getObjVal? "execution_statistics" then
          Aiur.printStats (Aiur.computeStats (← IO.ofExcept (Aiur.ExecutionMeasurements.fromJson raw)))
      if mode == "execute" then return { code, report }
      let fit := (report.getObjVal? "plan" >>= fun j => j.getObjValAs? Bool "fits").toOption.getD false
      if code != 0 || !fit then return { code := if code == 0 then 75 else code, report }
      if mode != "prove" then return { code, report }
      let proofAddr ← persistClaim p claim path
      IO.println (toString proofAddr)
      return { report, address := some proofAddr }
  catch e =>
    IO.eprintln s!"{label}: {e}"
    return { code := 1, report := Json.mkObj [("error", toJson e.toString)] }

structure PartResult where
  blocks : Array Address
  result : JobResult
  constants : Nat := 0

/-- `ix check`/`ix prove --exec-only` over a manifest: each selected shard
executed (and with `plan` planned) statelessly. Lean selects each claim; the
prover rebuilds the advice from the environment Lean loaded
(`Ix.Check.loadBoundIxe`) and rejects the request unless it recomputes the
same claim. -/
private def runManifest (p : Cli.Parsed) (artifactPath : String) (options : HostOptions)
    (mode ixe manifest : String) (jobs : Nat) : IO UInt32 := do
  let (env, handle) ← phase "env load" fun _ => Ix.Check.loadBoundIxe ixe
  let assumeBinding := p.hasFlag "assume-binding"
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
  unless ← phase "manifest coverage" fun _ => Ix.Shard.shardsCover env view.shards do
    throw (IO.userError "invalid manifest coverage")
  if p.hasFlag "shard" && p.hasFlag "shards" then throw (IO.userError "choose --shard or --shards")
  let selected ← match (p.flag? "shard").map (·.as! Nat), (p.flag? "shards").map (·.as! String) with
    | some k, _ => pure #[k]
    | _, some s => IO.ofExcept (Ix.Shard.Check.parseShardSelection s)
    | _, _ => pure (Array.range view.shards.size)
  for k in selected do
    unless k < view.shards.size do throw (IO.userError s!"shard {k} out of range")
  if p.hasFlag "plan-only" then
    for k in selected do
      IO.println s!"shard {k}: {view.shards[k]!.size} blocks; RAM reservation {options.ram} bytes"
    return 0
  -- One environment pass assigns the selected shards' constants; refined
  -- parts partition their parent's constants instead of rescanning.
  let ownedSelected ← phase "owned constants" fun _ =>
    pure (Ix.Shard.ownedConstsPer env (selected.map (view.shards[·]!)))
  let ownedOf : Std.HashMap Nat (Array Address) := (selected.zip ownedSelected).foldl
    (fun m (k, owned) => m.insert k owned) {}
  let formalEnv ← phase "formal env" fun _ => FormalProver.Env.ofHandle handle
  let jobs := max 1 (min jobs selected.size)
  -- `--json` writes one benchmark results row (`Ix.Benchmark.Results`) for
  -- `ix bench run --backend aiur-sharded-env`; its peak covers the prover.
  if p.hasFlag "json" then TracingTexray.startSampler
  let start ← IO.monoMsNow
  let results ← boundedMap jobs selected fun members k => do
    let options := options.forWave jobs members
    let mut pending := #[(view.shards[k]!, ownedOf.getD k #[])]
    let mut settled : Array PartResult := #[]
    while !pending.isEmpty do
      let (blocks, owned) := pending.back!
      pending := pending.pop
      if owned.isEmpty then
        settled := settled.push { blocks, result := {} }
        continue
      let (claim, _) ← phase s!"claim ({owned.size} constants)" fun _ =>
        IO.ofExcept (shardCheckEnvClaimTrees env owned assumeBinding)
      let result ← one p artifactPath options mode claim (fun _ => shardRequest formalEnv blocks claim)
        s!"shard {k} ({blocks.size} blocks)"
      let canSplit := (result.report.getObjValAs? Bool "can_split").toOption.getD true
      if result.code == 75 && canSplit && blocks.size > 1 && !p.hasFlag "trace-shards" then
        let parts := (result.report.getObjVal? "plan" >>= fun j => j.getObjValAs? Nat "suggested_parts").toOption.getD 2
        let cut := Ix.Shard.Check.cutBlocks blocks parts
        IO.println s!"[aiur] shard {k}: splitting into {cut.size} parts after resource planning"
        pending := pending ++ (cut.zip (Ix.Shard.partitionOwned env owned cut)).reverse
      else
        if result.code == 75 then
          IO.eprintln s!"shard {k}: cannot fit budget; {if canSplit then "increase --max-ram or refine the environment" else "increase the RAM share (fewer --jobs or a larger budget)"}"
        settled := settled.push { blocks, result, constants := owned.size }
        if result.code != 0 && !p.hasFlag "keep-going" then pending := #[]
    return (k, settled)
  let elapsedMs := (← IO.monoMsNow) - start
  let failures := results.foldl (fun n (_, parts) => n + parts.countP (·.result.code != 0)) 0
  let (refinements, measured) := Ix.Shard.Check.refinementsOfRuns view.shards.size
    (results.map fun (k, parts) => (k, parts.map fun r => (r.blocks, r.result.peak)))
  if let some flag := p.flag? "out-ixes" then
    let _ ← Ix.Shard.Check.emitRefinedManifest "aiur" handle manifest (flag.as! String) refinements measured failures
  let leafReports := results.map fun (k, parts) =>
    let reports := parts.map fun (part : PartResult) => Json.mkObj [
      ("blocks", toJson (part.blocks.map toString)), ("status", toJson part.result.code.toNat),
      ("proof", toJson (part.result.address.map toString)), ("report", part.result.report)]
    Json.mkObj [("shard", toJson k), ("parts", toJson reports)]
  let name := ((p.flag? "json-name").map (·.as! String)).getD "env"
  let report := Json.mkObj [("schema", toJson "ix-formal-run/1"), ("failures", toJson failures),
    ("name", toJson name),
    ("jobs", toJson jobs), ("options", options.json), ("leaves", toJson leafReports)]
  if let some flag := p.flag? "report" then IO.FS.writeFile (flag.as! String) report.pretty
  if let some flag := p.flag? "json" then
    let constants := results.foldl (fun n (_, parts) => parts.foldl (· + ·.constants) n) 0
    let leaves := results.foldl (fun n (_, parts) => n + parts.size) 0
    let costs := results.flatMap fun (_, parts) => parts.map fun part =>
      (part.result.report.getObjValAs? Nat "fft-cost").toOption
    let fftFields := if costs.all Option.isSome then
        [("fft-cost", toJson (costs.foldl (fun n c => n + c.getD 0) 0))] else []
    let secs := elapsedMs.toFloat / 1000.0
    let throughput := if elapsedMs > 0 then constants.toFloat * 1000.0 / elapsedMs.toFloat else 0.0
    Ix.Benchmark.Results.writeRow (flag.as! String) name
      (if failures == 0 then "ok" else "rejected")
      (fftFields ++ [("constants", toJson constants), ("shards", toJson leaves),
       ("check-time", Ix.Benchmark.Results.jsonRound 3 secs),
       ("throughput", Ix.Benchmark.Results.jsonRound 2 throughput),
       ("peak-rss", toJson (← TracingTexray.peakTreeRssBytes))])
    if failures != 0 then return Ix.Benchmark.Results.exitRejected
  return if failures == 0 then 0 else 1

/-- `ix prove --ixe --ixes` without aggregation: the selected claims proven
on the aggregate controller, CPU lanes (`--jobs`) or one CUDA device, with
legacy's claim rules (an oversized claim is bisected; the index resumes;
`--out-ixes` is the partition proven). Prints `shard-id address` per claim. -/
private def proveManifest (p : Cli.Parsed) (artifactPath : String) (options : HostOptions)
    (ixe manifest : String) (jobs : Nat) : IO UInt32 := do
  if p.hasFlag "keep-going" then
    throw (IO.userError "--keep-going: the controller stops at its first failure; rerun to resume")
  let (_, handle) ← Ix.Check.loadBoundIxe ixe
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
  if p.hasFlag "shard" && p.hasFlag "shards" then throw (IO.userError "choose --shard or --shards")
  let selected ← match (p.flag? "shard").map (·.as! Nat), (p.flag? "shards").map (·.as! String) with
    | some k, _ => pure (some #[k])
    | _, some s => some <$> IO.ofExcept (Ix.Shard.Check.parseShardSelection s)
    | _, _ => pure none
  let ids ← selected.mapM fun ks => ks.mapM fun k => do
    let some id := view.shardIds[k]? | throw (IO.userError s!"shard {k} out of range")
    pure id
  let lanes := if options.device.isSome then 1 else max 1 jobs
  let maxRam := match (p.flag? "max-ram").map (·.as! Nat) with
    | some gib => gib * 1024^3 / lanes
    | none => 0
  let config := Json.mkObj [("manifest", toJson manifest),
    ("ixvm_artifact", toJson artifactPath), ("aggr_artifact", toJson (← aggregationArtifact p)),
    ("lanes", toJson lanes), ("device", toJson options.device), ("max_ram_bytes", toJson maxRam),
    ("exec_jobs", toJson (((p.flag? "exec-jobs").map (·.as! Nat)).getD 0)),
    ("structural_above", toJson (0 : Nat)), ("use_index", toJson !(p.hasFlag "no-index")),
    ("out_manifest", toJson ((p.flag? "out-ixes").map (·.as! String))),
    ("assume_binding", toJson (p.hasFlag "assume-binding")),
    ("claims_only", toJson true), ("select", toJson ids), ("options", options.json)]
  let lines ← FormalProver.proveLanes handle config.compress
  for line in lines.splitOn "\n" do
    unless line.isEmpty do IO.println line
  if let some flag := p.flag? "report" then
    IO.FS.writeFile (flag.as! String) (Json.mkObj [("schema", toJson "ix-formal-run/1"),
      ("failures", toJson (0 : Nat)), ("claims", toJson (lines.splitOn "\n"))]).pretty
  return 0

def run (p : Cli.Parsed) (prove : Bool) : IO UInt32 := do
  rejectFlags p #["lanes"]
  -- Aggregation flags would otherwise be ignored here: `--binding-proof`
  -- only takes effect at an aggregate root, which this path never builds.
  for flag in #["direct-joins", "structural-above", "range", "no-cache", "aggr-artifact",
      "binding-proof"] do
    if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --aggregate or --lanes")
  if p.hasFlag "texray" && (!prove || p.hasFlag "exec-only") then
    throw (IO.userError "--texray requires proving")
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  -- Reject manifest-only flags before any artifact export.
  if manifest.isSome && ixe.isNone then throw (IO.userError "--ixes requires --ixe")
  if manifest.isNone then
    for flag in #["shard", "shards", "out-ixes", "report", "plan-only", "exec-jobs",
        "trace-shards", "json", "json-name"] do
      if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --ixe and --ixes")
  let requestedJobs ← jobCount p
  let jobs ← if p.hasFlag "exec-only" && p.hasFlag "exec-jobs" then
      executionJobs p requestedJobs
    else pure requestedJobs
  let options ← hostOptions p (if prove && !p.hasFlag "exec-only" then 1 else jobs)
  let artifactPath ← if p.hasFlag "plan-only" then pure "" else artifact p
  let mode := if prove && !p.hasFlag "exec-only" then "prove"
    else if prove || p.hasFlag "ram-budget" then "plan" else "execute"
  match ixe, manifest with
  | some ixe, some manifest =>
    if mode == "prove" && !p.hasFlag "plan-only" then
      proveManifest p artifactPath options ixe manifest jobs
    else runManifest p artifactPath options mode ixe manifest jobs
  | _, some _ => throw (IO.userError "--ixes requires --ixe")
  | _, none =>
    if jobs != 1 then throw (IO.userError "--jobs currently requires --ixe and --ixes")
    -- With `--ixe` every claim shares one bound environment, copied into the
    -- prover once; a compiled environment differs per target.
    let shared ← IO.mkRef (none : Option FormalProver.Env)
    Ix.Check.forEachClaim ixe ((p.flag? "claim").map (·.as! String))
      (p.variableArgsAs! String).toList (p.hasFlag "keep-going") "aiur" false
      (fun claim handle target label => do
        let env ← match ← shared.get, handle with
          | some env, _ => pure (some env)
          | none, some handle => do
            let env ← FormalProver.Env.ofHandle handle
            if ixe.isSome then shared.set (some env)
            pure (some env)
          | none, none => pure none
        return (← one p artifactPath options mode claim (fun _ => targetRequest env claim target) label).code)
      (p.hasFlag "assume-binding")

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["aggregate", "structural-above"]
  let proofs := p.variableArgsAs! String
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  let shard := (p.flag? "shard").map (·.as! Nat)
  let bindingProof? := (p.flag? "binding-proof").map (·.as! String)
  let assumeBinding := bindingProof?.isSome
  let mut expected : Array Ix.Claim := #[]
  let mut envCtx? : Option Ix.ClaimContext := none
  match ixe, manifest with
  | some ixe, some manifest =>
    let env ← IO.ofExcept (withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))))
    let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env assumeBinding)
    envCtx? := some ctx
    let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
    if !(← Ix.Shard.shardsCover env view.shards) then return 1
    match shard with
    | some k =>
      let some blocks := view.shards[k]? | throw (IO.userError "shard index out of range")
      let prepared ← IO.ofExcept (Aggr.Reference.prepareShards env #[blocks] #[] assumeBinding)
      expected := prepared.map (·.claim)
    | none =>
      let (view, _) ← IO.ofExcept (view.pruneEmpty env)
      let prepared ← IO.ofExcept (Aggr.Reference.prepareShards env view.shards #[] assumeBinding)
      expected := prepared.map (·.claim)
  | none, none =>
    if shard.isSome || p.hasFlag "record" || bindingProof?.isSome then
      throw (IO.userError "--shard/--record/--binding-proof requires --ixe and --ixes")
  | _, _ => throw (IO.userError "formal partition verification requires both --ixe and --ixes")
  if proofs.isEmpty then
    if expected.isEmpty then IO.eprintln "expected a proof address"; return 1
    for claim in expected do IO.println s!"CheckEnv claim digest: {Address.blake3 (Ix.Claim.ser claim)}"
    return 0
  let mut artifactPath? : Option String := none
  if let some bPath := bindingProof? then
    let some ctx := envCtx? | throw (IO.userError "missing environment context for binding proof")
    let bWrapper ← readProofFileOrStore bPath
    let expectedBindingClaim : Ix.Claim := .binding ctx.spec ctx.binding
    unless bWrapper.claim == expectedBindingClaim do
      IO.eprintln s!"binding proof {bPath} states {bWrapper.claim}, expected {expectedBindingClaim}"
      return 1
    try
      let path ← match artifactPath? with
        | some path => pure path
        | none => let path ← artifact p; artifactPath? := some path; pure path
      verifyWrapper path bWrapper
    catch e =>
      IO.eprintln s!"{bPath}: {e}"
      return 1
  let mut result := 0
  let mut covered : Array Ix.Claim := #[]
  for hex in proofs do
    try
      let some addr := Address.fromString hex | throw (IO.userError "invalid proof address")
      let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
      unless expected.isEmpty || expected.contains wrapper.claim do
        throw (IO.userError "proof does not match a requested manifest shard")
      if covered.contains wrapper.claim then throw (IO.userError "duplicate shard proof")
      let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
      if Compression.isCompressed wrapper.proof then
        let rc ← Compression.verifyProof addr wrapper (p.hasFlag "dev-srs")
        if rc != 0 then result := 1
        else covered := covered.push wrapper.claim
      else
        let path ← match artifactPath? with
          | some path => pure path
          | none => let path ← artifact p; artifactPath? := some path; pure path
        verifyWrapper path wrapper
        covered := covered.push wrapper.claim
        if p.hasFlag "record" then ShardProofIndex.writeAddress (← shardIndex) digest addr
        IO.println s!"ok: proof {addr} verifies claim {digest}: {wrapper.claim}"
        if expected.isEmpty then
          if let some ctx := Ix.Claim.context? wrapper.claim then
            if ctx.bindingAssumed then
              IO.println s!"  note: claim assumes its role binding ({ctx.binding}) meets spec {ctx.spec}"
    catch e => IO.eprintln s!"{hex}: {e}"; result := 1
  unless expected.all covered.contains do
    IO.eprintln "proofs do not cover every requested nonempty shard"
    return 1
  return result

end Ix.Cli.FormalAiur
end
