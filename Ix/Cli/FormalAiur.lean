module
public import Cli
public import Ix.Check
public import Ix.Shard.Check
public import Ix.Store
public import Ix.Aggr.Reference
public import Ix.Cli.ShardProofIndex
public import Ix.Cli.Compression
public import Ix.Cli.FormalPrograms
public import Ix.Cli.FormalKeys

/-! Application bridge to the separate Aiur/IxVM packages. This module reuses
Ix's claim and witness construction, not the legacy evaluator or compiler.
Programs come from the compiled-program cache or the linked compiler
(`Ix.Cli.FormalPrograms`).
Execution, proving and verification run in this process through the prover
library (`Ix.FormalProver`), on program and system handles that a command
loads once into its registry. The generic Aiur Lean library does not acquire
application-specific FFI. -/
public section
namespace Ix.Cli.FormalAiur
open Lean IxVM.ClaimHarness

def selected (p : Cli.Parsed) : IO Bool := do
  if p.hasFlag "formal" && p.hasFlag "legacy" then
    throw (IO.userError "--formal and --legacy cannot be combined")
  if p.hasFlag "legacy" && p.hasFlag "gpu-device" then
    throw (IO.userError "--gpu-device selects the new backend; legacy device selection uses its existing environment settings")
  if p.hasFlag "legacy" then
    throw (IO.userError "--legacy has been retired; use the default certified Aiur backend")
  return true

def commandStatus (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO UInt32 := do
  (← IO.getStdout).flush
  let child ← IO.Process.spawn { cmd, args, cwd, env, stdout := .inherit, stderr := .inherit }
  child.wait

def command (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO Unit := do
  let code ← commandStatus cmd args cwd env
  unless code == 0 do throw (IO.userError s!"{cmd} failed with status {code}")

/-- The trusted artifact a command's flag or variable selects for `c`. -/
def explicitArtifact (p : Cli.Parsed) (c : Certified) : IO (Option String) :=
  match p.flag? c.flag with
  | some path => pure (some (path.as! String))
  | none => IO.getEnv c.env

/-- Certified programs, in order: each is the trusted artifact the
command's flag or variable selects, or otherwise compiled or loaded from
the cache (`compiledPrograms`). -/
def compiledArtifacts (p : Cli.Parsed) (registry : FormalProver.Registry)
    (programs : Array Certified) : IO (Array Selected) :=
  compiledPrograms registry programs (explicitArtifact p)

/-- One certified program; see `compiledArtifacts`. -/
def compiledArtifact (p : Cli.Parsed) (registry : FormalProver.Registry) (c : Certified) :
    IO Selected := do
  let some selected := (← compiledArtifacts p registry #[c])[0]?
    | throw (IO.userError s!"no {c.name} program")
  return selected

def artifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  compiledArtifact p registry ixvmProgram

/-- The certified aggregation program (`MultiStark::ix_aggr`) with its circuits. -/
def aggregationArtifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  compiledArtifact p registry aggregationProgram

/-- The certified recursive verifier (`MultiStark::verify_multi_stark_proof`)
with its circuits. -/
def verifierArtifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  compiledArtifact p registry verifierProgram

/-- The certified IxVM and aggregation programs, compiled concurrently on a
miss. -/
def ixvmAndAggregation (p : Cli.Parsed) (registry : FormalProver.Registry) :
    IO (Selected × Selected) := do
  match ← compiledArtifacts p registry #[ixvmProgram, aggregationProgram] with
  | #[ixvm, aggregation] => return (ixvm, aggregation)
  | _ => throw (IO.userError "expected the IxVM and aggregation programs")

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

/-- The planner options the prover reads. -/
def HostOptions.job (o : HostOptions) : FormalProver.JobOptions where
  maxRows := if o.rows == 0 then none else some o.rows
  maxRamBytes := if o.ram == 0 then none else some o.ram
  device := o.device
  retention := match o.retention with
    | "retain" => .retain
    | "regenerate" => .regenerate
    | _ => .auto

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

def resources : IO FormalProver.Resources := FormalProver.resources

def jobCount (p : Cli.Parsed) : IO Nat := do
  let n := ((p.flag? "jobs").map (·.as! Nat)).getD 1
  if n != 0 then return n
  return max 1 (← resources).cores

def hostOptions (p : Cli.Parsed) (shares : Nat := 1) : IO HostOptions := do
  let rows := ((p.flag? "shard-rows").map (·.as! Nat)).getD 0
  unless rows == 0 || (rows &&& (rows - 1)) == 0 do
    throw (IO.userError "--shard-rows must be zero (automatic) or a power of two")
  let retention := ((p.flag? "retention").map (·.as! String)).getD "auto"
  unless #["auto", "retain", "regenerate"].contains retention do
    throw (IO.userError "--retention must be auto, retain or regenerate")
  let gib := ((p.flag? "max-ram").orElse fun _ => p.flag? "ram-budget").map (·.as! Nat)
  if gib == some 0 then throw (IO.userError "RAM budget must be positive")
  let ram ← match gib with
    | some n => pure (n * 1024^3)
    | none => pure (((← resources).availableBytes.getD (8 * 1024^3)) * 85 / 100)
  let device ← match (p.flag? "gpu-device").map (·.as! Nat) with
    | some n => pure (some n)
    | none => do
      if p.hasFlag "lanes" || (← IO.getEnv "IX_CUDA") == some "1" then
        pure (some (((← IO.getEnv "MULTI_STARK_CUDA_DEVICE").bind String.toNat?).getD 0))
      else pure none
  let cores := (← resources).cores
  return {
    rows, retention, ram := max 1 (ram / max shares 1), device
    threads := max 1 (cores / max shares 1) }

def executionJobs (p : Cli.Parsed) (jobs : Nat) : IO Nat := do
  let cores := (← resources).cores
  let n := ((p.flag? "exec-jobs").map (·.as! Nat)).getD (if p.hasFlag "lanes" then 0 else jobs)
  if n == 0 then return cores
  return if p.hasFlag "lanes" then n * (((p.flag? "lanes").map (·.as! Nat)).getD 1) else n

/-- Run one request: prove it, or with `execute` and `plan` check it
without proving. Execution alone needs no system. With `report` the outcome
carries the job's JSON report. -/
def runHost (selected : Selected) (mode : String) (request : FormalProver.Request) (output : String)
    (options : HostOptions) (report : Bool) : IO FormalProver.Outcome := do
  -- The library prints progress on the process's stdout.
  (← IO.getStdout).flush
  if mode == "prove" then
    let system ← selected.system
    phase "prover" fun _ =>
      system.prove request output options.job options.threads report
  else if mode == "execute" then
    phase s!"check {mode}" fun _ =>
      selected.program.check request options.threads report
  else if mode == "plan" then
    let system ← selected.system
    phase s!"check {mode}" fun _ =>
      system.plan request options.job options.threads report
  else throw (IO.userError s!"unknown prover mode {mode}")

/-- Stream metadata is small; each byte payload is transported exactly once.
The Rust host turns these into immutable vectors captured by hint closures. -/
def invocation (input : Array Aiur.G) (buffer : Aiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : Json :=
  Json.mkObj [("entry", toJson entry), ("args", toJson (input.map (·.n))),
    ("streams", toJson (buffer.map.toArray.map fun ((channel, key), info) =>
      Json.mkObj [("channel", toJson channel.n), ("key", toJson (key.map Aiur.G.n)),
        ("values", toJson ((buffer.data.getD channel #[]).extract info.idx (info.idx + info.len) |>.map Aiur.G.n))]))]

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

def verifyWrapper (system : FormalProver.System) (wrapper : Ixon.Proof) : IO Unit := do
  let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let _ ← system.verify "IxVM::verify_claim"
    ((packedDigestKey digest).map (·.val)) wrapper.proof

def readProofFileOrStore (pathOrHex : String) : IO Ixon.Proof := do
  let bytes ← if ← System.FilePath.pathExists pathOrHex then
      IO.FS.readBinFile pathOrHex
    else if let some addr := Address.fromString pathOrHex then
      StoreIO.toIO (Store.read addr)
    else
      throw (IO.userError s!"cannot find proof file or store address '{pathOrHex}'")
  IO.ofExcept (Ixon.Proof.de bytes)

def shardIndex : IO System.FilePath := StoreIO.toIO (Store.cacheDir "shard-proofs")

structure JobResult where
  code : UInt32 := 0
  plan : Option FormalProver.PlanSummary := none
  /-- The diagnostic report, when the command writes reports. -/
  report : Json := .null
  address : Option Address := none

def JobResult.peak (r : JobResult) : Nat :=
  match r.plan with
  | some plan => max plan.generationPeakBytes plan.provingPeakBytes
  | none => 0

/-- Whether the command writes job reports, which the prover then renders. -/
def wantsReports (p : Cli.Parsed) : Bool :=
  p.hasFlag "stats-out" || p.hasFlag "report" || p.hasFlag "json"

def persistClaim (p : Cli.Parsed) (claim : Ix.Claim) (path : System.FilePath) : IO Address := do
  let keyAddr ← StoreIO.toIO (Store.write (← IO.FS.readBinFile (path.toString ++ ".vk")))
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let wrapper : Ixon.Proof := { claim, proof := ← IO.FS.readBinFile path }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  unless p.hasFlag "no-index" do
    ShardProofIndex.writeAddress (← shardIndex) (Address.blake3 (Ix.Claim.ser claim)) proofAddr
  IO.println s!"verifying-key {keyAddr}"
  return proofAddr

def one (p : Cli.Parsed) (selected : Selected) (options : HostOptions)
    (mode : String) (claim : Ix.Claim) (request : Unit → IO FormalProver.Request) (label : String)
    (resume : Bool := false) : IO JobResult := do
  try
    let digest := Address.blake3 (Ix.Claim.ser claim)
    if mode == "prove" && (resume || p.hasFlag "skip-proven") && !p.hasFlag "no-index" then
      if let some addr ← ShardProofIndex.readAddress (← shardIndex) digest then
        try
          let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
          unless wrapper.claim == claim do throw (IO.userError "cached claim mismatch")
          verifyWrapper (← selected.system) wrapper
          IO.println s!"reused {addr}"
          return { address := some addr, report := Json.mkObj [("reused", toJson (toString addr))] }
        catch e => IO.eprintln s!"ignored cached proof {addr}: {e}"
    IO.println s!"[aiur] {mode} {label}"
    IO.FS.withTempDir fun dir => do
      let path := dir / "proof"
      let request ← phase "request" fun _ => request ()
      let outcome ← runHost selected mode request path.toString options (wantsReports p)
      let code := outcome.status
      if mode == "execute" then return { code }
      let report ← if outcome.report.isEmpty then pure Json.null
        else IO.ofExcept (Json.parse outcome.report)
      if let some flag := p.flag? "stats-out" then
        IO.FS.writeFile (flag.as! String) report.pretty
      let plan := outcome.plan
      let fit := (plan.map (·.fits)).getD false
      if code != 0 || !fit then return { code := if code == 0 then 75 else code, plan, report }
      if mode != "prove" then return { code, plan, report }
      let proofAddr ← persistClaim p claim path
      IO.println (toString proofAddr)
      return { plan, report, address := some proofAddr }
  catch e =>
    IO.eprintln s!"{label}: {e}"
    return { code := 1, report := Json.mkObj [("error", toJson e.toString)] }

structure PartResult where
  blocks : Array Address
  result : JobResult

/-- `ix check`/`ix prove --exec-only` over a manifest: each selected shard
executed (and with `plan` planned) statelessly. Lean selects each claim; the
prover rebuilds the advice from the environment Lean loaded
(`Ix.Check.loadBoundIxe`) and rejects the request unless it recomputes the
same claim. -/
private def runManifest (p : Cli.Parsed) (ixvm : Option Selected) (options : HostOptions)
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
  let some ixvm := ixvm | throw (IO.userError "missing the IxVM program")
  let formalEnv ← phase "formal env" fun _ => FormalProver.Env.ofHandle handle
  let jobs := max 1 (min jobs selected.size)
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
      let result ← one p ixvm options mode claim (fun _ => shardRequest formalEnv blocks claim)
        s!"shard {k} ({blocks.size} blocks)"
      let canSplit := (result.plan.map (·.canSplit)).getD true
      if result.code == 75 && canSplit && blocks.size > 1 && !p.hasFlag "trace-shards" then
        let parts := (result.plan.map (·.suggestedParts)).getD 2
        let cut := Ix.Shard.Check.cutBlocks blocks parts
        IO.println s!"[aiur] shard {k}: splitting into {cut.size} parts after resource planning"
        pending := pending ++ (cut.zip (Ix.Shard.partitionOwned env owned cut)).reverse
      else
        if result.code == 75 then
          IO.eprintln s!"shard {k}: cannot fit budget; {if canSplit then "increase --max-ram or refine the environment" else "increase the RAM share (fewer --jobs or a larger budget)"}"
        settled := settled.push { blocks, result }
        if result.code != 0 && !p.hasFlag "keep-going" then pending := #[]
    return (k, settled)
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
  let report := Json.mkObj [("schema", toJson "ix-formal-run/1"), ("failures", toJson failures),
    ("name", toJson (((p.flag? "json-name").map (·.as! String)).getD "env")),
    ("jobs", toJson jobs), ("options", options.json), ("leaves", toJson leafReports)]
  if let some flag := p.flag? "report" then IO.FS.writeFile (flag.as! String) report.pretty
  if let some flag := p.flag? "json" then
    let handle ← IO.FS.Handle.mk (flag.as! String) .append
    handle.putStrLn report.compress
  return if failures == 0 then 0 else 1

/-- `ix prove --ixe --ixes` without aggregation: the selected claims proven
on the aggregate controller, CPU lanes (`--jobs`) or one CUDA device, with
legacy's claim rules (an oversized claim is bisected; the index resumes;
`--out-ixes` is the partition proven). Prints `shard-id address` per claim. -/
private def proveManifest (p : Cli.Parsed) (ixvm aggregation : Selected) (options : HostOptions)
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
  let aggr ← aggregation.system
  let config : FormalProver.LaneConfig := {
    manifest, lanes, device := options.device, maxRamBytes := maxRam
    execJobs := ((p.flag? "exec-jobs").map (·.as! Nat)).getD 0
    structuralAbove := 0, outManifest := (p.flag? "out-ixes").map (·.as! String)
    select := ids, bindingProof := none, options := options.job
    useCache := true, useIndex := !(p.hasFlag "no-index"), claimsOnly := true
    assumeBinding := p.hasFlag "assume-binding" }
  let .claims proven ← FormalProver.proveLanes (← ixvm.system) aggr handle config
    | throw (IO.userError "the controller returned a root for a claims-only run")
  let lines := proven.map fun (id, address) => s!"{id} {hexOfBytes address}"
  for line in lines do IO.println line
  if let some flag := p.flag? "report" then
    IO.FS.writeFile (flag.as! String) (Json.mkObj [("schema", toJson "ix-formal-run/1"),
      ("failures", toJson (0 : Nat)), ("claims", toJson lines)]).pretty
  return 0

def run (p : Cli.Parsed) (prove : Bool) : IO UInt32 := do
  rejectFlags p #["interp", "lanes"]
  for flag in #["direct-joins", "structural-above", "range", "no-cache", "aggr-artifact"] do
    if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --aggregate or --lanes")
  if p.hasFlag "texray" && (!prove || p.hasFlag "exec-only") then
    throw (IO.userError "--texray requires proving")
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  let requestedJobs ← jobCount p
  let jobs ← if p.hasFlag "exec-only" && p.hasFlag "exec-jobs" then
      executionJobs p requestedJobs
    else pure requestedJobs
  let options ← hostOptions p (if prove && !p.hasFlag "exec-only" then 1 else jobs)
  let registry ← FormalProver.Registry.new
  let mode := if prove && !p.hasFlag "exec-only" then "prove"
    else if prove || p.hasFlag "ram-budget" || p.hasFlag "stats-out" then "plan" else "execute"
  -- Proving a manifest also needs aggregation; both compile concurrently.
  let (selected, aggregation) ← if p.hasFlag "plan-only" then pure (none, none)
    else if mode == "prove" && ixe.isSome && manifest.isSome then do
      let (ixvm, aggregation) ← ixvmAndAggregation p registry
      pure (some ixvm, some aggregation)
    else pure (some (← artifact p registry), none)
  match ixe, manifest with
  | some ixe, some manifest =>
    match selected, aggregation with
    | some selected, some aggregation =>
      proveManifest p selected aggregation options ixe manifest jobs
    | some selected, none => runManifest p selected options mode ixe manifest jobs
    | none, _ => runManifest p none options mode ixe manifest jobs
  | _, some _ => throw (IO.userError "--ixes requires --ixe")
  | _, none =>
    for flag in #["shard", "shards", "out-ixes", "report", "plan-only", "exec-jobs"] do
      if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --ixe and --ixes")
    if jobs != 1 then throw (IO.userError "--jobs currently requires --ixe and --ixes")
    let some selected := selected | throw (IO.userError "--plan-only requires --ixe and --ixes")
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
        return (← one p selected options mode claim (fun _ => targetRequest env claim target) label).code)
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
  let registry ← FormalProver.Registry.new
  let mut system? : Option FormalProver.System := none
  if let some bPath := bindingProof? then
    let some ctx := envCtx? | throw (IO.userError "missing environment context for binding proof")
    let bWrapper ← readProofFileOrStore bPath
    let expectedBindingClaim : Ix.Claim := .binding ctx.spec ctx.binding
    unless bWrapper.claim == expectedBindingClaim do
      IO.eprintln s!"binding proof {bPath} states {bWrapper.claim}, expected {expectedBindingClaim}"
      return 1
    try
      let system ← match system? with
        | some system => pure system
        | none =>
          let system ← (← artifact p registry).system
          FormalKeys.checkSystem "ixvm" system
          system? := some system
          pure system
      verifyWrapper system bWrapper
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
        let system ← match system? with
          | some system => pure system
          | none =>
            let system ← (← artifact p registry).system
            FormalKeys.checkSystem "ixvm" system
            system? := some system
            pure system
        verifyWrapper system wrapper
        covered := covered.push wrapper.claim
        if p.hasFlag "record" then ShardProofIndex.writeAddress (← shardIndex) digest addr
        IO.println s!"ok: proof {addr} verifies claim {digest}"
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
