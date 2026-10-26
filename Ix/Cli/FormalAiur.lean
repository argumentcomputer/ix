module
public import Cli
public import Ix.Check
public import Ix.Shard.Check
public import Ix.Store
public import Ix.Aggr.Reference
public import Ix.Cli.ShardProofIndex

/-! Application bridge to the separate Aiur/IxVM packages. This module reuses
Ix's claim and witness construction, not the legacy evaluator or compiler.
Compilation runs in the standalone exporter and is cached by its contents.
The generic Aiur Lean library does not acquire application-specific FFI. -/
public section
namespace Ix.Cli.FormalAiur
open Lean LegacyIxVM.ClaimHarness

def selected (p : Cli.Parsed) : IO Bool := do
  if p.hasFlag "formal" && p.hasFlag "legacy" then
    throw (IO.userError "--formal and --legacy cannot be combined")
  if p.hasFlag "legacy" && p.hasFlag "gpu-device" then
    throw (IO.userError "--gpu-device selects the new backend; legacy device selection uses its existing environment settings")
  return !p.hasFlag "legacy"

def commandStatus (cmd : String) (args : Array String) : IO UInt32 := do
  (← IO.getStdout).flush
  let child ← IO.Process.spawn { cmd, args, stdout := .inherit, stderr := .inherit }
  child.wait

def command (cmd : String) (args : Array String) : IO Unit := do
  let code ← commandStatus cmd args
  unless code == 0 do throw (IO.userError s!"{cmd} failed with status {code}")

def compiledArtifact (p : Cli.Parsed) (flag env exporterPath target sourcePath mode : String)
    (extra : Array String := #[]) : IO String := do
  if let some path := p.flag? flag then return path.as! String
  if let some path ← IO.getEnv env then return path
  let exporter := System.FilePath.mk exporterPath
  command "lake" #["-q", "build", target]
  let source ← IO.FS.readBinFile sourcePath
  let compiler ← IO.FS.readBinFile exporter
  let digest := Address.blake3 ((Address.blake3 compiler).hash ++ source)
  let directory := System.FilePath.mk ".lake/aiur"
  IO.FS.createDirAll directory
  let path := directory / s!"{target}-{digest}.json"
  unless ← path.pathExists do
    let pid ← IO.Process.getPID
    let stamp ← IO.monoNanosNow
    let tmp := directory / s!"{target}-{digest}.tmp.{pid}.{stamp}"
    try
      command "lake" (#["env", exporter.toString, mode, tmp.toString] ++ extra)
      IO.FS.rename tmp path
    finally
      if ← tmp.pathExists then IO.FS.removeFile tmp
  return path.toString

def artifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "aiur-artifact" "IX_AIUR_ARTIFACT" "IxVM/.lake/build/bin/ixvm"
    "ixvm" "IxVM/IxVM/Program.aiur" "export-claim-trace"

def rustHost (package binary env : String) (device : Option Nat := none) : IO String := do
  if let some path ← IO.getEnv (env ++ if device.isSome then "_CUDA" else "") then return path
  let directory := if device.isSome then "target/formal-cuda" else "target"
  let path := System.FilePath.mk directory / "release" / binary
  unless ← path.pathExists do
    command "cargo" #["build", "--release", "--locked", "-p", package, "--bin", binary,
      "--target-dir", directory, "--features", if device.isSome then "parallel,cuda" else "parallel"]
  return path.toString

def host : IO String := rustHost "ixvm" "ixvm-proof" "IX_AIUR_HOST"

structure HostOptions where
  rows : Nat := 65536
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

/-- Each wave is joined completely, including on failure, before a new wave
starts. The caller reserves a RAM share for every concurrent child process. -/
def boundedMap {α β : Type} (jobs : Nat) (xs : Array α) (f : Nat → α → IO β) : IO (Array β) := do
  let mut out := #[]
  let mut offset := 0
  while offset < xs.size do
    let wave := xs.extract offset (offset + max jobs 1)
    let tasks ← wave.mapM fun x => IO.asTask (prio := .dedicated) (f wave.size x)
    let results := tasks.map (·.get)
    for result in results do out := out.push (← IO.ofExcept result)
    offset := offset + wave.size
  return out

def resources : IO Json := do
  let result ← IO.Process.output { cmd := ← host, args := #["resources"] }
  unless result.exitCode == 0 do throw (IO.userError result.stderr)
  IO.ofExcept (Json.parse result.stdout)

def jobCount (p : Cli.Parsed) : IO Nat := do
  let n := ((p.flag? "jobs").map (·.as! Nat)).getD 1
  if n != 0 then return n
  return max 1 ((← resources).getObjValAs? Nat "cores" |>.toOption.getD 1)

def hostOptions (p : Cli.Parsed) (shares : Nat := 1) : IO HostOptions := do
  let rows := ((p.flag? "shard-rows").map (·.as! Nat)).getD 65536
  unless rows == 0 || (rows &&& (rows - 1)) == 0 do
    throw (IO.userError "--shard-rows must be zero (automatic) or a power of two")
  let retention := ((p.flag? "retention").map (·.as! String)).getD "auto"
  unless #["auto", "retain", "regenerate"].contains retention do
    throw (IO.userError "--retention must be auto, retain or regenerate")
  let gib := ((p.flag? "max-ram").orElse fun _ => p.flag? "ram-budget").map (·.as! Nat)
  if gib == some 0 then throw (IO.userError "RAM budget must be positive")
  let ram ← match gib with
    | some n => pure (n * 1024^3)
    | none => pure (((← resources).getObjValAs? Nat "available_bytes" |>.toOption.getD (8 * 1024^3)) * 85 / 100)
  let device ← match (p.flag? "gpu-device").map (·.as! Nat) with
    | some n => pure (some n)
    | none => do
      if (← IO.getEnv "IX_CUDA") == some "1" then
        pure (some (((← IO.getEnv "MULTI_STARK_CUDA_DEVICE").bind String.toNat?).getD 0))
      else pure none
  let cores := ((← resources).getObjValAs? Nat "cores").toOption.getD 1
  return {
    rows, retention, ram := max 1 (ram / max shares 1), device
    threads := max 1 (cores / max shares 1) }

def runHost (binary artifactPath mode : String) (input : Json) (output : String)
    (options : HostOptions) : IO UInt32 :=
  IO.FS.withTempFile fun h path => IO.FS.withTempFile fun oh opath => do
    h.putStr input.compress
    h.flush
    oh.putStr options.json.compress
    oh.flush
    (← IO.getStdout).flush
    let child ← IO.Process.spawn {
      cmd := binary
      args := #[mode, artifactPath, path.toString, output, toString options.rows, options.retention, opath.toString]
      env := if options.threads == 0 then #[] else #[("RAYON_NUM_THREADS", some (toString options.threads))]
      stdout := .inherit, stderr := .inherit }
    child.wait

/-- Stream metadata is small; each byte payload is transported exactly once.
The Rust host turns these into immutable vectors captured by hint closures. -/
def invocation (input : Array LegacyAiur.G) (buffer : LegacyAiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : Json :=
  Json.mkObj [("entry", toJson entry), ("args", toJson (input.map (·.n))),
    ("streams", toJson (buffer.map.toArray.map fun ((channel, key), info) =>
      Json.mkObj [("channel", toJson channel.n), ("key", toJson (key.map LegacyAiur.G.n)),
        ("values", toJson ((buffer.data.getD channel #[]).extract info.idx (info.idx + info.len) |>.map LegacyAiur.G.n))]))]

def invoke (artifactPath mode : String) (input : Json) (proofPath : String)
    (rows : Nat) (retention : String := "regenerate") : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr input.compress
    handle.flush
    command (← host) #[mode, artifactPath, path.toString, proofPath, toString rows, retention]

def rejectFlags (p : Cli.Parsed) (flags : Array String) : IO Unit := do
  for flag in flags do
    if p.hasFlag flag then
      throw (IO.userError s!"--{flag} currently requires --legacy")

def verifyWrapper (artifactPath : String) (wrapper : Ixon.Proof) : IO Unit := do
  let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path wrapper.proof
    invoke artifactPath "verify" (invocation (packedDigestKey digest) default) path.toString 65536

def shardIndex : IO System.FilePath := StoreIO.toIO (Store.cacheDir "formal-shard-proofs")

structure JobResult where
  code : UInt32 := 0
  report : Json := .null
  address : Option Address := none

def JobResult.peak (r : JobResult) : Nat :=
  let plan := (r.report.getObjVal? "plan").toOption.getD .null
  max ((plan.getObjValAs? Nat "generation_peak_bytes").toOption.getD 0)
    ((plan.getObjValAs? Nat "proving_peak_bytes").toOption.getD 0)

private def one (p : Cli.Parsed) (artifactPath binary : String) (options : HostOptions)
    (mode : String) (claim : Ix.Claim) (target : Ix.Check.Target) (label : String) : IO JobResult := do
  try
    let .leanW witness := target | throw (IO.userError "formal backend needs a stream witness")
    let digest := Address.blake3 (Ix.Claim.ser claim)
    if mode == "prove" && p.hasFlag "skip-proven" && !p.hasFlag "no-index" then
      if let some addr ← ShardProofIndex.readAddress (← shardIndex) digest then
        try
          let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
          unless wrapper.claim == claim do throw (IO.userError "cached claim mismatch")
          verifyWrapper artifactPath wrapper
          IO.println s!"reused {addr}"
          return { address := some addr, report := Json.mkObj [("reused", toJson (toString addr))] }
        catch e => IO.eprintln s!"ignored cached proof {addr}: {e}"
    IO.println s!"[aiur] {mode} {label}"
    IO.FS.withTempDir fun dir => do
      let path := dir / "proof"
      let input := invocation witness.input witness.inputIOBuffer
      let code ← runHost binary artifactPath mode input path.toString options
      if mode == "execute" then return { code }
      let reportPath := System.FilePath.mk (path.toString ++ ".report.json")
      let report ← if ← reportPath.pathExists then
          IO.ofExcept (Json.parse (← IO.FS.readFile reportPath)) else pure Json.null
      if let some flag := p.flag? "stats-out" then
        IO.FS.writeFile (flag.as! String) report.pretty
      let fit := (report.getObjVal? "plan" >>= fun j => j.getObjValAs? Bool "fits").toOption.getD false
      if code != 0 || !fit then return { code := if code == 0 then 75 else code, report }
      if mode != "prove" then return { code, report }
      let proof ← IO.FS.readBinFile path
      let key ← IO.FS.readBinFile (path.toString ++ ".vk")
      let keyAddr ← StoreIO.toIO (Store.write key)
      let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
      let wrapper : Ixon.Proof := { claim, proof }
      let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
      unless p.hasFlag "no-index" do
        ShardProofIndex.writeAddress (← shardIndex) digest proofAddr
      IO.println s!"verifying-key {keyAddr}"
      IO.println (toString proofAddr)
      return { report, address := some proofAddr }
  catch e =>
    IO.eprintln s!"{label}: {e}"
    return { code := 1, report := Json.mkObj [("error", toJson e.toString)] }

structure PartResult where
  blocks : Array Address
  result : JobResult

private def runManifest (p : Cli.Parsed) (artifactPath binary : String) (options : HostOptions)
    (mode ixe manifest : String) (jobs : Nat) : IO UInt32 := do
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
  unless ← Ix.Shard.shardsCover env view.shards do throw (IO.userError "invalid manifest coverage")
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
  let results ← boundedMap jobs selected fun members k => do
    let options := options.forWave jobs members
    let mut pending := #[view.shards[k]!]
    let mut settled : Array PartResult := #[]
    while !pending.isEmpty do
      let blocks := pending.back!
      pending := pending.pop
      let owned := Ix.Shard.ownedConstsForBlocks env blocks
      if owned.isEmpty then
        settled := settled.push { blocks, result := {} }
        continue
      let (claim, witness) ← IO.ofExcept (buildShardCheckEnvWitness env owned)
      let result ← one p artifactPath binary options mode claim (.leanW witness) s!"shard {k} ({blocks.size} blocks)"
      let canSplit := (result.report.getObjValAs? Bool "can_split").toOption.getD true
      if result.code == 75 && canSplit && blocks.size > 1 && !p.hasFlag "trace-shards" then
        let parts := (result.report.getObjVal? "plan" >>= fun j => j.getObjValAs? Nat "suggested_parts").toOption.getD 2
        let cut := Ix.Shard.Check.cutBlocks blocks parts
        IO.println s!"[aiur] shard {k}: splitting into {cut.size} parts after resource planning"
        pending := pending ++ cut.reverse
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
    let handle ← IO.ofExcept (LegacyAiur.EnvHandle.fromIxe ixe)
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

def run (p : Cli.Parsed) (prove : Bool) : IO UInt32 := do
  rejectFlags p #["interp", "distributed", "cells", "lanes", "exec-jobs", "texray"]
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  let jobs ← jobCount p
  let options ← hostOptions p jobs
  let artifactPath ← if p.hasFlag "plan-only" then pure "" else artifact p
  let mode := if prove && !p.hasFlag "exec-only" then "prove"
    else if prove || p.hasFlag "ram-budget" || p.hasFlag "stats-out" then "plan" else "execute"
  -- Resolve/build the host before concurrent workers start.
  let binary ← if p.hasFlag "plan-only" then pure ""
    else rustHost "ixvm" "ixvm-proof" "IX_AIUR_HOST" options.device
  match ixe, manifest with
  | some ixe, some manifest => runManifest p artifactPath binary options mode ixe manifest jobs
  | _, some _ => throw (IO.userError "--ixes requires --ixe")
  | _, none =>
    for flag in #["shard", "shards", "out-ixes", "report", "plan-only"] do
      if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --ixe and --ixes")
    if jobs != 1 then throw (IO.userError "--jobs currently requires --ixe and --ixes")
    Ix.Check.forEachClaim ixe ((p.flag? "claim").map (·.as! String))
      (p.variableArgsAs! String).toList (p.hasFlag "keep-going") "aiur" true
      (fun claim _ target label => return (← one p artifactPath binary options mode claim target label).code)

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["aggregate", "structural-above"]
  let artifactPath ← artifact p
  let proofs := p.variableArgsAs! String
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  let shard := (p.flag? "shard").map (·.as! Nat)
  let mut expected : Array Ix.Claim := #[]
  match ixe, manifest with
  | some ixe, some manifest =>
    let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
    let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
    if !(← Ix.Shard.shardsCover env view.shards) then return 1
    match shard with
    | some k =>
      let some blocks := view.shards[k]? | throw (IO.userError "shard index out of range")
      let prepared ← IO.ofExcept (Aggr.Reference.prepareShards env #[blocks])
      expected := prepared.map (·.claim)
    | none =>
      let (view, _) ← IO.ofExcept (view.pruneEmpty env)
      let prepared ← IO.ofExcept (Aggr.Reference.prepareShards env view.shards)
      expected := prepared.map (·.claim)
  | none, none =>
    if shard.isSome || p.hasFlag "record" then throw (IO.userError "--shard/--record requires --ixe and --ixes")
  | _, _ => throw (IO.userError "formal partition verification requires both --ixe and --ixes")
  if proofs.isEmpty then
    if expected.isEmpty then IO.eprintln "expected a proof address"; return 1
    for claim in expected do IO.println s!"CheckEnv claim digest: {Address.blake3 (Ix.Claim.ser claim)}"
    return 0
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
      verifyWrapper artifactPath wrapper
      covered := covered.push wrapper.claim
      if p.hasFlag "record" then ShardProofIndex.writeAddress (← shardIndex) digest addr
      IO.println s!"ok: proof {addr} verifies claim {digest}"
    catch e => IO.eprintln s!"{hex}: {e}"; result := 1
  unless expected.all covered.contains do
    IO.eprintln "proofs do not cover every requested nonempty shard"
    return 1
  return result

end Ix.Cli.FormalAiur
end
