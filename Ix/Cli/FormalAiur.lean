module
public import Cli
public import Ix.Check
public import Ix.Shard.Check
public import Ix.Store
public import Ix.Aggr.Reference
public import Ix.Cli.ShardProofIndex
public import Ix.Cli.Compression

/-! Application bridge to the separate Aiur/IxVM packages. This module reuses
Ix's claim and witness construction, not the legacy evaluator or compiler.
Compilation runs in the standalone exporter, which embeds the program; the
artifact is cached by the exporter and the program's digest.
The generic Aiur Lean library does not acquire application-specific FFI. -/
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

def commandStatus (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO UInt32 := do
  (← IO.getStdout).flush
  let child ← IO.Process.spawn { cmd, args, cwd, stdout := .inherit, stderr := .inherit }
  child.wait

def command (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO Unit := do
  let code ← commandStatus cmd args cwd
  unless code == 0 do throw (IO.userError s!"{cmd} failed with status {code}")

/-- The checkout this `ix` belongs to. The default backend's exporters, Rust
hosts and artifact cache live there, so commands work from any directory.
`IX_ROOT` overrides it; otherwise an executable at `<root>/.lake/build/bin`
identifies it, falling back to the working directory. -/
def repoRoot : IO System.FilePath := do
  if let some root ← IO.getEnv "IX_ROOT" then return root
  let app ← IO.appPath
  let root := do
    let bin ← app.parent
    let build ← bin.parent
    let lake ← build.parent
    lake.parent
  if let some root := root then
    if ← (root / "IxVM" / "lakefile.lean").pathExists then return root
  return "."

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
  if let some path := p.flag? flag then return path.as! String
  if let some path ← IO.getEnv env then return path
  let root ← repoRoot
  let exporter := root / exporterPath
  let buildTarget := if target == "ixvm" then "ixvm/ixvm"
    else if target == "stark-export" then "multiStark/stark-export"
    else target
  command "lake" #["-q", "build", buildTarget] root
  let program ← programDigest root exporter extra
  let compiler ← IO.FS.readBinFile exporter
  let digest := Address.blake3 ((Address.blake3 compiler).hash ++ program.toUTF8)
  let directory := root / ".lake" / "aiur"
  IO.FS.createDirAll directory
  let path := directory / s!"{target}-{digest}.json"
  unless ← path.pathExists do
    IO.eprintln s!"[aiur] exporting the certified {target} artifact (program {program}) to \
      {path}; this runs once per program and exporter build and takes several minutes \
      (`ix prepare` does it ahead of time)"
    let pid ← IO.Process.getPID
    let stamp ← IO.monoNanosNow
    let tmp := directory / s!"{target}-{digest}.tmp.{pid}.{stamp}"
    try
      command "lake" (#["env", exporter.toString, mode, tmp.toString] ++ extra) root
      IO.FS.rename tmp path
    finally
      if ← tmp.pathExists then IO.FS.removeFile tmp
  return path.toString

def artifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "aiur-artifact" "IX_AIUR_ARTIFACT" "IxVM/.lake/build/bin/ixvm"
    "ixvm" "export-claim-trace"

/-- A Rust host of the checkout. A missing host is built; `refresh` lets
cargo rebuild an existing one whose sources changed. -/
def rustHost (package binary env : String) (device : Option Nat := none)
    (refresh : Bool := false) : IO String := do
  if let some path ← IO.getEnv (env ++ if device.isSome then "_CUDA" else "") then return path
  let root ← repoRoot
  let directory := root / (if device.isSome then "target/formal-cuda" else "target")
  let path := directory / "release" / binary
  if refresh || !(← path.pathExists) then
    command "cargo" #["build", "--release", "--locked", "-p", package, "--bin", binary,
      "--target-dir", directory.toString,
      "--features", if device.isSome then "parallel,cuda" else "parallel"] root
  return path.toString

def host : IO String := rustHost "ixvm" "ixvm-proof" "IX_AIUR_HOST"

structure Resident where
  directory : System.FilePath
  running : IO Bool

structure HostOptions where
  rows : Nat := 0
  retention : String := "auto"
  ram : Nat := 0
  device : Option Nat := none
  threads : Nat := 0
  resident : Option Resident := none
  priority : Bool := false

def HostOptions.json (o : HostOptions) : Json := Json.mkObj [
  ("max_rows", if o.rows == 0 then .null else toJson o.rows),
  ("retention", toJson o.retention),
  ("max_ram_bytes", if o.ram == 0 then .null else toJson o.ram),
  ("device", toJson o.device)]

def HostOptions.forWave (o : HostOptions) (jobs members : Nat) : HostOptions :=
  if o.resident.isSome then o else
  { o with ram := o.ram * max jobs 1 / max members 1
           threads := o.threads * max jobs 1 / max members 1 }

/-- Keep workers occupied as individual jobs finish. All admitted tasks are
joined on failure, so temporary files and resident sessions outlive their jobs. -/
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

def resources : IO Json := do
  let result ← IO.Process.output { cmd := ← host, args := #["resources"] }
  unless result.exitCode == 0 do throw (IO.userError result.stderr)
  IO.ofExcept (Json.parse result.stdout)

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
  let gib := ((p.flag? "max-ram").orElse fun _ => p.flag? "ram-budget").map (·.as! Nat)
  if gib == some 0 then throw (IO.userError "RAM budget must be positive")
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
  let explicit := (p.flag? "exec-jobs").map (·.as! Nat)
  let ahead := (p.flag? "exec-ahead").map (·.as! Nat)
  let cores := ((← resources).getObjValAs? Nat "cores").toOption.getD 1
  let n := explicit.orElse (fun _ => ahead) |>.getD (if p.hasFlag "lanes" then 0 else jobs)
  if n == 0 then return if ahead == some 0 then jobs else cores
  return if p.hasFlag "lanes" then n * (((p.flag? "lanes").map (·.as! Nat)).getD 1) else n

/-- One process retains checked programs and one backend per device. It owns
the shared execution pool; Lean only schedules dependency-ready requests. -/
def withController {α : Type} (p : Cli.Parsed) (artifacts : Array (String × String))
    (options : HostOptions) (jobs : Nat) (f : HostOptions → IO α) : IO α := do
  if options.resident.isSome then return ← f options
  let lanes := ((p.flag? "lanes").map (·.as! Nat)).getD (if options.device.isSome then 1 else jobs)
  if lanes == 0 then throw (IO.userError "--lanes must be positive")
  let executors ← executionJobs p jobs
  let shared := (← IO.getEnv "IX_PROVER_SHARED_DEVICES") == some "1"
  let devices := (Array.range lanes).map fun i => options.device.map (· + if shared then 0 else i)
  let ram := if p.hasFlag "lanes" && p.hasFlag "max-ram" then options.ram * lanes else options.ram
  let binary ← rustHost "ix-prover" "ix-prover" "IX_PROVER_HOST" options.device
  let recordLimit ← match ← IO.getEnv "AIUR_RECORD_MAX_BYTES" with
    | none => pure Json.null
    | some s => match s.toNat? with
      | some n => pure (toJson n)
      | none => throw (IO.userError "AIUR_RECORD_MAX_BYTES must be a positive integer")
  IO.FS.withTempDir fun dir => do
    let config := Json.mkObj [
      ("artifacts", toJson (artifacts.map fun (path, kind) => Json.mkObj [("path", toJson path), ("kind", toJson kind)])),
      ("devices", toJson devices), ("exec_jobs", toJson executors),
      ("threads_per_prover", toJson (max 1 (options.threads / lanes))),
      ("max_ram_bytes", toJson ram), ("record_limit_bytes", recordLimit),
      ("texray", toJson (p.hasFlag "texray")),
      ("parent_pid", toJson (← IO.Process.getPID).toNat)]
    let path := dir / "config.json"
    IO.FS.writeFile path config.compress
    let child ← IO.Process.spawn {
      cmd := binary
      args := #["serve", path.toString, dir.toString]
      stdout := .inherit
      stderr := .inherit }
    let exited ← IO.asTask (prio := .dedicated) child.wait
    try
      while !(← (dir / "ready.json").pathExists) do
        if ← IO.hasFinished exited then
          let code ← IO.ofExcept exited.get
          let error ← if ← (dir / "failed.json").pathExists then IO.FS.readFile (dir / "failed.json") else pure ""
          throw (IO.userError s!"resident prover exited {code}: {error}")
        IO.sleep 10
      f { options with resident := some { directory := dir, running := do return !(← IO.hasFinished exited) } }
    finally
      IO.FS.writeFile (dir / "stop") ""
      let _ ← IO.wait exited
      if let some report := p.flag? "report" then
        for name in #["events.jsonl", "summary.json", "ready.json"] do
          if ← (dir / name).pathExists then
            IO.FS.writeFile (s!"{report.as! String}.{name}") (← IO.FS.readFile (dir / name))

private def residentRequest (resident : Resident) (artifactPath input output : String)
    (options : HostOptions) : IO UInt32 := do
  let id := toString (Address.blake3 input.toUTF8)
  let job := Json.mkObj [("id", toJson id), ("artifact", toJson artifactPath),
    ("input", toJson input), ("output", toJson output), ("options", options.json),
    ("priority", toJson options.priority)]
  let pending := resident.directory / "pending"
  let temp := pending / s!"{id}.tmp"
  IO.FS.writeFile temp job.compress
  IO.FS.rename temp (pending / s!"{id}.json")
  let donePath := resident.directory / "done" / s!"{id}.json"
  while !(← donePath.pathExists) do
    unless ← resident.running do throw (IO.userError "resident prover stopped before completing its request")
    IO.sleep 10
  let result ← IO.ofExcept (Json.parse (← IO.FS.readFile donePath))
  return UInt32.ofNat (← IO.ofExcept (result.getObjValAs? Nat "status"))

def runHost (binary artifactPath mode : String) (input : Json) (output : String)
    (options : HostOptions) : IO UInt32 :=
  IO.FS.withTempFile fun h path => IO.FS.withTempFile fun oh opath => do
    h.putStr input.compress
    h.flush
    oh.putStr options.json.compress
    oh.flush
    if let some resident := options.resident then
      if mode != "prove" then throw (IO.userError "resident session requires prove mode")
      return ← residentRequest resident artifactPath path.toString output options
    (← IO.getStdout).flush
    let child ← IO.Process.spawn {
      cmd := binary
      args := #[mode, artifactPath, path.toString, output, toString options.rows, options.retention, opath.toString]
      env := if options.threads == 0 then #[] else #[("RAYON_NUM_THREADS", some (toString options.threads))]
      stdout := .inherit, stderr := .inherit }
    child.wait

/-- Stream metadata is small; each byte payload is transported exactly once.
The Rust host turns these into immutable vectors captured by hint closures. -/
def invocation (input : Array Aiur.G) (buffer : Aiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : Json :=
  Json.mkObj [("entry", toJson entry), ("args", toJson (input.map (·.n))),
    ("streams", toJson (buffer.map.toArray.map fun ((channel, key), info) =>
      Json.mkObj [("channel", toJson channel.n), ("key", toJson (key.map Aiur.G.n)),
        ("values", toJson ((buffer.data.getD channel #[]).extract info.idx (info.idx + info.len) |>.map Aiur.G.n))]))]

def invoke (artifactPath mode : String) (input : Json) (proofPath : String)
    (rows : Nat) (retention : String := "regenerate") : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr input.compress
    handle.flush
    command (← host) #[mode, artifactPath, path.toString, proofPath, toString rows, retention]

def rejectFlags (p : Cli.Parsed) (flags : Array String) : IO Unit := do
  for flag in flags do
    if p.hasFlag flag then
      throw (IO.userError s!"--{flag} is not supported")

def verifyWrapper (artifactPath : String) (wrapper : Ixon.Proof) : IO Unit := do
  let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path wrapper.proof
    invoke artifactPath "verify" (invocation (packedDigestKey digest) default) path.toString 65536

def readProofFileOrStore (pathOrHex : String) : IO Ixon.Proof := do
  let bytes ← if ← System.FilePath.pathExists pathOrHex then
      IO.FS.readBinFile pathOrHex
    else if let some addr := Address.fromString pathOrHex then
      StoreIO.toIO (Store.read addr)
    else
      throw (IO.userError s!"cannot find proof file or store address '{pathOrHex}'")
  IO.ofExcept (Ixon.Proof.de bytes)

def shardIndex : IO System.FilePath := StoreIO.toIO (Store.cacheDir "formal-shard-proofs")

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

def one (p : Cli.Parsed) (artifactPath binary : String) (options : HostOptions)
    (mode : String) (claim : Ix.Claim) (target : Ix.Check.Target) (label : String)
    (resume : Bool := false) : IO JobResult := do
  try
    let .leanW witness := target | throw (IO.userError "formal backend needs a stream witness")
    let digest := Address.blake3 (Ix.Claim.ser claim)
    if mode == "prove" && (resume || p.hasFlag "skip-proven") && !p.hasFlag "no-index" then
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
      let proofAddr ← persistClaim p claim path
      IO.println (toString proofAddr)
      return { report, address := some proofAddr }
  catch e =>
    IO.eprintln s!"{label}: {e}"
    return { code := 1, report := Json.mkObj [("error", toJson e.toString)] }

structure PartResult where
  blocks : Array Address
  result : JobResult

private def runDistributed (p : Cli.Parsed) (artifactPath : String) (options : HostOptions)
    (ixe manifest : String) : IO UInt32 := do
  for flag in #["shard", "shards", "lanes", "jobs"] do
    if p.hasFlag flag then throw (IO.userError s!"--distributed cannot be combined with --{flag}")
  let env ← IO.ofExcept (withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))))
  let some binding := env.roleBinding | throw (IO.userError "distributed environment carries no role binding")
  let assumeBinding := p.hasFlag "assume-binding"
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env assumeBinding)
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
  unless ← Ix.Shard.shardsCover env view.shards do throw (IO.userError "invalid manifest coverage")
  let indexed := (view.shards.mapIdx fun i b => (i, Ix.Shard.ownedConstsForBlocks env b)).filter (!·.2.isEmpty)
  let owners := indexed.map (·.2)
  if owners.isEmpty then throw (IO.userError "distributed environment has no owned constants")
  let primitives := Ix.primAddrSet.toArray.filter env.consts.contains
  let bRoots := bindingRoots env
  let scopes := owners.map fun owned => closureFromRoots env (owned ++ primitives ++ bRoots)
  let jobs ← executionJobs p owners.size
  if p.hasFlag "plan-only" then
    for i in [:owners.size] do
      let callers := (Array.range owners.size).filter fun j => j != i &&
        (j == 0 || owners[i]!.any scopes[j]!.contains)
      IO.println s!"worker {i}: {owners[i]!.size} constants, {scopes[i]!.size} in byte scope; potential callers {callers}"
    IO.println s!"[aiur distributed] {min jobs owners.size} execution workers; replay one record at a time for batch proving"
    return 0
  let some tree := envCanonicalTree env | throw (IO.userError "empty environment")
  let claim := Ix.Claim.checkEnv ctx tree.root none
  let bytes := Ix.Claim.ser claim
  let digest := Address.blake3 bytes
  let args := packedDigestKey digest
  if p.hasFlag "skip-proven" && !p.hasFlag "no-index" && !p.hasFlag "exec-only" then
    if let some addr ← ShardProofIndex.readAddress (← shardIndex) digest then
      try
        let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
        unless wrapper.claim == claim do throw (IO.userError "cached distributed claim mismatch")
        verifyWrapper artifactPath wrapper
        IO.println (toString addr)
        return 0
      catch e => IO.eprintln s!"ignored distributed cache: {e}"
  let binary ← rustHost "ix-prover" "ix-prover" "IX_PROVER_HOST" options.device
  let validator := (Ix.Claim.validatorOf claim).toNat
  IO.FS.withTempDir fun dir => do
    let mut workers := #[]
    for i in [:owners.size] do
      let mut io := addEntries env scopes[i]!.contains (seedBinding env default)
      if i == 0 then
        io := io.extend 0 args (bytes.data.map Aiur.G.ofUInt8)
        io := io.extend 1 (tree.root.hash.data.map Aiur.G.ofUInt8) (tree.ser.data.map Aiur.G.ofUInt8)
      let input := dir / s!"worker-{i}.json"
      IO.FS.writeFile input (invocation args io).compress
      workers := workers.push (Json.mkObj [("input", toJson input.toString),
        ("owned", toJson (owners[i]!.map fun a =>
          binding.address.hash.data.map UInt8.toNat ++ #[validator] ++ a.hash.data.map UInt8.toNat))])
    let spec := Json.mkObj [("invocation", invocation args default), ("workers", toJson workers),
      ("exec_jobs", toJson (min jobs owners.size)), ("exec_only", toJson (p.hasFlag "exec-only")),
      ("texray", toJson (p.hasFlag "texray")),
      ("cells", toJson (((p.flag? "cells").map (·.as! Nat)).getD 0))]
    let specPath := dir / "distributed.json"
    let optionPath := dir / "options.json"
    let proofPath := dir / "proof"
    IO.FS.writeFile specPath spec.compress
    IO.FS.writeFile optionPath options.json.compress
    let child ← IO.Process.spawn {
      cmd := binary
      args := #["distributed", artifactPath, specPath.toString, proofPath.toString, optionPath.toString]
      env := #[("RAYON_NUM_THREADS", some (toString options.threads))]
      stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    let reportPath := System.FilePath.mk (proofPath.toString ++ ".report.json")
    if let some flag := p.flag? "report" then
      if ← reportPath.pathExists then IO.FS.writeFile (flag.as! String) (← IO.FS.readFile reportPath)
    if code != 0 then return code
    if let some flag := p.flag? "out-ixes" then
      let report ← IO.ofExcept (Json.parse (← IO.FS.readFile reportPath))
      let measured ← IO.ofExcept (report.getObjValAs? (Array Json) "workers")
      let mut peaks := Array.replicate view.shards.size 0
      for ((index, _), i) in indexed.zipIdx do
        peaks := peaks.set! index ((measured[i]!.getObjValAs? Nat "record_bytes").toOption.getD 0)
      let handle ← IO.ofExcept (Aiur.EnvHandle.fromIxe ixe)
      let _ ← Ix.Shard.Check.emitRefinedManifest "aiur distributed" handle manifest (flag.as! String) #[] peaks 0
    unless p.hasFlag "exec-only" do IO.println (toString (← persistClaim p claim proofPath))
    return 0

private def runManifest (p : Cli.Parsed) (artifactPath binary : String) (options : HostOptions)
    (mode ixe manifest : String) (jobs : Nat) : IO UInt32 := do
  let env ← IO.ofExcept (withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))))
  let assumeBinding := p.hasFlag "assume-binding"
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
  let jobs := max 1 (min jobs selected.size)
  let drive (options : HostOptions) : IO UInt32 := do
    let capacity ← if options.resident.isSome then pure (jobs + (← executionJobs p jobs)) else pure jobs
    let results ← boundedMap capacity selected fun members k => do
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
        let (claim, witness) ← IO.ofExcept (buildShardCheckEnvWitness env owned assumeBinding)
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
      let handle ← IO.ofExcept (Aiur.EnvHandle.fromIxe ixe)
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
  if mode == "prove" then withController p #[(artifactPath, "ixvm")] options jobs drive
  else drive options

def run (p : Cli.Parsed) (prove : Bool) : IO UInt32 := do
  rejectFlags p #["interp", "lanes"]
  for flag in #["direct-joins", "structural-above", "range", "no-cache", "aggr-artifact"] do
    if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --aggregate or --lanes")
  if p.hasFlag "texray" && (!prove || p.hasFlag "exec-only") && !p.hasFlag "distributed" then
    throw (IO.userError "--texray requires proving or --distributed")
  if p.hasFlag "cells" && !p.hasFlag "distributed" then throw (IO.userError "--cells requires --distributed")
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  let requestedJobs ← jobCount p
  let jobs ← if p.hasFlag "exec-only" && p.hasFlag "exec-jobs" && !p.hasFlag "distributed" then
      executionJobs p requestedJobs
    else pure requestedJobs
  let options ← hostOptions p (if prove && !p.hasFlag "exec-only" then 1 else jobs)
  let artifactPath ← if p.hasFlag "plan-only" then pure "" else artifact p
  let mode := if prove && !p.hasFlag "exec-only" then "prove"
    else if prove || p.hasFlag "ram-budget" || p.hasFlag "stats-out" then "plan" else "execute"
  let binary ← if p.hasFlag "plan-only" then pure ""
    else rustHost "ixvm" "ixvm-proof" "IX_AIUR_HOST" options.device
  match ixe, manifest with
  | some ixe, some manifest =>
    if p.hasFlag "distributed" then runDistributed p artifactPath options ixe manifest
    else runManifest p artifactPath binary options mode ixe manifest jobs
  | _, some _ => throw (IO.userError "--ixes requires --ixe")
  | _, none =>
    for flag in #["shard", "shards", "out-ixes", "report", "plan-only", "distributed", "exec-jobs"] do
      if p.hasFlag flag then throw (IO.userError s!"--{flag} requires --ixe and --ixes")
    if jobs != 1 then throw (IO.userError "--jobs currently requires --ixe and --ixes")
    let run options := Ix.Check.forEachClaim ixe ((p.flag? "claim").map (·.as! String))
        (p.variableArgsAs! String).toList (p.hasFlag "keep-going") "aiur" true
        (fun claim _ target label => return (← one p artifactPath binary options mode claim target label).code)
        (p.hasFlag "assume-binding")
    if mode == "prove" then withController p #[(artifactPath, "ixvm")] options 1 run
    else run options

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["aggregate", "structural-above"]
  if p.hasFlag "distributed" && (p.hasFlag "shard" || !p.hasFlag "ixe" || !p.hasFlag "ixes") then
    throw (IO.userError "--distributed verification requires --ixe and --ixes, without --shard")
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
      if p.hasFlag "distributed" then
        let some tree := envCanonicalTree env | throw (IO.userError "empty distributed environment")
        expected := #[.checkEnv ctx tree.root none]
      else
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
