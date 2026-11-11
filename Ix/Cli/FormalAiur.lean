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
public import Ix.Cli.FormalKeys

/-! Application bridge to the separate Aiur/IxVM packages. This module reuses
Ix's claim and witness construction, not the legacy evaluator or compiler.
`ix` links the certified compiler (`Ix.FormalCompiler`) and compiles a
program in process when the cache under `.lake/aiur` misses; an executable
that does not link it runs the standalone exporter instead. Either way the
package is cached by the compiler's identity and the program's digest.
Execution, proving and verification run in this process through the prover
library (`Ix.FormalProver`), on program and system handles that a command
loads once into its registry. The generic Aiur Lean library does not acquire
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

/-- The name a target's packages are cached and admitted under. -/
def cacheName : FormalProver.Target → String
  | .ixvm => "ixvm"
  | .verifier | .aggregation => "stark-export"

/-- The standalone exporter of a target: its binary, its Lake target, the mode
that exports the package with circuits, and extra arguments. -/
private def exporter : FormalProver.Target → String × String × String × Array String
  | .ixvm => ("IxVM/.lake/build/bin/ixvm", "ixvm/ixvm", "export-claim-trace", #[])
  | .verifier =>
    ("MultiStark/.lake/build/bin/stark-export", "multiStark/stark-export", "export-trace", #[])
  | .aggregation => ("MultiStark/.lake/build/bin/stark-export", "multiStark/stark-export",
    "export-trace", #["--aggregate"])

/-- The package of `target`, compiled once and cached under `.lake/aiur`
(`AiurArtifact.cached`), unless the flag `flag` or the variable `env` names a
trusted one. Either is admitted against the digest pinned by `--{flag}-digest`
or `{env}_DIGEST`. The cache key is BLAKE3 of the compiler's identity and the
digest of the program: the program alone determines the circuit only together
with the compiler. With the compiler linked into this executable
(`FormalProver.compiler?`), a miss compiles in process and the identity is
`compiler_identity%` of that code; otherwise the standalone exporter compiles,
and the identity is the digest of its binary. -/
def compiledArtifact (p : Cli.Parsed) (flag env : String) (target : FormalProver.Target) :
    IO String := do
  let name := cacheName target
  let expected ← AiurArtifact.expected ((p.flag? s!"{flag}-digest").map (·.as! String)) env
  if let some path := (p.flag? flag).map (·.as! String) then
    let _ ← AiurArtifact.admit name path expected; return path
  if let some path ← IO.getEnv env then
    let _ ← AiurArtifact.admit name path expected; return path
  let root ← repoRoot
  let cache := root / ".lake" / "aiur"
  if let some compiler ← FormalProver.compiler? then
    let identity := s!"ix-formal-compiler/{compiler.identity}".toUTF8
    let key := Address.blake3 ((Address.blake3 identity).hash ++ (compiler.digest target).toUTF8)
    return ← AiurArtifact.cached cache name key expected fun tmp => do
      let bytes ← phase s!"compile {name}" fun _ => compiler.compile target
      IO.FS.writeBinFile tmp bytes
  let (exporterPath, buildTarget, mode, extra) := exporter target
  let binary := root / exporterPath
  command "lake" #["-q", "build", buildTarget] root
  let program ← programDigest root binary extra
  let compiler ← IO.FS.readBinFile binary
  let key := Address.blake3 ((Address.blake3 compiler).hash ++ program.toUTF8)
  AiurArtifact.cached cache name key expected fun tmp =>
    command "lake" (#["env", binary.toString, mode, tmp.toString] ++ extra) root

/-- The flag and variable that name a trusted package for `target`. -/
private def selection : FormalProver.Target → String × String
  | .ixvm => ("aiur-artifact", "IX_AIUR_ARTIFACT")
  | .verifier => ("verifier-artifact", "IX_VERIFIER_ARTIFACT")
  | .aggregation => ("aggr-artifact", "IX_AGGR_ARTIFACT")

/-- The package of `target` (`compiledArtifact`). -/
def targetPath (p : Cli.Parsed) (target : FormalProver.Target) : IO String :=
  let (flag, env) := selection target
  compiledArtifact p flag env target

/-- The packages of `targets`, in order, selected concurrently: misses
compile at the same time. -/
def targetPaths (p : Cli.Parsed) (targets : Array FormalProver.Target) : IO (Array String) := do
  let tasks ← targets.mapM fun target => IO.asTask (prio := .dedicated) (targetPath p target)
  tasks.mapM fun task => do IO.ofExcept (← IO.wait task)

/-- The certified IxVM claim program with its circuits. -/
def artifactPath (p : Cli.Parsed) : IO String := targetPath p .ixvm

/-- The certified aggregation program (`MultiStark::ix_aggr`) with its circuits. -/
def aggregationArtifactPath (p : Cli.Parsed) : IO String := targetPath p .aggregation

/-- The certified recursive verifier (`MultiStark::verify_multi_stark_proof`)
with its circuits. -/
def verifierArtifactPath (p : Cli.Parsed) : IO String := targetPath p .verifier

/-- A program a command selected, in the registry that prepares its system. -/
structure Selected where
  registry : FormalProver.Registry
  program : FormalProver.Program
  /-- The package file it was loaded from. -/
  path : String

/-- Load the admitted package at `path` into `registry`. -/
def Selected.load (registry : FormalProver.Registry) (path : String) : IO Selected := do
  return { registry, program := ← registry.load path, path }

/-- The program's system under the default STARK parameters, prepared once
per registry. -/
def Selected.system (s : Selected) : IO FormalProver.System :=
  s.registry.system s.program {}

/-- The name a target's generated sources and native executor are filed
under (`ix_prover::codegen::PROGRAMS`). -/
def generatedName : FormalProver.Target → String
  | .ixvm => "ixvm"
  | .verifier => "verifier"
  | .aggregation => "aggregation"

/-- Report the executor `target`'s program runs on, and when this build links
a native executor for it, check that it was generated from exactly the
selected program: under `IX_FORMAL_NATIVE=1` a stale executor is an error,
otherwise it is reported. A stale executor is never used: the program runs on
the interpreter, which produces identical records and proofs. -/
def checkExecutor (target : FormalProver.Target) (s : Selected) : IO Unit := do
  let name := generatedName target
  if (← IO.getEnv "IX_PROVER_EXECUTOR") == some "interpreter" then
    IO.eprintln s!"[aiur] {name} executor interpreter (IX_PROVER_EXECUTOR)"
    return
  let (executor, fingerprint, _) ← s.program.executor
  IO.eprintln s!"[aiur] {name} executor {executor}"
  unless (← FormalProver.executors).contains s!"native-{name}" do return
  if executor == s!"native-{name}" then return
  let message := s!"the linked native {name} executor was generated from a different \
    program than {s.path} (native fingerprint {fingerprint}), so it runs on the interpreter. \
    Rebuild `ix` (`lake build ix`) to generate it for the current programs."
  if (← IO.getEnv "IX_FORMAL_NATIVE") == some "1" then
    throw (IO.userError s!"IX_FORMAL_NATIVE=1: {message}")
  IO.eprintln s!"[aiur] {message}"

/-- The programs of `targets`, in order, loaded into `registry` and checked
against the linked native executors; misses compile concurrently. -/
def selectAll (p : Cli.Parsed) (registry : FormalProver.Registry)
    (targets : Array FormalProver.Target) : IO (Array Selected) := do
  let paths ← targetPaths p targets
  (targets.zip paths).mapM fun (target, path) => do
    let selected ← Selected.load registry path
    checkExecutor target selected
    return selected

/-- The program of `target`, loaded into `registry` (`selectAll`). -/
def select (p : Cli.Parsed) (registry : FormalProver.Registry) (target : FormalProver.Target) :
    IO Selected := do
  let some selected := (← selectAll p registry #[target])[0]?
    | throw (IO.userError "missing selected program")
  return selected

def artifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  select p registry .ixvm

def aggregationArtifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  select p registry .aggregation

def verifierArtifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  select p registry .verifier

/-- Write the generated sources of the formal programs under `directory`:
each program's native executor, and with `cuda` its trace writers
(`FormalProver.Program.codegen`). A file is rewritten only when its contents
change, so Cargo recompiles only what changed; files that are no longer
generated, CUDA output in a CPU build included, are removed. Prints each
program's package, native fingerprint and linked executor. -/
def writeGenerated (p : Cli.Parsed) (directory : System.FilePath) (cuda : Bool) : IO Unit := do
  let targets := #[FormalProver.Target.ixvm, .verifier, .aggregation]
  let paths ← targetPaths p targets
  let registry ← FormalProver.Registry.new
  let mut expected : Array System.FilePath := #[]
  for target in targets, path in paths do
    let name := generatedName target
    let selected ← Selected.load registry path
    let files ← selected.program.codegen name cuda
    let (executor, fingerprint, _) ← selected.program.executor
    let bytes := files.foldl (fun n (_, contents) => n + contents.utf8ByteSize) 0
    IO.println s!"{name} artifact {path}"
    IO.println s!"{name} native fingerprint {fingerprint}; linked executor {executor}"
    IO.println s!"{name} generated {files.size} files, {bytes} bytes"
    for (relative, contents) in files do
      let file := directory / relative
      expected := expected.push file
      let existing ← try pure (some (← IO.FS.readFile file)) catch _ => pure none
      unless existing == some contents do
        if let some parent := file.parent then IO.FS.createDirAll parent
        let temporary := file.addExtension "tmp"
        IO.FS.writeFile temporary contents
        IO.FS.rename temporary file
  for sub in #["native", "cuda"] do
    let dir := directory / sub
    if ← dir.isDir then
      for entry in ← dir.walkDir do
        unless (← entry.isDir) || expected.contains entry do IO.FS.removeFile entry
  let cudaDir := directory / "cuda"
  if !cuda && (← cudaDir.isDir) then IO.FS.removeDirAll cudaDir

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
  let maxRam := (p.flag? "max-ram").map (·.as! Nat)
  if maxRam == some 0 then throw (IO.userError "RAM budget must be positive")
  let gib := maxRam.orElse fun _ => ((p.flag? "ram-budget").map (·.as! Nat)).filter (· != 0)
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

/-- Run one request on the selected program's system: prove it, or with
`execute` and `plan` check it without proving. With `report` the outcome
carries the job's JSON report. -/
def runHost (selected : Selected) (mode : String) (request : FormalProver.Request)
    (output : String) (options : HostOptions) (report : Bool) : IO FormalProver.Outcome := do
  -- The library prints progress on the process's stdout.
  (← IO.getStdout).flush
  let system ← selected.system
  if mode == "prove" then
    phase "prover" fun _ =>
      system.prove request output options.job options.threads report
  else if mode == "execute" then
    phase s!"check {mode}" fun _ => system.check request options.threads report
  else if mode == "plan" then
    phase s!"check {mode}" fun _ =>
      system.plan request options.job options.threads report
  else throw (IO.userError s!"unknown prover mode {mode}")

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

def shardIndex : IO System.FilePath := ShardProofIndex.indexDir

structure JobResult where
  code : UInt32 := 0
  plan : Option FormalProver.PlanSummary := none
  /-- The diagnostic report, when the job rendered one (`wantsReport`). -/
  report : Json := .null
  address : Option Address := none

def JobResult.peak (r : JobResult) : Nat :=
  match r.plan with
  | some plan => max plan.generationPeakBytes plan.provingPeakBytes
  | none => 0

/-- Whether a job's JSON report is needed: the command writes reports, or
prints a single claim's circuit statistics. The prover renders it only then. -/
def wantsReport (p : Cli.Parsed) : Bool :=
  p.hasFlag "stats-out" || p.hasFlag "report" || p.hasFlag "json" ||
    (p.variableArgsAs! String).size == 1 || p.hasFlag "claim" || p.hasFlag "shard"

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
    -- A verified proof of exactly this claim settles it: proving reuses it,
    -- and checking (`ix shard refine`) keeps its leaf rather than orphan it.
    let lookup := (resume && mode == "prove" || p.hasFlag "skip-proven") &&
      !p.hasFlag "no-index" && !p.hasFlag "fresh"
    if lookup then
      if let some addr ← ShardProofIndex.readAddress (← shardIndex) digest then
        try
          let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
          unless wrapper.claim == claim do throw (IO.userError "cached claim mismatch")
          verifyWrapper (← selected.system) wrapper
          IO.println s!"{label}: verified proof {addr} of this claim in the shard-proof index; reused"
          if mode == "prove" then IO.println (toString addr)
          return { address := some addr, report := Json.mkObj [("reused", toJson (toString addr))] }
        catch e => IO.eprintln s!"ignored cached proof {addr}: {e}"
    IO.println s!"[aiur] {mode} {label}"
    IO.FS.withTempDir fun dir => do
      let path := dir / "proof"
      let request ← phase "request" fun _ => request ()
      let wants := wantsReport p
      let outcome ← runHost selected mode request path.toString options wants
      let code := outcome.status
      let plan := outcome.plan
      let report ← if wants then IO.ofExcept (Json.parse outcome.report) else pure Json.null
      if wants && code == 0 && (report.getObjVal? "execution_statistics").toOption.isNone then
        throw (IO.userError "successful execution returned no circuit statistics")
      let report ← if wants then IO.ofExcept (Aiur.enrichExecutionReport report) else pure report
      if let some flag := p.flag? "stats-out" then
        IO.FS.writeFile (flag.as! String) report.pretty
      else if (p.variableArgsAs! String).size == 1 || p.hasFlag "claim" || p.hasFlag "shard" then
        if let .ok raw := report.getObjVal? "execution_statistics" then
          Aiur.printStats (Aiur.computeStats (← IO.ofExcept (Aiur.ExecutionMeasurements.fromJson raw)))
      if mode == "execute" then return { code, report }
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
  constants : Nat := 0

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
private def proveManifest (p : Cli.Parsed) (ixvm : Selected) (options : HostOptions)
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
  let aggr ← (← aggregationArtifact p ixvm.registry).system
  let config : FormalProver.LaneConfig := {
    manifest, lanes, device := options.device, maxRamBytes := maxRam
    execJobs := ((p.flag? "exec-jobs").map (·.as! Nat)).getD 0
    structuralAbove := 0, outManifest := (p.flag? "out-ixes").map (·.as! String)
    select := ids, bindingProof := none, options := options.job
    useCache := true, useIndex := !(p.hasFlag "no-index"), claimsOnly := true
    assumeBinding := p.hasFlag "assume-binding" }
  let .claims proven ← FormalProver.proveLanes (← ixvm.system) aggr handle config
    | throw (IO.userError "the controller returned a root for a claims-only run")
  let lines := proven.map fun (id, address) => s!"{id} {(⟨address⟩ : Address)}"
  for line in lines do IO.println line
  if let some flag := p.flag? "report" then
    IO.FS.writeFile (flag.as! String) (Json.mkObj [("schema", toJson "ix-formal-run/1"),
      ("failures", toJson (0 : Nat)), ("claims", toJson lines)]).pretty
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
  let registry ← FormalProver.Registry.new
  let selected ← if p.hasFlag "plan-only" then pure none else some <$> artifact p registry
  let mode := if prove && !p.hasFlag "exec-only" then "prove"
    else if prove || p.hasFlag "ram-budget" then "plan" else "execute"
  match ixe, manifest with
  | some ixe, some manifest =>
    match selected with
    | some selected =>
      if mode == "prove" then proveManifest p selected options ixe manifest jobs
      else runManifest p (some selected) options mode ixe manifest jobs
    | none => runManifest p none options mode ixe manifest jobs
  | _, some _ => throw (IO.userError "--ixes requires --ixe")
  | _, none =>
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
