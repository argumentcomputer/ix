import Lean

/-!
Compare CPU and CUDA BN254 KZG development proofs using independently built
binaries. Replaces `tests/kzg_backend_parity.py`.

Run from the repository root on a CUDA host:

```sh
lake env lean --run Scripts/KzgBackendParity.lean --out /path/to/empty-dir
```

Also supports `--help` and `--self-test` (which runs unit checks without
invoking `cargo` or requiring a GPU).
-/

namespace KzgBackendParity

open Lean System

def usage : String :=
  "usage: lake env lean --run Scripts/KzgBackendParity.lean --out DIR\n" ++
  "       lake env lean --run Scripts/KzgBackendParity.lean [--self-test | --help]\n\n" ++
  "Compare CPU and CUDA development proofs using independently built binaries."

inductive Mode where
  | help
  | selfTest
  | run (out : FilePath)
  deriving BEq, Repr

def parseArgs : List String → Except String Mode
  | ["--help"] | ["-h"] => .ok .help
  | ["--self-test"] => .ok .selfTest
  | ["--out", dir] =>
    if dir.isEmpty then .error "--out requires a non-empty path" else .ok (.run dir)
  | [arg] =>
    if arg.startsWith "--out=" then
      let dir := (arg.drop 6).toString
      if dir.isEmpty then .error "--out requires a non-empty path" else .ok (.run dir)
    else .error s!"unknown argument: {arg}"
  | _ => .error "expected --out DIR (or --help / --self-test)"

private def hasSubstr (text pattern : String) : Bool :=
  (text.splitOn pattern).length > 1

private def setEnv (env : Array (String × Option String)) (key : String) (val : Option String) :
    Array (String × Option String) :=
  match env.findIdx? (·.1 == key) with
  | some i => env.set! i (key, val)
  | none => env.push (key, val)

private def floatJson (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | .inr n => .num n
  | .inl _ => .null

/-- SHA-256 hex digest of a file via `sha256sum`. -/
def sha256 (path : FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"sha256sum {path}: {out.stderr}"
  let hex := (out.stdout.splitOn " ").headD ""
  unless hex.length == 64 do
    throw <| IO.userError s!"unexpected sha256sum output for {path}: {out.stdout}"
  return hex

private def checkedOutput (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"{cmd} {" ".intercalate args.toList} failed (exit {out.exitCode}): {out.stderr}"
  return out.stdout

structure RunRecord where
  command : Array String
  log : String
  exitCode : Nat
  elapsedSeconds : Float
  timing : Option String
  dispatch : Option (Array String) := none
  deriving Repr

def RunRecord.toJson (r : RunRecord) : Json :=
  let base : List (String × Json) := [
    ("command", Lean.toJson r.command),
    ("log", Lean.toJson r.log),
    ("exit_code", Lean.toJson r.exitCode),
    ("elapsed_seconds", floatJson r.elapsedSeconds),
    ("timing", match r.timing with | some t => Lean.toJson t | none => .null)
  ]
  let fields := match r.dispatch with
    | some d => base ++ [("dispatch", Lean.toJson d)]
    | none => base
  Json.mkObj fields

structure BuildRecord where
  run : RunRecord
  features : String
  binary : String
  binarySha256 : String
  nativeSha256 : Option String := none
  deriving Repr

def BuildRecord.toJson (b : BuildRecord) : Json :=
  let base : List (String × Json) := [
    ("command", Lean.toJson b.run.command),
    ("log", Lean.toJson b.run.log),
    ("exit_code", Lean.toJson b.run.exitCode),
    ("elapsed_seconds", floatJson b.run.elapsedSeconds),
    ("timing", match b.run.timing with | some t => Lean.toJson t | none => .null),
    ("features", Lean.toJson b.features),
    ("binary", Lean.toJson b.binary),
    ("binary_sha256", Lean.toJson b.binarySha256)
  ]
  let fields := match b.nativeSha256 with
    | some h => base ++ [("native_sha256", Lean.toJson h)]
    | none => base
  Json.mkObj fields

/-- Run `command`, redirecting stdout and stderr to `log` and wrapping with
`/usr/bin/time -v` when available. -/
def runCommand (command : Array String) (log : FilePath)
    (env : Array (String × Option String)) (success : Bool := true)
    (expectedError : Option String := none) : IO RunRecord := do
  IO.println (Json.mkObj [
    ("command", Lean.toJson command),
    ("log", Lean.toJson log.toString)
  ]).compress
  (← IO.getStdout).flush
  let started ← IO.monoNanosNow
  let timing := log.withExtension "time"
  let timeBin : FilePath := "/usr/bin/time"
  let hasTime ← do
    if ← timeBin.pathExists then pure !(← timeBin.isDir) else pure false
  let argv :=
    if hasTime then #["/usr/bin/time", "-v", "-o", timing.toString, "--"] ++ command
    else command
  let some cmd := argv[0]? | throw <| IO.userError "empty command"
  let child ← IO.Process.spawn {
    cmd := "sh"
    args := #["-c", "log=$1; shift; exec \"$@\" >\"$log\" 2>&1", "sh", log.toString, cmd] ++
      argv.extract 1 argv.size
    env
  }
  let code ← child.wait
  let expectedCode : UInt32 := if success then 0 else 1
  if code != expectedCode then
    throw <| IO.userError s!"unexpected exit {code}: {log}"
  if let some needle := expectedError then
    let text ← IO.FS.readFile log
    unless hasSubstr text needle do
      throw <| IO.userError s!"missing expected rejection {repr needle}: {log}"
  let elapsed := ((← IO.monoNanosNow) - started).toFloat / 1e9
  let timing? := if ← timing.pathExists then some timing.toString else none
  return {
    command, log := log.toString, exitCode := code.toNat,
    elapsedSeconds := elapsed, timing := timing?
  }

/-- Extract the compiled `kzg_backend_parity` example path and optional
`libmulti_stark_cuda.so` path from Cargo JSON diagnostic lines. -/
def parseCargoArtifacts (jsonl : String) : Option String × Option FilePath := Id.run do
  let mut executable : Option String := none
  let mut native : Option FilePath := none
  for line in jsonl.splitOn "\n" do
    let .ok event := Json.parse line | continue
    let reason := (event.getObjValAs? String "reason").toOption
    let targetName := (event.getObjVal? "target" >>= (·.getObjValAs? String "name")).toOption
    if reason == some "compiler-artifact" && targetName == some "kzg_backend_parity" then
      if let .ok exe := event.getObjValAs? String "executable" then
        executable := some exe
    if let .ok libs := event.getObjValAs? (Array String) "linked_libs" then
      if libs.contains "dylib=multi_stark_cuda" then
        if let .ok outDir := event.getObjValAs? String "out_dir" then
          native := some (FilePath.mk outDir / "libmulti_stark_cuda.so")
  return (executable, native)

def buildVariant (cuda : Bool) (directory : FilePath)
    (env : Array (String × Option String)) : IO (FilePath × BuildRecord) := do
  let mode := if cuda then "cuda" else "cpu"
  let features := if cuda then "parallel,cuda" else "parallel"
  let command : Array String := #[
    "cargo", "build", "--offline", "--locked", "-p", "ix-proof-compression",
    "--no-default-features", "--features", features,
    "--example", "kzg_backend_parity", "--message-format=json-render-diagnostics"
  ]
  let log := directory / s!"build-{mode}.jsonl"
  let recRun ← runCommand command log env
  let (executable?, native?) := parseCargoArtifacts (← IO.FS.readFile log)
  let some executable := executable?
    | throw <| IO.userError s!"Cargo did not report the requested artifacts: {log}"
  if cuda && native?.isNone then
    throw <| IO.userError s!"Cargo did not report the requested artifacts: {log}"
  -- Cargo reuses the example's output name across feature selections.
  -- Snapshot each binary and its shared library before building another one.
  let binary := directory / "bin" / mode
  IO.FS.createDirAll (directory / "bin")
  discard <| checkedOutput "cp" #["-p", executable, binary.toString]
  let nativeSha ← match cuda, native? with
    | true, some native =>
      let some libName := native.fileName
        | throw <| IO.userError s!"native library has no filename: {native}"
      let libDir := directory / "lib"
      IO.FS.createDirAll libDir
      let library := libDir / libName
      discard <| checkedOutput "cp" #["-p", native.toString, library.toString]
      pure (some (← sha256 library))
    | _, _ => pure none
  let binSha ← sha256 binary
  return (binary, {
    run := recRun, features, binary := binary.toString,
    binarySha256 := binSha, nativeSha256 := nativeSha
  })

/-- Required GPU dispatch log lines for a CUDA proving mode. -/
def requiredDispatch (mode : String) : Array String :=
  let base :=
    if mode == "passes" then
      #["KZG lookup constructed in GPU passes", "KZG quotient evaluated in GPU passes"]
    else
      #["KZG lookup constructed on device", "KZG quotient evaluated on device"]
  let withQueue := base.push "KZG interpolation queue"
  if mode == "cached" then withQueue.push "KZG SRS cache access" else withQueue

def checkDispatchText (text : String) (mode : String) (logLabel : String) :
    Except String (Array String) :=
  let required := requiredDispatch mode
  let missing := required.filter (!hasSubstr text ·)
  if missing.isEmpty then .ok required
  else .error s!"missing GPU dispatch evidence {repr missing}: {logLabel}"

def checkDispatch (log : FilePath) (mode : String) : IO (Array String) := do
  let text ← IO.FS.readFile log
  IO.ofExcept (checkDispatchText text mode log.toString)

private def trackedSourceExt (p : FilePath) : Bool :=
  match p.extension with
  | some ext => #["rs", "cu", "cuh", "cpp", "h", "hpp", "toml", "lock", "lean"].contains ext
  | none => false

def runParity (outDir : FilePath) : IO UInt32 := do
  if ← outDir.pathExists then
    if !(← outDir.readDir).isEmpty then
      IO.eprintln "error: output directory must be empty"
      return 2
  IO.FS.createDirAll outDir
  let root ← IO.FS.realPath outDir
  let baseEnv : Array (String × Option String) := #[
    ("RUST_LOG", some "ix_proof_compression=debug")
  ]
  let baselineRev := (← checkedOutput "git" #["rev-parse", "HEAD"]).trimAscii.toString
  let scope :=
    "Two ordinary BN254 KZG circuits at 4096/8192 rows with development parameters; " ++
    "no FRI or recursive KZG proving."
  let lsOut ← checkedOutput "git" #[
    "ls-files", "--cached", "--others", "--exclude-standard", "--",
    "crates/proof-compression", "crates/aiur", "Cargo.toml", "Cargo.lock",
    ".cargo/config.toml", "rust-toolchain.toml", "Scripts/KzgBackendParity.lean"
  ]
  let mut srcSet : Std.HashMap String Unit := {}
  for line in lsOut.splitOn "\n" do
    let p : String := line.trimAscii.toString
    if !p.isEmpty && trackedSourceExt (FilePath.mk p) then
      srcSet := srcSet.insert p ()
  let sortedSources : Array String := (srcSet.toArray.map (·.1)).qsort (· < ·)
  let mut sourceHashes : List (String × Json) := []
  for p in sortedSources do
    sourceHashes := sourceHashes ++ [(p, Lean.toJson (← sha256 (FilePath.mk p)))]

  let (cpu, cpuBuild) ← buildVariant false root baseEnv
  let cpuEnv := setEnv baseEnv "CUDA_VISIBLE_DEVICES" (some "")
  let cpuRun ← runCommand #[cpu.toString, "prove", (root / "cpu").toString, "cpu"]
    (root / "prove-cpu.log") cpuEnv
  let reference ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "cpu" / "report.json"))

  let (gpu, gpuBuild) ← buildVariant true root baseEnv
  let existingLd := (← IO.getEnv "LD_LIBRARY_PATH").getD ""
  let ldPath :=
    if existingLd.isEmpty then (root / "lib").toString
    else s!"{root / "lib"}:{existingLd}"
  let gpuEnv :=
    setEnv (setEnv baseEnv "CUDA_VISIBLE_DEVICES" (some "0")) "LD_LIBRARY_PATH" (some ldPath)

  let mut provingRuns : Array (String × RunRecord) := #[("cpu", cpuRun)]
  for mode in #["dense", "passes", "cached"] do
    let log := root / s!"prove-{mode}.log"
    let recRun ← runCommand #[gpu.toString, "prove", (root / mode).toString, mode] log gpuEnv
    let dispatch ← checkDispatch log mode
    provingRuns := provingRuns.push (mode, { recRun with dispatch := some dispatch })
    let candidate ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / mode / "report.json"))
    for key in #["curve", "input_blake3", "proof_blake3", "verifier_blake3"] do
      let refVal ← IO.ofExcept (reference.getObjVal? key)
      let candVal ← IO.ofExcept (candidate.getObjVal? key)
      if candVal != refVal then
        throw <| IO.userError s!"{mode}: {key} differs from CPU"
    for artifact in #["proof.bin", "vk.bin"] do
      let candBytes ← IO.FS.readBinFile (root / mode / artifact)
      let refBytes ← IO.FS.readBinFile (root / "cpu" / artifact)
      if candBytes.data != refBytes.data then
        throw <| IO.userError s!"{mode}: {artifact} differs from CPU"

  let verifier := root / "cpu" / "vk.bin"
  let pin ← IO.ofExcept (reference.getObjValAs? String "verifier_blake3")
  let mut verified : Array RunRecord := #[]
  for (mode, _) in provingRuns do
    let r ← runCommand #[cpu.toString, "verify", (root / mode / "proof.bin").toString,
      verifier.toString, pin] (root / s!"verify-{mode}-on-cpu.log") cpuEnv
    verified := verified.push r
  let gpuCpuVerify ← runCommand #[gpu.toString, "verify", (root / "cpu" / "proof.bin").toString,
    verifier.toString, pin] (root / "verify-cpu-on-cuda-binary.log")
    (setEnv gpuEnv "CUDA_VISIBLE_DEVICES" (some ""))
  verified := verified.push gpuCpuVerify

  let wrongPin := String.ofList (List.replicate 64 '0')
  let rejected ← runCommand #[cpu.toString, "verify", (root / "cpu" / "proof.bin").toString,
    verifier.toString, wrongPin] (root / "reject-verifier-pin.log") cpuEnv
    (success := false) (expectedError := some "verifier differs from the independently supplied pin")

  let proofBytes ← IO.ofExcept (reference.getObjVal? "proof_bytes")
  let proofBlake3 ← IO.ofExcept (reference.getObjVal? "proof_blake3")
  let inputBlake3 ← IO.ofExcept (reference.getObjVal? "input_blake3")
  let report := Json.mkObj [
    ("baseline_revision", Lean.toJson baselineRev),
    ("scope", Lean.toJson scope),
    ("source_sha256", Json.mkObj sourceHashes),
    ("builds", Json.arr #[cpuBuild.toJson, gpuBuild.toJson]),
    ("proving_runs", Json.mkObj (provingRuns.toList.map fun (m, r) => (m, r.toJson))),
    ("verification_runs", Json.arr (verified.map (·.toJson))),
    ("wrong_pin_rejection", rejected.toJson),
    ("proof_bytes", proofBytes),
    ("proof_blake3", proofBlake3),
    ("verifier_blake3", Lean.toJson pin),
    ("input_blake3", inputBlake3),
    ("exact_byte_parity", Lean.toJson true)
  ]
  let reportPath := root / "report.json"
  IO.FS.writeFile reportPath (report.pretty ++ "\n")
  IO.println (Json.mkObj [
    ("report", Lean.toJson reportPath.toString),
    ("exact_byte_parity", Lean.toJson true)
  ]).compress
  (← IO.getStdout).flush
  return 0

private def ensure (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def selfTest : IO Unit := do
  ensure ((parseArgs ["--help"]).toOption == some .help) "help arg"
  ensure ((parseArgs ["--self-test"]).toOption == some .selfTest) "self-test arg"
  ensure ((parseArgs ["--out", "/tmp/kzg-out"]).toOption == some (.run "/tmp/kzg-out")) "--out arg"
  ensure ((parseArgs ["--out=/tmp/kzg-out"]).toOption == some (.run "/tmp/kzg-out")) "--out= arg"
  ensure ((parseArgs []).toOption.isNone) "missing --out rejected"
  ensure ((parseArgs ["--unknown"]).toOption.isNone) "unknown flag rejected"

  let sampleCargo :=
    "{\"reason\":\"build-script-executed\",\"linked_libs\":[\"dylib=multi_stark_cuda\"],\"out_dir\":\"/tmp/out\"}\n" ++
    "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"kzg_backend_parity\"},\"executable\":\"/tmp/bin/kzg\"}\n"
  let (exe?, nat?) := parseCargoArtifacts sampleCargo
  ensure (exe? == some "/tmp/bin/kzg") "cargo executable extraction"
  ensure (nat? == some (FilePath.mk "/tmp/out/libmulti_stark_cuda.so")) "cargo native lib extraction"

  let denseLog :=
    "KZG lookup constructed on device\nKZG quotient evaluated on device\nKZG interpolation queue\n"
  let passesLog :=
    "KZG lookup constructed in GPU passes\nKZG quotient evaluated in GPU passes\nKZG interpolation queue\n"
  let cachedLog := denseLog ++ "KZG SRS cache access\n"
  ensure ((checkDispatchText denseLog "dense" "dense.log").isOk) "dense dispatch"
  ensure ((checkDispatchText passesLog "passes" "passes.log").isOk) "passes dispatch"
  ensure ((checkDispatchText cachedLog "cached" "cached.log").isOk) "cached dispatch"
  ensure ((checkDispatchText denseLog "cached" "dense.log").toOption.isNone) "cached missing SRS rejected"

  let stamp := (← IO.monoNanosNow) + 7919 * (← IO.Process.getPID).toNat
  let tmpFile : FilePath := s!"/tmp/kzg-parity-selftest-{stamp}.txt"
  try
    IO.FS.writeFile tmpFile "abc"
    let digest ← sha256 tmpFile
    ensure (digest == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
      s!"sha256 mismatch: {digest}"
  finally
    try IO.FS.removeFile tmpFile catch _ => pure ()
  IO.println "KzgBackendParity self-tests passed."

end KzgBackendParity

def main (args : List String) : IO UInt32 := do
  match KzgBackendParity.parseArgs args with
  | .error e =>
    IO.eprintln s!"error: {e}\n{KzgBackendParity.usage}"
    return 2
  | .ok .help =>
    IO.println KzgBackendParity.usage
    return 0
  | .ok .selfTest =>
    KzgBackendParity.selfTest
    return 0
  | .ok (.run out) =>
    KzgBackendParity.runParity out
