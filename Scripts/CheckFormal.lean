import Lean

/-!
Integration gate for the separate formal packages (`IxVM`, `MultiStark`, `Aiur`)
and the `ix` CLI. Replaces `tools/ixvm/check-formal.sh`.

Run from the repository root:

```sh
lean --run Scripts/CheckFormal.lean [--dry-run | --self-test | --help]
```

Environment variables:
- `IX_TEST_OUTPUT_DIR`: keep exported artifacts and logs in this directory
  instead of a temporary directory (which is otherwise removed on exit).
- `IX_TEST_CUDA=1`: also build CUDA hosts into `target/formal-cuda`, run the
  single-device controller gate, and run full CPU/CUDA proof parity.
- `MULTI_STARK_CUDA_DEVICE`: CUDA device index for the hardware controller gate
  (default `0`).
- `IX_AIUR_ARTIFACT`, `IX_RECURSION_ARTIFACT`, `IX_AGGR_ARTIFACT`: reuse
  pre-exported `.ixa` artifacts instead of re-exporting them.
- `IX_CHECK_FORMAL_SKIP_BUILD=1`: skip the initial `lake build` and `cargo build`
  steps when an upstream CI build job has already compiled all binaries.
- `IX_CHECK_FORMAL_SKIP_AIUR_UNITS=1`: skip `u32_tests` when an upstream CI job
  has already run the standalone Aiur unit tests.
-/

namespace CheckFormal

open System

def usage : String :=
  "usage: lean --run Scripts/CheckFormal.lean [--dry-run | --self-test | --security-128-gate | --help]\n\n" ++
  "Integration gate for IxVM, MultiStark, Aiur, and the ix CLI.\n" ++
  "Honors IX_TEST_OUTPUT_DIR, IX_TEST_CUDA, MULTI_STARK_CUDA_DEVICE,\n" ++
  "IX_AIUR_ARTIFACT, IX_RECURSION_ARTIFACT, and IX_AGGR_ARTIFACT."

inductive Mode where
  | run
  | dryRun
  | selfTest
  | security128Gate
  | help
  deriving BEq, Repr

def parseArgs : List String → Except String Mode
  | [] => .ok .run
  | ["--help"] | ["-h"] => .ok .help
  | ["--dry-run"] => .ok .dryRun
  | ["--self-test"] => .ok .selfTest
  | ["--security-128-gate"] => .ok .security128Gate
  | other => .error s!"unexpected arguments: {" ".intercalate other}"

/-- Return the value of an environment variable when it is set and non-empty,
matching bash `${VAR:-}`. -/
def getNonEmptyEnv (name : String) : IO (Option String) := do
  match ← IO.getEnv name with
  | some v => return if v.isEmpty then none else some v
  | none => return none

/-- Update or append an environment override without duplicating keys. -/
def setEnv (env : Array (String × Option String)) (key : String) (val : Option String) :
    Array (String × Option String) :=
  match env.findIdx? (·.1 == key) with
  | some i => env.set! i (key, val)
  | none => env.push (key, val)

/-- Extract the last line of stdout, matching `tail -n 1` on a file. -/
def lastLine (text : String) : String :=
  let stripped := if text.endsWith "\n" then (text.dropEnd 1).toString else text
  let line := (stripped.splitOn "\n").getLastD ""
  if line.endsWith "\r" then (line.dropEnd 1).toString else line

/-- Find the repository root from the current directory by walking up to
`lakefile.lean`. -/
partial def findRepoRoot (dir : FilePath) : IO FilePath := do
  if ← (dir / "lakefile.lean").pathExists then
    return dir
  match dir.parent with
  | some parent =>
    if parent == dir then
      throw <| IO.userError "could not locate repository root (lakefile.lean)"
    findRepoRoot parent
  | none =>
    throw <| IO.userError "could not locate repository root (lakefile.lean)"

/-- Create a fresh unique directory `<parent>/<prefix><8 hex chars>`. -/
partial def freshDir (parent : FilePath) (pre : String) : IO FilePath := do
  let stamp := (← IO.monoNanosNow) + 7919 * (← IO.Process.getPID).toNat
  let name := String.ofList ((Nat.toDigits 16 (stamp % 16 ^ 8 + 16 ^ 8)).drop 1)
  let dir := parent / s!"{pre}{name}"
  try
    IO.FS.createDir dir
    return dir
  catch _ =>
    if ← dir.pathExists then freshDir parent pre
    else throw <| IO.userError s!"cannot create directory {dir}"

structure EnvConfig where
  outputDir : Option String := none
  testCuda : Bool := false
  cudaDevice : String := "0"
  aiurArtifact : Option String := none
  recursionArtifact : Option String := none
  aggrArtifact : Option String := none
  skipBuild : Bool := false
  skipAiurUnits : Bool := false
  deriving BEq, Repr

def readEnvConfig : IO EnvConfig := do
  let outputDir ← getNonEmptyEnv "IX_TEST_OUTPUT_DIR"
  let testCuda := (← getNonEmptyEnv "IX_TEST_CUDA") == some "1"
  let cudaDevice := (← getNonEmptyEnv "MULTI_STARK_CUDA_DEVICE").getD "0"
  let aiurArtifact ← getNonEmptyEnv "IX_AIUR_ARTIFACT"
  let recursionArtifact ← getNonEmptyEnv "IX_RECURSION_ARTIFACT"
  let aggrArtifact ← getNonEmptyEnv "IX_AGGR_ARTIFACT"
  let skipBuild := (← getNonEmptyEnv "IX_CHECK_FORMAL_SKIP_BUILD") == some "1"
  let skipAiurUnits := (← getNonEmptyEnv "IX_CHECK_FORMAL_SKIP_AIUR_UNITS") == some "1"
  return {
    outputDir, testCuda, cudaDevice, aiurArtifact, recursionArtifact, aggrArtifact,
    skipBuild, skipAiurUnits
  }

/-- A single step in the formal gate plan. -/
inductive Step where
  | exec (cmd : String) (args : Array String) (env : Array (String × Option String))
  | parallel (substeps : Array (String × Array String × Array (String × Option String)))
  | proveAndVerify (proveLog : FilePath) (env : Array (String × Option String))
  | security128Gate (env : Array (String × Option String))
  deriving BEq, Repr

/-- Reference instance `(logTrace=20, columns=200, constraints=200, maxDegree=5,
lookupRows=1048576, lookupWidth=10)` and positive/negative parameter controls
exercised by the 128-bit `fri-security` gate: `(label, expectPass, cliArgs)`. -/
def security128GateCases : Array (String × Bool × Array String) :=
  let inst := "20,200,200,5,1048576,10"
  #[
    ("Fp3 v6 UD (2,160,0,20) 48B XOF >= 128b proven", true,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "2,160,0,20", "--require-min-bits", "128", "--regime", "proven"]),
    ("Fp3 v6 Johnson (2,128,0,20) 48B XOF >= 128b johnson", true,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "2,128,0,20", "--require-min-bits", "128", "--regime", "johnson"]),
    ("Fp3 v6 Johnson (2,118,0,20) 48B XOF >= 128b johnson", true,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "2,118,0,20", "--require-min-bits", "128", "--regime", "johnson"]),
    ("NEG: Fp2 (2,160,0,20) rejected at 128b proven", false,
      #["--instance", inst, "--extension-degree", "2", "--digest-bytes", "48",
        "--parameters", "2,160,0,20", "--require-min-bits", "128", "--regime", "proven"]),
    ("NEG: Fp2 (2,160,0,20) rejected at 128b johnson", false,
      #["--instance", inst, "--extension-degree", "2", "--digest-bytes", "48",
        "--parameters", "2,160,0,20", "--require-min-bits", "128", "--regime", "johnson"]),
    ("NEG: Fp3 v5 default (2,100,0,20) rejected at 128b proven", false,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "2,100,0,20", "--require-min-bits", "128", "--regime", "proven"]),
    ("NEG: Fp3 v5 default (2,100,0,20) rejected at 128b johnson", false,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "2,100,0,20", "--require-min-bits", "128", "--regime", "johnson"]),
    ("NEG: Fp3 deceptive (4,55,0,0) rejected at 128b proven", false,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "4,55,0,0", "--require-min-bits", "128", "--regime", "proven"]),
    ("NEG: Fp3 deceptive (4,55,0,0) rejected at 128b johnson", false,
      #["--instance", inst, "--extension-degree", "3", "--digest-bytes", "48",
        "--parameters", "4,55,0,0", "--require-min-bits", "128", "--regime", "johnson"])
  ]

/-- Construct the full ordered command plan for the formal gate. -/
def buildPlan (cfg : EnvConfig) (formalTmp : FilePath) : Array Step := Id.run do
  -- Proving environment settings must not switch the baseline CLI to CUDA or
  -- poison its CPU-only witness generation. The hardware gate scopes them itself.
  let mut env : Array (String × Option String) := #[
    ("IX_CUDA", some "0"),
    ("AIUR_TRACE_ONLY_LOOKUPS", some "0")
  ]
  let mut steps : Array Step := #[]
  let push (cmd : String) (args : Array String) (e : Array (String × Option String))
      (s : Array Step) : Array Step :=
    s.push (.exec cmd args e)

  unless cfg.skipBuild do
    steps := push "lake" #[
      "build", "ix", "fri-security", "ixvm/ixvm", "multiStark/stark-export",
      "formal-aiur-tests", "formal-aggregate-tests", "formal-checks",
      "aiur/grouping_example", "aiur/depth_example", "aiur/Aiur.Library.U8Facts",
      "aiur/u32_tests", "aiur/library_tests"
    ] env steps
    steps := push "cargo" #[
      "build", "--release", "--locked", "-p", "ixvm", "-p", "stark-verifier", "-p", "ix-prover",
      "--features", "parallel",
      "--bin", "ixvm-proof", "--bin", "stark-verifier", "--bin", "ix-prover",
      "--example", "claim_fixture"
    ] env steps

  -- 128-bit FRI security gate (positive Fp^3 profiles + sub-128-bit negative controls).
  steps := steps.push (.security128Gate env)

  let aiurArt := match cfg.aiurArtifact with
    | some path => path
    | none => (formalTmp / "ixvm.ixa").toString
  let recArt := match cfg.recursionArtifact with
    | some path => path
    | none => (formalTmp / "recursion.ixa").toString
  let aggrArt := match cfg.aggrArtifact with
    | some path => path
    | none => (formalTmp / "aggregate.ixa").toString

  -- Wave 1: independent codegen/Aiur unit/fixture checks and any missing `.ixa` exports.
  -- The IxVM and MultiStark modules are Lean source (`aiur⟦ … ⟧`). Only
  -- IxVM/IxVM/Source/KernelRoleSpec.lean is rendered, from IxC's role specifications.
  let mut wave1 : Array (String × Array String × Array (String × Option String)) := #[
    (".lake/build/bin/ix", #["codegen", "--check"], env)
  ]
  unless cfg.skipAiurUnits do
    wave1 := wave1.push ("lake", #["env", "Aiur/.lake/build/bin/u32_tests"], env)
  wave1 := wave1 ++ #[
    ("lake", #["env", "Aiur/.lake/build/bin/library_tests",
      (formalTmp / "library.ixa").toString], env),
    ("lake", #["env", "Aiur/.lake/build/bin/grouping_example",
      "crates/aiur/tests/fixtures/grouping.ixa", "--check"], env),
    ("lake", #["env", "Aiur/.lake/build/bin/depth_example",
      "crates/aiur/tests/fixtures/depth.ixa", "--check"], env)
  ]
  if cfg.aiurArtifact.isNone then
    wave1 := wave1.push
      ("lake", #["env", "IxVM/.lake/build/bin/ixvm", "export-claim-trace", aiurArt], env)
  if cfg.recursionArtifact.isNone then
    wave1 := wave1.push
      ("lake", #["env", "MultiStark/.lake/build/bin/stark-export", "export-trace", recArt], env)
  if cfg.aggrArtifact.isNone then
    wave1 := wave1.push
      ("lake", #["env", "MultiStark/.lake/build/bin/stark-export", "export-trace", aggrArt, "--aggregate"], env)
  steps := steps.push (.parallel wave1)

  env := setEnv env "IX_AIUR_ARTIFACT" (some aiurArt)
  env := setEnv env "IX_AGGR_ARTIFACT" (some aggrArt)

  -- Wave 2: Aiur library check + independent fixture generation for IxVM, recursion, and aggregate.
  let libraryCheckStep : String × Array String × Array (String × Option String) :=
    if cfg.skipBuild then
      ("target/release/examples/library_check", #[(formalTmp / "library.ixa").toString], env)
    else
      ("cargo", #[
        "run", "--release", "--locked", "-p", "aiur", "--features", "stark,parallel",
        "--example", "library_check", "--", (formalTmp / "library.ixa").toString
      ], env)
  steps := steps.push (.parallel #[
    libraryCheckStep,
    ("lake", #["env", ".lake/build/bin/formal-aiur-tests",
      (formalTmp / "claims.ixt").toString], env),
    ("target/release/stark-verifier", #["fixture", (formalTmp / "inner").toString], env),
    (".lake/build/bin/formal-aggregate-tests", #[(formalTmp / "aggregation.ixt").toString], env)
  ])

  -- Wave 3: independent execution checks and range splitting across all three legs.
  steps := steps.push (.parallel #[
    ("target/release/ixvm-proof", #["test", aiurArt, (formalTmp / "claims.ixt").toString], env),
    (".lake/build/bin/ix", #["check", "--ixe", (formalTmp / "claims.ixt.ixe").toString, "Nat.add_comm"], env),
    ("target/release/stark-verifier",
      #["ranges", (formalTmp / "inner" / "proof.bin").toString, (formalTmp / "ranges").toString, "1"], env),
    ("target/release/stark-verifier",
      #["test", recArt, (formalTmp / "inner" / "input.ixi").toString], env),
    ("target/release/stark-verifier",
      #["cases", aggrArt, (formalTmp / "aggregation.ixt").toString], env)
  ])

  -- Wave 4: range verification + independent recursion and aggregate STARK proofs.
  steps := steps.push (.parallel #[
    (".lake/build/bin/formal-checks", #["ranges", formalTmp.toString], env),
    ("target/release/stark-verifier",
      #["prove", recArt, (formalTmp / "inner" / "input.ixi").toString, (formalTmp / "outer").toString], env),
    ("target/release/stark-verifier",
      #["prove", aggrArt, (formalTmp / "aggregation.ixt.wrap.ixi").toString, (formalTmp / "aggregate").toString], env)
  ])

  -- Wave 5: independent STARK verifications of the recursion and aggregate proofs.
  steps := steps.push (.parallel #[
    ("target/release/stark-verifier",
      #["verify", recArt, (formalTmp / "outer" / "public.ixi").toString,
        (formalTmp / "outer" / "proof.bin").toString], env),
    ("target/release/stark-verifier",
      #["verify", recArt, (formalTmp / "outer" / "public.ixi").toString,
        (formalTmp / "outer" / "proof.bin").toString],
      setEnv env "AIUR_TRACE_ONLY_LOOKUPS" (some "1")),
    ("target/release/stark-verifier",
      #["verify", aggrArt, (formalTmp / "aggregate" / "public.ixi").toString,
        (formalTmp / "aggregate" / "proof.bin").toString], env)
  ])

  steps := steps.push (.proveAndVerify (formalTmp / "prove.log") env)

  let artifactArgs := #[
    "--ixvm-artifact", aiurArt,
    "--recursion-artifact", recArt,
    "--aggregate-artifact", aggrArt
  ]
  steps := push ".lake/build/bin/formal-checks"
    (#["controller", formalTmp.toString] ++ artifactArgs) env steps
  steps := push ".lake/build/bin/formal-checks"
    #["checking", formalTmp.toString, "--ixvm-artifact", aiurArt] env steps

  -- Optional hardware gate: prove with CUDA and independently verify with CPU
  -- binaries. The separate target directory is the same one the CLI selects.
  let mut cudaCheckArgs : Array String := #["--cpu-only"]
  if cfg.testCuda then
    steps := push "cargo" #[
      "build", "--release", "--locked", "--target-dir", "target/formal-cuda",
      "-p", "ixvm", "-p", "stark-verifier", "-p", "ix-prover",
      "--features", "parallel,cuda",
      "--bin", "ixvm-proof", "--bin", "stark-verifier", "--bin", "ix-prover"
    ] env steps
    steps := push ".lake/build/bin/formal-checks"
      (#["controller", formalTmp.toString] ++ artifactArgs ++ #["--devices", cfg.cudaDevice])
      env steps
    cudaCheckArgs := #[]
  steps := push ".lake/build/bin/formal-checks"
    (#["cuda", formalTmp.toString] ++ artifactArgs ++ cudaCheckArgs) env steps
  return steps

def formatEnv (env : Array (String × Option String)) : String :=
  " ".intercalate <| env.toList.filterMap fun (k, v) =>
    v.map fun val => s!"{k}={val}"

def formatExec (cmd : String) (args : Array String) (env : Array (String × Option String)) : String :=
  let e := formatEnv env
  let argv := " ".intercalate (cmd :: args.toList)
  if e.isEmpty then argv else s!"{e} {argv}"

def formatStep : Step → String
  | .exec cmd args env => formatExec cmd args env
  | .parallel substeps =>
    let parts := substeps.toList.map fun (cmd, args, env) =>
      formatExec cmd args env
    s!"parallel [{"; ".intercalate parts}]"
  | .proveAndVerify log env =>
    let e := formatEnv env
    let eLookup := formatEnv (setEnv env "AIUR_TRACE_ONLY_LOOKUPS" (some "1"))
    s!"{e} .lake/build/bin/ix prove Nat.add_comm > {log}; " ++
    s!"{e} .lake/build/bin/ix verify <last-line>; " ++
    s!"{eLookup} .lake/build/bin/ix verify <last-line>"
  | .security128Gate env =>
    let e := formatEnv env
    let base := s!".lake/build/bin/fri-security --require-min-bits 128 ({security128GateCases.size} cases)"
    if e.isEmpty then base else s!"{e} {base}"

/-- Remove entries under Lean's `sysroot` from a colon-separated `LD_LIBRARY_PATH`.
Running under an outer `lake env` prepends Lean's bundled `libLLVM` (built without
RTTI) to `LD_LIBRARY_PATH`, which breaks `bindgen`'s `dlopen` of the system
`libclang` when `lake build` or `cargo` builds `lean-ffi`. -/
def stripSysrootFromPath (sysroot : String) (ldPath : String) : Option String :=
  let prefixSlash := if sysroot.endsWith "/" then sysroot else sysroot ++ "/"
  let kept := (ldPath.splitOn ":").filter fun entry =>
    !entry.isEmpty && entry != sysroot && !entry.startsWith prefixSlash
  if kept.isEmpty then none else some (":".intercalate kept)

/-- Sanitize `LD_LIBRARY_PATH` for `lake` and `cargo` child processes. -/
def sanitizeEnvForCmd (sysroot : String) (cmd : String)
    (env : Array (String × Option String)) : IO (Array (String × Option String)) := do
  if cmd != "lake" && cmd != "cargo" then
    return env
  match ← IO.getEnv "LD_LIBRARY_PATH" with
  | none => return env
  | some ldPath =>
    let cleaned := stripSysrootFromPath sysroot ldPath
    if cleaned == some ldPath then return env
    else return setEnv env "LD_LIBRARY_PATH" cleaned

def runExec (cwd : FilePath) (sysroot : String) (cmd : String) (args : Array String)
    (env : Array (String × Option String)) : IO UInt32 := do
  let env ← sanitizeEnvForCmd sysroot cmd env
  let child ← IO.Process.spawn {
    cmd, args, cwd := some cwd, env
    stdout := .inherit, stderr := .inherit
  }
  let code ← child.wait
  unless code == 0 do
    IO.eprintln s!"[check-formal] command failed (exit {code}): {cmd} {" ".intercalate args.toList}"
  return code

def runProveAndVerify (cwd : FilePath) (sysroot : String) (proveLog : FilePath)
    (env : Array (String × Option String)) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := ".lake/build/bin/ix"
    args := #["prove", "Nat.add_comm"]
    cwd := some cwd
    env
    stdout := .piped
    stderr := .inherit
  }
  let out ← child.stdout.readToEnd
  let code ← child.wait
  IO.FS.writeFile proveLog out
  IO.print out
  (← IO.getStdout).flush
  unless code == 0 do
    IO.eprintln s!"[check-formal] command failed (exit {code}): .lake/build/bin/ix prove Nat.add_comm"
    return code
  let formalProof := lastLine out
  if formalProof.isEmpty then
    IO.eprintln s!"[check-formal] empty proof path in {proveLog}"
    return 1
  let t1 ← IO.asTask (prio := .dedicated)
    (runExec cwd sysroot ".lake/build/bin/ix" #["verify", formalProof] env)
  let t2 ← IO.asTask (prio := .dedicated)
    (runExec cwd sysroot ".lake/build/bin/ix" #["verify", formalProof]
      (setEnv env "AIUR_TRACE_ONLY_LOOKUPS" (some "1")))
  let rc1 ← IO.ofExcept (← IO.wait t1)
  let rc2 ← IO.ofExcept (← IO.wait t2)
  return if rc1 != 0 then rc1 else rc2

/-- Run the self-tested 128-bit `fri-security` gate (positive `Fp^3` profiles must exit 0;
sub-128-bit `Fp^2`, `(2,100,0,20)`, and `(4,55,0,0)` controls must exit non-zero). -/
def runSecurity128Gate (cwd : FilePath) (sysroot : String)
    (env : Array (String × Option String)) : IO UInt32 := do
  let binPath := cwd / ".lake" / "build" / "bin" / "fri-security"
  let useBin ← binPath.pathExists
  let (cmd, baseArgs) :=
    if useBin then (binPath.toString, #[])
    else ("lake", #["exe", "fri-security"])
  let env ← sanitizeEnvForCmd sysroot cmd env
  for (label, expectPass, cliArgs) in security128GateCases do
    let out ← IO.Process.output {
      cmd, args := baseArgs ++ cliArgs, cwd := some cwd, env
    }
    let passed := out.exitCode == 0
    if passed != expectPass then
      let want := if expectPass then "PASS (exit 0)" else "FAIL (non-zero exit)"
      IO.eprintln s!"[check-formal:128b] MISMATCH for '{label}': expected {want}, got exit {out.exitCode}"
      if !out.stdout.isEmpty then IO.eprintln out.stdout
      if !out.stderr.isEmpty then IO.eprintln out.stderr
      return 1
  IO.println s!"[check-formal:128b] OK: {security128GateCases.size} 128-bit fri-security gate controls passed."
  return 0

def runStep (cwd : FilePath) (sysroot : String) : Step → IO UInt32
  | .exec cmd args env => runExec cwd sysroot cmd args env
  | .parallel substeps => do
    let tasks ← substeps.mapM fun (cmd, args, env) =>
      IO.asTask (prio := .dedicated) (runExec cwd sysroot cmd args env)
    let mut firstErr : UInt32 := 0
    for task in tasks do
      let code ← IO.ofExcept (← IO.wait task)
      if code != 0 && firstErr == 0 then firstErr := code
    return firstErr
  | .proveAndVerify proveLog env => runProveAndVerify cwd sysroot proveLog env
  | .security128Gate env => runSecurity128Gate cwd sysroot env

def prepareWorkDir (repoRoot : FilePath) (cfg : EnvConfig) : IO (FilePath × Bool) := do
  if let some outDir := cfg.outputDir then
    let p : FilePath := outDir
    let resolved := if p.isAbsolute then p else repoRoot / p
    IO.FS.createDirAll resolved
    return (← IO.FS.realPath resolved, false)
  else if cfg.testCuda then
    let lakeDir := repoRoot / ".lake"
    IO.FS.createDirAll lakeDir
    let dir ← freshDir lakeDir "formal-cuda-check."
    return (← IO.FS.realPath dir, false)
  else
    let tmpBase : FilePath := (← getNonEmptyEnv "TMPDIR").getD "/tmp"
    let dir ← freshDir tmpBase "formal-check."
    return (← IO.FS.realPath dir, true)

def ensure (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def selfTest : IO Unit := do
  ensure ((parseArgs []).toOption == some .run) "default mode"
  ensure ((parseArgs ["--dry-run"]).toOption == some .dryRun) "dry-run mode"
  ensure ((parseArgs ["--self-test"]).toOption == some .selfTest) "self-test mode"
  ensure ((parseArgs ["--security-128-gate"]).toOption == some .security128Gate) "security-128-gate mode"
  ensure ((parseArgs ["--help"]).toOption == some .help) "help mode"
  ensure ((parseArgs ["--bogus"]).toOption.isNone) "reject unknown flag"
  ensure (lastLine "line1\n/tmp/proof.bin\n" == "/tmp/proof.bin") "lastLine trailing newline"
  ensure (lastLine "line1\n/tmp/proof.bin" == "/tmp/proof.bin") "lastLine no newline"
  ensure (lastLine "line1\r\n/tmp/proof.bin\r\n" == "/tmp/proof.bin") "lastLine CRLF"
  let e0 := setEnv #[("IX_CUDA", some "0"), ("AIUR_TRACE_ONLY_LOOKUPS", some "0")]
    "AIUR_TRACE_ONLY_LOOKUPS" (some "1")
  ensure (e0.size == 2 && e0[1]! == ("AIUR_TRACE_ONLY_LOOKUPS", some "1")) "setEnv replaces in place"
  let cpuPlan := buildPlan {} "/tmp/formal"
  let cudaPlan := buildPlan { testCuda := true, cudaDevice := "2" } "/tmp/formal"
  let reusePlan := buildPlan {
    aiurArtifact := some "/a/ixvm.ixa"
    recursionArtifact := some "/a/rec.ixa"
    aggrArtifact := some "/a/aggr.ixa"
  } "/tmp/formal"
  let partialReusePlan := buildPlan {
    aiurArtifact := some "/a/ixvm.ixa"
    recursionArtifact := some "/a/rec.ixa"
  } "/tmp/formal"
  let skipPlan := buildPlan { skipBuild := true, skipAiurUnits := true } "/tmp/formal"
  let countSubsteps (plan : Array Step) : Nat :=
    plan.foldl (init := 0) fun acc s =>
      acc + match s with
      | .parallel substeps => substeps.size
      | _ => 1
  let hasSubcmd (plan : Array Step) (pred : String → Array String → Bool) : Bool :=
    plan.any fun
      | .exec cmd args _ => pred cmd args
      | .parallel substeps => substeps.any fun (cmd, args, _) => pred cmd args
      | .proveAndVerify .. => false
      | .security128Gate .. => false
  let hasSecurity128Gate (plan : Array Step) : Bool :=
    plan.any fun
      | .security128Gate .. => true
      | _ => false
  ensure (cpuPlan.size == 12) s!"unexpected cpu plan length {cpuPlan.size}"
  ensure (countSubsteps cpuPlan == 30) s!"unexpected cpu substep count {countSubsteps cpuPlan}"
  ensure (hasSecurity128Gate cpuPlan) "cpu plan runs 128-bit fri-security gate"
  ensure (hasSecurity128Gate skipPlan) "skipBuild plan still runs 128-bit fri-security gate"
  ensure (hasSubcmd cpuPlan fun cmd args =>
      cmd == ".lake/build/bin/formal-checks" && args.contains "checking")
    "cpu plan runs formal-checks checking gate"
  ensure (cudaPlan.size == cpuPlan.size + 2) "cuda adds build + device controller"
  ensure (reusePlan.size == cpuPlan.size && countSubsteps reusePlan == countSubsteps cpuPlan - 3)
    "full artifact reuse skips 3 exports"
  ensure (partialReusePlan.size == cpuPlan.size &&
      countSubsteps partialReusePlan == countSubsteps cpuPlan - 2)
    "partial artifact reuse skips 2 exports"
  ensure (skipPlan.size == cpuPlan.size - 2 &&
      countSubsteps skipPlan == countSubsteps cpuPlan - 3)
    "skipBuild + skipAiurUnits drops 2 build steps and u32_tests"
  ensure (hasSubcmd cpuPlan fun cmd args => cmd == "cargo" && args.contains "library_check")
    "default cpu plan invokes library_check via cargo run"
  ensure (hasSubcmd skipPlan fun cmd _ => cmd == "target/release/examples/library_check")
    "skipBuild invokes target/release/examples/library_check directly"
  ensure (!(hasSubcmd skipPlan fun cmd _ => cmd == "cargo"))
    "skipBuild never invokes cargo"
  let hasCpuOnly := cpuPlan.any fun
    | .exec ".lake/build/bin/formal-checks" args _ => args.contains "--cpu-only"
    | _ => false
  let cudaHasDevice := cudaPlan.any fun
    | .exec ".lake/build/bin/formal-checks" args _ => args.contains "--devices" && args.contains "2"
    | _ => false
  ensure hasCpuOnly "cpu plan runs cuda gate with --cpu-only"
  ensure cudaHasDevice "cuda plan runs controller with requested device"
  ensure (stripSysrootFromPath "/opt/lean" "/opt/lean/lib/lean:/opt/lean/lib:/usr/local/lib" ==
    some "/usr/local/lib") "stripSysrootFromPath removes lean sysroot entries"
  ensure (stripSysrootFromPath "/opt/lean" "/opt/lean/lib/lean:/opt/lean/lib" == none)
    "stripSysrootFromPath unsets empty LD_LIBRARY_PATH"
  let repoRoot ← findRepoRoot (← IO.currentDir)
  let sysroot := (← Lean.findSysroot).toString
  let gateRc ← runSecurity128Gate repoRoot sysroot #[]
  ensure (gateRc == 0) s!"128-bit fri-security gate failed with exit code {gateRc}"
  IO.println "CheckFormal self-tests passed."

end CheckFormal

def main (args : List String) : IO UInt32 := do
  match CheckFormal.parseArgs args with
  | .error e =>
    IO.eprintln s!"error: {e}\n{CheckFormal.usage}"
    return 2
  | .ok .help =>
    IO.println CheckFormal.usage
    return 0
  | .ok .selfTest =>
    CheckFormal.selfTest
    return 0
  | .ok .security128Gate =>
    let repoRoot ← CheckFormal.findRepoRoot (← IO.currentDir)
    let sysroot := (← Lean.findSysroot).toString
    CheckFormal.runSecurity128Gate repoRoot sysroot #[]
  | .ok .dryRun =>
    let repoRoot ← CheckFormal.findRepoRoot (← IO.currentDir)
    let cfg ← CheckFormal.readEnvConfig
    let formalTmp : System.FilePath :=
      match cfg.outputDir with
      | some d =>
        let p : System.FilePath := d
        if p.isAbsolute then p else repoRoot / p
      | none =>
        if cfg.testCuda then repoRoot / ".lake" / "formal-cuda-check.DRYRUN"
        else "/tmp/formal-check.DRYRUN"
    let steps := CheckFormal.buildPlan cfg formalTmp
    IO.println s!"[check-formal dry-run] cwd={repoRoot} tmp={formalTmp} cuda={cfg.testCuda} steps={steps.size}"
    for (step, idx) in steps.zipIdx do
      IO.println s!"{idx + 1}. {CheckFormal.formatStep step}"
    return 0
  | .ok .run =>
    let repoRoot ← CheckFormal.findRepoRoot (← IO.currentDir)
    let sysroot := (← Lean.findSysroot).toString
    let cfg ← CheckFormal.readEnvConfig
    let (formalTmp, cleanup) ← CheckFormal.prepareWorkDir repoRoot cfg
    let steps := CheckFormal.buildPlan cfg formalTmp
    let removeTmp : IO Unit := do
      if cleanup then
        try IO.FS.removeDirAll formalTmp catch _ => pure ()
    try
      for step in steps do
        let code ← CheckFormal.runStep repoRoot sysroot step
        unless code == 0 do
          removeTmp
          return code
      removeTmp
      return 0
    catch e =>
      removeTmp
      throw e
