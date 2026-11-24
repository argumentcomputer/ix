import Lean

/-! # Aiur compression compiler fixture gate (`Scripts/CheckAiurCompressionFixtures.lean`)

Builds and checks (or with `--update`, regenerates) all committed BN254 / KZG /
emulated-Goldilocks / pairing / CompressFinal Aiur compiler fixtures under
`crates/aiur/tests/fixtures/`. Replaces `tools/check-aiur-compression-fixtures.sh`.

Independent fixture binaries run in parallel with bounded concurrency via
`IO.asTask`, failing closed if any build, uniqueness check, byte comparison, or
fixture binary exits non-zero.

Usage:
  `lake env lean --run Scripts/CheckAiurCompressionFixtures.lean [--check | --update | --self-test | --help]`

Environment variables:
- `IX_FIXTURE_JOBS`: maximum concurrent fixture processes (default `8`).
-/

namespace CheckAiurCompressionFixtures

open System

def usage : String :=
  "usage: lake env lean --run Scripts/CheckAiurCompressionFixtures.lean [--check | --update | --self-test | --help]\n\n" ++
  "Build and verify (or with `--update`, regenerate) committed Aiur compression fixtures."

inductive Mode where
  | check
  | update
  | selfTest
  | help
  deriving BEq, Repr

def parseArgs : List String → Except String Mode
  | [] | ["--check"] => .ok .check
  | ["--update"] => .ok .update
  | ["--self-test"] => .ok .selfTest
  | ["--help"] | ["-h"] => .ok .help
  | other => .error s!"unexpected arguments: {" ".intercalate other}"

/-- All Lake targets built in one batched `lake build --wfail` invocation. -/
def buildTargets : Array String := #[
  "aiur/bn254_execution_fixture", "aiur/bn254_trace_fixture",
  "aiur/bn254_grouped_fixture", "aiur/bn254_gap_fixture", "aiur/bn254_inactive_fixture",
  "aiur/bn254_fq_fixture", "aiur/bn254_fq_relation_fixture", "aiur/bn254_g1_fixture",
  "aiur/bn254_g1_encoding_fixture", "aiur/bn254_fq_products_fixture", "aiur/bn254_pairing_fixture",
  "aiur/bn254_preparation_check", "aiur/emulated_goldilocks_fixture", "aiur/wide_artifact_fixture",
  "aiur/table_uniqueness_checks",
  "multiStark/kzg_xof_fixture", "multiStark/kzg_source_fixture", "multiStark/kzg_packed_export",
  "multiStark/compress_final_export", "multiStark/MultiStark",
  "multiStark/compress_narrow_fixed_export", "multiStark/compress_final_narrow_export"
]

def fixturesRelDir : FilePath := "crates" / "aiur" / "tests" / "fixtures"

/-- Direct `Aiur` fixture binaries: `(executableName, artifactStem)`. -/
def aiurFixtures : Array (String × String) := #[
  ("bn254_execution_fixture", "bn254-execution"),
  ("bn254_trace_fixture", "bn254-trace"),
  ("bn254_grouped_fixture", "bn254-grouped"),
  ("bn254_gap_fixture", "bn254-gap"),
  ("bn254_inactive_fixture", "bn254-inactive"),
  ("bn254_fq_fixture", "bn254-fq"),
  ("bn254_fq_relation_fixture", "bn254-fq-relation"),
  ("bn254_g1_fixture", "bn254-g1"),
  ("bn254_g1_encoding_fixture", "bn254-g1-encoding"),
  ("bn254_fq_products_fixture", "bn254-fq-products"),
  ("emulated_goldilocks_fixture", "goldilocks-emulated"),
  ("wide_artifact_fixture", "bn254-wide")
]

/-- Direct `MultiStark` fixture binaries: `(executableName, artifactStem)`. -/
def multiStarkFixtures : Array (String × String) := #[
  ("kzg_xof_fixture", "kzg-xof"),
  ("kzg_source_fixture", "kzg-source"),
  ("kzg_packed_export", "kzg-packed-shplonk")
]

/-- Pairing fixture profiles: `(scratchSubdir, fixturePrefix)`. -/
def pairingProfiles : Array (String × String) := #[
  ("generator", "bn254-pairing"),
  ("ignition", "bn254-pairing-ignition")
]

structure JobSpec where
  label : String
  cmd : String
  args : Array String
  deriving BEq, Repr, Inhabited

structure JobResult where
  label : String
  exitCode : UInt32
  stdout : String
  stderr : String
  deriving BEq, Repr

/-- Find the repository root from `dir` by walking up to `lakefile.lean`. -/
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

/-- Create a fresh unique scratch directory `<parent>/<prefix><8 hex chars>`. -/
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

/-- When invoked via `lake env lean --run`, `lake env` injects `LEAN_SYSROOT`
equal to the toolchain sysroot. Clear it for child `lake` calls when `lake env`
injected it so nested builds match the outer shell environment. -/
def childEnvFor (cmd : String) : IO (Array (String × Option String)) := do
  if cmd == "lake" && (← IO.getEnv "LEAN_RECURSION_COUNT").isSome then
    let sysroot := (← Lean.findSysroot).toString
    if (← IO.getEnv "LEAN_SYSROOT") == some sysroot then
      return #[("LEAN_SYSROOT", none)]
  return #[]

/-- Run a single foreground command inheriting stdout/stderr, failing closed on non-zero exit. -/
def runForeground (cwd : FilePath) (cmd : String) (args : Array String) : IO UInt32 := do
  let env ← childEnvFor cmd
  let child ← IO.Process.spawn {
    cmd, args, cwd := some cwd, env
    stdout := .inherit, stderr := .inherit
  }
  let code ← child.wait
  unless code == 0 do
    IO.eprintln s!"[check-aiur-compression-fixtures] command failed (exit {code}): {cmd} {" ".intercalate args.toList}"
  return code

/-- Run one job capturing its output so concurrent tasks do not interleave stdout/stderr. -/
def runCaptured (cwd : FilePath) (job : JobSpec) : IO JobResult := do
  let env ← childEnvFor job.cmd
  let out ← IO.Process.output {
    cmd := job.cmd
    args := job.args
    cwd := some cwd
    env
  }
  return {
    label := job.label
    exitCode := out.exitCode
    stdout := out.stdout
    stderr := out.stderr
  }

/-- Partition `items` into contiguous batches of size at most `maxBatch` (at least 1). -/
def chunkArray {α : Type} (items : Array α) (maxBatch : Nat) : Array (Array α) := Id.run do
  let width := max maxBatch 1
  let mut batches : Array (Array α) := #[]
  let mut idx := 0
  while idx < items.size do
    let stop := min (idx + width) items.size
    batches := batches.push (items.extract idx stop)
    idx := stop
  return batches

/-- Execute `jobs` in parallel with bounded concurrency (`maxJobs`), printing each
job's output deterministically in submission order and failing closed if any job
returns a non-zero exit code. -/
def runParallelBounded (cwd : FilePath) (maxJobs : Nat)
    (jobs : Array JobSpec) : IO UInt32 := do
  let mut firstErr : UInt32 := 0
  let mut failedLabels : Array String := #[]
  for batch in chunkArray jobs maxJobs do
    let tasks ← batch.mapM fun job =>
      IO.asTask (prio := .dedicated) (runCaptured cwd job)
    for task in tasks do
      let res ← IO.ofExcept (← IO.wait task)
      if res.exitCode == 0 then
        IO.println s!"  ok   {res.label}"
        if !res.stdout.isEmpty then IO.print res.stdout
        if !res.stderr.isEmpty then IO.eprint res.stderr
      else
        IO.eprintln s!"  FAIL {res.label} (exit {res.exitCode})"
        if !res.stdout.isEmpty then IO.eprint res.stdout
        if !res.stderr.isEmpty then IO.eprint res.stderr
        failedLabels := failedLabels.push res.label
        if firstErr == 0 then firstErr := res.exitCode
  unless failedLabels.isEmpty do
    IO.eprintln s!"[check-aiur-compression-fixtures] {failedLabels.size} job(s) failed: {", ".intercalate failedLabels.toList}"
  return firstErr

/-- Compare two files byte-for-byte, or copy `generated` to `committed` in `--update` mode. -/
def syncOrCompareFile (update : Bool) (generated committed : FilePath) : IO UInt32 := do
  let genBytes ← IO.FS.readBinFile generated
  if update then
    IO.FS.writeBinFile committed genBytes
    IO.println s!"  updated {committed}"
    return 0
  unless ← committed.pathExists do
    IO.eprintln s!"[check-aiur-compression-fixtures] missing committed fixture: {committed}"
    return 1
  let curBytes ← IO.FS.readBinFile committed
  if genBytes == curBytes then
    return 0
  IO.eprintln s!"[check-aiur-compression-fixtures] fixture differs from generated output: {committed} ({curBytes.size} bytes vs {genBytes.size} bytes)"
  return 1

/-- Build the 16 independent Wave-1 fixture jobs (`table_uniqueness_checks` +
12 `Aiur` fixtures + 3 `MultiStark` fixtures). -/
def wave1Jobs (update : Bool) : Array JobSpec := Id.run do
  let checkArgs : Array String := if update then #[] else #["--check"]
  let mut jobs : Array JobSpec := #[
    { label := "aiur/table_uniqueness_checks"
      cmd := "lake"
      args := #["env", "Aiur/.lake/build/bin/table_uniqueness_checks"] }
  ]
  for (exe, stem) in aiurFixtures do
    jobs := jobs.push {
      label := s!"aiur/{exe} ({stem}.ixa)"
      cmd := "lake"
      args := #["env", s!"Aiur/.lake/build/bin/{exe}",
        (fixturesRelDir / s!"{stem}.ixa").toString] ++ checkArgs
    }
  for (exe, stem) in multiStarkFixtures do
    jobs := jobs.push {
      label := s!"multiStark/{exe} ({stem}.ixa)"
      cmd := "lake"
      args := #["env", s!"MultiStark/.lake/build/bin/{exe}",
        (fixturesRelDir / s!"{stem}.ixa").toString] ++ checkArgs
    }
  return jobs

/-- Build the Wave-2 jobs for `compress_final_export` and `bn254_pairing_fixture`
(run after `bn254_preparation_check` validates the pairing lines). -/
def wave2ExportJobs (update : Bool) : Array JobSpec :=
  let checkArgs : Array String := if update then #[] else #["--check"]
  let finalJson := (fixturesRelDir / "compress-final.json").toString
  #[
    { label := "multiStark/compress_final_export (compress-final.ixa)"
      cmd := "lake"
      args := #["env", "MultiStark/.lake/build/bin/compress_final_export",
        finalJson, (fixturesRelDir / "compress-final.ixa").toString] ++ checkArgs },
    { label := "multiStark/compress_final_export (compress-final-accumulator.ixa)"
      cmd := "lake"
      args := #["env", "MultiStark/.lake/build/bin/compress_final_export",
        finalJson, (fixturesRelDir / "compress-final-accumulator.ixa").toString,
        "--accumulator"] ++ checkArgs },
    { label := "aiur/bn254_pairing_fixture (bn254-pairing.ixa)"
      cmd := "lake"
      args := #["env", "Aiur/.lake/build/bin/bn254_pairing_fixture",
        (fixturesRelDir / "bn254-pairing-lines.txt").toString,
        (fixturesRelDir / "bn254-pairing.ixa").toString] ++ checkArgs },
    { label := "aiur/bn254_pairing_fixture (bn254-pairing-ignition.ixa)"
      cmd := "lake"
      args := #["env", "Aiur/.lake/build/bin/bn254_pairing_fixture",
        (fixturesRelDir / "bn254-pairing-ignition-lines.txt").toString,
        (fixturesRelDir / "bn254-pairing-ignition.ixa").toString] ++ checkArgs }
  ]

def readMaxJobs : IO Nat := do
  match ← IO.getEnv "IX_FIXTURE_JOBS" with
  | some raw =>
    match raw.trimAscii.toString.toNat? with
    | some n => if n > 0 then return n else return 8
    | none => return 8
  | none => return 8

def ensure (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def selfTest : IO Unit := do
  ensure ((parseArgs []).toOption == some .check) "default mode is check"
  ensure ((parseArgs ["--check"]).toOption == some .check) "explicit --check mode"
  ensure ((parseArgs ["--update"]).toOption == some .update) "--update mode"
  ensure ((parseArgs ["--self-test"]).toOption == some .selfTest) "--self-test mode"
  ensure ((parseArgs ["--help"]).toOption == some .help) "--help mode"
  ensure ((parseArgs ["-h"]).toOption == some .help) "-h mode"
  ensure ((parseArgs ["--bogus"]).toOption.isNone) "reject unknown flag"
  ensure ((parseArgs ["--check", "--update"]).toOption.isNone) "reject conflicting flags"
  ensure (buildTargets.size == 22) s!"expected 22 build targets, got {buildTargets.size}"
  let w1Check := wave1Jobs false
  let w1Update := wave1Jobs true
  ensure (w1Check.size == 16) s!"expected 16 wave-1 jobs, got {w1Check.size}"
  ensure (w1Update.size == 16) s!"expected 16 wave-1 update jobs, got {w1Update.size}"
  ensure (w1Check[1]!.args.contains "--check") "check mode passes --check"
  ensure (!w1Update[1]!.args.contains "--check") "update mode omits --check"
  let w2Check := wave2ExportJobs false
  ensure (w2Check.size == 4) s!"expected 4 wave-2 export jobs, got {w2Check.size}"
  let chunks := chunkArray #[1, 2, 3, 4, 5] 2
  ensure (chunks == #[#[1, 2], #[3, 4], #[5]]) s!"unexpected chunking: {repr chunks}"
  IO.println "[check-aiur-compression-fixtures] self-tests passed."

def run (update : Bool) : IO UInt32 := do
  let repoRoot ← findRepoRoot (← IO.currentDir)
  let maxJobs ← readMaxJobs
  let fixturesDir := repoRoot / fixturesRelDir
  let modeLabel := if update then "update" else "check"

  IO.println s!"[check-aiur-compression-fixtures] building {buildTargets.size} Lake targets (--wfail)"
  let rcBuild ← runForeground repoRoot "lake" (#["build", "--wfail"] ++ buildTargets)
  unless rcBuild == 0 do return rcBuild

  IO.println s!"[check-aiur-compression-fixtures] running 16 independent fixture checks in parallel (jobs={maxJobs}, mode={modeLabel})"
  let rcWave1 ← runParallelBounded repoRoot maxJobs (wave1Jobs update)
  unless rcWave1 == 0 do return rcWave1

  let tmpBase : FilePath :=
    match ← IO.getEnv "TMPDIR" with
    | some d => if d.isEmpty then "/tmp" else d
    | none => "/tmp"
  let scratch ← freshDir tmpBase "aiur-compression-fixtures."
  let cleanup : IO Unit := do
    try IO.FS.removeDirAll scratch catch _ => pure ()

  try
    -- Prebuild the two Rust fixture generator examples once so subsequent runs are lock-free.
    IO.println "[check-aiur-compression-fixtures] generating Rust pairing lines and final configuration"
    let rcCargoBuild ← runForeground repoRoot "cargo" #[
      "build", "--release", "--locked", "-p", "ix-proof-compression",
      "--example", "aiur_pairing_lines", "--example", "aiur_final_fixture"
    ]
    unless rcCargoBuild == 0 do
      cleanup
      return rcCargoBuild

    for (exampleName, extraArgs) in #[
      ("aiur_pairing_lines", #[(scratch / "generator").toString]),
      ("aiur_pairing_lines", #[(scratch / "ignition").toString, "--ignition"]),
      ("aiur_final_fixture", #[(scratch / "final").toString])
    ] do
      let rc ← runForeground repoRoot "cargo" (
        #["run", "--release", "--locked", "-p", "ix-proof-compression",
          "--example", exampleName, "--"] ++ extraArgs)
      unless rc == 0 do
        cleanup
        return rc

    let rcFinalCfg ← syncOrCompareFile update
      (scratch / "final" / "configuration.json")
      (fixturesDir / "compress-final.json")
    unless rcFinalCfg == 0 do
      cleanup
      return rcFinalCfg

    for (kind, prefixName) in pairingProfiles do
      let rcLines ← syncOrCompareFile update
        (scratch / kind / "lines.txt")
        (fixturesDir / s!"{prefixName}-lines.txt")
      unless rcLines == 0 do
        cleanup
        return rcLines
      let rcProv ← syncOrCompareFile update
        (scratch / kind / "provenance.json")
        (fixturesDir / s!"{prefixName}-lines.json")
      unless rcProv == 0 do
        cleanup
        return rcProv

    IO.println "[check-aiur-compression-fixtures] checking BN254 pairing preparations"
    let prepJobs : Array JobSpec := pairingProfiles.map fun (_, prefixName) => {
      label := s!"aiur/bn254_preparation_check ({prefixName})"
      cmd := "lake"
      args := #["env", "Aiur/.lake/build/bin/bn254_preparation_check",
        (fixturesRelDir / s!"{prefixName}-lines.json").toString,
        (fixturesRelDir / s!"{prefixName}-lines.txt").toString]
    }
    let rcPrep ← runParallelBounded repoRoot maxJobs prepJobs
    unless rcPrep == 0 do
      cleanup
      return rcPrep

    IO.println s!"[check-aiur-compression-fixtures] running 4 final/pairing fixture exports in parallel (jobs={maxJobs}, mode={modeLabel})"
    let rcWave2 ← runParallelBounded repoRoot maxJobs (wave2ExportJobs update)
    cleanup
    if rcWave2 == 0 then
      IO.println s!"[check-aiur-compression-fixtures] OK: all Aiur compression fixtures verified ({modeLabel})."
    return rcWave2
  catch e =>
    cleanup
    throw e

end CheckAiurCompressionFixtures

def main (args : List String) : IO UInt32 := do
  match CheckAiurCompressionFixtures.parseArgs args with
  | .error e =>
    IO.eprintln s!"error: {e}\n{CheckAiurCompressionFixtures.usage}"
    return 2
  | .ok .help =>
    IO.println CheckAiurCompressionFixtures.usage
    return 0
  | .ok .selfTest =>
    CheckAiurCompressionFixtures.selfTest
    return 0
  | .ok .check =>
    CheckAiurCompressionFixtures.run false
  | .ok .update =>
    CheckAiurCompressionFixtures.run true
