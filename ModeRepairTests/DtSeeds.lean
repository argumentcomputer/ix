import Lean

/-!
# Parallel 8-seed differential test runner for `ModeRepairTests`

Pure Lean 4 replacement for `ModeRepairTests/dt-seeds.sh`.

Runs seeds `1..8` of `ModeRepairTests`'s `difftest` executable in parallel,
each capped at 8 GiB memory and 1 hour (`systemd-run --user --scope` with
`MemoryMax=8G` and `MemorySwapMax=0` + `timeout 3600`, falling back to
`prlimit --as=8589934592` + `timeout 3600` when a user systemd scope is
unavailable). Writes `OUT/seed-1.log..OUT/seed-8.log`, prints each seed's
tally block to stdout, and exits non-zero if any seed fails.

Run from anywhere after `lake -d ModeRepairTests build difftest`.

## Usage

```
lean --run ModeRepairTests/DtSeeds.lean [--dry-run] [--bin PATH] OUT [ARGS...]
lean --run ModeRepairTests/DtSeeds.lean --selftest
```

Example (the 800,000-program run):
```
lean --run ModeRepairTests/DtSeeds.lean OUT --n 100000 --shrink 300 --classify --stuck 4
```
-/

namespace DtSeeds

open System

def seeds : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8]
def memCapBytes : String := "8589934592" -- 8 GiB
def timeCapSecs : String := "3600"       -- 1 hour

inductive Limiter where
  | systemdRun
  | prlimit
  | timeoutOnly
  | none
  deriving BEq, Repr

def Limiter.describe : Limiter → String
  | .systemdRun  => "systemd-run --user --scope (MemoryMax=8G, MemorySwapMax=0) + timeout 3600"
  | .prlimit     => "prlimit --as=8589934592 + timeout 3600"
  | .timeoutOnly => "timeout 3600 (no memory cap tool available)"
  | .none        => "uncapped (neither systemd-run, prlimit, nor timeout available)"

/-- Build `(cmd, args)` for launching one seed of `difftest`. -/
def buildSeedCommand (lim : Limiter) (difftestBin outDir : String) (seed : Nat)
    (extraArgs : Array String) : String × Array String :=
  let baseArgs := #["--seed", toString seed, "--out", outDir] ++ extraArgs
  match lim with
  | .systemdRun =>
    ("systemd-run",
      #["--user", "--scope", "-q", "-p", "MemoryMax=8G", "-p", "MemorySwapMax=0",
        "timeout", timeCapSecs, difftestBin] ++ baseArgs)
  | .prlimit =>
    ("prlimit",
      #[s!"--as={memCapBytes}", "--", "timeout", timeCapSecs, difftestBin] ++ baseArgs)
  | .timeoutOnly =>
    ("timeout", #[timeCapSecs, difftestBin] ++ baseArgs)
  | .none =>
    (difftestBin, baseArgs)

/-- Extract the tally suffix starting at the first line matching `^seed <s> done`,
equivalent to `sed -n "/^seed $s done/,\$p"`. -/
def extractSeedTally (seed : Nat) (logText : String) : String := Id.run do
  let marker := s!"seed {seed} done"
  let lines := logText.splitOn "\n"
  let mut found := false
  let mut acc : Array String := #[]
  for line in lines do
    if !found && line.startsWith marker then
      found := true
    if found then
      acc := acc.push line
  if !found then
    return ""
  -- Preserve trailing newline semantics without adding extra blank lines.
  let joined := "\n".intercalate acc.toList
  if joined.endsWith "\n" then joined else joined ++ "\n"

/-! ## CLI parsing -/

structure Config where
  outDir : Option FilePath := none
  binOverride : Option FilePath := none
  dryRun : Bool := false
  selftest : Bool := false
  showHelp : Bool := false
  extraArgs : Array String := #[]
  deriving BEq, Repr

def usageText : String :=
  "Usage:\n\
   \x20 lean --run ModeRepairTests/DtSeeds.lean [--dry-run] [--bin PATH] OUT [ARGS...]\n\
   \x20 lean --run ModeRepairTests/DtSeeds.lean --selftest"

/-- Parse launcher options before `OUT`; every argument after `OUT` is forwarded
verbatim to `difftest`. -/
def parseArgs (args : List String) : Except String Config := do
  let rec go (cfg : Config) : List String → Except String Config
    | [] => .ok cfg
    | "--help" :: _ | "-h" :: _ => .ok { cfg with showHelp := true }
    | "--selftest" :: _ => .ok { cfg with selftest := true }
    | "--dry-run" :: rest => go { cfg with dryRun := true } rest
    | "--bin" :: p :: rest => go { cfg with binOverride := some (FilePath.mk p) } rest
    | "--bin" :: [] => .error "--bin requires a path argument"
    | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown option before OUT: {arg}"
      else
        .ok { cfg with outDir := some (FilePath.mk arg), extraArgs := rest.toArray }
  let cfg ← go {} args
  if !cfg.showHelp && !cfg.selftest && cfg.outDir.isNone then
    .error "missing required OUT directory argument"
  return cfg

/-! ## Environment probing & execution -/

def probeCmd (cmd : String) (args : Array String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args }
    return out.exitCode == 0
  catch _ =>
    return false

def detectLimiter : IO Limiter := do
  if ← probeCmd "systemd-run" #["--user", "--scope", "-q", "-p", "MemoryMax=8G", "-p", "MemorySwapMax=0", "true"] then
    return .systemdRun
  if ← probeCmd "prlimit" #[s!"--as={memCapBytes}", "--", "true"] then
    return .prlimit
  if ← probeCmd "timeout" #[timeCapSecs, "true"] then
    return .timeoutOnly
  return .none

def resolveDifftestBin (override? : Option FilePath) : IO FilePath := do
  if let some p := override? then
    return p
  if let some envBin := ← IO.getEnv "DIFFTEST_BIN" then
    if !envBin.isEmpty then return FilePath.mk envBin
  let candidates : Array FilePath := #[
    FilePath.mk ".lake" / "build" / "bin" / "difftest",
    FilePath.mk "ModeRepairTests" / ".lake" / "build" / "bin" / "difftest"
  ]
  for c in candidates do
    if ← c.pathExists then
      return (← IO.FS.realPath c)
  -- Try locating repository root via git so the script works from any directory.
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "--show-toplevel"] }
    if out.exitCode == 0 then
      let top := FilePath.mk out.stdout.trimAscii.toString
      let c := top / "ModeRepairTests" / ".lake" / "build" / "bin" / "difftest"
      if ← c.pathExists then
        return (← IO.FS.realPath c)
  catch _ => pure ()
  throw <| IO.userError
    "difftest binary not found; build it first with `lake -d ModeRepairTests build difftest` (or pass --bin PATH)"

def printUtcTimestamp : IO Unit := do
  try
    let out ← IO.Process.output { cmd := "date", args := #["-u"] }
    if out.exitCode == 0 then
      IO.print out.stdout
      return
  catch _ => pure ()
  IO.println s!"(mono_ms={← IO.monoMsNow})"

def runSeeds (cfg : Config) : IO UInt32 := do
  let some outDir := cfg.outDir
    | throw <| IO.userError "missing OUT directory"
  let lim ← detectLimiter
  if cfg.dryRun then
    let binStr ← match cfg.binOverride with
      | some p => pure p.toString
      | none =>
        try
          pure (← resolveDifftestBin none).toString
        catch _ =>
          pure "ModeRepairTests/.lake/build/bin/difftest"
    IO.println s!"[dt-seeds] dry-run ({lim.describe}):"
    for s in seeds do
      let (cmd, args) := buildSeedCommand lim binStr outDir.toString s cfg.extraArgs
      IO.println s!"  seed {s}: {cmd} {" ".intercalate args.toList} > {outDir}/seed-{s}.log 2>&1"
    return 0

  let binPath ← resolveDifftestBin cfg.binOverride
  if lim != .systemdRun then
    IO.eprintln s!"[dt-seeds] note: using fallback limiter: {lim.describe}"
  IO.FS.createDirAll outDir
  printUtcTimestamp
  (← IO.getStdout).flush

  let mut tasks : Array (Task (Except IO.Error (Nat × UInt32))) := Array.emptyWithCapacity seeds.size
  for s in seeds do
    let (cmd, args) := buildSeedCommand lim binPath.toString outDir.toString s cfg.extraArgs
    let logPath := outDir / s!"seed-{s}.log"
    let t ← IO.asTask (prio := .dedicated) do
      let out ← IO.Process.output { cmd, args }
      IO.FS.writeFile logPath (out.stdout ++ out.stderr)
      return (s, out.exitCode)
    tasks := tasks.push t

  let mut failed : Array (Nat × UInt32) := #[]
  for t in tasks do
    let (s, rc) ← IO.ofExcept (← IO.wait t)
    if rc != 0 then
      failed := failed.push (s, rc)

  printUtcTimestamp
  for s in seeds do
    IO.println s!"=== seed {s}"
    let logPath := outDir / s!"seed-{s}.log"
    if ← logPath.pathExists then
      let text ← IO.FS.readFile logPath
      IO.print (extractSeedTally s text)

  if failed.isEmpty then
    return 0
  else
    let desc := ", ".intercalate (failed.toList.map fun (s, rc) => s!"seed {s} (exit {rc})")
    IO.eprintln s!"dt-seeds: {failed.size} seed(s) failed: {desc}"
    return 1

/-! ## Built-in unit self-tests -/

def assertTrue (label : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"selftest FAILED [{label}]"

def runSelfTests : IO Unit := do
  -- 1. Argument parsing preserves all difftest flags after OUT verbatim
  assertTrue "parseArgs forwards extra args"
    ((parseArgs ["/tmp/out", "--n", "100000", "--shrink", "300", "--classify", "--stuck", "4"]).toOption ==
      some { outDir := some (FilePath.mk "/tmp/out"),
             extraArgs := #["--n", "100000", "--shrink", "300", "--classify", "--stuck", "4"] })
  assertTrue "parseArgs dry-run + bin"
    ((parseArgs ["--dry-run", "--bin", "/x/difftest", "/tmp/o", "--n", "50"]).toOption ==
      some { outDir := some (FilePath.mk "/tmp/o"),
             binOverride := some (FilePath.mk "/x/difftest"),
             dryRun := true,
             extraArgs := #["--n", "50"] })
  assertTrue "parseArgs requires OUT" (!(parseArgs ["--dry-run"]).isOk)
  assertTrue "parseArgs rejects unknown pre-OUT flag" (!(parseArgs ["--bogus", "/tmp/o"]).isOk)

  -- 2. Command builders for systemd-run and prlimit
  let (c1, a1) := buildSeedCommand .systemdRun "/p/difftest" "/out" 3 #["--n", "50"]
  assertTrue "systemd-run cmd"
    (c1 == "systemd-run" &&
     a1 == #["--user", "--scope", "-q", "-p", "MemoryMax=8G", "-p", "MemorySwapMax=0",
             "timeout", "3600", "/p/difftest", "--seed", "3", "--out", "/out", "--n", "50"])
  let (c2, a2) := buildSeedCommand .prlimit "/p/difftest" "/out" 7 #[]
  assertTrue "prlimit cmd"
    (c2 == "prlimit" &&
     a2 == #["--as=8589934592", "--", "timeout", "3600", "/p/difftest", "--seed", "7", "--out", "/out"])

  -- 3. Tally extraction matching `sed -n "/^seed $s done/,$p"`
  let sampleLog :=
    "difftest: seed 4, cases 0 to 49\n\
     statement: ...\n\
     seed 4 done in 120 ms (2400 ms per thousand programs)\n\
     tally: 50 programs, 0 counterexamples\n"
  let wantTally :=
    "seed 4 done in 120 ms (2400 ms per thousand programs)\n\
     tally: 50 programs, 0 counterexamples\n"
  assertTrue "extractSeedTally match" (extractSeedTally 4 sampleLog == wantTally)
  assertTrue "extractSeedTally wrong seed empty" (extractSeedTally 5 sampleLog == "")

  IO.println "[dt-seeds] selftest passed (all 8 assertions)"

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
    IO.eprintln s!"dt-seeds: {e}\n{usageText}"
    return 2
  | .ok cfg =>
    if cfg.showHelp then
      IO.println usageText
      return 0
    if cfg.selftest then
      runSelfTests
      return 0
    runSeeds cfg

end DtSeeds

def main (args : List String) : IO UInt32 := DtSeeds.main args
