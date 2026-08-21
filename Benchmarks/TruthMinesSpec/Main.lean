/-
  `lake exe truthmines` — the corpus driver: Mathlib-parity ergonomics for
  the TruthMines catalog. Everything is projected from the typed records in
  `Benchmarks.TruthMinesSpec`; there is no version or toolchain handshake
  because ix and the corpus live in one repo on one toolchain.

    gen [--check]   project the workspace files (lakefile.lean, lean-toolchain)
    spec            print the `ix catalog --spec` JSON for the admission spec
    build [--out truthmines.ixe] [--report truthmines.report.json]
          [--audit-only Qual[,Qual…]] [--ceiling-gb N] [--no-watchdog]
                    gen-check, build the member root oleans (network +
                    `lake exe cache get` on first run), then run
                    `ix catalog` over the rendered spec — one command,
                    one artifact.

  The heavy steps (workspace build, `ix catalog`) run under a memory
  watchdog: a systemd user scope with cgroup MemoryMax and swap off,
  whole-scope kill on breach (exit 137) — the same "an unenforced
  ceiling is not a benchmark run" principle `ix bench` enforces via
  `.github/scripts/watchdog.sh` (inlined here so a lake exe carries no
  runtime dependency on CI scripts), learned the hard way: the first
  corpus run without it OOM'd the whole box instead of the scope.
  Default ceiling is total RAM − 15 GiB (the bench convention);
  `--ceiling-gb N` overrides, `--no-watchdog` opts out explicitly
  (required on non-systemd platforms).

  Run from the repo root; `build` needs `lake build ix` first.
-/
import Benchmarks.TruthMinesSpec.Projection

open TruthMinesSpec

private def usage : String :=
  "usage: lake exe truthmines <gen [--check] | spec | build [--out PATH] \
[--report PATH] [--audit-only Qual[,Qual…]] [--ceiling-gb N] [--no-watchdog]>"

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- Total physical RAM in GiB, from `/proc/meminfo` (Linux only). -/
private def totalRamGb? : IO (Option Nat) := do
  let content ← try IO.FS.readFile "/proc/meminfo" catch _ => return none
  let some line := (content.splitOn "\n").find? (·.startsWith "MemTotal:")
    | return none
  let tokens := (line.splitOn " ").filter (!·.isEmpty)
  let some kb := tokens[1]?.bind (·.toNat?) | return none
  return some (kb / (1024 * 1024))

private structure GenFile where
  path : System.FilePath
  content : String

private def genFiles : List GenFile := [
  ⟨workspaceLakefilePath, renderWorkspaceLakefile⟩,
  ⟨workspaceToolchainPath, renderWorkspaceToolchain⟩]

private def readIfExists (path : System.FilePath) : IO (Option String) := do
  if (← path.pathExists) then return some (← IO.FS.readFile path)
  return none

private def stalePaths : IO (List String) := do
  let mut stale := []
  for file in genFiles do
    unless (← readIfExists file.path) == some file.content do
      stale := stale ++ [file.path.toString]
  return stale

private def runGen (check : Bool) : IO UInt32 := do
  let stale ← stalePaths
  if check then
    if stale.isEmpty then
      IO.println "truthmines gen --check: up to date"
      return 0
    IO.eprintln s!"truthmines gen --check: stale generated files {stale} — \
run `lake exe truthmines gen`"
    return 1
  if stale.isEmpty then
    IO.println "truthmines gen: up to date"
    return 0
  for file in genFiles do
    if let some parent := file.path.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile file.path file.content
  IO.println s!"truthmines gen: wrote {stale}"
  return 0

private structure BuildOptions where
  out : String := "truthmines.ixe"
  report : String := "truthmines.report.json"
  auditOnly : Option String := none
  ceilingGb : Option Nat := none
  noWatchdog : Bool := false

private def parseBuild : List String → Except String BuildOptions
  | [] => .ok {}
  | "--out" :: value :: rest => do pure { ← parseBuild rest with out := value }
  | "--report" :: value :: rest => do pure { ← parseBuild rest with report := value }
  | "--audit-only" :: value :: rest => do
    pure { ← parseBuild rest with auditOnly := some value }
  | "--ceiling-gb" :: value :: rest => do
    let some gb := value.toNat? | .error s!"--ceiling-gb needs a number, got `{value}`"
    pure { ← parseBuild rest with ceilingGb := some gb }
  | "--no-watchdog" :: rest => do
    pure { ← parseBuild rest with noWatchdog := true }
  | arg :: _ => .error s!"unknown build argument `{arg}`"

private def inherited (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args, cwd := some cwd }
  child.wait

/-- Run a heavy step under a cgroup memory ceiling; `none` runs it bare
    (`--no-watchdog`).

    Inlined systemd-run invocation with the same kill semantics as
    `.github/scripts/watchdog.sh` (the bench watchdog — kept as the shared
    spec, not a runtime dependency): a user scope with `MemoryMax`, swap
    off, and `memory.oom.group=1` so a breach kills the WHOLE scope with
    SIGKILL (exit 137) instead of singling out the biggest process; if the
    oom.group write fails, exit 2 rather than run with wrong kill
    semantics. Omitted relative to the script: the CI linger bootstrap (a
    desktop session already runs a user manager — if `systemd-run --user`
    fails here, the error is visible and `--no-watchdog` is the escape
    hatch) and the Open MPI signal-handler workaround (zisk-host-specific;
    nothing on this path links MPI). -/
private def watched (ceiling? : Option Nat) (cmd : String)
    (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  match ceiling? with
  | none => inherited cmd args cwd
  | some ceiling =>
    let oomGroupThenExec :=
      "echo 1 > \"/sys/fs/cgroup$(cut -d: -f3- /proc/self/cgroup)/memory.oom.group\" \
|| { echo \"truthmines watchdog: cannot set memory.oom.group\" >&2; exit 2; }; \
exec \"$@\""
    inherited "systemd-run"
      (#["--user", "--scope", "--quiet",
         "-p", s!"MemoryMax={ceiling}G", "-p", "MemorySwapMax=0",
         "bash", "-c", oomGroupThenExec, "watchdog", cmd] ++ args) cwd

private def reportOom (exit : UInt32) (ceiling? : Option Nat)
    (step : String) : IO Unit := do
  if exit == 137 then
    if let some ceiling := ceiling? then
      IO.eprintln s!"{step} hit the {ceiling} GiB memory ceiling (cgroup \
OOM kill, whole scope). Rerun with a higher --ceiling-gb, more RAM, or a \
smaller corpus — the box itself was protected."

private def runBuild (options : BuildOptions) : IO UInt32 := do
  let stale ← stalePaths
  unless stale.isEmpty do
    IO.eprintln s!"stale generated workspace files {stale} — \
run `lake exe truthmines gen` first"
    return 1
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  -- Resolve the memory ceiling: an unenforced ceiling is not a corpus run.
  let ceiling? : Option Nat ←
    if options.noWatchdog then
      pure none
    else
      match options.ceilingGb with
      | some gb => pure (some gb)
      | none =>
        match ← totalRamGb? with
        | some total => pure (some (if total > 20 then total - 15 else total))
        | none => pure none
  if ceiling?.isNone && !options.noWatchdog then
    IO.eprintln "cannot read total RAM for the default memory ceiling — \
pass --ceiling-gb N, or --no-watchdog to run unprotected"
    return 1
  if let some ceiling := ceiling? then
    IO.println s!"truthmines build: {ceiling} GiB memory ceiling (cgroup \
scope, swap off; --ceiling-gb / --no-watchdog to change)"
  -- Member root oleans. First run needs network and pulls the mathlib olean
  -- cache; `cache get` failure is tolerated — the build below is
  -- authoritative (`catalogOleans` is the workspace default target).
  let _ ← inherited "lake" #["exe", "cache", "get"] workspaceDir
  let buildExit ← watched ceiling? "lake" #["build"] workspaceDir
  if buildExit != 0 then
    reportOom buildExit ceiling? "corpus workspace build"
    IO.eprintln s!"corpus workspace build failed ({buildExit})"
    return buildExit
  -- The spec is rendered at invocation time; the typed records stay the only
  -- checked-in representation.
  IO.FS.createDirAll (workspaceDir / ".lake")
  let specPath := workspaceDir / ".lake" / "truthmines-spec.json"
  IO.FS.writeFile specPath renderSpecJson
  let root ← IO.currentDir
  let exe ← IO.FS.realPath ixExe
  -- The frozen admission spec already carries closed (augmented, terminal)
  -- roots; `--close-roots` recomputation belongs to spec REGENERATION, not
  -- to every build.
  let mut args := #["catalog",
    "--spec", (root / specPath).toString,
    "--out", (root / options.out).toString,
    "--report", (root / options.report).toString]
  if let some qualifiers := options.auditOnly then
    args := args ++ #["--audit-only", qualifiers]
  let exit ← watched ceiling? exe.toString args workspaceDir
  if exit == 0 then
    IO.println s!"truthmines build: wrote {options.out} (report: {options.report})"
  else
    reportOom exit ceiling? "ix catalog"
  return exit

def main (args : List String) : IO UInt32 := do
  unless (← (("Benchmarks" : System.FilePath) / "TruthMinesSpec").pathExists) do
    IO.eprintln "run `lake exe truthmines` from the ix repo root"
    return 1
  match args with
  | ["gen"] => runGen (check := false)
  | ["gen", "--check"] => runGen (check := true)
  | ["spec"] => IO.println renderSpecJson; return 0
  | "build" :: rest =>
    match parseBuild rest with
    | .ok options => runBuild options
    | .error message => IO.eprintln message; IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
