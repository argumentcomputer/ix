/-
  `lake exe truthmines` — the corpus driver: Mathlib-parity ergonomics for
  the TruthMines catalog. Everything is projected from the typed records in
  `Benchmarks.TruthMinesSpec`; there is no version or toolchain handshake
  because ix and the corpus live in one repo on one toolchain.

    gen [--check]   project the workspace files (lakefile.lean, lean-toolchain)
    spec [--mini]   print the positional `Qualifier=Root[,Root…]` member
                    vector `ix catalog` is invoked with (full or mini)
    build [--mini] [--out PATH] [--report PATH]
          [--audit-only Qual[,Qual…]] [--ceiling-gb N] [--no-watchdog]
                    gen-check, build the member root oleans (network +
                    `lake exe cache get` on first run), then run
                    `ix catalog` over the rendered spec — one command,
                    one artifact. `--mini` builds the small
                    infrastructure tier (`truthmines-mini.ixe`: fixtures
                    + spine + Mathlib + FLT, mini ⊆ full by policy);
                    the default is the full corpus (`truthmines.ixe`).

  The heavy steps (workspace build, `ix catalog`) run under the typed
  RAM watchdog (`Ix.Watchdog`, shared with `ix bench`): a systemd user
  scope with cgroup MemoryMax and swap off, whole-scope kill on breach
  (exit 137) — "an unenforced ceiling is not a benchmark run", learned
  the hard way: the first corpus run without it OOM'd the whole box
  instead of the scope. Default ceiling is total RAM − 15 GiB;
  `--ceiling-gb N` overrides, `--no-watchdog` opts out explicitly
  (required on non-systemd platforms, where the availability probe
  refuses to run unprotected by default).

  Run from the repo root; `build` needs `lake build ix` first.
-/
import Benchmarks.TruthMinesSpec.Projection
import Ix.Watchdog

open TruthMinesSpec

private def usage : String :=
  "usage: lake exe truthmines <gen [--check] | spec [--mini] | build \
[--mini] [--out PATH] [--report PATH] [--audit-only Qual[,Qual…]] \
[--ceiling-gb N] [--no-watchdog]>"

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

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
  out? : Option String := none
  report? : Option String := none
  auditOnly : Option String := none
  ceilingGb : Option Nat := none
  noWatchdog : Bool := false
  /-- Build the mini tier (`catalogMiniSpec`) instead of the full corpus. -/
  mini : Bool := false

private def parseBuild : List String → Except String BuildOptions
  | [] => .ok {}
  | "--out" :: value :: rest => do pure { ← parseBuild rest with out? := some value }
  | "--report" :: value :: rest => do
    pure { ← parseBuild rest with report? := some value }
  | "--audit-only" :: value :: rest => do
    pure { ← parseBuild rest with auditOnly := some value }
  | "--ceiling-gb" :: value :: rest => do
    let some gb := value.toNat? | .error s!"--ceiling-gb needs a number, got `{value}`"
    pure { ← parseBuild rest with ceilingGb := some gb }
  | "--no-watchdog" :: rest => do
    pure { ← parseBuild rest with noWatchdog := true }
  | "--mini" :: rest => do
    pure { ← parseBuild rest with mini := true }
  | arg :: _ => .error s!"unknown build argument `{arg}`"

private def inherited (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args, cwd := some cwd }
  child.wait

/-- Run a heavy step under the typed watchdog's cgroup memory ceiling
    (`Ix.Watchdog.run`: whole-scope kill on breach, exit 137); `none`
    runs it bare (`--no-watchdog`). -/
private def watched (ceiling? : Option Nat) (cmd : String)
    (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  match ceiling? with
  | none => inherited cmd args cwd
  | some ceiling => Ix.Watchdog.run ceiling cmd args (some cwd)

private def reportOom (exit : UInt32) (ceiling? : Option Nat)
    (step : String) : IO Unit := do
  if exit == Ix.Watchdog.oomExitCode then
    if let some ceiling := ceiling? then
      IO.eprintln s!"{step} hit the {ceiling} GiB memory ceiling (cgroup \
OOM kill, whole scope). Rerun with a higher --ceiling-gb, more RAM, or a \
smaller corpus — the box itself was protected."

private def runBuild (options : BuildOptions) : IO UInt32 := do
  let tier := if options.mini then "mini" else "corpus"
  let spec := if options.mini then catalogMiniSpec else catalogSpec
  let out := options.out?.getD <|
    if options.mini then "truthmines-mini.ixe" else "truthmines.ixe"
  let report := options.report?.getD <|
    if options.mini then "truthmines-mini.report.json"
    else "truthmines.report.json"
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
    else if ← Ix.Watchdog.available then
      match options.ceilingGb with
      | some gb => pure (some gb)
      | none => pure (some (← Ix.Watchdog.defaultCeilingGb))
    else
      IO.eprintln "RAM watchdog unavailable (systemd user scope with \
cgroup memory.oom.group failed the probe) — pass --no-watchdog to run \
unprotected"
      return 1
  if let some ceiling := ceiling? then
    IO.println s!"truthmines build ({tier}): {ceiling} GiB memory ceiling \
(cgroup scope, swap off; --ceiling-gb / --no-watchdog to change)"
  -- Member root oleans. First run needs network and pulls the mathlib olean
  -- cache; `cache get` failure is tolerated — the build below is
  -- authoritative (`catalogOleans` is the workspace default target;
  -- `catalogMiniOleans` covers just the mini tier's roots).
  let _ ← inherited "lake" #["exe", "cache", "get"] workspaceDir
  let buildTarget := if options.mini then #["build", "catalogMiniOleans"]
    else #["build"]
  let buildExit ← watched ceiling? "lake" buildTarget workspaceDir
  if buildExit != 0 then
    reportOom buildExit ceiling? s!"{tier} workspace build"
    IO.eprintln s!"{tier} workspace build failed ({buildExit})"
    return buildExit
  let root ← IO.currentDir
  let exe ← IO.FS.realPath ixExe
  -- The typed records render straight to `ix catalog`'s positional
  -- argument vector — no spec file, no intermediate format. The frozen
  -- specs already carry closed (augmented, terminal) roots;
  -- `--close-roots` recomputation belongs to spec REGENERATION, not to
  -- every build.
  let mut args := #["catalog",
    "--prefix", spec.catalogPrefix.toString (escape := false),
    "--out", (root / out).toString,
    "--report", (root / report).toString]
  if let some qualifiers := options.auditOnly then
    args := args ++ #["--audit-only", qualifiers]
  args := args ++ commandArguments spec
  let exit ← watched ceiling? exe.toString args workspaceDir
  if exit == 0 then
    IO.println s!"truthmines build ({tier}): wrote {out} (report: {report})"
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
  | ["spec"] =>
    IO.println (String.intercalate " " (commandArguments catalogSpec).toList)
    return 0
  | ["spec", "--mini"] =>
    IO.println (String.intercalate " " (commandArguments catalogMiniSpec).toList)
    return 0
  | "build" :: rest =>
    match parseBuild rest with
    | .ok options => runBuild options
    | .error message => IO.eprintln message; IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
