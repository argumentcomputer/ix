/-
  `lake exe truthmines` — the corpus driver: Mathlib-parity ergonomics for
  the TruthMines catalog. Everything is projected from the typed records in
  `Benchmarks.TruthMinesSpec`; there is no version or toolchain handshake
  because ix and the corpus live in one repo on one toolchain.

    gen [--check]   project the workspace files (lakefile.lean, lean-toolchain)
    spec            print the `ix catalog --spec` JSON for the admission spec
    build [--out truthmines.ixe] [--report truthmines.report.json]
          [--audit-only Qual[,Qual…]]
                    gen-check, build the member root oleans (network +
                    `lake exe cache get` on first run), then run
                    `ix catalog` over the rendered spec — one command,
                    one artifact.

  Run from the repo root; `build` needs `lake build ix` first.
-/
import Benchmarks.TruthMinesSpec.Projection

open TruthMinesSpec

private def usage : String :=
  "usage: lake exe truthmines <gen [--check] | spec | build [--out PATH] \
[--report PATH] [--audit-only Qual[,Qual…]]>"

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
  out : String := "truthmines.ixe"
  report : String := "truthmines.report.json"
  auditOnly : Option String := none

private def parseBuild : List String → Except String BuildOptions
  | [] => .ok {}
  | "--out" :: value :: rest => do pure { ← parseBuild rest with out := value }
  | "--report" :: value :: rest => do pure { ← parseBuild rest with report := value }
  | "--audit-only" :: value :: rest => do
    pure { ← parseBuild rest with auditOnly := some value }
  | arg :: _ => .error s!"unknown build argument `{arg}`"

private def inherited (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args, cwd := some cwd }
  child.wait

private def runBuild (options : BuildOptions) : IO UInt32 := do
  let stale ← stalePaths
  unless stale.isEmpty do
    IO.eprintln s!"stale generated workspace files {stale} — \
run `lake exe truthmines gen` first"
    return 1
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  -- Member root oleans. First run needs network and pulls the mathlib olean
  -- cache; `cache get` failure is tolerated — the build below is
  -- authoritative (`catalogOleans` is the workspace default target).
  let _ ← inherited "lake" #["exe", "cache", "get"] workspaceDir
  let buildExit ← inherited "lake" #["build"] workspaceDir
  if buildExit != 0 then
    IO.eprintln s!"corpus workspace build failed ({buildExit})"
    return buildExit
  -- The spec is rendered at invocation time; the typed records stay the only
  -- checked-in representation.
  IO.FS.createDirAll (workspaceDir / ".lake")
  let specPath := workspaceDir / ".lake" / "truthmines-spec.json"
  IO.FS.writeFile specPath renderSpecJson
  let root ← IO.currentDir
  let exe ← IO.FS.realPath ixExe
  let mut args := #["catalog",
    "--spec", (root / specPath).toString,
    "--out", (root / options.out).toString,
    "--report", (root / options.report).toString]
  if let some qualifiers := options.auditOnly then
    args := args ++ #["--audit-only", qualifiers]
  let exit ← inherited exe.toString args workspaceDir
  if exit == 0 then
    IO.println s!"truthmines build: wrote {options.out} (report: {options.report})"
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
