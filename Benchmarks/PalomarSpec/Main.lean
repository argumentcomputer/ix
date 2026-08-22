/- `lake exe palomar`: generate, build, validate, and inspect the 19-project
Palomar snapshot without ever co-loading their colliding `Solution` modules. -/
module

public import Benchmarks.PalomarSpec.Build

public section

open PalomarSpec

private def usage : String :=
  "usage: lake exe palomar <gen [--check] | spec | build [--out DIR.ixc] \
[--only Q[,Q…]] [--jobs N] [--ceiling-gb N] [--no-watchdog] [--no-cache] | \
check [--ixc DIR.ixc] [--only Q[,Q…]] | validate [--only Q[,Q…]] \
[--ceiling-gb N] [--no-watchdog]>"

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

private def selectEntries (only : Option (List String)) : Except String (Array Entry) := do
  match only with
  | none => pure catalog
  | some wanted =>
    for q in wanted do
      unless catalog.any (·.qualifier.toString (escape := false) == q) do
        throw s!"--only names unknown Palomar qualifier `{q}`"
    pure <| catalog.filter fun entry =>
      wanted.contains (entry.qualifier.toString (escape := false))

private structure BuildOptions where
  out : String := "palomar.ixc"
  only : Option (List String) := none
  jobs? : Option Nat := none
  ceilingGb : Option Nat := none
  noWatchdog : Bool := false
  noCache : Bool := false

private def parseOnly (value : String) : Except String (List String) :=
  let values := (value.splitOn ",").filter (!·.isEmpty)
  if values.isEmpty then .error "--only needs at least one qualifier"
  else .ok values

private def parseBuild : List String → Except String BuildOptions
  | [] => .ok {}
  | "--out" :: value :: rest => do pure { ← parseBuild rest with out := value }
  | "--only" :: value :: rest => do
    pure { ← parseBuild rest with only := some (← parseOnly value) }
  | "--jobs" :: value :: rest => do
    let some n := value.toNat? | throw s!"--jobs needs a number, got `{value}`"
    if n == 0 then throw "--jobs must be at least 1"
    pure { ← parseBuild rest with jobs? := some n }
  | "--ceiling-gb" :: value :: rest => do
    let some n := value.toNat? | throw s!"--ceiling-gb needs a number, got `{value}`"
    pure { ← parseBuild rest with ceilingGb := some n }
  | "--no-watchdog" :: rest => do pure { ← parseBuild rest with noWatchdog := true }
  | "--no-cache" :: rest => do pure { ← parseBuild rest with noCache := true }
  | arg :: _ => .error s!"unknown build argument `{arg}`"

private def buildCeiling (options : BuildOptions) : IO (Except String (Option Nat)) := do
  if options.noWatchdog then return .ok none
  unless ← Ix.Watchdog.available do
    return .error "RAM watchdog unavailable — pass --no-watchdog to run unprotected"
  return .ok (some (options.ceilingGb.getD 25))

private def runBuild (options : BuildOptions) : IO UInt32 := do
  let stale ← staleGeneratedPaths
  unless stale.isEmpty do
    IO.eprintln "stale Palomar workspaces — run `lake exe palomar gen` first"
    return 1
  unless ← ixExe.pathExists do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  let entries ← match selectEntries options.only with
    | .ok entries => pure entries
    | .error error => IO.eprintln error; return 1
  let ceiling? ← match ← buildCeiling options with
    | .ok ceiling => pure ceiling
    | .error error => IO.eprintln error; return 1
  let jobs := options.jobs?.getD 1
  let root ← IO.currentDir
  let ixc := root / options.out
  let outcomes ← buildPieces {
    ixExe
    ixcDir := ixc
    ceiling?
    jobs
    noCache := options.noCache
  } entries
  let failures := outcomes.filter (·.exit != 0)
  unless failures.isEmpty do
    IO.eprintln s!"[palomar] failed: {failures.map fun o => (o.qualifier, o.exit)}"
    return 1
  let exe ← IO.FS.realPath ixExe
  let labels := entries.map (·.qualifier.toString (escape := false))
  let pieces := labels.map fun q => (ixc / s!"{q}.ixe").toString
  let pins := entries.map fun entry =>
    s!"git:{entry.source.url}@{entry.source.rev}"
  let assembleArgs := #["catalog", "assemble", ixc.toString] ++ pieces ++ #[
    "--labels", String.intercalate "," labels.toList,
    "--toolchains", expectedToolchain,
    "--pins", String.intercalate "," pins.toList
  ]
  let assembleExit ← inherited exe.toString assembleArgs root
  if assembleExit != 0 then return assembleExit
  let verifyExit ← inherited exe.toString
    #["catalog", "verify", ixc.toString] root
  if verifyExit != 0 then return verifyExit
  let cached := outcomes.filter (·.cached) |>.size
  Ix.progressLine s!"[palomar] done — {options.out}: {entries.size} project(s), \
{cached} from cache"
  return 0

private structure SweepOptions where
  ixc : String := "palomar.ixc"
  only : Option (List String) := none
  ceilingGb : Option Nat := none
  noWatchdog : Bool := false

private def parseSweep : List String → Except String SweepOptions
  | [] => .ok {}
  | "--ixc" :: value :: rest => do pure { ← parseSweep rest with ixc := value }
  | "--only" :: value :: rest => do
    pure { ← parseSweep rest with only := some (← parseOnly value) }
  | "--ceiling-gb" :: value :: rest => do
    let some n := value.toNat? | throw s!"--ceiling-gb needs a number, got `{value}`"
    pure { ← parseSweep rest with ceilingGb := some n }
  | "--no-watchdog" :: rest => do pure { ← parseSweep rest with noWatchdog := true }
  | arg :: _ => .error s!"unknown argument `{arg}`"

private def runCheck (options : SweepOptions) : IO UInt32 := do
  unless ← ixExe.pathExists do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  let entries ← match selectEntries options.only with
    | .ok entries => pure entries
    | .error error => IO.eprintln error; return 1
  let exe ← IO.FS.realPath ixExe
  let root ← IO.currentDir
  for entry in entries do
    let q := entry.qualifier.toString (escape := false)
    let piece := root / options.ixc / s!"{q}.ixe"
    unless ← piece.pathExists do
      IO.eprintln s!"missing {piece} — run `lake exe palomar build` first"
      return 1
    let exit ← inherited exe.toString #["check-rs", piece.toString, "--anon"] root
    if exit != 0 then return exit
  return 0

private def runValidate (options : SweepOptions) : IO UInt32 := do
  let stale ← staleGeneratedPaths
  unless stale.isEmpty do
    IO.eprintln "stale Palomar workspaces — run `lake exe palomar gen` first"
    return 1
  unless ← ixExe.pathExists do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  let entries ← match selectEntries options.only with
    | .ok entries => pure entries
    | .error error => IO.eprintln error; return 1
  let ceiling? : Option Nat ←
    if options.noWatchdog then pure none
    else if ← Ix.Watchdog.available then pure (some (options.ceilingGb.getD 25))
    else IO.eprintln "RAM watchdog unavailable — pass --no-watchdog"; return 1
  let exe ← IO.FS.realPath ixExe
  for entry in entries do
    let q := entry.qualifier.toString (escape := false)
    Ix.progressLine s!"[palomar] validating {q}…"
    let exit ← watched ceiling? "lake"
      #["env", exe.toString, "validate", "Driver.lean"]
      (entryWorkspaceDir entry)
    if exit != 0 then return exit
  return 0

private def runSpec : IO UInt32 := do
  for entry in catalog do
    IO.println s!"{entry.qualifier}\t{entry.registryPath}\t\
{entry.upstreamToolchain}\t{entry.source.url}@{entry.source.rev}\t\
{entry.solutionModule}"
  return 0

def main (args : List String) : IO UInt32 := do
  unless ← (("Benchmarks" : System.FilePath) / "PalomarSpec").pathExists do
    IO.eprintln "run `lake exe palomar` from the ix repo root"
    return 1
  match args with
  | ["gen"] => generate false
  | ["gen", "--check"] => generate true
  | ["spec"] => runSpec
  | "build" :: rest =>
    match parseBuild rest with
    | .ok options => runBuild options
    | .error error => IO.eprintln error; IO.eprintln usage; return 1
  | "check" :: rest =>
    match parseSweep rest with
    | .ok options => runCheck options
    | .error error => IO.eprintln error; IO.eprintln usage; return 1
  | "validate" :: rest =>
    match parseSweep rest with
    | .ok options => runValidate options
    | .error error => IO.eprintln error; IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
