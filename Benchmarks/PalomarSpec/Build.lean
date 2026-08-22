module

public import Benchmarks.PalomarSpec.Projection
public import Ix.Common
public import Ix.Watchdog

@[expose] public section

namespace PalomarSpec

def readIfExists (path : System.FilePath) : IO (Option String) := do
  if ← path.pathExists then return some (← IO.FS.readFile path)
  return none

def staleGeneratedPaths : IO (Array System.FilePath) := do
  let mut stale := #[]
  for file in generatedFiles do
    unless (← readIfExists file.path) == some file.content do
      stale := stale.push file.path
  return stale

def generate (checkOnly : Bool) : IO UInt32 := do
  let stale ← staleGeneratedPaths
  if checkOnly then
    if stale.isEmpty then
      IO.println "palomar gen --check: up to date"
      return 0
    IO.eprintln s!"palomar gen --check: stale generated files \
{stale.map (·.toString)} — run `lake exe palomar gen`"
    return 1
  if stale.isEmpty then
    IO.println "palomar gen: up to date"
    return 0
  for file in generatedFiles do
    if let some parent := file.path.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile file.path file.content
  IO.println s!"palomar gen: wrote {stale.size} generated file(s)"
  return 0

def inherited (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args, cwd := some cwd }
  child.wait

def watched (ceiling? : Option Nat) (cmd : String)
    (args : Array String) (cwd : System.FilePath) : IO UInt32 :=
  match ceiling? with
  | none => inherited cmd args cwd
  | some ceiling => Ix.Watchdog.run ceiling cmd args (some cwd)

structure PieceBuildOptions where
  ixExe : System.FilePath
  ixcDir : System.FilePath
  ceiling? : Option Nat := none
  jobs : Nat := 1
  noCache : Bool := false

structure PieceOutcome where
  qualifier : String
  cached : Bool
  exit : UInt32

def entryCacheKey (entry : Entry) : String :=
  s!"ix={Ix.versionString};toolchain={expectedToolchain};\
registry={entry.registryPath};source={entry.source.url}@{entry.source.rev};\
subdir={entry.source.subdir?.getD ""};root={entry.solutionModule};\
mathlib={compatibilityMathlibRevision}"

def cachePaths (options : PieceBuildOptions) (entry : Entry) :
    System.FilePath × System.FilePath :=
  let q := entry.qualifier.toString (escape := false)
  (options.ixcDir / s!"{q}.ixe", options.ixcDir / ".cache" / s!"{q}.key")

def entryCached (options : PieceBuildOptions) (entry : Entry) : IO Bool := do
  if options.noCache then return false
  let (piece, keyPath) := cachePaths options entry
  return (← piece.pathExists) &&
    (← readIfExists keyPath) == some (entryCacheKey entry)

def manifestContainsRevision (path : System.FilePath) (revision : String) : IO Bool := do
  return (← readIfExists path).any (·.contains revision)

/-- Materialize the shared current-Mathlib compatibility spine once. A cache
hook failure is tolerated only when Lake did materialize Mathlib: the wrapper
builds below are the authoritative compatibility check. -/
def prepareCore (ceiling? : Option Nat) : IO UInt32 := do
  let mathlibDir := coreWorkspaceDir / ".lake" / "packages" / "mathlib"
  let manifest := coreWorkspaceDir / "lake-manifest.json"
  let revision := compatibilityMathlibRevision
  unless (← mathlibDir.pathExists) &&
      (← manifestContainsRevision manifest revision) do
    Ix.progressLine "[palomar] compatibility spine: lake update"
    let updateExit ← watched ceiling? "lake" #["update"] coreWorkspaceDir
    unless (← mathlibDir.pathExists) &&
        (← manifestContainsRevision manifest revision) do
      IO.eprintln s!"[palomar] compatibility spine was not materialized ({updateExit})"
      return if updateExit == 0 then 1 else updateExit
  let _ ← inherited "lake" #["exe", "cache", "get"] coreWorkspaceDir
  return 0

def buildEntryPiece (options : PieceBuildOptions) (entry : Entry) :
    IO PieceOutcome := do
  let q := entry.qualifier.toString (escape := false)
  if ← entryCached options entry then
    return { qualifier := q, cached := true, exit := 0 }
  let (_, keyPath) := cachePaths options entry
  if ← keyPath.pathExists then IO.FS.removeFile keyPath
  Ix.progressLine s!"[palomar] {q}: build {entry.solutionModule}"
  let workspace := entryWorkspaceDir entry
  let manifest := entryManifestPath entry
  unless ← manifestContainsRevision manifest entry.source.rev do
    let updateExit ← watched options.ceiling? "lake" #["update"] workspace
    unless ← manifestContainsRevision manifest entry.source.rev do
      let exit := if updateExit == 0 then 1 else updateExit
      return { qualifier := q, cached := false, exit }
    if updateExit != 0 then
      Ix.progressLine s!"[palomar] {q}: Lake post-update hook exited \
{updateExit}; lockfile exists, continuing to authoritative build"
  let buildExit ← watched options.ceiling? "lake" #["build", "Driver"] workspace
  if buildExit != 0 then
    return { qualifier := q, cached := false, exit := buildExit }
  let exe ← IO.FS.realPath options.ixExe
  let pieceAbs := (← IO.FS.realPath options.ixcDir) / s!"{q}.ixe"
  let compileExit ← watched options.ceiling? "lake"
    #["env", exe.toString, "compile", "Driver.lean", "--out", pieceAbs.toString]
    workspace
  if compileExit == 0 then
    IO.FS.writeFile keyPath (entryCacheKey entry)
  return { qualifier := q, cached := false, exit := compileExit }

/-- Build selected Palomar pieces with a bounded process pool. The common
Mathlib checkout is shared read-only; each root repository and manifest has a
qualifier-specific packages directory. -/
def buildPieces (options : PieceBuildOptions)
    (entries : Array Entry := catalog) : IO (Array PieceOutcome) := do
  IO.FS.createDirAll (options.ixcDir / ".cache")
  let mut needsCore := false
  for entry in entries do
    unless ← entryCached options entry do needsCore := true
  if needsCore then
    let coreExit ← prepareCore options.ceiling?
    if coreExit != 0 then
      return entries.map fun entry => {
        qualifier := entry.qualifier.toString (escape := false)
        cached := false
        exit := coreExit
      }
  let jobs := max 1 options.jobs
  let mut pending := entries.toList
  let mut inFlight : Array (Task (Except IO.Error PieceOutcome)) := #[]
  let mut outcomes := #[]
  while !pending.isEmpty || !inFlight.isEmpty do
    while !pending.isEmpty && inFlight.size < jobs do
      let entry := pending.head!
      pending := pending.tail!
      inFlight := inFlight.push (← IO.asTask (buildEntryPiece options entry))
    let some task := inFlight[0]? | break
    inFlight := inFlight.eraseIdx! 0
    outcomes := outcomes.push (← IO.ofExcept task.get)
  return outcomes

end PalomarSpec
