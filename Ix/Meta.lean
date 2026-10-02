module
public import Lean.Meta.Reduce
public import Ix.Address
public import Ix.CompileM
public import Batteries.Data.String

public section

open Lean

open System (FilePath)

/-- Spawn env for nested `lake` invocations: drop LD_LIBRARY_PATH. `lake exe`
    and `lake test` prepend the Lean toolchain's lib dir there, and the
    toolchain bundles its own libLLVM. Under a system LLVM of the same major
    version, cargo build scripts spawned by the nested lake would then load
    the system libclang against Lean's libLLVM and fail on missing symbols.
    lake and lean locate their own libraries through RUNPATH. -/
def lakeSpawnEnv : Array (String × Option String) :=
  #[("LD_LIBRARY_PATH", none)]

/-- Print `[lean] <what>: <time since start>` to stderr when `IX_VERBOSE` (or
the driver's `IX_COMPILE_DBG`) is set: the wall time of one step of the Lean
side before the compiler runs (Lake, search path, import, elaboration). -/
def leanPhaseLine (what : String) (startMs : Nat) : IO Unit := do
  if (← IO.getEnv "IX_VERBOSE").isSome || (← IO.getEnv "IX_COMPILE_DBG").isSome then
    IO.eprintln s!"[lean] {what}: {((← IO.monoMsNow) - startMs).formatMs}"

/-- `lake env printenv <vars>` run in `cwd`: Lake's exit code and stdout (one
line per variable, in order). -/
def queryLakeEnv (cwd : Option FilePath) (vars : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output
    { cmd := "lake", args := #["env", "printenv"] ++ vars, cwd, env := lakeSpawnEnv }
  return (out.exitCode, out.stdout)

/-- `lake env printenv LEAN_PATH` run in `cwd`: Lake's exit code and stdout. -/
def queryLakeLeanPath (cwd : Option FilePath) : IO (UInt32 × String) :=
  queryLakeEnv cwd #["LEAN_PATH"]

/-- Successful `lake env printenv LEAN_PATH` outputs of this process, keyed by
the directory Lake ran in. A workspace's search path changes only when Lake
reconfigures or materializes the workspace, which happens in `lake build`;
`buildFile` refreshes the entry of the workspace it builds. Without the memo a
compile asks Lake twice for module-mode files (`getFileEnvCore`, then
`moduleVisibleNames`), at about 2.4 s per query on Mathlib. -/
initialize leanPathMemo : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- Initialize Lean's module search path.

When `cwd` is provided, query `lake env printenv LEAN_PATH` from that directory
unconditionally — the caller is loading a file from a specific lake project, and
the inherited `LEAN_PATH` (e.g., set by an outer `lake exe ix` invocation) would
point at the wrong project's packages. When `cwd` is `none`, honor the inherited
`LEAN_PATH` if set, falling back to querying lake in the current directory.
A query this process already made for the same directory is reused
(`leanPathMemo`). -/
def initLeanSearchPath (cwd : Option FilePath := none) : IO Unit := do
  -- If a target cwd is supplied, always query that cwd's LEAN_PATH.
  -- Otherwise, trust the inherited LEAN_PATH when present.
  if cwd.isSome || (← IO.getEnv "LEAN_PATH").isNone then
    let key := (← match cwd with | some dir => pure dir | none => IO.currentDir).toString
    let stdout ← match (← leanPathMemo.get)[key]? with
      | some stdout => pure stdout
      | none =>
        let start ← IO.monoMsNow
        let (exitCode, stdout) ← queryLakeLeanPath cwd
        leanPhaseLine "search path (lake env)" start
        -- As before the memo, a failed query still yields its (empty) output
        -- here; it is just not remembered.
        if exitCode == 0 then leanPathMemo.modify (·.insert key stdout)
        pure stdout
    let paths := stdout.trimAscii.toString.splitOn ":" |>.map FilePath.mk
    initSearchPath (← findSysroot) paths
  else
    initSearchPath (← findSysroot)

/-- Walk up from `start` looking for `lake-manifest.json`. -/
partial def findLakeRoot (start : FilePath) : IO (Option FilePath) := do
  if ← (start / "lake-manifest.json").pathExists then
    return some start
  match start.parent with
  | none => return none
  | some p => if p == start then return none else findLakeRoot p

/-- Search path for elaborating `file`: query lake at the file's LAKE
    ROOT, not its immediate parent — `lake env` does not walk up, so a
    file nested inside a workspace (`Benchmarks/TruthMines/Drivers/…`)
    would otherwise resolve to a bare toolchain path and fail on its
    first workspace import. Files sitting at a workspace root behave
    exactly as before. -/
def initLeanSearchPathFor (file : FilePath) : IO Unit := do
  let parent := file.parent.getD ⟨"."⟩
  initLeanSearchPath (some ((← findLakeRoot parent).getD parent))

/-- A file's elaborated environment plus whether its header declares `module`. -/
structure FileEnv where
  env : Environment
  isModule : Bool

open Elab in
/-- A file whose header has been imported and whose body is still to be
elaborated: the state between the two halves of `getFileEnvCore`. -/
structure FileHeaderImport where
  inputCtx : Parser.InputContext
  parserState : Parser.ModuleParserState
  header : HeaderSyntax
  env : Environment
  messages : MessageLog

/-- The error a failed import or elaboration reports. -/
def messagesError (messages : MessageLog) : IO IO.Error := do
  return IO.userError $ "\n\n".intercalate $
    (← messages.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)

open Elab in
/-- The first half of `getFileEnvCore`: parse the header of the canonical
`path` and import it, at the classic level, with the current search path.
Import errors are left in `messages`. -/
def importFileHeader (path : FilePath) (what : String := "import") : IO FileHeaderImport := do
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- Required for `processHeaderCore`'s `loadExts := true` import; a completed
  -- import resets the flag, so it is re-armed before every import.
  unsafe enableInitializersExecution
  let start ← IO.monoMsNow
  let (env, messages) ← processHeaderCore
    (HeaderSyntax.startPos header) (HeaderSyntax.imports header)
    (isModule := false) default messages inputCtx 0
  leanPhaseLine what start
  return { inputCtx, parserState, header, env, messages }

open Elab in
/-- The second half of `getFileEnvCore`: report import errors, then elaborate
the file body. -/
def elaborateFileBody (imported : FileHeaderImport) : IO FileEnv := do
  if imported.messages.hasErrors then
    throw (← messagesError imported.messages)
  -- Elaborate the file body too, so the env contains the file's own
  -- definitions and not just its imports. Classic elaboration accepts
  -- module-syntax bodies (`public def` etc.) and yields their real content.
  let env := imported.env.setMainModule default
  let start ← IO.monoMsNow
  let s ← IO.processCommands imported.inputCtx imported.parserState
    (Command.mkState env imported.messages)
  leanPhaseLine "elaborate file body" start
  let cmdMessages := s.commandState.messages
  if cmdMessages.hasErrors then
    throw (← messagesError cmdMessages)
  return ⟨s.commandState.env, HeaderSyntax.isModule imported.header⟩

open Elab in
/-- Loads a Lean `Environment` from a file path provided at runtime, together
with the header's `module` mode.

The import always happens at the classic (`OLeanLevel.private`) level,
regardless of the header. A module-mode (`OLeanLevel.exported`) import loads
every imported public theorem as a body-less **axiom** and omits non-exported
`_private.*` constants entirely — fine for elaboration, fatally wrong as
compiler input: content-addressing such an env axiomizes imported proofs, so
kernel checks pass vacuously and every address drifts from the private-level
compile of the same constants (the catalog path, `getCompileEnv`, and the
pinned `PrimAddrs` all live at the private level). This regressed once as the
`tc-pins`/`tc-accel-diff` failures on main.

The header's `module` mode is still honored, but as *scoping*, not content:
the CLI's default compile of a module-mode file seeds its named rows from the
module-visible surface (`moduleVisibleNames`) and pulls referenced private
content in through the dependency closure — preserving the qualified-package
isolation the mode exists for (TruthMines' `module-header-v1` patch) without
corrupting stored content. See `Ix.EnvScope.defaultConstList`. -/
def getFileEnvCore (path : FilePath) : IO FileEnv := do
  let path ← IO.FS.realPath path
  initLeanSearchPathFor path
  elaborateFileBody (← importFileHeader path)

/-- Loads a Lean `Environment` from a file path provided at runtime.
Full-content: see `getFileEnvCore` for why the header's `module` mode never
trims what the environment carries. -/
def getFileEnv (path : FilePath) : IO Environment := (·.env) <$> getFileEnvCore path

open Elab in
/-- The module-visible constant names of a module-mode file: what an
`OLeanLevel.exported` import of its header yields (imported public theorems
appear there as body-less axioms — which is exactly why this set is only ever
used to pick *names*, never content). Returns `none` for classic headers (no
restriction). Header-only: the file's own body is not elaborated here, so
callers union locally-elaborated names (`getModuleIdxFor? · |>.isNone`) from
the full-content env. -/
def moduleVisibleNames (path : FilePath) : IO (Option NameSet) := do
  let path ← IO.FS.realPath path
  initLeanSearchPathFor path
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, _, messages) ← Parser.parseHeader inputCtx
  if !HeaderSyntax.isModule header then return none
  unsafe enableInitializersExecution  -- re-armed per import; see `getFileEnvCore`
  let start ← IO.monoMsNow
  let (env, messages) ← processHeaderCore
    (HeaderSyntax.startPos header) (HeaderSyntax.imports header)
    (isModule := true) default messages inputCtx 0
  leanPhaseLine "import at the exported level (module-visible names)" start
  if messages.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← messages.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)
  let mut visible : NameSet := {}
  for (n, _) in env.constants.toList do
    visible := visible.insert n
  return some visible

/-- Captures the current module and its imports at compile time. -/
elab "this_file!" : term => do
  let env ← getEnv
  return toExpr (env.header.imports.map (·.module) |>.push env.header.mainModule)

/-- Loads a Lean `Environment` from compiled `.olean` files.

Uses `loadExts := true` so that persistent environment extensions (e.g.
`SimplePersistentEnvExtension` state registered via `registerTestCase`,
attribute maps, etc.) are hydrated from the imported `.olean` data. Without
this, `importModules` leaves every extension at its `addImportedFn #[]`
initial value — all imported entries sit in raw form but the computed state
σ is empty, which silently breaks any test that reads extension state via
`get_env!`. Matches `Lean.Elab.processHeaderCore`'s import path (used by
`getFileEnv`) and Lake's own `importModulesUsingCache`. -/
def getCompileEnv (imports : Array Name) : IO Environment := do
  initLeanSearchPath
  unsafe enableInitializersExecution  -- required for `loadExts := true`
  importModules (imports.map ({ module := · : Import })) default (loadExts := true)

macro "get_env!" : term =>
  `(getCompileEnv this_file!)

/-- If the project depends on Mathlib, download the Mathlib cache. -/
def fetchMathlibCache (cwd : Option FilePath) : IO Unit := do
  let root := cwd.getD "."
  let manifest := root / "lake-manifest.json"
  let contents ← IO.FS.readFile manifest
  if contents.contains "leanprover-community/mathlib4" then
    let packagesDir :=
      (Lean.Json.parse contents).toOption
        |>.bind (fun json => (json.getObjVal? "packagesDir").toOption)
        |>.bind (fun value => value.getStr?.toOption)
        |>.map FilePath.mk
        |>.getD (".lake" / "packages")
    let packagesRoot :=
      if packagesDir.isAbsolute then packagesDir else root / packagesDir
    let mathlibBuild := packagesRoot / "mathlib" / ".lake" / "build"
    if ← mathlibBuild.pathExists then
      println! "Mathlib cache already present, skipping fetch."
      return
    println! "Detected Mathlib dependency. Fetching Mathlib cache..."
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["exe", "cache", "get"]
      cwd := cwd
      env := lakeSpawnEnv
      stdout := .inherit
      stderr := .inherit
    }
    let exitCode ← child.wait
    if exitCode != 0 then
      throw $ IO.userError "lake exe cache get failed"

/-- Walk up from `cur` collecting directory names until reaching `root`,
yielding the path components between them (in top-down order). -/
partial def collectRelParts (root cur : FilePath) (acc : List String) : Option (List String) :=
  if cur == root then some acc
  else match cur.fileName, cur.parent with
    | some name, some par =>
      if par == cur then none else collectRelParts root par (name :: acc)
    | _, _ => none

/-- The modification stamps of what a Lake process rewrites when it
(re)configures or materializes the workspace at `root`: the manifest, the
packages directory and each package checkout's `HEAD`, and the compiled
package configurations under `.lake/config` (their traces and `.olean`s). If
the stamps are equal before and after a window, no Lake process changed the
workspace's configuration in it. -/
def lakeWorkspaceStamp (root : FilePath) : IO (Array (FilePath × String)) := do
  let stampOf (p : FilePath) : IO (FilePath × String) := do
    let s ← try
        let m ← p.metadata
        pure s!"{m.modified.sec}.{m.modified.nsec}/{m.byteSize}"
      catch _ => pure "absent"
    return (p, s)
  let entries (dir : FilePath) : IO (Array FilePath) := do
    try
      let es ← dir.readDir
      return (es.map (·.path)).qsort (·.toString < ·.toString)
    catch _ => return #[]
  let manifest := root / "lake-manifest.json"
  let packagesDir :=
    (← try pure ((Lean.Json.parse (← IO.FS.readFile manifest)).toOption) catch _ => pure none)
      |>.bind (fun json => (json.getObjVal? "packagesDir").toOption)
      |>.bind (fun value => value.getStr?.toOption)
      |>.map FilePath.mk
      |>.getD (".lake" / "packages")
  let packagesDir := if packagesDir.isAbsolute then packagesDir else root / packagesDir
  let configDir := root / ".lake" / "config"
  let mut stamps := #[← stampOf manifest, ← stampOf packagesDir, ← stampOf configDir]
  for pkg in ← entries packagesDir do
    stamps := stamps.push (← stampOf (pkg / ".git" / "HEAD"))
  for cfg in ← entries configDir do
    stamps := stamps.push (← stampOf (cfg / "lakefile.olean.trace"))
    stamps := stamps.push (← stampOf (cfg / "lakefile.olean"))
  return stamps

/-- Build the Lean module at `path` with Lake (fetching the Mathlib cache first
if the project depends on it), and run `alongside` while the build runs.

The workspace's search path does not depend on the build, so the
`lake env printenv <queryVars>` query (`LEAN_PATH` first) that loading the file
needs runs alongside `lake build`: the two Lake processes do not wait on each
other, and on Mathlib the pair takes as long as the build alone, ~2.4 s less
than in sequence. `prepare` runs with the workspace root right before
`lake build` starts (after the Mathlib cache step). `alongside` runs on this
thread with `prepare`'s result and the query's answer (exit code and stdout) as
soon as that is in, usually while `lake build` is still running; it must not
throw. The `LEAN_PATH` line goes to `leanPathMemo` for `initLeanSearchPath`.

Two Lake processes on one workspace can collide only when one of them
(re)configures or materializes it: Lake then gives the configuration lock to
one process and fails the other. So the answer is kept only if the workspace
stamps (`lakeWorkspaceStamp`) are unchanged across both runs; otherwise the
search path is queried again later, as before. If the build fails in a window
in which the workspace changed while the query succeeded, the build may have
lost that lock, and it runs once more on its own before failing.

Returns `alongside`'s result and whether the stamps were unchanged. -/
def buildFileWith (path : FilePath) (queryVars : Array String) (prepare : FilePath → IO β)
    (alongside : β → Except IO.Error (UInt32 × String) → IO α) : IO (α × Bool) := do
  let path ← IO.FS.realPath path
  let some stem := path.fileStem
    | throw $ IO.userError s!"cannot determine module name from {path}"
  let some parent := path.parent
    | throw $ IO.userError s!"cannot determine parent of {path}"
  let some root ← findLakeRoot parent
    | throw $ IO.userError s!"no lake-manifest.json found at or above {parent}"
  let some relParts := collectRelParts root parent []
    | throw $ IO.userError s!"{path} is not under {root}"
  let moduleName := ".".intercalate (relParts ++ [stem])
  fetchMathlibCache root
  let build (what : String) : IO UInt32 := do
    let start ← IO.monoMsNow
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["build", moduleName]
      cwd := root
      env := lakeSpawnEnv
      stdout := .inherit
      stderr := .inherit
    }
    let exitCode ← child.wait
    leanPhaseLine what start
    return exitCode
  let key := root.toString
  let stampBefore ← lakeWorkspaceStamp root
  let prepared ← prepare root
  let building ← IO.asTask (prio := .dedicated) (build s!"lake build {moduleName}")
  let start ← IO.monoMsNow
  let answer ← (queryLakeEnv (some root) queryVars).toBaseIO
  leanPhaseLine "search path (lake env, alongside lake build)" start
  let result ← alongside prepared answer
  let mut exitCode ← IO.ofExcept (← IO.wait building)
  let undisturbed := (← lakeWorkspaceStamp root) == stampBefore
  let queryOk := match answer with | .ok (0, _) => true | _ => false
  if exitCode != 0 && !undisturbed && queryOk then
    exitCode ← build s!"lake build {moduleName} (again, alone)"
  match answer with
  | .ok (0, stdout) =>
    if undisturbed then leanPathMemo.modify (·.insert key ((stdout.splitOn "\n").headD ""))
    else leanPathMemo.modify (·.erase key)
  | _ => leanPathMemo.modify (·.erase key)
  if exitCode != 0 then
    throw $ IO.userError "lake build failed"
  return (result, undisturbed)

/-- Build the Lean module at the given file path using Lake.
Also fetches Mathlib cache if the project depends on it. The search path is
queried alongside the build (`buildFileWith`). -/
def buildFile (path : FilePath) : IO Unit :=
  discard <| buildFileWith path #["LEAN_PATH"] (fun _ => pure ()) fun _ _ => pure ()

/-- The current time as the file system holding `dir` records it: the
modification time of a fresh empty file created (and removed again) in `dir`.
On a network file system the server's clock sets file times, so the time is
taken where the files that are compared with it live. -/
def fileSystemNow (dir : FilePath) : IO IO.FS.SystemTime := do
  let probe := dir / s!".ix-time-{← IO.Process.getPID}"
  IO.FS.writeFile probe ""
  try return (← probe.metadata).modified
  finally IO.FS.removeFile probe

/-- Why an import that produced `env` with the search path `sp` may differ
from an import of the same header made now, or `none` if it cannot. `before`
is a time, taken on the workspace's file system, from before `lake build`
started.

Each imported `.olean` part (and IR part) is one region of `env.header`. While
the build runs, Lake changes a module's files only by removing them
(`clearOutputArtifacts`) and by renaming freshly written temporary files over
them (`lean -o`, `leanir` and `leantar -x` all write a temporary file and rename
it; `leantar` gives it the current time) or, when restoring from its artifact
cache, by a hard link or a copy (`buildFileImporting` imports nothing alongside
the build when such a cache exists). Checked against the Lean 4.33 sources and
with `strace`. So if every region's file still exists and was last modified
before the build started, every file the import read is still the file at its
path, unchanged. A margin of 2 s below `before` covers coarse file-time
granularity (a file modified in that margin counts as changed, which only costs
a fresh start).

The search path must also still resolve each package root (the first path
component under its search-path entry) to the entry the import used: Lean's
`findOLean` takes the first entry with a directory `<root>` or a file
`<root>.olean`. -/
def importStillCurrent (env : Environment) (sp : SearchPath) (before : IO.FS.SystemTime) :
    IO (Option String) := do
  let regions := env.header.regions
  if regions.isEmpty then return some "the import read no files"
  let limit : IO.FS.SystemTime := { before with sec := before.sec - 2 }
  -- One `stat` per region (26k on Mathlib), spread over the task pool.
  let chunk := 1024
  let tasks ← (List.range ((regions.size + chunk - 1) / chunk)).toArray.mapM fun c =>
    IO.asTask do
      for r in regions.extract (c * chunk) ((c + 1) * chunk) do
        let p := r.filePath
        match ← (p.metadata.toBaseIO) with
        | .ok m => if limit ≤ m.modified then return some s!"{p} was written during the build"
        | .error _ => return some s!"{p} is gone"
      return none
  for t in tasks do
    match ← IO.wait t with
    | .ok none => pure ()
    | .ok (some why) => return some why
    | .error e => return some s!"{e}"
  let entries : Array String := sp.toArray.map (·.toString)
  let mut roots : Std.HashMap String Nat := {}
  let mut k := 0
  for r in regions do
    let p := r.filePath.toString
    -- Consecutive regions are usually under the same entry.
    unless k < entries.size && p.startsWith (entries[k]! ++ "/") do
      let some k' := entries.findIdx? (fun e => p.startsWith (e ++ "/"))
        | return some s!"{p} is not under the search path"
      k := k'
    let rel := (p.drop (entries[k]!.length + 1)).toString
    let root := ((rel.splitOn "/").headD rel |>.splitOn ".").headD rel
    match roots[root]? with
    | none => roots := roots.insert root k
    | some k' => if k' != k then return some s!"{root} was found under two search path entries"
  for (root, found) in roots do
    let mut first : Option Nat := none
    for i in [:entries.size] do
      let e : FilePath := ⟨entries[i]!⟩
      if (← (e / root).isDir) || (← (e / (root ++ ".olean")).pathExists) then
        first := some i
        break
    if first != some found then
      return some s!"the search path now resolves {root} elsewhere"
  return none

/-- What `buildFileImporting` did. -/
inductive BuildImport where
  /-- The file's header was imported while `lake build` ran, and that import
  is still current: the caller elaborates the body (`elaborateFileBody`). -/
  | imported (header : FileHeaderImport)
  /-- The build ran but no import was made in this process (the reason is
  given): load the file as after `buildFile` (`getFileEnvCore`). -/
  | notAttempted (why : String)
  /-- The build ran, but the import made alongside it read files that Lake
  replaced afterwards (or it could not be confirmed). This process must not
  import the file again: the first import's files stay mapped at their fixed
  addresses, so a second import would be read into memory instead (the whole
  import's size again, in anonymous memory), and the module initializers the
  first one ran would not run again. Start over in a fresh process. -/
  | stale (why : String)

/-- What the import attempted alongside `lake build` came to. -/
inductive AlongsideImport where
  | skipped (why : String)
  | failed (why : String)
  | done (imported : FileHeaderImport) (sp : SearchPath) (before : IO.FS.SystemTime)

/-- `buildFile` followed by the import of the file's header, with the import
made while `lake build` is still running (it needs only the search path, whose
query `buildFileWith` runs alongside the build); on a Mathlib no-op build this
takes the ~2.4 s import off the critical path. The result says whether the
import can be used (`BuildImport`).

The import is attempted only when no file it reads can be seen half written,
and when every change Lake can make to those files gives them a fresh
modification time (`importStillCurrent` relies on it). Lean, `leanir` and
`leantar` replace an `.olean` by renaming a complete, freshly written
temporary file over it, but Lake restores an artifact from its artifact cache
by a hard link (keeping the cached file's old time) or, if that fails, by
`copyFile`, which writes the file in place at its final path; and a truncated
`.olean` makes the importing process crash (SIGSEGV), not fail. So nothing is
imported alongside the build if Lake's cache directory (`LAKE_CACHE_DIR` as
`lake env` reports it) has an `artifacts` or `outputs` directory to restore
from. The reference time for `importStillCurrent` is taken right before
`lake build` starts, in the workspace's `.lake` (on the file system Lake writes
to); a workspace without one, which Lake has not set up yet, has nothing to
import alongside. `IX_IMPORT_ALONGSIDE_BUILD=0` turns the overlap off
(`buildFile`, then the caller imports as before). -/
def buildFileImporting (path : FilePath) : IO BuildImport := do
  let path ← IO.FS.realPath path
  if (← IO.getEnv "IX_IMPORT_ALONGSIDE_BUILD") == some "0" then
    buildFile path
    return .notAttempted "IX_IMPORT_ALONGSIDE_BUILD=0"
  let takeTime (root : FilePath) : IO (Option IO.FS.SystemTime) := do
    let dir := root / ".lake"
    unless ← dir.isDir do return none
    try return some (← fileSystemNow dir) catch _ => return none
  let (attempt, undisturbed) ← buildFileWith path #["LEAN_PATH", "LAKE_CACHE_DIR"] takeTime
      fun before? answer => show IO AlongsideImport from do
    let some before := before?
      | return .skipped "no writable .lake directory to take the time in"
    let .ok (0, stdout) := answer
      | return .skipped "the search-path query failed"
    let lines := stdout.splitOn "\n"
    let cacheDir := lines[1]?.getD ""
    if cacheDir.isEmpty then
      return .skipped "Lake reported no cache directory"
    let cache : FilePath := cacheDir
    if (← (cache / "artifacts").pathExists) || (← (cache / "outputs").pathExists) then
      return .skipped s!"Lake may restore artifacts from {cacheDir} into place"
    try
      let paths := ((lines[0]?.getD "").trimAscii.toString.splitOn ":").map FilePath.mk
      initSearchPath (← findSysroot) paths
      let imported ← importFileHeader path "import (alongside lake build)"
      return .done imported (← searchPathRef.get) before
    catch e =>
      return .failed s!"{e}"
  match attempt with
  | .skipped why => return .notAttempted why
  | .failed err => return .stale s!"the import failed: {err}"
  | .done imported sp before =>
    if !undisturbed then
      return .stale "the workspace configuration changed during the build"
    if imported.messages.hasErrors then
      return .stale "the import failed while Lake was building"
    let start ← IO.monoMsNow
    let why? ← importStillCurrent imported.env sp before
    leanPhaseLine "check the import against the built workspace" start
    match why? with
    | none => return .imported imported
    | some why => return .stale why

def runCore (f : CoreM α) (env : Environment) : IO α :=
  Prod.fst <$> f.toIO { fileName := default, fileMap := default } { env }

def runMeta (f : MetaM α) (env : Environment) : IO α :=
  Prod.fst <$> f.toIO { fileName := default, fileMap := default } { env }

def metaMakeList (α: Lean.Expr) (names: List Lean.Name) : MetaM Expr := do
  let nil <- Meta.mkAppOptM ``List.nil #[.some α]
  names.foldrM (fun n t => Meta.mkAppOptM ``List.cons #[.some α, mkConst n, t]) nil

def metaMakeDef [Lean.ToExpr α] (a: α) : MetaM (List Lean.Name × Lean.Expr × Lean.Expr) := do
  let val := Lean.toExpr a
  let typ <- Meta.inferType val
  let lvls := (Lean.collectLevelParams default typ).params.toList
  return (lvls, typ, val)

def metaMakeEvalClaim (func: Lean.Name) (args : List Lean.Expr)
  : MetaM (List Lean.Name × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let input <- Meta.mkAppM func args.toArray
  let output <- Meta.reduce input
  let type <- Meta.inferType output
  let sort <- Meta.inferType type
  let lvls := (Lean.collectLevelParams default input).params.toList
  return (lvls, input, output, type, sort)

end
