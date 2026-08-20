module
public import Lean.Meta.Reduce
public import Ix.Address
public import Ix.CompileM
public import Batteries.Data.String

public section

open Lean

open System (FilePath)

/-- Initialize Lean's module search path.

When `cwd` is provided, query `lake env printenv LEAN_PATH` from that directory
unconditionally — the caller is loading a file from a specific lake project, and
the inherited `LEAN_PATH` (e.g., set by an outer `lake exe ix` invocation) would
point at the wrong project's packages. When `cwd` is `none`, honor the inherited
`LEAN_PATH` if set, falling back to querying lake in the current directory. -/
def initLeanSearchPath (cwd : Option FilePath := none) : IO Unit := do
  -- If a target cwd is supplied, always query that cwd's LEAN_PATH.
  -- Otherwise, trust the inherited LEAN_PATH when present.
  if cwd.isSome || (← IO.getEnv "LEAN_PATH").isNone then
    let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd }
    let paths := out.stdout.trimAscii.toString.splitOn ":" |>.map FilePath.mk
    initSearchPath (← findSysroot) paths
  else
    initSearchPath (← findSysroot)

/-- A file's elaborated environment plus whether its header declares `module`. -/
structure FileEnv where
  env : Environment
  isModule : Bool

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
  initLeanSearchPath path.parent
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- Required for `processHeaderCore`'s `loadExts := true` import; a completed
  -- import resets the flag, so it is re-armed before every import.
  unsafe enableInitializersExecution
  let (env, messages) ← processHeaderCore
    (HeaderSyntax.startPos header) (HeaderSyntax.imports header)
    (isModule := false) default messages inputCtx 0
  if messages.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← messages.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)
  -- Elaborate the file body too, so the env contains the file's own
  -- definitions and not just its imports. Classic elaboration accepts
  -- module-syntax bodies (`public def` etc.) and yields their real content.
  let env := env.setMainModule default
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages)
  let cmdMessages := s.commandState.messages
  if cmdMessages.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← cmdMessages.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)
  return ⟨s.commandState.env, HeaderSyntax.isModule header⟩

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
  initLeanSearchPath path.parent
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, _, messages) ← Parser.parseHeader inputCtx
  if !HeaderSyntax.isModule header then return none
  unsafe enableInitializersExecution  -- re-armed per import; see `getFileEnvCore`
  let (env, messages) ← processHeaderCore
    (HeaderSyntax.startPos header) (HeaderSyntax.imports header)
    (isModule := true) default messages inputCtx 0
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
    let mathlibBuild := root / ".lake" / "packages" / "mathlib" / ".lake" / "build"
    if ← mathlibBuild.pathExists then
      println! "Mathlib cache already present, skipping fetch."
      return
    println! "Detected Mathlib dependency. Fetching Mathlib cache..."
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["exe", "cache", "get"]
      cwd := cwd
      stdout := .inherit
      stderr := .inherit
    }
    let exitCode ← child.wait
    if exitCode != 0 then
      throw $ IO.userError "lake exe cache get failed"

/-- Walk up from `start` looking for `lake-manifest.json`. -/
partial def findLakeRoot (start : FilePath) : IO (Option FilePath) := do
  if ← (start / "lake-manifest.json").pathExists then
    return some start
  match start.parent with
  | none => return none
  | some p => if p == start then return none else findLakeRoot p

/-- Walk up from `cur` collecting directory names until reaching `root`,
yielding the path components between them (in top-down order). -/
partial def collectRelParts (root cur : FilePath) (acc : List String) : Option (List String) :=
  if cur == root then some acc
  else match cur.fileName, cur.parent with
    | some name, some par =>
      if par == cur then none else collectRelParts root par (name :: acc)
    | _, _ => none

/-- Build the Lean module at the given file path using Lake.
Also fetches Mathlib cache if the project depends on it. -/
def buildFile (path : FilePath) : IO Unit := do
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
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", moduleName]
    cwd := root
    stdout := .inherit
    stderr := .inherit
  }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw $ IO.userError "lake build failed"

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
