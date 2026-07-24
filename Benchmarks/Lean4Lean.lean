import Cli
import Lean4Lean.Environment
import Ix.Meta
import Ix.TracingTexray
import Ix.Benchmark.Results
import Ix.Cli.ConstsFile

/-!
# lean4lean typecheck benchmark

Benchmarks the reference Lean4-in-Lean4 kernel —
[lean4lean](https://github.com/digama0/lean4lean), required by the lakefile
at a pinned rev — over the same library envs the other kernel backends
measure (`Benchmarks/Compile/Compile<Lib>.lean`). It is the external
yardstick for the Ix kernels: `ix check-rs` (Rust, the `ooc` backend) and
`ix check-lean` (pure-Lean `Ix.Tc`) check the serialized `.ixe` of an env;
this tool has lean4lean check the same library from its `.olean`s.

```
lake exe bench-lean4lean <path-to-env.lean> [flags]

  <path>                the env's Lean source, same input `ix compile` takes
                        (e.g. `Benchmarks/Compile/CompileInitStd.lean`). Its
                        lake project supplies the module search path; the
                        module set is the file's transitive import closure.
  --consts <n1,n2,…>    per-constant mode: replay each named constant's whole
                        transitive closure into a fresh kernel environment —
                        one row per name, the lean4lean counterpart of the ooc
                        backend's full-closure rows. Same flag/shape as
                        `ix check-rs --consts`.
  --consts-file <path>  additionally read names from a file (one per line,
                        `#` comments ignored). Unions with --consts.
  --json <path>         write benchmark results rows to <path> (the shared
                        row contract, `Ix.Benchmark.Results`).
  --json-name <name>    row key for the whole-library row (default: the
                        file's stem). The orchestrator passes the env name.
  --no-build            skip the `lake build` of the env module (for callers
                        that know the oleans are fresh).
  --verbose             print each declaration as it is added.
```

Without `--consts` the tool measures the **whole library**: every module in
the import closure is replayed through lean4lean — each module's new
constants are re-checked against its imports, one `IO.asTask` per module —
upstream `lake exe lean4lean`'s default mode, i.e. the canonical "how does
lean4lean perform on this library" number. Two driver divergences from
upstream, both required to run at all on this toolchain (the kernel itself
is untouched): duplicated cross-module realizations are skipped instead of
spuriously rejected, and only import regions are freed per task — the
stock binary segfaults freeing a module's own parts (see
`replayFromImports` for both). The row
carries `check-time` (wall over the sweep), `constants` (Σ declarations
added), `throughput` (constants/s), `peak-rss`. Caveats for cross-kernel
reading: lean4lean trusts `.olean` loading for a module's *imports* (every
constant is still checked exactly once, in its home module's task), its
parallelism unit is the module (tune with `LEAN_NUM_THREADS`), the
constant count is Lean declarations rather than Ixon constants — compare
end-to-end library numbers, not per-constant arithmetic — and auto-generated
lemmas that v4.29 multi-part oleans materialize in several modules are
checked once and skipped as duplicates thereafter (see `replayFromImports`;
upstream re-declares and spuriously rejects them).

A kernel rejection writes the row as `{"status": "rejected"}` (no metrics —
a rejection is a correctness signal, not a benchmark datum) and the run
exits with the reserved code 3; a missing `.olean` is an infrastructure
error (exit 1) detected before any timed window. Rows are flushed after
every result, so a killed run keeps the rows measured so far.

The replay machinery (`Context`/`State`/`replayConstant`/`replay`,
`replayFromImports`) is adapted from lean4lean's own `Main.lean`
(Apache 2.0, © the lean4lean authors) at the pinned rev — kept in lockstep
with the require so both sides agree on `Lean4Lean.addDecl`'s surface.
-/

open Lean hiding Environment Exception
open Kernel

namespace BenchLean4Lean

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants (c : ConstantInfo) : NameSet :=
  getUsedConstants' c.type ++ match c.value? with
  | some v => getUsedConstants' v
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => getUsedConstants' val.value
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  verbose := false
  checkQuot := true

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  numAdded : Nat := 0
  hasStrings := false

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def mapEnvM [Monad m] (ex : Exception) (f : Environment → m Environment) : m Exception := do
  match ex with
  | .unknownConstant env c => return .unknownConstant (← f env) c
  | .alreadyDeclared env c => return .alreadyDeclared (← f env) c
  | .declTypeMismatch env d t => return .declTypeMismatch env d t
  | .declHasMVars env c e => return .declHasMVars (← f env) c e
  | .declHasFVars env c e => return .declHasFVars (← f env) c e
  | .funExpected env lctx e => return .funExpected (← f env) lctx e
  | .typeExpected env lctx e => return .typeExpected (← f env) lctx e
  | .letTypeMismatch env lctx n t1 t2 => return .letTypeMismatch (← f env) lctx n t1 t2
  | .exprTypeMismatch env lctx e t => return .exprTypeMismatch (← f env) lctx e t
  | .appTypeMismatch env lctx e fn arg => return .appTypeMismatch (← f env) lctx e fn arg
  | .invalidProj env lctx e => return .invalidProj (← f env) lctx e
  | .thmTypeIsNotProp env c t => return .thmTypeIsNotProp (← f env) c t
  | .other _
  | .deterministicTimeout
  | .excessiveMemory
  | .deepRecursion
  | .interrupted => return ex

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Exception) : M α := do
  let options := pp.match.set (pp.rawOnError.set {} true) false
  -- The replayed environment has no extension state, so it cannot back the
  -- pretty printer; a fresh empty environment is good enough for basic
  -- printing of the offending declaration.
  let env ← mkEmptyEnvironment
  let ex ← mapEnvM ex fun _ => return env.toKernelEnv
  Prod.fst <$> (Lean.Core.CoreM.toIO · { fileName := "", options, fileMap := default } { env }) do
    Lean.throwKernelException ex

def declName : Declaration → String
  | .axiomDecl d => s!"axiomDecl {d.name}"
  | .defnDecl d => s!"defnDecl {d.name}"
  | .thmDecl d => s!"thmDecl {d.name}"
  | .opaqueDecl d => s!"opaqueDecl {d.name}"
  | .quotDecl => s!"quotDecl"
  | .mutualDefnDecl d => s!"mutualDefnDecl {d.map (·.name)}"
  | .inductDecl _ _ d _ => s!"inductDecl {d.map (·.name)}"

/-- Add a declaration through the lean4lean kernel, possibly throwing a
    `KernelException`. -/
def addDecl (d : Declaration) : M Unit := do
  if (← read).verbose then
    println! "adding {declName d}"
  let t1 ← IO.monoMsNow
  match Lean4Lean.addDecl (← get).env d true with
  | .ok env =>
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      println! "{declName d}: lean4lean took {t2 - t1}ms"
    modify fun s => { s with env, numAdded := s.numAdded + 1 }
  | .error ex =>
    throwKernelException ex

def hasStrLit (e : Expr) : Bool := (e.find? (·.isStringLit)).isSome

def constHasStrLit (ci : ConstantInfo) : Bool :=
  hasStrLit ci.type || ci.value?.any hasStrLit

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

Then construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    let mut usedConstants := getUsedConstants ci
    -- We want `String.ofList` to be available when encountering string literals.
    unless (← get).hasStrings do
      if constHasStrLit ci then
        usedConstants := usedConstants.insert ``String.ofList
        usedConstants := usedConstants.insert ``Char.ofNat
        modify ({· with hasStrings := true })
    replayConstants usedConstants
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      let addDeclAt (d : Declaration) :=
        try addDecl d catch e => throw <| IO.userError s!"at {name}: {e.toString}"
      match ci with
      | .defnInfo   info => addDeclAt (.defnDecl   info)
      | .thmInfo    info => addDeclAt (.thmDecl    info)
      | .axiomInfo  info => addDeclAt (.axiomDecl  info)
      | .opaqueInfo info => addDeclAt (.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| (← read).newConstants[n]!
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure (← read).newConstants[n]!)
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants (getUsedConstants ctor)
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDeclAt (.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ => addDeclAt .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

end BenchLean4Lean

deriving instance BEq for ConstantVal
deriving instance BEq for ConstructorVal
deriving instance BEq for RecursorRule
deriving instance BEq for RecursorVal

namespace BenchLean4Lean

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.constants.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      unless info == info' do throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.constants.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      unless info == info' do throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

/-- Check that at the end of (any) file, the quotient module is initialized.
(It will already be initialized at the beginning, unless this is the very
first file, which is responsible for initializing it.) -/
def checkQuotInit : M Unit := do
  unless (← get).env.quotInit do
    throw <| IO.userError s!"initial import (Init.Prelude) didn't initialize quotient module"

/-- "Replay" some constants into an `Environment`, sending them to the
    lean4lean kernel for checking. Returns the number of declarations added
    and the final environment. -/
def replay (ctx : Context) (env : Environment) (decl : Option Name := none) :
    IO (Nat × Environment) := do
  let mut remaining : NameSet := ∅
  for (n, ci) in ctx.newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := ctx) do
      match decl with
      | some d => replayConstant d
      | none =>
        for n in remaining do
          replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
      if (← read).checkQuot then checkQuotInit
  return (s.numAdded, s.env)

/-- Read a module's olean parts (base + server + private when present),
    most complete last — the shape `readModuleDataParts` and the
    toolchain's own `LeanChecker` frontend use. Shared by the closure
    scanner and the replay tasks so both see the same (private-level)
    import set. Throws when the base olean is missing. -/
def readModuleParts (module : Name) : IO (Array (ModuleData × CompactedRegion)) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  readModuleDataParts fnames

open private ImportedModule.mk from Lean.Environment in
/-- Replay one module's new constants against its (trusted-loaded) imports —
    upstream `lake exe lean4lean`'s per-module unit of work. -/
unsafe def replayFromImports (module : Name) (verbose := false) : IO Nat := do
  let parts ← readModuleParts module
  let some (mod, _) := parts[parts.size - 1]? | unreachable! -- load private module data
  let (_, s) ← (importModulesCore mod.imports).run
  let env ← match Kernel.Environment.finalizeImport s mod.imports module 0 with
    | .ok env => pure env
    | .error e => throw <| .userError <| ← (e.toMessageData {}).toString
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    -- v4.29 multi-part oleans can materialize the same auto-generated
    -- lemma (`*.eq_1`, `*.congr_simp`, …) in several modules' parts; a
    -- real import dedups those realizations in `finalizeImport`, so the
    -- replay must skip names the imported env already provides instead of
    -- re-declaring them (upstream replays them and spuriously rejects,
    -- e.g. on v4.29 Std).
    if (env.constants.find? name).isNone then
      newConstants := newConstants.insert name ci
  let (n, env') ← replay { newConstants, verbose } env
  -- Free the task's IMPORT regions only (the memory that scales with the
  -- sweep: every task maps its whole import closure). Upstream also frees
  -- the module's own `parts` regions, which segfaults — reproducibly, in
  -- the stock `lean4lean` binary too on this toolchain (decref of
  -- persistent region objects after munmap at scope exit) — so the small
  -- per-module parts stay mapped: one copy of the library across the
  -- sweep, not one closure per task.
  (Environment.ofKernelEnv env').freeRegions
  pure n

/-- Replay every module of the library through lean4lean, one `IO.asTask`
    per module (parallelism follows the task pool, i.e. `LEAN_NUM_THREADS`).
    Callers pre-flight olean existence via `moduleClosure`, so a task
    failure here is a kernel rejection, not infrastructure. Returns the
    total declarations added plus per-module failures. -/
unsafe def replayLibrary (modules : Array Name) (verbose : Bool) :
    IO (Nat × Array (Name × String)) := do
  let mut tasks := #[]
  for m in modules do
    tasks := tasks.push (m, ← IO.asTask (replayFromImports m verbose))
  let mut added := 0
  let mut failures : Array (Name × String) := #[]
  for (m, t) in tasks do
    match t.get with
    | .error e => failures := failures.push (m, toString e)
    | .ok n => added := added + n
  return (added, failures)

/-- Transitive module closure of `roots`, discovered by scanning olean
    headers (private-level parts, so `private import`s are covered). No
    environment is imported here: the whole-library sweep's tasks free
    their compacted regions when done — upstream's memory bound — which is
    only sound while nothing else in the process shares mapped regions.
    The scanner's own header regions stay mapped (the returned `Name`s
    live inside them): one copy of the library's headers, not one per
    task. A missing olean throws here, before any timed window. -/
def moduleClosure (roots : Array Name) : IO (Array Name) := do
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  let mut stack : List Name := roots.toList
  repeat
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if seen.contains m then
        continue
      seen := seen.insert m
      order := order.push m
      let parts ← readModuleParts m
      let some (mod, _) := parts[parts.size - 1]? | unreachable!
      for imp in mod.imports do
        unless seen.contains imp.module do
          stack := imp.module :: stack
  return order

/-- Replay `target`'s whole transitive closure into a fresh kernel
    environment — the full-closure check semantics of the ooc backend's
    per-constant rows. Returns the closure size (declarations added). -/
def replayClosure (env : Lean.Environment) (newConstants : Std.HashMap Name ConstantInfo)
    (target : Name) (verbose : Bool) : IO Nat := do
  let _ := env
  (·.1) <$> replay { newConstants, verbose, checkQuot := false } (.empty default) (some target)

/-- Resolve a raw `--consts` string against the env: `toName` first, then a
    displayed-form scan (numeric/private components don't round-trip through
    `toName`) — the same fallback the other tools' resolvers use. -/
def resolveName (env : Lean.Environment) (raw : String) : Option Name :=
  let n := raw.toName
  if env.constants.contains n then some n
  else env.constants.fold (init := none) fun acc cn _ =>
    acc <|> if toString cn == raw then some cn else none

open Ix.Benchmark.Results in
unsafe def runBenchCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to the env's Lean source (e.g. Benchmarks/Compile/CompileInitStd.lean)"
      return exitUsage
  let path := pathArg.as! String
  let jsonOut : Option String := (p.flag? "json").map (·.as! String)
  let jsonName := ((p.flag? "json-name").map (·.as! String)).getD
    ((System.FilePath.mk path).fileStem.getD path)
  let verbose := p.hasFlag "verbose"
  let rawNames ← Ix.Cli.ConstsFile.gather p

  -- Build the env module first (outside every timed window). The file's
  -- lake project supplies the module search path — the same entry
  -- `ix compile` uses, so both backends accept the same registry
  -- `module` path.
  unless p.hasFlag "no-build" do buildFile path

  if rawNames.isEmpty then
    -- Whole-library mode. The import closure is enumerated by scanning
    -- olean headers — deliberately WITHOUT importing an environment into
    -- this process: the replay tasks free their compacted regions when
    -- done (upstream's memory bound, ~steady-state instead of the whole
    -- library's fixed-up regions accumulating), and those frees are only
    -- sound while no co-resident env shares mapped regions.
    initLeanSearchPath (← IO.FS.realPath path).parent
    let header ← Lean.parseImports' (← IO.FS.readFile path) path
    let modules ← moduleClosure (header.imports.map (·.module))
    IO.println s!"Loaded {path}: {modules.size} modules in the import closure"
    TracingTexray.startSampler
    -- Whole-library row: module-parallel replay of the import closure.
    IO.println s!"replaying {modules.size} modules through lean4lean …"
    (← IO.getStdout).flush
    TracingTexray.resetPeakTreeRss
    let t0 ← IO.monoNanosNow
    let (added, failures) ← replayLibrary modules verbose
    let t1 ← IO.monoNanosNow
    let secs := (t1 - t0).toFloat / 1e9
    let peak ← TracingTexray.peakTreeRssBytes
    if failures.isEmpty then
      if let some out := jsonOut then
        writeRow out jsonName "ok"
          [ ("check-time", jsonRound 6 secs)
          , ("constants", Lean.toJson added)
          , ("throughput", jsonRound 2 (if secs > 0 then added.toFloat / secs else 0))
          , ("peak-rss", Lean.toJson peak) ]
      IO.println s!"{jsonName}: checked {added} declarations in {secs}s \
        ({(added.toFloat / secs).toUInt64} consts/s)"
      return 0
    else
      for (m, e) in failures do
        IO.eprintln s!"❌ lean4lean REJECTED module {m}: {e}"
      if let some out := jsonOut then
        writeRow out jsonName "rejected" []
      return exitRejected
  else
    -- Per-constant mode: the elaborated file env supplies the constants
    -- map (`getFileEnv`, the same entry `ix compile` uses — it also sets
    -- the search path). Closure replays never free regions, so the
    -- co-resident env is fine here. Each row is the name's whole
    -- transitive closure into a fresh kernel env.
    let env ← getFileEnv path
    TracingTexray.startSampler
    let newConstants := env.constants.fold
      (init := ({} : Std.HashMap Name ConstantInfo)) fun m n ci => m.insert n ci
    let mut anyRejected := false
    let mut idx := 0
    for raw in rawNames do
      idx := idx + 1
      match resolveName env raw with
      | none => IO.eprintln s!"warning: {raw} not found in the env; skipping"
      | some target =>
        -- Announce BEFORE the replay (flushed): a kill mid-replay must
        -- leave the in-flight constant's name in the log.
        IO.println s!"  [{idx}/{rawNames.size}] replaying closure of {raw} …"
        (← IO.getStdout).flush
        TracingTexray.resetPeakTreeRss
        let t0 ← IO.monoNanosNow
        let res ← (replayClosure env newConstants target verbose).toBaseIO
        let t1 ← IO.monoNanosNow
        let secs := (t1 - t0).toFloat / 1e9
        let peak ← TracingTexray.peakTreeRssBytes
        match res with
        | .ok added =>
          if let some out := jsonOut then
            writeRow out raw "ok"
              [ ("check-time", jsonRound 6 secs)
              , ("constants", Lean.toJson added)
              , ("throughput", jsonRound 2 (if secs > 0 then added.toFloat / secs else 0))
              , ("peak-rss", Lean.toJson peak) ]
          IO.println s!"  {raw}: constants={added} check={secs}s"
        | .error e =>
          IO.eprintln s!"  ❌ {raw} FAILED TO TYPECHECK: {e}"
          if let some out := jsonOut then
            writeRow out raw "rejected" []
          anyRejected := true
    return if anyRejected then exitRejected else 0

end BenchLean4Lean

unsafe def benchLean4LeanCmd : Cli.Cmd := `[Cli|
  "bench-lean4lean" VIA BenchLean4Lean.runBenchCmd;
  "Benchmark the lean4lean reference kernel over a library env (whole-library module replay, or per-constant closures with --consts)"

  FLAGS:
    consts        : String; "Per-constant mode: comma-separated fully-qualified names, each replayed as its whole transitive closure into a fresh kernel env (the ooc backend's full-closure row shape). Same flag/shape as `ix check-rs --consts`."
    "consts-file" : String; "Additionally read constant names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    json          : String; "Write benchmark results rows to this path (shared row contract). Off by default."
    "json-name"   : String; "Row key for the whole-library row (default: the file stem; the orchestrator passes the registry env name)."
    "no-build";             "Skip the `lake build` of the env module (callers that know the oleans are fresh)."
    verbose;                "Print each declaration as it is added."

  ARGS:
    path : String; "Path to the env's Lean source, e.g. Benchmarks/Compile/CompileInitStd.lean (same input as `ix compile`)"
]

