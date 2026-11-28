import Lean.CoreM
import Lean.Replay

/-! # Full-closure kernel replay (`Scripts/KernelReplay.lean`)

Re-checks with Lean's kernel every declaration of every project module in the
import closure of the given roots, so that a declaration that entered an
`.olean` without a kernel check (`debug.skipKernelTC`, `addDeclWithoutChecking`,
an unchecked `@[csimp]` theorem) fails the gate wherever it sits below an audit
module, not only when it sits in the module a gate names.

`leanchecker M` (Lean 4.34.1, `src/lean/LeanChecker.lean`) replays the modules
whose name has `M` as a prefix, each on top of its imports read from `.olean`
files; the imports themselves are not replayed. A gate that names only leaf
audit modules therefore checks only those modules. This script computes the
import closure of its roots from the `.olean` headers and replays every
project module in it, one module at a time, each with the toolchain's own
`replayFromImports` (copied verbatim below, with a count of the constants it
replays). Modules are replayed in worker processes (`--jobs`), a batch of
modules per process (`--batch`), so memory stays bounded.

What is not replayed: modules of the toolchain and of third-party dependencies
(`dependencyRoots`: `Init`, `Std`, `Lean`, `Lake`, `Mathlib`, `Batteries`, …),
whose `.olean` files come from the pinned toolchain and Mathlib's cache.
`--include-deps` replays them too. Every other module in the closure is
replayed, so a new project library is covered without editing this file.

The `.olean` files must be up to date with the sources: run the build of the
roots first (CI does, in the same job). A root or closure module without an
`.olean` fails the gate.

Usage (from the workspace root, inside `lake env`):

  lean --run Scripts/KernelReplay.lean [--jobs N] [--batch N] [--include-deps]
      [--tree DIR:PREFIX]... [--list] [--self PATH] ROOT...
  lean --run Scripts/KernelReplay.lean --worker MODULE...

  ROOT              a module name; its whole import closure is replayed.
  --tree DIR:PREFIX every `.lean` file under DIR (skipping `.lake` and
                    `lakefile.lean`) is a root, named PREFIX plus its path
                    below DIR (`--tree IxCK/Kernel:IxCK.Kernel`).
  --list            print the selected modules and exit without replaying.
  --self PATH       this script's path, for the workers (default
                    `Scripts/KernelReplay.lean`).
  --worker          replay exactly the given modules in this process (the
                    worker mode the main mode spawns).

Each replayed module prints `REPLAY <module> OK consts=<n> <ms>ms` or
`REPLAY <module> FAIL <error>`. The exit code is 0 only when every selected
module printed `OK`.
-/

open Lean

namespace KernelReplay

/-- Root components of modules that belong to the toolchain or to third-party
dependencies, which the gate does not replay unless `--include-deps` is given. -/
def dependencyRoots : List String :=
  ["Init", "Std", "Lean", "Lake", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets",
   "Plausible", "ImportGraph", "LeanSearchClient"]

def isDependency (m : Name) : Bool :=
  dependencyRoots.contains m.getRoot.toString

/-! ## Worker: replay exactly the named modules -/

/-- The toolchain's `replayFromImports` (Lean 4.34.1 `src/lean/LeanChecker.lean`),
returning the number of constants replayed. -/
unsafe def replayOne (module : Name) : IO Nat := do
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
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let n := newConstants.size
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions
  return n

unsafe def worker (mods : List String) : IO UInt32 := do
  let mut bad := 0
  for a in mods do
    let t0 ← IO.monoMsNow
    try
      let n ← replayOne a.toName
      IO.println s!"REPLAY {a} OK consts={n} {(← IO.monoMsNow) - t0}ms"
    catch e =>
      bad := bad + 1
      let msg := (toString e).replace "\n" " "
      IO.println s!"REPLAY {a} FAIL {msg}"
    (← IO.getStdout).flush
  return if bad == 0 then 0 else 1

/-! ## Main: the closure of the roots, replayed in worker processes -/

/-- The modules `m` imports, read from its `.olean` header. The mapped region
is not freed: the names live in it, and the main process reads only headers. -/
unsafe def importsOf (m : Name) : IO (Array Name) := do
  let mFile ← findOLean m
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {m} does not exist (build it first)"
  let parts ← readModuleDataParts #[mFile]
  if h : parts.size = 0 then throw <| IO.userError s!"failed to read module data of {m}" else
  return parts[0].1.imports.map (·.module)

/-- The import closure of `roots`, roots included, in a deterministic order. The
imports of a module for which `expand` is false (a dependency) are not read:
no dependency imports a project module. -/
unsafe def closure (roots : Array Name) (expand : Name → Bool) : IO (Array Name) := do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut out : Array Name := #[]
  while true do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      seen := seen.insert m
      out := out.push m
      if expand m then
        for i in ← importsOf m do
          unless seen.contains i do todo := i :: todo
  return out.qsort (·.toString < ·.toString)

/-- The non-empty components of a path. -/
def comps (p : System.FilePath) : List String :=
  p.components.filter (fun c => c != "" && c != ".")

/-- The modules of the `.lean` files under `dir`, named `pfx` plus their path
below `dir`; `.lake` directories and `lakefile.lean` are skipped. -/
def treeModules (dir : System.FilePath) (pfx : Name) : IO (Array Name) := do
  unless ← dir.isDir do
    throw <| IO.userError s!"--tree: {dir} is not a directory"
  let files ← dir.walkDir fun d => return d.fileName != some ".lake"
  let dc := comps dir
  let mut out := #[]
  for f in files do
    if f.extension != some "lean" || f.fileName == some "lakefile.lean" then continue
    let fc := comps f
    unless fc.take dc.length == dc do
      throw <| IO.userError s!"--tree: {f} is not below {dir}"
    let rel := fc.drop dc.length
    let some last := rel.getLast? | continue
    let parts := rel.dropLast ++ [String.ofList (last.toList.take (last.length - 5))]
    out := out.push (parts.foldl Name.str pfx)
  return out.qsort (·.toString < ·.toString)

structure Options where
  roots : Array Name := #[]
  trees : Array (System.FilePath × Name) := #[]
  jobs : Nat := 4
  batch : Nat := 12
  includeDeps : Bool := false
  list : Bool := false
  self : String := "Scripts/KernelReplay.lean"

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--include-deps" :: rest, o => parse rest { o with includeDeps := true }
  | "--list" :: rest, o => parse rest { o with list := true }
  | "--jobs" :: v :: rest, o =>
    match v.toNat? with
    | some n => if n == 0 then .error "--jobs must be positive" else parse rest { o with jobs := n }
    | none => .error s!"--jobs: not a number: {v}"
  | "--batch" :: v :: rest, o =>
    match v.toNat? with
    | some n => if n == 0 then .error "--batch must be positive" else parse rest { o with batch := n }
    | none => .error s!"--batch: not a number: {v}"
  | "--self" :: v :: rest, o => parse rest { o with self := v }
  | "--tree" :: v :: rest, o =>
    match v.splitOn ":" with
    | [d, p] =>
      if d.isEmpty || p.isEmpty then .error s!"--tree takes DIR:PREFIX, got {v}"
      else parse rest { o with trees := o.trees.push (d, p.toName) }
    | _ => .error s!"--tree takes DIR:PREFIX, got {v}"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown option {a}"
    else
      let m := a.toName
      if m.isAnonymous then .error s!"not a module name: {a}"
      else parse rest { o with roots := o.roots.push m }

/-- The result of one worker process: the `REPLAY` lines it printed and its exit code. -/
structure BatchResult where
  mods : Array Name
  lines : Array String
  exitCode : UInt32
  stderr : String

def runBatch (self : String) (mods : Array Name) : IO BatchResult := do
  let lean ← IO.appPath
  let out ← IO.Process.output {
    cmd := lean.toString
    args := #["--run", self, "--worker"] ++ mods.map (·.toString) }
  let lines := (out.stdout.splitOn "\n").toArray.filter (·.startsWith "REPLAY ")
  return { mods, lines, exitCode := out.exitCode, stderr := out.stderr }

unsafe def main (o : Options) : IO UInt32 := do
  let mut roots := o.roots
  for (dir, pfx) in o.trees do
    roots := roots ++ (← treeModules dir pfx)
  if roots.isEmpty then
    IO.eprintln "[kernel-replay] no roots given"
    return 2
  let all ← closure roots fun m => o.includeDeps || !isDependency m
  let selected := all.filter fun m => o.includeDeps || !isDependency m
  let skipped := all.size - selected.size
  let rootsSet : NameSet := roots.foldl (·.insert ·) {}
  for r in roots do
    if isDependency r && !o.includeDeps then
      IO.eprintln s!"[kernel-replay] root {r} is a dependency module; pass --include-deps to replay it"
      return 2
  IO.println s!"[kernel-replay] {roots.size} roots; import closure {all.size} modules; \
    replaying {selected.size} ({skipped} toolchain/third-party modules not replayed: \
    {dependencyRoots})"
  if o.list then
    for m in selected do
      IO.println s!"{if rootsSet.contains m then "root " else "      "}{m}"
    return 0
  unless ← System.FilePath.pathExists o.self do
    IO.eprintln s!"[kernel-replay] cannot find this script at {o.self} (pass --self PATH)"
    return 2
  -- Batches of `o.batch` modules, handed out to `o.jobs` lanes from a shared queue.
  let mut batches : Array (Array Name) := #[]
  let mut i := 0
  while i < selected.size do
    batches := batches.push (selected.extract i (i + o.batch))
    i := i + o.batch
  let queue ← IO.mkRef batches.toList
  let t0 ← IO.monoMsNow
  let lane : IO (Array BatchResult) := do
    let mut acc := #[]
    while true do
      let next ← queue.modifyGet fun q => (q.head?, q.tail)
      match next with
      | none => break
      | some mods =>
        let r ← runBatch o.self mods
        for l in r.lines do
          if (l.splitOn " ").getD 2 "" != "OK" then IO.println l
        acc := acc.push r
    return acc
  let mut tasks := #[]
  for _ in [0:o.jobs] do
    tasks := tasks.push (← IO.asTask lane (prio := .dedicated))
  let mut results : Array BatchResult := #[]
  for t in tasks do
    match t.get with
    | .ok rs => results := results ++ rs
    | .error e =>
      IO.eprintln s!"[kernel-replay] a worker lane failed: {e}"
      return 1
  -- Every selected module must have printed exactly one `OK` line.
  let mut ok : NameSet := {}
  let mut failed : Array String := #[]
  let mut consts := 0
  for r in results do
    for l in r.lines do
      match l.splitOn " " with
      | _ :: m :: "OK" :: c :: _ =>
        ok := ok.insert m.toName
        consts := consts + ((c.dropPrefix? "consts=").bind (·.toString.toNat?)).getD 0
      | _ :: m :: _ => failed := failed.push s!"{m}: {l}"
      | _ => pure ()
    if r.exitCode != 0 && !r.stderr.isEmpty then
      IO.eprintln s!"[kernel-replay] worker for {r.mods.size} modules exited {r.exitCode}: \
        {String.ofList (r.stderr.toList.take 2000)}"
  let missing := selected.filter (!ok.contains ·)
  let secs := ((← IO.monoMsNow) - t0) / 1000
  if missing.isEmpty then
    IO.println s!"[kernel-replay] OK: {selected.size} modules, {consts} constants replayed \
      in {secs}s ({o.jobs} workers)"
    return 0
  IO.eprintln s!"[kernel-replay] FAILED: {missing.size} of {selected.size} modules not replayed \
    successfully ({secs}s)"
  for f in failed do IO.eprintln s!"    {f}"
  for m in missing do
    unless failed.any (·.startsWith s!"{m}:") do
      IO.eprintln s!"    {m}: no result (worker crashed or was killed)"
  return 1

end KernelReplay

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | "--worker" :: mods => KernelReplay.worker mods
  | _ =>
    match KernelReplay.parse args {} with
    | .error e =>
      IO.eprintln s!"[kernel-replay] {e}"
      return 2
    | .ok o => KernelReplay.main o
