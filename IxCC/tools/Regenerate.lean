import Lean
import Std.Sync.Mutex

/-!
# Regenerate every IxCC fixture, table, and generated module

Pure Lean 4 replacement for `IxCC/tools/regenerate.sh`.

Regenerates every fixture, table, and generated module that this repository's
`ix` determines (`docs/corpus.md`, "Refreezing"), either in place or (`--check`)
in a scratch export of `HEAD`, and reports per file whether the result equals
what is committed.

## Usage

```
lean --run IxCC/tools/Regenerate.lean [--check] [--work DIR] [--jobs N]
lean --run IxCC/tools/Regenerate.lean --selftest
```

Run from anywhere inside the repository, in ix's dev shell (`nix develop`),
with `ix` and the IxCC tools buildable.

* Without `--check`: rewrites the checkout in place (a refreeze; review with
  `git diff`, `docs/corpus.md`).
* With `--check`: leaves the checkout alone, regenerates into `WORK/tree`
  (an export of `HEAD`), lists every file that differs, then runs
  `IxCC/tools/Citations.lean --fixtures`; exits 0 only if nothing differs and
  nothing is cited ("current and self-contained").
* Not covered (not written by `ix`): `fixtures/ixon-v4/bench-k1/steps.json`
  (a measurement of compiled code: `check-steps`), `docs/`.
* Families are discovered dynamically from every `corpus.json` under
  `IxCC/fixtures/` and rebuilt in parallel up to `--jobs N` workers (default 10).
-/

namespace Regenerate

open System

def toolTargets : Array String := #[
  "corpus",
  "tests-own",
  "refreeze-ixon",
  "pin-src-tables",
  "gen-src-artifacts",
  "gen-recheck-artifacts",
  "tests-fir"
]

def tableCheckPaths : Array String := #[
  "IxCC/fixtures/ixon-v4",
  "IxCC/IxCC/Src/Pinned.lean",
  "IxCC/IxCC/Src/Syntax.lean",
  "IxCC/IxCC/Ixon/V3/PrimAddrs.lean"
]

/-! ## Pure helpers -/

def splitNonEmptyLines (s : String) : Array String :=
  ((s.splitOn "\n").map fun l =>
    if l.endsWith "\r" then String.ofList (l.toList.dropLast) else l)
    |>.filter (!·.isEmpty) |>.toArray

def splitNul (s : String) : Array String :=
  (s.splitOn "\x00").filter (!·.isEmpty) |>.toArray

/-- Extract module names from `^import <mod>` lines (matching `grep -h '^import ' | awk '{print $2}'`). -/
def parseImportedModules (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "import " then
      let rest := (line.dropPrefix? "import ").map (·.toString) |>.getD ""
      let parts := (rest.splitOn " ").flatMap (·.splitOn "\t")
        |>.map (fun p => p.trimAscii.toString)
        |>.filter (!·.isEmpty)
      if let some modName := parts.head? then
        out := out.push modName
  return out

/-- Single-quote a string safely for POSIX `/bin/sh`. -/
def shSingleQuote (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Render the runtime-only `lake` stand-in script written into `WORK/fake/lake`
(so `ix compile` asking `lake env printenv LEAN_PATH` gets the root workspace's `LEAN_PATH`). -/
def renderFakeLake (leanPath : String) : String :=
  s!"#!/bin/sh\n[ \"$*\" = \"env printenv LEAN_PATH\" ] && \{ printf '%s\\n' {shSingleQuote leanPath}; exit 0; }\nexit 1\n"

/-- Strip leading `"IxCC/"` from a repository-relative manifest path. -/
def stripIxccPrefix (p : String) : String :=
  match p.dropPrefix? "IxCC/" with
  | some rest => rest.toString
  | none => p

def manifestSlug (m : String) : String :=
  m.replace "/" "_"

/-! ## Subprocess & logging helpers -/

def die (msg : String) : IO α := do
  IO.eprintln s!"regenerate: {msg}"
  IO.Process.exit 1

def defaultEnv (extra : Array (String × Option String)) : Array (String × Option String) :=
  #[("GIT_TERMINAL_PROMPT", some "0")] ++ extra

def runCapture (cmd : String) (args : Array String)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd, env := defaultEnv env }

def runChecked (label cmd : String) (args : Array String)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO String := do
  let out ← runCapture cmd args cwd env
  unless out.exitCode == 0 do
    die s!"{label} failed (exit {out.exitCode}): {out.stderr}"
  return out.stdout

def runStep (label cmd : String) (args : Array String) (logPath : FilePath)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[])
    (appendLog : Bool := false) : IO Unit := do
  IO.println s!"== {label}"
  (← IO.getStdout).flush
  let t0 ← IO.monoMsNow
  let out ← runCapture cmd args cwd env
  let elapsed := (← IO.monoMsNow) - t0
  let secs := elapsed / 1000
  let logBody := out.stdout ++ out.stderr
  if appendLog && (← logPath.pathExists) then
    let prev ← IO.FS.readFile logPath
    IO.FS.writeFile logPath (prev ++ logBody)
  else
    IO.FS.writeFile logPath logBody
  IO.println s!"   ({secs} s, exit {out.exitCode})"
  (← IO.getStdout).flush
  unless out.exitCode == 0 do
    die s!"{label} failed ({logPath})"

def prependPath (dir : FilePath) : IO (String × Option String) := do
  let cur := (← IO.getEnv "PATH").getD ""
  return ("PATH", some s!"{dir}:{cur}")

def resolveLeanExe : IO String := do
  if let some l := ← IO.getEnv "LEAN" then
    if !l.isEmpty then return l
  let probe ← runCapture "lean" #["--version"]
  if probe.exitCode == 0 then return "lean"
  let app ← IO.appPath
  if let some dir := app.parent then
    let sibling := dir / "lean"
    if ← sibling.pathExists then return sibling.toString
  return app.toString

def discoverRootMods (root : FilePath) : IO (Array String) := do
  let out ← runChecked "git ls-files fixtures/*.lean" "git"
    #["-C", root.toString, "ls-files", "-z", "IxCC/fixtures/*.lean"]
  let mut seen : Std.HashSet String := {}
  let mut mods : Array String := #[]
  for rel in splitNul out do
    let text ← IO.FS.readFile (root / rel)
    for m in parseImportedModules text do
      if !seen.contains m then
        seen := seen.insert m
        let modFile := root / (m.replace "." "/" ++ ".lean")
        if ← modFile.pathExists then
          mods := mods.push m
  return mods.qsort (· < ·)

/-! ## Parallel corpus-family worker pool -/

structure RebuildOutcome where
  manifest : String
  ok : Bool
  logPath : FilePath

def rebuildFamiliesParallel (jobs : Nat) (manifests : Array String)
    (corpusBin ixBin fakeDir workDir logDir ixccDir : FilePath) (leanPath : String) :
    IO (Array RebuildOutcome) := do
  let nWorkers := Nat.min (Nat.max 1 jobs) manifests.size
  let nextIdx ← Std.Mutex.new (0 : Nat)
  let printLock ← Std.Mutex.new ()
  let mut tasks : Array (Task (Except IO.Error (Array RebuildOutcome))) :=
    Array.emptyWithCapacity nWorkers
  for _ in [0:nWorkers] do
    let t ← IO.asTask (prio := .dedicated) do
      let mut localResults : Array RebuildOutcome := #[]
      while true do
        let idx? ← nextIdx.atomically do
          let i ← get
          if i < manifests.size then
            set (i + 1)
            return some i
          else
            return none
        match idx? with
        | none => break
        | some i =>
          let m := manifests[i]!
          let slug := manifestSlug m
          let logPath := logDir / s!"rebuild-{slug}.log"
          let out ← runCapture corpusBin.toString
            #["rebuild", m,
              "--ix", ixBin.toString,
              "--ix-path", fakeDir.toString,
              "--work", (workDir / "rebuild" / slug).toString]
            (some ixccDir)
            #[("LEAN_PATH", some leanPath)]
          IO.FS.writeFile logPath (out.stdout ++ out.stderr)
          let ok := out.exitCode == 0
          printLock.atomically do
            if ok then
              IO.println s!"   {m} ok"
            else
              IO.println s!"   {m} FAILED (see {logPath})"
            (← IO.getStdout).flush
          localResults := localResults.push { manifest := m, ok, logPath }
      return localResults
    tasks := tasks.push t
  let mut all : Array RebuildOutcome := Array.emptyWithCapacity manifests.size
  for t in tasks do
    let part ← IO.ofExcept (← IO.wait t)
    all := all ++ part
  return all

/-! ## CLI parsing & main workflow -/

structure Config where
  check : Bool := false
  work : Option FilePath := none
  jobs : Nat := 10
  selftest : Bool := false
  showHelp : Bool := false
  deriving BEq, Repr

def usageText : String :=
  "usage: lean --run IxCC/tools/Regenerate.lean [--check] [--work DIR] [--jobs N] [--selftest]"

def parseArgs (args : List String) : Except String Config := do
  let rec go (cfg : Config) : List String → Except String Config
    | [] => .ok cfg
    | "--check" :: rest => go { cfg with check := true } rest
    | "--selftest" :: rest => go { cfg with selftest := true } rest
    | "--help" :: rest | "-h" :: rest => go { cfg with showHelp := true } rest
    | "--work" :: dir :: rest => go { cfg with work := some (FilePath.mk dir) } rest
    | "--work" :: [] => .error "--work requires a directory argument"
    | "--jobs" :: nStr :: rest =>
      match nStr.toNat? with
      | some n =>
        if n == 0 then .error "--jobs must be >= 1"
        else go { cfg with jobs := n } rest
      | none => .error s!"invalid --jobs value: {nStr}"
    | "--jobs" :: [] => .error "--jobs requires a numeric argument"
    | other :: _ => .error s!"unknown argument: {other}"
  go {} args

def runRegenerate (cfg : Config) : IO UInt32 := do
  let rootOut ← runChecked "git rev-parse" "git" #["rev-parse", "--show-toplevel"]
  let root ← IO.FS.realPath (FilePath.mk rootOut.trimAscii.toString)
  let workRaw := cfg.work.getD (root / "IxCC" / "plans" / "regenerate")
  IO.FS.createDirAll workRaw
  let work ← IO.FS.realPath workRaw
  let logDir := work / "logs"
  IO.FS.createDirAll logDir

  -- 0. Producer (`ix` + fixture-imported root modules), runtime `lake` stand-in, and IxCC tools
  let rootMods ← discoverRootMods root
  let rootModsDesc := if rootMods.isEmpty then "none" else " ".intercalate rootMods.toList
  IO.println s!"== the root modules the fixtures' sources import: {rootModsDesc}"
  runStep s!"lake build ix {if rootMods.isEmpty then "" else rootModsDesc}".trimAscii.toString
    "lake" (#["build", "ix"] ++ rootMods) (logDir / "ix-build.log") (some root)
  let ixBin := root / ".lake" / "build" / "bin" / "ix"

  let fakeDir := work / "fake"
  IO.FS.createDirAll fakeDir
  let leanPath := (← runChecked "lake env printenv LEAN_PATH" "lake"
    #["env", "printenv", "LEAN_PATH"] (some root)).trimAscii.toString
  let fakeLake := fakeDir / "lake"
  IO.FS.writeFile fakeLake (renderFakeLake leanPath)
  IO.setAccessRights fakeLake {
    user := { read := true, write := true, execution := true }
    group := { read := true, execution := true }
    other := { read := true, execution := true }
  }

  let rootIxcc := root / "IxCC"
  runStep s!"lake build {" ".intercalate toolTargets.toList}"
    "lake" (#["build"] ++ toolTargets) (logDir / "tools-build.log") (some rootIxcc)
  let binDir := rootIxcc / ".lake" / "build" / "bin"

  -- Target tree: checkout in place, or fresh git-tracked export of HEAD under WORK/tree
  let (treeDir?, ixccDir) ← if cfg.check then
    let tree := work / "tree"
    if ← tree.pathExists then
      die s!"{tree} exists; remove it or pass another --work"
    IO.FS.createDirAll tree
    let tarPath := work / "ixcc-head.tar"
    try
      let _ ← runChecked "git archive" "git"
        #["-C", root.toString, "archive", "--output", tarPath.toString, "HEAD", "IxCC"]
      let _ ← runChecked "tar extract" "tar" #["-xf", tarPath.toString, "-C", tree.toString]
    finally
      if ← tarPath.pathExists then IO.FS.removeFile tarPath
    let _ ← runChecked "git init" "git" #["-C", tree.toString, "init", "-q"]
    let _ ← runChecked "git add" "git" #["-C", tree.toString, "add", "-A"]
    let _ ← runChecked "git commit" "git"
      #["-C", tree.toString, "-c", "user.name=regenerate", "-c", "user.email=regenerate",
        "commit", "-qm", "HEAD"]
    pure (some tree, tree / "IxCC")
  else
    pure (none, rootIxcc)

  let fakePathEnv ← prependPath fakeDir

  -- 1. Tables first (census and ingress read them)
  let oldPrims ← runChecked "git show primitives.tsv" "git"
    #["-C", root.toString, "show", "HEAD:IxCC/fixtures/ixon-v4/primitives.tsv"]
  let oldPrimsPath := work / "old-primitives.tsv"
  IO.FS.writeFile oldPrimsPath oldPrims
  let oldSrcTables ← runChecked "git show src-tables.tsv" "git"
    #["-C", root.toString, "show", "HEAD:IxCC/fixtures/ixon-v4/src-tables.tsv"]
  let oldSrcTablesPath := work / "old-src-tables.tsv"
  IO.FS.writeFile oldSrcTablesPath oldSrcTables

  runStep "refreeze-ixon package" (binDir / "refreeze-ixon").toString
    #["package", "--ix-repo", root.toString, "--ix-revision", "HEAD"]
    (logDir / "package.log") (some ixccDir)
  runStep "refreeze-ixon tc-primitives" (binDir / "refreeze-ixon").toString
    #["tc-primitives", "--ix-repo", root.toString, "--ix-revision", "HEAD"]
    (logDir / "tc-primitives.log") (some ixccDir)
  runStep "pin-src-tables" (binDir / "pin-src-tables").toString
    #["--ix", ixBin.toString, "--work", (work / "src-tables").toString]
    (logDir / "src-tables.log") (some ixccDir) #[fakePathEnv]

  let repinLog := logDir / "repin.log"
  if ← repinLog.pathExists then IO.FS.removeFile repinLog
  for f in #["IxCC/Src/Pinned.lean", "IxCC/Src/Syntax.lean"] do
    runStep s!"pin-src-tables --repin {f}" (binDir / "pin-src-tables").toString
      #["--repin", f,
        "--old-primitives", oldPrimsPath.toString,
        "--old-tables", oldSrcTablesPath.toString]
      repinLog (some ixccDir) #[] (appendLog := true)

  match treeDir? with
  | some tree =>
    let stale ← runChecked "git status tables" "git"
      (#["-C", tree.toString, "status", "--porcelain", "--"] ++ tableCheckPaths)
    if !stale.trimAscii.toString.isEmpty then
      IO.println "The tables differ from the committed ones, so the tools built from the checkout are stale"
      IO.println "for the rest of the check: the fixtures are not current. Regenerate in place (without --check)."
      let shortStatus ← runChecked "git status --short" "git" #["-C", tree.toString, "status", "--short"]
      IO.print shortStatus
      return 1
  | none =>
    runStep s!"lake build (rebuild) {" ".intercalate toolTargets.toList}"
      "lake" (#["build"] ++ toolTargets) (logDir / "tools-rebuild.log") (some rootIxcc)

  -- 2. Every corpus family in parallel; then verdicts, RC inputs, fold, and roots-only fixtures
  let rawManifests ← runChecked "git ls-files corpus.json" "git"
    #["-C", root.toString, "ls-files", "IxCC/fixtures/**/corpus.json"]
  let manifests := (splitNonEmptyLines rawManifests).map stripIxccPrefix
  IO.FS.writeFile (work / "manifests") ("\n".intercalate manifests.toList ++ "\n")
  IO.println s!"== {manifests.size} families: {" ".intercalate manifests.toList}"
  let famStart ← IO.monoMsNow
  let outcomes ← rebuildFamiliesParallel cfg.jobs manifests
    (binDir / "corpus") ixBin fakeDir work logDir ixccDir leanPath
  let famSecs := ((← IO.monoMsNow) - famStart) / 1000
  let rebuildOutLines := outcomes.map fun o =>
    if o.ok then s!"   {o.manifest} ok" else s!"   {o.manifest} FAILED (see {o.logPath})"
  IO.FS.writeFile (work / "rebuild.out") ("\n".intercalate rebuildOutLines.toList ++ "\n")
  IO.println s!"   ({famSecs} s)"
  if outcomes.any (!·.ok) then
    die "a family did not rebuild"

  let withLeanPath : Array (String × Option String) := #[("LEAN_PATH", some leanPath)]
  runStep "tests-own verdicts" (binDir / "tests-own").toString
    #["verdicts", "--ix", ixBin.toString, "--ix-path", fakeDir.toString,
      "--work", (work / "verdicts").toString]
    (logDir / "verdicts.log") (some ixccDir) withLeanPath
  runStep "refreeze-ixon rc-real-source" (binDir / "refreeze-ixon").toString
    #["rc-real-source", "--ix", ixBin.toString, "--ix-path", fakeDir.toString,
      "--work", work.toString]
    (logDir / "rc.log") (some ixccDir) withLeanPath
  runStep "refreeze-ixon rc-budget" (binDir / "refreeze-ixon").toString
    #["rc-budget", "--ix", ixBin.toString, "--ix-path", fakeDir.toString,
      "--work", work.toString]
    (logDir / "rc-budget.log") (some ixccDir) withLeanPath
  runStep "refreeze-ixon rc-deep" (binDir / "refreeze-ixon").toString
    #["rc-deep", "--ix", ixBin.toString, "--ix-path", fakeDir.toString,
      "--work", work.toString]
    (logDir / "rc-deep.log") (some ixccDir) withLeanPath
  runStep "refreeze-ixon fold" (binDir / "refreeze-ixon").toString
    #["fold", "--ix", ixBin.toString, "--ix-path", fakeDir.toString,
      "--work", work.toString]
    (logDir / "fold.log") (some ixccDir) withLeanPath

  let noLeanPathFake : Array (String × Option String) := #[("LEAN_PATH", none), fakePathEnv]
  for (flag, dir, workSub, logName) in #[
    ("--diagnostics",   "fixtures/ixon-v4/src-diag",      "diag",          "diag.log"),
    ("--sortpoly",      "fixtures/ixon-v4/src-sortpoly",  "sortpoly",      "sortpoly.log"),
    ("--words",         "fixtures/ixon-v4/src-words",     "words",         "words.log"),
    ("--kernel-hints",  "fixtures/ixon-v4/kernel-hints",  "kernel-hints",  "kernel-hints.log"),
    ("--erased-blocks", "fixtures/ixon-v4/erased-blocks", "erased-blocks", "erased-blocks.log")
  ] do
    runStep s!"pin-src-tables {flag}" (binDir / "pin-src-tables").toString
      #["--ix", ixBin.toString, flag, dir, "--work", (work / workSub).toString]
      (logDir / logName) (some ixccDir) noLeanPathFake

  -- 3. Generated modules (generators read the tree's fixtures; LEAN_PATH unset)
  let noLeanPath : Array (String × Option String) := #[("LEAN_PATH", none)]
  runStep "gen-src-artifacts" (binDir / "gen-src-artifacts").toString #[]
    (logDir / "gen-src.log") (some ixccDir) noLeanPath
  runStep "gen-recheck-artifacts" (binDir / "gen-recheck-artifacts").toString #[]
    (logDir / "gen-recheck.log") (some ixccDir) noLeanPath
  runStep "corpus kernel-artifacts" (binDir / "corpus").toString #["kernel-artifacts"]
    (logDir / "kernel-artifacts.log") (some ixccDir) noLeanPath

  IO.println "== tests-fir --render-artifacts"
  let firStart ← IO.monoMsNow
  let firOut ← runCapture (binDir / "tests-fir").toString #["--render-artifacts"]
    (some ixccDir) noLeanPath
  let firSecs := ((← IO.monoMsNow) - firStart) / 1000
  IO.println s!"   ({firSecs} s, exit {firOut.exitCode})"
  unless firOut.exitCode == 0 do
    IO.FS.writeFile (logDir / "tests-fir-artifacts.log") (firOut.stdout ++ firOut.stderr)
    die s!"tests-fir --render-artifacts failed ({logDir / "tests-fir-artifacts.log"})"
  IO.FS.writeFile (ixccDir / "IxCCTests" / "Fir" / "Artifacts.lean") firOut.stdout

  -- 4. Report
  match treeDir? with
  | some tree =>
    let changedRaw ← runChecked "git status --porcelain" "git"
      #["-C", tree.toString, "status", "--porcelain"]
    let changedLines := splitNonEmptyLines changedRaw
    let trackedRaw ← runChecked "git ls-files" "git" #["-C", tree.toString, "ls-files"]
    let totalFiles := (splitNonEmptyLines trackedRaw).size
    IO.println s!"== per file: {changedLines.size} of {totalFiles} files differ from HEAD"
    for line in changedLines do
      IO.println line
    IO.println "== citations (commits and paths outside the repository, in fixtures, manifests, READMEs and generated modules)"
    let leanExe ← resolveLeanExe
    let citOut ← runChecked "Citations.lean --fixtures" leanExe
      #["--run", "IxCC/tools/Citations.lean", "--fixtures"] (some root) noLeanPath
    let citedLines := splitNonEmptyLines citOut
    for line in citedLines do
      IO.println line
    if changedLines.isEmpty && citedLines.isEmpty then
      IO.println "regenerate --check: current and self-contained"
      return 0
    else
      IO.println "regenerate --check: NOT current or not self-contained"
      return 1
  | none =>
    IO.println "== regenerated in place; review with git diff (docs/corpus.md, Refreezing)"
    let statusRaw ← runChecked "git status --short" "git" #["-C", root.toString, "status", "--short"]
    for line in (splitNonEmptyLines statusRaw).toList.take 50 do
      IO.println line
    return 0

/-! ## Built-in unit self-tests -/

def assertTrue (label : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"selftest FAILED [{label}]"

def runSelfTests : IO Unit := do
  assertTrue "parseArgs default" ((parseArgs []).toOption == some {})
  assertTrue "parseArgs check+work+jobs"
    ((parseArgs ["--check", "--work", "/tmp/w", "--jobs", "16"]).toOption ==
      some { check := true, work := some (FilePath.mk "/tmp/w"), jobs := 16 })
  assertTrue "parseArgs rejects jobs=0" (!(parseArgs ["--jobs", "0"]).isOk)
  assertTrue "parseArgs rejects unknown" (!(parseArgs ["--bogus"]).isOk)

  let sampleSrc :=
    "import Init\n\
     import   Ix.Compile.SourceContract.Elab -- comment\n\
     -- import Ignored.Mod\n\
     import Foo.Bar\n"
  assertTrue "parseImportedModules"
    (parseImportedModules sampleSrc == #["Init", "Ix.Compile.SourceContract.Elab", "Foo.Bar"])

  assertTrue "shSingleQuote plain" (shSingleQuote "/a/b:/c/d" == "'/a/b:/c/d'")
  assertTrue "shSingleQuote embedded quote" (shSingleQuote "a'b" == "'a'\\''b'")
  assertTrue "stripIxccPrefix"
    (stripIxccPrefix "IxCC/fixtures/corpus/k1/corpus.json" == "fixtures/corpus/k1/corpus.json")
  assertTrue "manifestSlug"
    (manifestSlug "fixtures/corpus/k1/corpus.json" == "fixtures_corpus_k1_corpus.json")

  IO.println "[regenerate] selftest passed (all 9 assertions)"

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
    IO.eprintln s!"regenerate: {e}\n{usageText}"
    return 2
  | .ok cfg =>
    if cfg.showHelp then
      IO.println usageText
      return 0
    if cfg.selftest then
      runSelfTests
      return 0
    runRegenerate cfg

end Regenerate

def main (args : List String) : IO UInt32 := Regenerate.main args
