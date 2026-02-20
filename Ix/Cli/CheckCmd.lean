import Cli
import Ix.Common
import Ix.Kernel
import Ix.Meta
import Ix.CompileM
import Lean

open System (FilePath)

/-- If the project depends on Mathlib, download the Mathlib cache. -/
private def fetchMathlibCache (cwd : Option FilePath) : IO Unit := do
  let root := cwd.getD "."
  let manifest := root / "lake-manifest.json"
  let contents ← IO.FS.readFile manifest
  if contents.containsSubstr "leanprover-community/mathlib4" then
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

/-- Build the Lean module at the given file path using Lake. -/
private def buildFile (path : FilePath) : IO Unit := do
  let path ← IO.FS.realPath path
  let some moduleName := path.fileStem
    | throw $ IO.userError s!"cannot determine module name from {path}"
  fetchMathlibCache path.parent
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", moduleName]
    cwd := path.parent
    stdout := .inherit
    stderr := .inherit
  }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw $ IO.userError "lake build failed"

/-- Run the Lean NbE kernel checker. -/
private def runLeanCheck (leanEnv : Lean.Environment) : IO UInt32 := do
  println! "Compiling to Ixon..."
  let compileStart ← IO.monoMsNow
  let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
  let compileElapsed := (← IO.monoMsNow) - compileStart
  let numConsts := ixonEnv.consts.size
  println! "Compiled {numConsts} constants in {compileElapsed.formatMs}"

  println! "Converting Ixon → Kernel..."
  let convertStart ← IO.monoMsNow
  match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
  | .error e =>
    println! "Conversion error: {e}"
    return 1
  | .ok (kenv, prims, quotInit) =>
    let convertElapsed := (← IO.monoMsNow) - convertStart
    println! "Converted {kenv.size} constants in {convertElapsed.formatMs}"

    println! "Typechecking..."
    let checkStart ← IO.monoMsNow
    match Ix.Kernel.typecheckAll kenv prims quotInit with
    | .error e =>
      let elapsed := (← IO.monoMsNow) - checkStart
      println! "Kernel check failed in {elapsed.formatMs}: {e}"
      return 1
    | .ok () =>
      let elapsed := (← IO.monoMsNow) - checkStart
      println! "Checked {kenv.size} constants in {elapsed.formatMs}"
      return 0

/-- Run the Rust kernel checker. -/
private def runRustCheck (leanEnv : Lean.Environment) : IO UInt32 := do
  let totalConsts := leanEnv.constants.toList.length
  println! "Total constants: {totalConsts}"

  let start ← IO.monoMsNow
  let errors ← Ix.Kernel.rsCheckEnv leanEnv
  let elapsed := (← IO.monoMsNow) - start

  if errors.isEmpty then
    println! "Checked {totalConsts} constants in {elapsed.formatMs}"
    return 0
  else
    println! "Kernel check failed with {errors.size} error(s) in {elapsed.formatMs}:"
    for (name, err) in errors[:min 50 errors.size] do
      println! "  {repr name}: {repr err}"
    return 1

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String
  let useLean := p.hasFlag "lean"

  buildFile pathStr
  let leanEnv ← getFileEnv pathStr

  if useLean then
    println! "Running Lean NbE kernel checker on {pathStr}"
    runLeanCheck leanEnv
  else
    println! "Running Rust kernel checker on {pathStr}"
    runRustCheck leanEnv

def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Type-check Lean file with kernel"

  FLAGS:
    path : String; "Path to file to check"
    lean; "Use Lean NbE kernel instead of Rust kernel"
]
