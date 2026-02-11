import Cli
import Ix.Common
import Ix.CompileM
import Ix.Meta
import Lean

open System (FilePath)

/-- If the project depends on Mathlib, download the Mathlib cache. -/
private def fetchMathlibCache (cwd : Option FilePath) : IO Unit := do
  let manifest := (cwd.getD ".") / "lake-manifest.json"
  let contents ← IO.FS.readFile manifest
  if contents.containsSubstr "leanprover-community/mathlib4" then
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

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String

  buildFile pathStr
  let leanEnv ← getFileEnv pathStr

  println! "Running Ix compiler on {pathStr}"

  let totalConsts := leanEnv.constants.toList.length
  println! "Total constants: {totalConsts}"

  let start ← IO.monoMsNow
  let bytes ← Ix.CompileM.rsCompileEnvBytes leanEnv
  let elapsed := (← IO.monoMsNow) - start

  println! "Compiled {fmtBytes bytes.size} env in {elapsed.formatMs}"
  return 0
    

def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile Lean file to Ixon"

  FLAGS:
    path : String; "Path to file to compile"
]
