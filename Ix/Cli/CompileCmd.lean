import Cli
import Ix.Common
import Ix.CompileM
import Ix.Meta
import Lean

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String

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
