module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta

public section

open System (FilePath)

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
  -- Machine-readable line for CI benchmark tracking
  IO.println s!"##benchmark## {elapsed} {bytes.size} {totalConsts}"
  return 0


def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile Lean file to Ixon"

  FLAGS:
    path : String; "Path to file to compile"
]

end
