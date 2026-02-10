import Cli
import Ix.Common
import Ix.CompileM
import Ix.Meta
import Lean

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let leanEnv ← getFileEnv <| path.as! String

  IO.println s!"Running Ix compiler"

  let start ← IO.monoMsNow
  let phases ← Ix.CompileM.rsCompilePhases leanEnv
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"{phases.rawEnv.consts.size} consts, {phases.condensed.blocks.size} blocks, {phases.compileEnv.constCount} compiled in {elapsed}ms"
  return 0
    

def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile Lean file to Ixon"

  FLAGS:
    path : String; "Path to file to compile"
]
