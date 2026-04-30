module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta

public section

open System (FilePath)

private def defaultOutPathFor (pathStr : String) : String :=
  let path := FilePath.mk pathStr
  let stem := path.fileStem.getD (path.fileName.getD pathStr)
  stem.toLower ++ ".ixe"

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String
  let outPath : String :=
    (p.flag? "out").map (·.as! String) |>.getD (defaultOutPathFor pathStr)

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

  -- Persist the serialized IxonEnv (`Env::put` bytes) to disk so subsequent
  -- runs (e.g. `ix check-ixon`) can skip the Lean → IxOn compile step. The
  -- resulting file is the canonical streaming format produced by
  -- `Ixon.Env::put` (see `src/ix/ixon/serialize.rs:1093-1297`); it round-trips
  -- through `Ixon.Env::get`.
  let writeStart ← IO.monoMsNow
  IO.FS.writeBinFile outPath bytes
  let writeMs := (← IO.monoMsNow) - writeStart
  println! "Wrote {fmtBytes bytes.size} to {outPath} in {writeMs.formatMs}"
  return 0


def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile Lean file to Ixon"

  FLAGS:
    path : String; "Path to file to compile"
    out  : String; "Output path for serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe` (e.g. CompileMathlib.lean -> compilemathlib.ixe)"
]

end
