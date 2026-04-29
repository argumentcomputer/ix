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
  let outPath? : Option String := (p.flag? "out").map (·.as! String)

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

  -- Optionally persist the serialized IxonEnv (`Env::put` bytes) to disk so
  -- subsequent runs (e.g. `ix check-ixon`) can skip the Lean → IxOn compile
  -- step. The resulting file is the canonical streaming format produced by
  -- `Ixon.Env::put` (see `src/ix/ixon/serialize.rs:1093-1297`); it round-
  -- trips through `Ixon.Env::get`.
  match outPath? with
  | none => return 0
  | some out =>
    let writeStart ← IO.monoMsNow
    IO.FS.writeBinFile out bytes
    let writeMs := (← IO.monoMsNow) - writeStart
    println! "Wrote {fmtBytes bytes.size} to {out} in {writeMs.formatMs}"
    return 0


def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile Lean file to Ixon"

  FLAGS:
    path : String; "Path to file to compile"
    out  : String; "Optional output path: write the serialized Ixon.Env bytes (`Env::put` format) so later runs can load via `ix check-ixon --env <path>`"
]

end
