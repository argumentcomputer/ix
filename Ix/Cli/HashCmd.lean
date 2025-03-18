import Cli
import Ix.Cronos
import Ix.Common
import Ix.CanonM
import Lean

def runHash (p : Cli.Parsed) : IO UInt32 := do
  -- Get Lean source file name
  let source  : String       := p.positionalArg! "input" |>.as! String
  IO.println <| "Source: " ++ source
  -- Run Lean frontend
  let mut cronos ← Cronos.new.clock "Run Lean frontend"
  Lean.setLibsPaths source
  --IO.println <| "setlibs"
  let path := ⟨source⟩
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile path) path
  leanEnv.constants.forM fun n y => do
    IO.println <| s!"constant {n}"
  let (constMap, delta) := leanEnv.getConstsAndDelta
  IO.println <| "delta"
  IO.println <| s!"delta len {delta.length}"
  delta.forM fun x => do
     IO.println <| s!"constant'' {x.name}"
  --cronos ← cronos.clock "Run Lean frontend"

 -- IO.println <| "content-address"
 -- -- Start content-addressing
 -- cronos ← cronos.clock "Content-address"
 -- let stt ← match ← Ix.CanonM.canon constMap delta with
 --   | .error err => IO.eprintln err; return 1
 --   | .ok stt => pure stt
 -- cronos ← cronos.clock "Content-address"
 -- stt.store.forM fun adr _ => do
 --    IO.println <| s!"{adr}"

 -- IO.println cronos.summary
  return 0

def hashCmd : Cli.Cmd := `[Cli|
  hash VIA runHash;
  "Hashes a given Lean source file"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
    input  : String; "Source file input"
]
