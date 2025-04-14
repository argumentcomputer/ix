import Cli
import Ix.Cronos
import Ix.Common
import Ix.CompileM
import Ix.Store
import Ix.Address
import Ix.Meta
import Lean

-- ix prove eval AcmeInput
-- ix prove eval --address deadbeef
-- ix prove eval AcmeFun AcmeArg1 AcmeArg2
-- ix prove eval --address abcde 1234 5678
-- ix prove check --name AcmeTheo
-- ix prove check --address deadbeef

def runProve (p : Cli.Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  --if p.hasFlag "name" then
  IO.println <| "Input: " ++ input
  return 0

def runProveCheck (p: Cli.Parsed): IO UInt32 := do
  let input : String       := p.positionalArg! "input" |>.as! String
  let const : String       := p.positionalArg! "const" |>.as! String
  let path := ⟨input⟩
  Lean.setLibsPaths input
  let env ← Lean.runFrontend (← IO.FS.readFile path) path
  let constInfo <- match env.constants.find? const.toName with
    | some c => pure c
    | none => throw $ IO.userError s!"unknown constant {const.toName}"
  let constTypeSort <- runMeta (Lean.Meta.inferType constInfo.type) env
  let commit := p.hasFlag "commit"
  let ((claim, _, _), _) <- 
    (Ix.Compile.checkClaim const.toName constInfo.type constTypeSort
    constInfo.levelParams commit).runIO' 200000 (.init env)
  IO.println $ s!"checking {const.toName} in {input}"
  IO.println $ s!"claim {claim}"
  return 0


def proveCheckCmd : Cli.Cmd := `[Cli|
  check VIA runProveCheck;
  "prove typechecking"

  FLAGS:
    cron, "cronos"; "enable Cronos timings"
    address, "address"; "lookup inputs by address"
    commit, "commit"; "commit inputs"

  ARGS:
   input  : String; "Source file input"
   const  : String; "constant name"
]

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProve;
  "Generates a ZK proof of a given Lean source file"

  FLAGS:
    cron, "cronos"   : String; "enable Cronos timings"
    address, "address"   : String; "lookup inputs by address"

  ARGS:
   input  : String; "Source file input"

  SUBCOMMANDS:
    proveCheckCmd
]
