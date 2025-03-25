import Cli
import Ix.Cronos
import Ix.Common
import Ix.CanonM
import Ix.Store
import Ix.Address
import Lean

-- ix store <lean file>
-- ix store get <address>

def runStore (p : Cli.Parsed) : IO UInt32 := do
  return 0

def runGet (p : Cli.Parsed) : IO UInt32 := do
  let input : String       := p.positionalArg! "input" |>.as! String
  IO.println <| "Input: " ++ input
  let address : Address <- IO.ofExcept $
    match Address.fromString input with
    | .some a => .ok a
    | .none => .error "bad address"
  let const <- EIO.toIO storeErrorToIOError (readConst address)
  IO.println <| s!"{repr const}"
  return 0

def storeGetCmd : Cli.Cmd := `[Cli|
  get VIA runGet;
  "print a store entry"
  ARGS:
    input  : String; "Source file input"
]

def storeCmd : Cli.Cmd := `[Cli|
  store VIA runStore;
  "Interact with the Ix store"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
input  : String; "Source file input"

  SUBCOMMANDS:
    storeGetCmd
]

