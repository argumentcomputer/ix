import Cli

def runProve (p : Cli.Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  IO.println <| "Input: " ++ input
  return 0

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProve;
  "Generates a ZK proof of a given Lean source file"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
   input  : String; "Source file input"
]
