import Cli

def runHash (p : Cli.Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  IO.println <| "Input: " ++ input
  return 0

def hashCmd : Cli.Cmd := `[Cli|
  hash VIA runHash;
  "Hashes a given Lean source file"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
    input  : String; "Source file input"
]
