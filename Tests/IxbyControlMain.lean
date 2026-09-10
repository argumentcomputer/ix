import Tests.IxbyControl

def main (args : List String) : IO UInt32 := do
  unless args.all (fun arg => arg == "--execute-only" || arg == "--stats") do
    IO.eprintln "usage: IxbyControlTests [--execute-only] [--stats]"
    return 1
  Tests.IxbyControl.suite (!args.contains "--execute-only") (args.contains "--stats")
