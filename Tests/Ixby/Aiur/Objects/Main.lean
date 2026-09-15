import Tests.Ixby.Aiur.Objects

def main (args : List String) : IO UInt32 := do
  unless args.all (fun arg => arg == "--execute-only" || arg == "--stats") do
    IO.eprintln "usage: IxbyObjectsTests [--execute-only] [--stats]"
    return 1
  Tests.Ixby.Aiur.Objects.suite (!args.contains "--execute-only") (args.contains "--stats")
