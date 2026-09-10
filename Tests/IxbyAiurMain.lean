import Tests.IxbyAiur

/-- Small standalone runner avoids building or running unrelated integration
suites. Proofs use explicitly test-only parameters. -/
def main (args : List String) : IO UInt32 := do
  unless args.all (fun arg => arg == "--execute-only" || arg == "--stats") do
    IO.eprintln "usage: IxbyAiurTests [--execute-only] [--stats]"
    return 1
  Tests.IxbyAiur.suite (!args.contains "--execute-only") (args.contains "--stats")
