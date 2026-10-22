import Apps.ZKVoting.Election

def main (args : List String) : IO UInt32 := do
  try
    ZKVoting.verifyElection args
    return 0
  catch e =>
    IO.eprintln s!"REJECTED: {e}"
    return 1
