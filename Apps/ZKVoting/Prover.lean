import Apps.ZKVoting.Election

def main (args : List String) : IO UInt32 := do
  try
    let args ← if args.isEmpty then do
        let dir ← IO.FS.createTempDir
        pure [(dir / "election").toString]
      else pure args
    ZKVoting.proveElection args
    return 0
  catch e =>
    IO.eprintln s!"Election failed: {e}"
    return 1
