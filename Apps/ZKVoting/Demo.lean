import Apps.ZKVoting.Election

def main (args : List String) : IO UInt32 := do
  try
    let dir : System.FilePath ← match args with
      | [] => do pure ((← IO.FS.createTempDir) / "election")
      | [path] => pure path
      | _ => throw <| IO.userError "Usage: lake exe Apps.ZKVoting.Demo [NEW_DIRECTORY]"
    IO.println "Verifiable voting: Alice, Alice, Bob"
    IO.println "Synthetic ballots only: the current backend does not guarantee vote secrecy."
    ZKVoting.proveElection [dir.toString, "alice", "alice", "bob"]
    IO.println "\nNow verify independently as voter 1, then try tampering:"
    ZKVoting.verifyElection [dir.toString, (dir / "voter-1.receipt").toString, "--show-tampering"]
    IO.println s!"\nArtifacts retained at: {dir}"
    return 0
  catch e =>
    IO.eprintln s!"Demo failed: {e}"
    return 1
