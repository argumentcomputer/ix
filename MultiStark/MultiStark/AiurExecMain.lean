import MultiStark.AiurExecProgram

/-! `aiurexec-export digest` prints the `aiurExec` aggregator's source digest;
`aiurexec-export export PATH [--ungrouped]` writes its compiled package. -/

def main (args : List String) : IO Unit := do
  match args with
  | ["digest"] => IO.println MultiStark.aiurExecDigest
  | "export" :: path :: rest =>
    IO.eprintln s!"aiurExec program {MultiStark.aiurExecDigest}"
    let package ← MultiStark.compileAiurExecPackage (!rest.contains "--ungrouped")
    Aiur.Artifact.write path package
    IO.eprintln s!"Wrote {path}"
  | _ => throw (IO.userError "usage: aiurexec-export digest | export PATH [--ungrouped]")
