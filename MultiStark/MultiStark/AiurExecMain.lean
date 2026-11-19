import MultiStark.AiurExecProgram

/-! `aiurexec-export digest [--block]` prints the `aiurExec` aggregator's source digest;
`aiurexec-export export PATH [--ungrouped] [--block]` writes its compiled package. `--block`
selects the instance for `Fixed::train_block` claims. -/

def main (args : List String) : IO Unit := do
  match args with
  | ["digest"] => IO.println MultiStark.aiurExecDigest
  | ["digest", "--block"] => IO.println MultiStark.aiurExecBlockDigest
  | "export" :: path :: rest =>
    let block := rest.contains "--block"
    let (digest, program) := if block then
        (MultiStark.aiurExecBlockDigest, MultiStark.aiurExecBlockProgram)
      else (MultiStark.aiurExecDigest, MultiStark.aiurExecProgram)
    IO.eprintln s!"aiurExec program {digest}"
    let package ← MultiStark.compileAiurExecPackage (!rest.contains "--ungrouped") program
    Aiur.Artifact.write path package
    IO.eprintln s!"Wrote {path}"
  | _ => throw (IO.userError "usage: aiurexec-export digest [--block] | export PATH [--ungrouped] [--block]")
