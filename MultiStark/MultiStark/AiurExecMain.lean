import MultiStark.AiurExecProgram

/-! `aiurexec-export digest [--block | --train]` prints the `aiurExec` aggregator's source digest;
`aiurexec-export export PATH [--ungrouped] [--block | --train]` writes its compiled package.
`--block` selects the instance for `Fixed::train_block` claims, `--train` the one for
`FixedTree::train_tree` claims. -/

def main (args : List String) : IO Unit := do
  match args with
  | ["digest"] => IO.println MultiStark.aiurExecDigest
  | ["digest", "--block"] => IO.println MultiStark.aiurExecBlockDigest
  | ["digest", "--train"] => IO.println MultiStark.aiurExecTrainDigest
  | "export" :: path :: rest =>
    let (digest, program) :=
      if rest.contains "--block" then (MultiStark.aiurExecBlockDigest, MultiStark.aiurExecBlockProgram)
      else if rest.contains "--train" then (MultiStark.aiurExecTrainDigest, MultiStark.aiurExecTrainProgram)
      else (MultiStark.aiurExecDigest, MultiStark.aiurExecProgram)
    IO.eprintln s!"aiurExec program {digest}"
    let package ← MultiStark.compileAiurExecPackage (!rest.contains "--ungrouped") program
    Aiur.Artifact.write path package
    IO.eprintln s!"Wrote {path}"
  | _ => throw (IO.userError "usage: aiurexec-export digest [--block | --train] | export PATH [--ungrouped] [--block | --train]")
