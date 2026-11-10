import Ix.FormalCompiler
import Ix.Cli.FormalAiur

/-! `formal-codegen DIR [--cuda]`: the step of `lake build ix` that writes
the generated native executors of the certified IxVM, recursive verifier and
aggregation programs, and with `--cuda` their CUDA trace writers, under
`DIR` (`.lake/build/formal-generated`) before Cargo compiles them into `ix`.
Each program comes from the artifact cache (`.lake/aiur`); misses compile in
process, concurrently, once per compiler and program revision. The
`IX_*_ARTIFACT` variables select trusted packages instead. -/

def main (args : List String) : IO UInt32 := do
  let (directory, cuda) ← match args with
    | [directory] => pure (directory, false)
    | [directory, "--cuda"] => pure (directory, true)
    | _ => throw (IO.userError "usage: formal-codegen DIR [--cuda]")
  Ix.Cli.FormalAiur.writeGenerated default directory cuda
  return 0
