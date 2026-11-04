import Ix.FormalCompiler
import Ix.Cli.FormalPrograms

/-! `formal-codegen DIR [--cuda]`: the step of `lake build ix` that writes
the generated native executors of the certified IxVM, recursive verifier and
aggregation programs, and with `--cuda` their CUDA trace writers, under
`DIR` (`.lake/build/formal-generated`) before Cargo compiles them into `ix`.
Each program comes from the compiled-program cache; misses compile in
process, concurrently, once per source revision and compiler. -/

open Ix.Cli.FormalAiur in
def main (args : List String) : IO UInt32 := do
  let (directory, cuda) ← match args with
    | [directory] => pure (directory, false)
    | [directory, "--cuda"] => pure (directory, true)
    | _ => throw (IO.userError "usage: formal-codegen DIR [--cuda]")
  let programs := #[ixvmProgram, verifierProgram, aggregationProgram]
  let selected ← compiledPrograms (← Ix.FormalProver.Registry.new) programs
    (checkExecutors := false)
  writeGenerated programs selected directory cuda
  return 0
