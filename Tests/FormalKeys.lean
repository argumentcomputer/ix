import Ix.FormalCompiler
import Ix.Cli.FormalAiur
import Ix.Cli.FormalKeys

/-! `formal-keys`: the pin file (`tools/formal-aiur.keys`) of the checkout's
certified IxVM, recursive verifier and aggregation programs, on stdout. Each
program comes from the artifact cache, misses compiling in process; its key is
derived under the default STARK parameters.
`tools/check-formal-keys.sh` compares the output with the committed file. -/

open Ix.Cli Ix.Cli.FormalAiur in
def main (_ : List String) : IO UInt32 := do
  let targets : Array Ix.FormalProver.Target := #[.ixvm, .verifier, .aggregation]
  let selected ← selectAll default (← Ix.FormalProver.Registry.new) targets
  let pins ← (targets.zip selected).mapM fun (target, s) => do
    let system ← s.system
    return ({ program := generatedName target, identity := hexOfBytes (← s.program.identity)
              key := FormalKeys.keyDigest (← system.key) } : FormalKeys.Pin)
  IO.print (FormalKeys.render pins)
  return 0
