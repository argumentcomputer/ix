import Ix.FormalCompiler
import Ix.Cli.FormalAiur
import Ix.Cli.FormalKeys
import Ix.Cli.FormalAggregate

/-! `formal-keys`: the pin file (`tools/formal-aiur.keys`) of the checkout's
certified IxVM, recursive verifier and aggregation programs, on stdout. Each
program comes from the artifact cache, misses compiling in process; its key is
derived under the default STARK parameters, and the IxVM and aggregation
programs' entry function indices as acceptance derives them.
`Scripts/CheckFormalKeys.lean` compares the output with the committed file. -/

/-- The entry function index acceptance derives for `target`'s `system`
(`FormalAggregate.identity`), for the programs whose index is pinned. -/
def entryIndex (target : Ix.FormalProver.Target) (system : Ix.FormalProver.System) :
    IO (Option Nat) :=
  match target with
  | .ixvm => do
    let identity ← Ix.Cli.FormalAggregate.identity system false
    return some identity.index
  | .aggregation => do
    let identity ← Ix.Cli.FormalAggregate.identity system true
    return some identity.index
  | .verifier => pure none

open Ix.Cli Ix.Cli.FormalAiur in
def main (_ : List String) : IO UInt32 := do
  let targets : Array Ix.FormalProver.Target := #[.ixvm, .verifier, .aggregation]
  let selected ← selectAll default (← Ix.FormalProver.Registry.new) targets
  let pins ← (targets.zip selected).mapM fun (target, s) => do
    let system ← s.system
    let entry ← entryIndex target system
    return ({ program := generatedName target, identity := hexOfBytes (← s.program.identity)
              key := FormalKeys.keyDigest (← system.key), entry } : FormalKeys.Pin)
  IO.print (FormalKeys.render pins)
  return 0
