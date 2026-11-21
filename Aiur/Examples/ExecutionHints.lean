import Aiur.Modules.Frontend
import Aiur.Execution
import Mathlib.Algebra.Field.ZMod

open Aiur

namespace ExecutionHintsExample

def source : Modules.Program Nat := aiur_modules% "
module Demo {
  struct Preimage { parts: [Field; 2] }
  fn recover(digest: Field) -> Preimage {
    let witness = hint::<Preimage>(digest);
    let sum = witness.parts[0] + witness.parts[1];
    assert_eq!(sum * sum, digest, \"incorrect preimage\");
    witness
  }
  fn run(digest: Field) -> (Preimage, Preimage) {
    (recover(digest), recover(digest))
  }
}
"

/-- Ordinary Lean data; no enum tags, padding or field offsets to calculate. -/
def hints : Array (Execution.HintEntry (ZMod 97)) := #[
  ⟨.named "Demo::Preimage" [], 49,
    .record (.named "Demo::Preimage" []) [("parts", .array .field [3,4])], ""⟩
]

def main : IO Unit := do
  let exported ← IO.ofExcept do
    let prepared ← Modules.prepare (source.toField (ZMod 97)) ["Demo::run"]
    prepared.exportExecution
  let result ← IO.ofExcept (← exported.runFlat "Demo::run" #[49] hints)
  IO.println (result.pretty_output.getD "<opaque result>")
  for query in result.queries do
    IO.println s!"{query.name}: multiplicity {query.multiplicity}"

end ExecutionHintsExample

def main : IO Unit := ExecutionHintsExample.main
