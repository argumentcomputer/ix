import Aiur.Modules.Frontend
import Aiur.Execution
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

open Aiur

namespace ExecutionExample

def source : Modules.Program Nat := aiur_modules% "
module Demo {
    struct Result { value: Field, repeated: [Field; 2] }
    fn fib(n: Field) -> Field {
        match n { 0 => 0, 1 => 1, _ => fib(n - 1) + fib(n - 2) }
    }
    fn run(ns: [Field; 3]) -> Result {
        Result { value: fib(ns[0]), repeated: [fib(ns[1]), fib(ns[2])] }
    }
}
"

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

def main : IO Unit := do
  let exported ← IO.ofExcept do
    let prepared ← Modules.prepare (source.toField (ZMod 65537)) ["Demo::run"]
    prepared.exportExecution
  -- One array argument is written structurally; Rust flattens it using the
  -- selected entry's IO description and unflattens the returned struct.
  let result ← IO.ofExcept (← exported.run "Demo::run" #[Lean.toJson ([20, 20, 20] : List Nat)])
  IO.println (result.pretty_output.getD "<opaque result>")
  IO.println s!"{result.queries.size} distinct queries; {result.instructions} executed instructions"
  for query in result.queries do
    IO.println s!"{query.name}{query.args.toList} -> {query.output.toList}, multiplicity {query.multiplicity}"

end ExecutionExample

def main : IO Unit := ExecutionExample.main
