import Aiur.Modules
import Mathlib.Algebra.Field.Rat

open Aiur

namespace CircuitStatsExample

def source : Modules.Program Nat := aiur% "
module Arithmetic {
  fn square(x: Field) -> Field { x * x }
  fn main(x: Field) -> Field {
    let p = &x;
    match *p { 0 => 0, _ => square(x * x * x) }
  }
}
"

def circuit : Except String (Circuit.System Rat) := do
  let p ← Modules.prepare (source.toField Rat) ["Arithmetic::main"]
  let compiled ← p.compile
  return compiled.circuit.system

-- Reports the actual chips after specialization and mandatory inlining.
#eval show IO Unit from do
  match circuit with
  | .error message => throw (IO.userError message)
  | .ok system => system.printStats

-- Structured measurements are available without printing or witness rows.
#eval circuit.map (fun system => system.stats.map (fun stats => (stats.name, stats.columns)))

end CircuitStatsExample
