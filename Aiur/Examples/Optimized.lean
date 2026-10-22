import Aiur.Modules
import Mathlib.Algebra.Field.Rat

open Aiur
namespace OptimizedExample

def source : Modules.Program Nat := aiur% "
module Arithmetic {
  fn left(x: Field) -> Field { match x { 0 => 0, _ => right(x - 1) + 1 } }
  fn right(x: Field) -> Field { match x { 0 => 0, _ => left(x - 1) + 2 } }
  fn copy_left(x: Field) -> Field { match x { 0 => 0, _ => copy_right(x - 1) + 1 } }
  fn copy_right(x: Field) -> Field { match x { 0 => 0, _ => copy_left(x - 1) + 2 } }
  fn main(x: Field) -> (Field, Field) { (left(x), copy_left(x)) }
  fn branch(x: Field, y: Field, z: Field) -> Field {
    match x { 0 => y * y * y * y / z, _ => z * z * z * z / y }
  }
}
"

#eval show IO Unit from do
  let result : Except String _ := do
    let prepared ← Modules.prepare (source.toField Rat) ["Arithmetic::main", "Arithmetic::branch"]
    let reference ← prepared.compile
    let optimized ← prepared.compileOptimized
    return (reference.circuit.system, optimized.circuit.artifact)
  match result with
  | .error message => throw (IO.userError message)
  | .ok (reference, optimized) =>
    IO.println s!"Reference: {reference.chips.length} chips"
    reference.printStats
    IO.println s!"Optimized: {optimized.system.chips.length} chips"
    optimized.system.printStats
    IO.println s!"Representatives: {repr optimized.representatives}"

-- Every successful artifact carries a proof of its reported degree bounds.
example (artifact : Optimized.Artifact Rat) (chip : Circuit.Chip Rat)
    (member : chip ∈ artifact.system.chips) :
    chip.stats.maxConstraintDegree ≤ artifact.config.maxDegree :=
  (artifact.degreeBound chip member).1

-- The alternative source soundness/completeness theorem is not yet supplied.
end OptimizedExample
