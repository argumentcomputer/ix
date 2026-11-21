import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur
namespace InlineExample

def source : Modules.Program Nat := aiur% "
module Arithmetic {
  inline fn square(x: Field) -> Field { x * x }
  fn main(x: Field) -> Field { square(x) + 1 }
}
module Count {
  fn count(n: Field) -> Field { match n { 0 => 0, _ => step(n) } }
  inline fn step(n: Field) -> Field { count(n - 1) + 1 }
}
"

-- Source execution still uses the original function bodies and ordinary calls.
#eval do
  let p ← Modules.prepare (source.toField Rat) ["Arithmetic::main", "Count::count"]
  p.run "Arithmetic::main" [3] -- 10

-- Only the two selected ordinary functions produce chips. Count's chip sends
-- a recursive message to itself after expanding step; square sends nothing.
#eval do
  let p ← Modules.prepare (source.toField Rat) ["Arithmetic::main", "Count::count"]
  let c ← p.compile
  return c.circuit.system.chips.map fun (chip : Circuit.Chip Rat) => (chip.name, chip.sends.map (fun (send : Circuit.Send Rat) => send.channel))

-- Inline helpers cannot become protocol entrypoints.
#eval (Modules.prepare (source.toField Rat) ["Arithmetic::square"]).map (fun _ => ())

#print axioms Generic.Compiled.native_entry_iff
#print axioms Modules.Compiled.check_complete
#print axioms Modules.Compiled.checkMemo_acyclic_sound

end InlineExample
