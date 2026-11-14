import Aiur.Modules
import Mathlib.Algebra.Field.Rat

open Aiur
namespace OpacityExample

def source : Modules.Program Nat := aiur% "
signature BitOperations {
  opaque type Bit;
  fn raw_xor(a: Field, b: Field) -> Bit;
  fn read(x: Bit) -> Field;
}

module Bits: BitOperations {
  opaque type Bit = Field;
  table inputs: (Field, Field) { (0, 0), (0, 1), (1, 0), (1, 1) }
  table outputs: Bit { 0, 1, 1, 0 }
  map raw_xor(a: Field, b: Field) -> Bit = inputs => outputs;
  inline fn read(x: Bit) -> Field { x }
}

module Xor<B: BitOperations> {
  fn main(a: Field, b: Field) -> Field { B::read(B::raw_xor(a, b)) }
}
module App = Xor::<Bits>;
"

-- The caller supplies fields; the table creates the opaque result.
#eval do
  let p ← Modules.prepare (source.toField Rat) ["App::main"]
  p.run "App::main" [1, 0]

-- Opaque aliases use their representation layout: three columns, one lookup.
#eval do
  let p ← Modules.prepare (source.toField Rat) ["App::main"]
  let compiled ← p.compileOptimized
  return compiled.circuit.system.stats.map
    (fun (s : Circuit.ChipStats) => (s.columns, s.lookups))

end OpacityExample
