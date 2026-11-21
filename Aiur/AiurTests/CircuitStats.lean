import Aiur.Modules
import Mathlib.Algebra.Field.Rat

open Aiur

namespace AiurCircuitStatsTests

def source : Modules.Program Nat := aiur% "
module Metrics {
  fn square(x: Field) -> Field { x * x }
  fn calls(x: Field) -> Field {
    let a = square(x);
    let b = square(x);
    a + b
  }
  fn product(a: Field, b: Field, c: Field, d: Field) -> Field { a * b * c * d }
  fn memory(x: Field) -> Field { let p = &x; *p }
  fn choice(x: Field) -> Field { match x { 0 => square(x), _ => square(x + 1) } }
  fn lookup_product(a: Field, b: Field, c: Field) -> Field { square(a * b * c) }
  fn unit() -> () { () }
  inline fn helper(x: Field) -> Field { x * x }
  fn inlined(x: Field) -> Field { helper(x) }
  table inputs: (Field, Field) { (1, 2) }
  table outputs: Field { 3 }
  map add(a: Field, b: Field) -> Field = Metrics::inputs => Metrics::outputs;
  fn table_call() -> Field { add(1, 2) }
}
"

private def checkEqual [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  let get {α : Type} (r : Except String α) : IO α := match r with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let entries := ["calls", "product", "memory", "choice", "lookup_product",
    "unit", "inlined", "table_call"].map ("Metrics::" ++ ·)
  let p ← get <| Modules.prepare (source.toField Rat) entries
  let compiled ← get p.compile
  let system := compiled.circuit.system
  checkEqual "chip order" (system.stats.map (·.name)) (system.chips.map (·.name))
  for expected in ([
      ⟨"Metrics::square", 2, 2, 0, 0, 1⟩,
      ⟨"Metrics::calls", 4, 1, 2, 0, 1⟩,
      ⟨"Metrics::product", 5, 4, 0, 0, 1⟩,
      ⟨"Metrics::memory", 4, 1, 0, 2, 1⟩,
      ⟨"Metrics::lookup_product", 5, 1, 1, 0, 3⟩,
      ⟨"Metrics::unit", 0, 0, 0, 0, 0⟩,
      ⟨"Metrics::inlined", 2, 2, 0, 0, 1⟩,
      ⟨"Metrics::table_call", 2, 1, 1, 0, 1⟩
    ] : List Circuit.ChipStats) do
    let some chip := system.findChip? expected.name |
      throw (IO.userError s!"missing chip {expected.name}")
    checkEqual expected.name chip.stats expected
  let some choice := system.findChip? "Metrics::choice" |
    throw (IO.userError "missing branch example")
  checkEqual "both guarded call slots count" choice.stats.lookups 2
  checkEqual "inline helpers and maps have no chip" system.chips.length 9
  -- Even statically disabled slots occupy the chip's declared lookup list.
  let disabledSends := choice.sends.map fun (send : Circuit.Send Rat) =>
    { send with enable := .const 0 }
  let disabled := { choice with sends := disabledSends }
  checkEqual "disabled call slots count" disabled.stats.callLookups 2
  -- Structural degree deliberately does not cancel equal terms.
  let x : Circuit.ArithExpr Rat := .var 0
  let cubic : Circuit.ArithExpr Rat := .mul x (.mul x x)
  let guarded : Circuit.ArithExpr Rat := .mul x (.sub cubic cubic)
  checkEqual "structural degree includes guards" guarded.degree 4
  let outputOnly : Circuit.Chip Rat := {
    name := "output", inputs := [.field 0], output := .field cubic,
    numVars := 1, constraints := [], sends := [], memory := [] }
  checkEqual "provided expressions count toward the degree bound" outputOnly.stats.maxLookupDegree 3
  checkEqual "provided claim does not add a required lookup slot" outputOnly.stats.lookups 0
  let empty : Circuit.System Rat := ⟨[], [], [], []⟩
  checkEqual "empty circuit" empty.stats []
  checkEqual "empty report" empty.formatStats "No chips."
  IO.println "Passed circuit statistics checks (columns, degrees, call/map/ROM slots, and inlining)."

end AiurCircuitStatsTests
