import Aiur.Modules
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurTaglessTests
open Aiur

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def source : Program Nat := aiur% "
enum Unit { Unit }
enum Other { Unit }
enum Wrap { Wrap(Field) }
enum Nested { Nested((Unit, Wrap, Unit)) }
enum Choice { Empty(Unit), Full(Nested) }
enum Cover { Cover(Choice) }
fn make() -> Unit { Unit::Unit }
fn identity(u: Unit) -> Unit { let Unit::Unit = u; u }
fn caller() -> Unit { identity(make()) }
fn hinted() -> Unit { hint::<Unit>(()) }
fn memory() -> Unit { let p = &Unit::Unit; *p }
fn wrap(x: Field) -> Wrap { Wrap::Wrap(x) }
table inputs: (Unit,) { (Unit::Unit,) }
table outputs: Unit { Unit::Unit }
map unit_map(u: Unit) -> Unit = inputs => outputs;
fn mapped() -> Unit { unit_map(Unit::Unit) }
"

def aggregates : Generic.Program Nat := aiur% "
struct Empty {}
struct Bundle { values: [Empty; 3], pair: (Empty, Empty) }
fn make() -> Bundle { Bundle { values: [Empty {}; 3], pair: (Empty {}, Empty {}) } }
fn inspect(b: Bundle) -> Field {
  let Bundle { values, pair } = b;
  let Empty {} = values[2];
  let Empty {} = pair.1;
  9
}
fn caller() -> Field { inspect(make()) }
"

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def checkEncoding [Field F] [DecidableEq F] (fieldName : String) : IO Unit := do
  let unit : Value F := .construct "Unit" "Unit" []
  let wrap : Value F := .construct "Wrap" "Wrap" [7]
  let nested : Value F := .construct "Nested" "Nested" [.tuple [unit, wrap, unit]]
  let cases : List (Value F × List F) := [
    (unit, []), (wrap, [7]), (nested, [7]),
    (.construct "Choice" "Empty" [unit], [0, 0]),
    (.construct "Choice" "Full" [nested], [1, 7]),
    (.construct "Cover" "Cover" [.construct "Choice" "Full" [nested]], [1, 7])]
  for (value, words) in cases do
    let wire : WireValue F := ⟨value.type, words⟩
    ensure s!"{fieldName}: wrong tagless encoding" (value.encode source.enums == some wire)
    ensure s!"{fieldName}: wrong tagless decoding" (wire.decode source.enums == some value)
    let layout ← get <| (source.enums.layout value.type).mapError reprStr
    ensure s!"{fieldName}: wrong tagless width" (layout.width == words.length)
  for wire in ([⟨.enum "Unit", [0]⟩, ⟨.enum "Wrap", []⟩, ⟨.enum "Wrap", [0, 7]⟩,
      ⟨.enum "Choice", [0, 7]⟩, ⟨.enum "Choice", [1]⟩,
      ⟨.enum "Cover", [2, 0]⟩, ⟨.enum "Cover", [0, 7]⟩] : List (WireValue F)) do
    ensure s!"{fieldName}: malformed encoding accepted" (wire.decode source.enums).isNone
  let pointer ← get <| (source.enums.layout (.ptr (.enum "Unit"))).mapError reprStr
  ensure "pointer to zero-width value lost its address" (pointer.width == 1)

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def run : IO Unit := do
  checkEncoding (F := Rat) "Rat"
  checkEncoding (F := ZMod 3) "F3"
  let program := source.toField Rat
  let entries := program.functions.map (·.name)
  let optimized ← get <| Optimized.compile program entries
  let reference ← get <| (Circuit.compile program).mapError reprStr
  let unit : WireValue Rat := ⟨.enum "Unit", []⟩
  let identity : Circuit.Message Rat := ⟨"identity", [unit], unit⟩
  let cases : List (Circuit.Message Rat × List String) := [
    (⟨"make", [], unit⟩, ["make"]), (identity, ["identity"]),
    (⟨"caller", [], unit⟩, ["caller", "make", "identity"]),
    (⟨"hinted", [], unit⟩, ["hinted"]), (⟨"mapped", [], unit⟩, ["mapped"])]
  for (claim, names) in cases do
    for system in [reference, optimized.system] do
      let rows ← names.mapM fun name => do
        let some chip := system.findChip? name | throw (IO.userError s!"missing {name}")
        -- Reference single-constructor validation tests the implicit zero tag.
        -- Each equality gadget has witnesses [equal = 1, inverse = 0].
        return (⟨name, (List.range chip.numVars).map fun i => if i % 2 == 0 then 1 else 0⟩ : Circuit.Row Rat)
      let _ ← get <| (system.check ⟨[]⟩ claim rows).mapError reprStr
      let _ ← get <| (system.checkMemo ⟨[]⟩ claim (rows.map fun row => ⟨row, 1⟩)).mapError reprStr
    for name in names do
      let some chip := optimized.system.findChip? name | throw (IO.userError s!"missing {name}")
      ensure s!"{name}: unit operation retained columns" (chip.numVars == 0)
      ensure s!"{name}: unit output retained a tag" (chip.output.words.isEmpty)
  ensure "zero-width call premise was dropped"
    (optimized.check ⟨[]⟩ ⟨"caller", [], unit⟩ [⟨"caller", []⟩]).toOption.isNone
  ensure "zero-width input erased its argument position"
    (optimized.check ⟨[]⟩ ⟨"identity", [], unit⟩ [⟨"identity", []⟩]).toOption.isNone
  ensure "nominal type identity was erased"
    (optimized.check ⟨[]⟩ ⟨"identity", [⟨.enum "Other", []⟩], unit⟩ [⟨"identity", []⟩]).toOption.isNone
  let rom : WireROM Rat := ⟨[(0, unit)]⟩
  let memory : Circuit.Message Rat := ⟨"memory", [], unit⟩
  let rows : List (Circuit.Row Rat) := [⟨"memory", [0]⟩]
  let _ ← get <| optimized.check rom memory rows
  let _ ← get <| optimized.checkMemo rom memory (rows.map fun row => ⟨row, 1⟩)
  ensure "empty ROM payload lost its membership check" (optimized.check ⟨[]⟩ memory rows).toOption.isNone
  let prepared ← get <| Generic.prepare (aggregates.toField Rat)
  let specialized ← get <| Generic.specialize prepared ["make", "inspect", "caller"]
  let compiled ← get specialized.compileOptimized
  let empty : WireValue Rat := ⟨.enum "Bundle", []⟩
  let _ ← get <| compiled.artifact.check ⟨[]⟩ ⟨"make", [], empty⟩ [⟨"make", []⟩]
  let _ ← get <| compiled.artifact.check ⟨[]⟩ ⟨"inspect", [empty], .field 9⟩ [⟨"inspect", []⟩]
  let rows : List (Circuit.Row Rat) := [⟨"caller", [9]⟩, ⟨"make", []⟩, ⟨"inspect", []⟩]
  let _ ← get <| compiled.artifact.check ⟨[]⟩ ⟨"caller", [], .field 9⟩ rows
  let _ ← get <| compiled.artifact.checkMemo ⟨[]⟩ ⟨"caller", [], .field 9⟩
    (rows.map fun row => ⟨row, 1⟩)
  IO.println "Passed tagless enum checks: empty/nested encodings, structs, arrays, fields, calls, hints, maps, ROM, and both checkers."

/-- info: 'Aiur.Layout.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Layout.decode_encode
/-- info: 'Aiur.Layout.encode_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Layout.encode_decode

end AiurTaglessTests
