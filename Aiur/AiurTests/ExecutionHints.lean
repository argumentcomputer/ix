import Aiur.Modules.Frontend
import Aiur.Execution
import Mathlib.Algebra.Field.ZMod

open Aiur

namespace AiurExecutionHintTests

def source : Modules.Program Nat := aiur_modules% "
module Witness {
  type Numbers = [Field; 2];
  struct Pair { left: Field, right: Field }
  struct Box<T> { value: T }
  enum Choice { None, Some(Numbers), Large(Pair, Field) }
  enum Outer { Empty, Wrap(Choice), Large(Choice, Choice) }
  enum Unit { Unit }
  enum Other { Unit }
  opaque type Secret = Field;
  opaque struct SecretBox { value: Field }
  enum Hidden { Public, Private(Secret) }
  struct HasPointer { value: &Field }
  fn preimage(h: Field) -> Field {
    let p = hint::<Field>(h); assert_eq!(p * p, h, \"incorrect preimage\"); p
  }
  fn repeated(h: Field) -> Field { preimage(h) + preimage(h) }
  fn typed_keys() -> (Field, Field, Field, Field, Field) {
    (hint::<Field>(7), hint::<Field>((7,)), hint::<Field>(Unit::Unit),
      hint::<Field>(Other::Unit), hint::<Field>(()))
  }
  fn typed_results() -> (Field, (Field,)) { (hint::<Field>(7), hint::<(Field,)>(\"singleton\", 7)) }
  fn nested(key: Pair) -> Outer { hint::<Outer>(key) }
  fn boxed(n: Field) -> Box<Numbers> { hint::<Box<Numbers>>(\"boxed\", n) }
  fn zero() -> (Unit, [Unit; 2], [Field; 0]) { hint::<(Unit, [Unit; 2], [Field; 0])>(\"zero\", ()) }
  inline fn sample(n: Field) -> Field { hint::<Field>(\"sample\", n) }
  fn inlined(n: Field) -> (Field, Field) { (sample(n), sample(n)) }
  fn key_helper(x: Field) -> Field { x + 1 }
  fn key_effects(x: Field) -> Field { let p = &x; hint::<Field>(*p + key_helper(x)) }
  fn lazy(n: Field) -> Field { match n { 0 => 9, _ => hint::<Field>(n) } }
}
"

abbrev F := ZMod 97

private def named (name : String) : Generic.Ty := .named ("Witness::" ++ name) []

private def unit (name : String) : Execution.DataValue F := .construct (named name) "Unit" []

def entries : List String := ["Witness::repeated", "Witness::typed_keys", "Witness::typed_results",
  "Witness::nested", "Witness::boxed", "Witness::zero", "Witness::inlined", "Witness::key_effects", "Witness::lazy"]

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def query (result : Execution.Result) (name : String) : IO Execution.Query :=
  match result.queries.find? (·.name == name) with
  | some q => pure q
  | none => throw (IO.userError s!"missing query {name}")

private def expectError (result : Except String α) (part : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"expected error containing {part}")
  | .error message => check ((message.splitOn part).length > 1) s!"unexpected error: {message}"

def run : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let data : Array (Execution.HintEntry F) := #[⟨.field, 49, 7, ""⟩]
  let repeated ← IO.ofExcept (← exported.runFlat "Witness::repeated" #[49] data)
  check (repeated.output == #[14]) "hinted preimage result"
  let child ← query repeated "Witness::preimage"
  check (child.multiplicity == 2 && child.output == #[7]) "cached hinted query"
  let other ← IO.ofExcept (← exported.runFlat "Witness::repeated" #[49] #[⟨.field, 49, 90, ""⟩])
  check (other.output == #[83]) "execution sessions shared hints or query caches"
  expectError (← exported.runFlat "Witness::repeated" #[49]) "missing hint"
  expectError (← exported.runFlat "Witness::repeated" #[49] #[⟨.field, 49, 8, ""⟩]) "incorrect preimage"
  let duplicate ← IO.ofExcept (← exported.runFlat "Witness::repeated" #[49] (data ++ data))
  check (duplicate.output == #[14]) "identical hint rows rejected"
  -- A serialized IxVM fixture has more than 100,000 hint rows. Preparing the
  -- dataset must not consume one native stack frame per entry.
  let many : Array (Execution.HintEntry F) := Array.replicate 110000 ⟨.field, 49, 7, ""⟩
  let large ← IO.ofExcept (← exported.runFlat "Witness::repeated" #[49] many)
  check (large.output == #[14]) "large hint dataset"
  expectError (← exported.runFlat "Witness::repeated" #[49] (data.push ⟨.field, 49, 90, ""⟩)) "conflicting hint"

  let keys : Array (Execution.HintEntry F) := #[
    ⟨.field, 7, 1, ""⟩, ⟨.field, .tuple [7], 2, ""⟩,
    ⟨.field, unit "Unit", 3, ""⟩, ⟨.field, unit "Other", 4, ""⟩, ⟨.field, .tuple [], 5, ""⟩]
  let typed ← IO.ofExcept (← exported.runFlat "Witness::typed_keys" #[] keys)
  check (typed.output == #[1,2,3,4,5]) "hint key types lost during flattening"
  let results ← IO.ofExcept (← exported.runFlat "Witness::typed_results" #[]
    #[⟨.field, 7, 1, ""⟩, ⟨.tuple [.field], 7, .tuple [2], "singleton"⟩])
  check (results.output == #[1,2]) "hint result types lost during flattening"

  let key : Execution.DataValue F := .record (named "Pair") [("right", 4), ("left", 3)]
  let output : Execution.DataValue F := .construct (named "Outer") "Wrap"
    [.construct (named "Choice") "Some" [.array .field [5,6]]]
  let nestedData : Array (Execution.HintEntry F) := #[⟨named "Outer", key, output, ""⟩]
  let flat ← IO.ofExcept (exported.prepareHints nestedData)
  check (flat[0]!.key == [3,4]) "hint struct key field ordering"
  check (flat[0]!.output == [1,1,5,6,0,0,0,0,0]) "nested hint tags and padding"
  let nested ← IO.ofExcept (← exported.run "Witness::nested"
    #[← IO.ofExcept (Lean.Json.parse "{\"right\":4,\"left\":3}")] nestedData)
  check (nested.pretty_output == some "Witness::Outer::Wrap(Witness::Choice::Some([5, 6]))")
    "structured hinted output formatting"
  let boxedType : Generic.Ty := .named "Witness::Box" [named "Numbers"]
  let boxed : Execution.DataValue F := .record boxedType [("value", .array .field [8,9])]
  let box ← IO.ofExcept (← exported.runFlat "Witness::boxed" #[7] #[⟨boxedType, 7, boxed, "boxed"⟩])
  check (box.output == #[8,9]) "generic aliases in hint type did not resolve to compiler instance"
  let zeroType : Generic.Ty := .tuple [named "Unit", .array (named "Unit") 2, .array .field 0]
  let zeroValue : Execution.DataValue F := .tuple [unit "Unit",
    .array (named "Unit") [unit "Unit", unit "Unit"], .array .field []]
  let zero ← IO.ofExcept (← exported.runFlat "Witness::zero" #[] #[⟨zeroType, .tuple [], zeroValue, "zero"⟩])
  check zero.output.isEmpty "zero-width hint result"
  expectError (← exported.runFlat "Witness::zero" #[]) "missing hint"

  let inlined ← IO.ofExcept (← exported.runFlat "Witness::inlined" #[49] #[⟨.field, 49, 7, "sample"⟩])
  check (inlined.queries.size == 1 && inlined.output == #[7,7]) "inlined hints"
  let effects ← IO.ofExcept (← exported.runFlat "Witness::key_effects" #[4] #[⟨.field, 9, 17, ""⟩])
  check (effects.output == #[17] && effects.memory.size == 1) "hint key effects were skipped"
  check (effects.memory[0]!.multiplicity == 2 && (← query effects "Witness::key_helper").multiplicity == 1)
    "hint key call/store/load accounting"
  let lazy ← IO.ofExcept (← exported.runFlat "Witness::lazy" #[0])
  check (lazy.output == #[9]) "inactive hint requested a provider"

  for (bad, message) in ([
    (⟨.field, 7, .tuple [1], ""⟩, "hint output type mismatch"),
    (⟨.array .field 2, 7, .array .field [1, .tuple []], ""⟩, "component type mismatch"),
    (⟨named "Outer", 7, .construct (named "Outer") "Missing" [], ""⟩, "unknown data constructor"),
    (⟨named "Pair", 7, .record (named "Pair") [("left",1), ("left",2)], ""⟩, "duplicate field"),
    (⟨named "Pair", 7, .record (named "Pair") [("left",1), ("wrong",2)], ""⟩, "missing execution struct field"),
    (⟨named "Secret", 7, 1, ""⟩, "opaque"),
    (⟨.array (named "Secret") 0, 7, .array (named "Secret") [], ""⟩, "opaque"),
    (⟨named "Hidden", 7, .construct (named "Hidden") "Public" [], ""⟩, "opaque"),
    (⟨named "SecretBox", 7, .record (named "SecretBox") [("value",1)], ""⟩, "opaque"),
    (⟨.ptr .field, 7, 1, ""⟩, "pointers"),
    (⟨named "HasPointer", 7, .record (named "HasPointer") [("value",1)], ""⟩, "opaque component"),
    (⟨.field, .array (named "Secret") [], 1, ""⟩, "opaque"),
    (⟨.param "T", 7, 1, ""⟩, "concrete type")
  ] : List (Execution.HintEntry F × String)) do
    expectError (exported.prepareHints #[bad]) message
  IO.println "Passed Lean-defined hint data, Rust lookup, hinted execution, structured encoding and rejection checks."

end AiurExecutionHintTests
