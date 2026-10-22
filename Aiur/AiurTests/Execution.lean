import Aiur.Modules.Frontend
import Aiur.Execution
import AiurTests.ExecutionHints
import Mathlib.Algebra.Field.ZMod

open Aiur

namespace AiurExecutionTests

def source : Modules.Program Nat := aiur_modules% "
module Test {
  struct Pair { left: Field, right: Field }
  struct Box<T> { value: T }
  enum Choice { None, Some([Field; 2]), Large(Pair, Field) }
  enum Outer { Empty, Wrap(Choice), Pair(Choice, Choice) }
  enum Unit { Unit }
  opaque type Secret = Field;
  enum Mixed { Public(Field), Private(Secret) }
  type Numbers = [Field; 2];
  table inputs: (Field, Field) { (0,0), (0,1), (1,0), (1,1) }
  table sums: Field { 0,1,1,2 }
  table products: Field { 0,0,0,1 }
  map add(a: Field, b: Field) -> Field = inputs => sums;
  map mul(a: Field, b: Field) -> Field = inputs => products;
  inline fn twice(x: Field) -> Field { x + x }
  fn inner(x: Field) -> Field { x + 1 }
  fn outer(x: Field) -> Field { inner(x) + inner(x) }
  fn sharing(x: Field) -> Field { outer(x) + outer(x) }
  fn fib(n: Field) -> Field {
    match n { 0 => 0, 1 => 1, _ => fib(n - 1) + fib(n - 2) }
  }
  fn pair(n: Field) -> Pair { Pair { right: fib(n), left: fib(n) } }
  fn array(xs: Numbers) -> Box<Numbers> {
    Box { value: xs with { [0] = twice(xs[1]) } }
  }
  fn choice(x: Choice) -> Choice {
    match x { Choice::Some([0, a]) => Choice::Some([a, 0]), _ => x }
  }
  fn nested(x: Outer) -> Outer { x }
  fn unit(x: Unit) -> (Unit, [Unit; 2]) { (x, [x; 2]) }
  fn loaded(p: &[Field; 2]) -> Field { let &a = p; a[0] + a[1] }
  fn memory(x: Field) -> Field {
    let p = &[x, x + 1]; let q = &[x, x + 1]; loaded(p) + loaded(q)
  }
  fn table(a: Field, b: Field) -> (Field, Field, Field) { (add(a,b), mul(a,b), add(a,b)) }
  fn arithmetic(a: Field, b: Field) -> Field { -(a * b) + a / b - 1 }
  fn choose(x: Field) -> Field {
    let y = 'chosen: { match x { 0 => break 'chosen 7, 1 => return 20, _ => () }; 9 };
    y + 1
  }
  fn refutable(x: Field) -> Field { let 3 = x; 8 }
  fn asserted(x: Field) -> Field { assert_eq!(x, 4, \"expected four\"); 9 }
  fn constrained(x: Field) -> Field { constrain_eq!(x * x, 4, \"expected square four\"); 9 }
  fn hint_key(x: Field) -> Field { 1 / x }
  fn hinted(x: Field) -> Field { hint::<Field>(hint_key(x)) }
  fn lazy(x: Field) -> Field { match x { 0 => 7, _ => hinted(1) } }
  fn secret() -> Secret { 5 }
  fn mixed() -> Mixed { Mixed::Public(5) }
  fn empty_secret() -> [Secret; 0] { [] }
  fn pointer() -> &Field { &5 }
  fn cycle(x: Field) -> Field { cycle(x) }
}
module Alias = Test;
"

instance : Fact (Nat.Prime 97) := ⟨by decide⟩
abbrev F := ZMod 97

def entries : List String := ["Test::sharing", "Alias::pair", "Test::fib", "Test::array", "Test::choice",
  "Test::unit", "Test::memory", "Test::table", "Test::arithmetic", "Test::choose", "Test::refutable",
  "Test::asserted", "Test::hinted", "Test::lazy", "Test::secret", "Test::pointer", "Test::cycle",
  "Test::nested", "Test::mixed", "Test::empty_secret", "Test::constrained"]

def largeFieldSource : Modules.Program Nat := aiur_modules% "
module Large {
  fn identity(x: Field) -> Field { x }
  fn square(x: Field) -> Field { x * x }
}
"

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def query (result : Execution.Result) (name : String) (args : Array Nat) : IO Execution.Query :=
  match result.queries.find? (fun q => q.name == name && q.args == args) with
  | some q => pure q
  | none => throw (IO.userError s!"missing query {name}{args.toList}")

private def json (source : String) : IO Lean.Json := IO.ofExcept (Lean.Json.parse source)

def run : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) entries)
  let exported ← IO.ofExcept prepared.exportExecution
  check (!(exported.bytecode.functions.map (·.name)).contains "Test::twice") "inline helper survived"
  let runFlat := fun (name : String) (args : Array Nat) => do IO.ofExcept (← exported.runFlat name args)
  let sharing ← runFlat "Test::sharing" #[4]
  check (sharing.output == #[20]) "memoized result"
  check ((← query sharing "Test::sharing" #[4]).multiplicity == 1) "entry multiplicity"
  check ((← query sharing "Test::outer" #[4]).multiplicity == 2) "cache hit multiplicity"
  check ((← query sharing "Test::inner" #[4]).multiplicity == 2) "cache hit repeated child effects"
  let fib ← runFlat "Test::fib" #[10]
  check (fib.output == #[55] && fib.queries.size == 11) "Fibonacci memoization"
  let pair ← runFlat "Alias::pair" #[10]
  check (pair.output == #[55,55]) "struct initializer order"
  check (pair.pretty_output == some "Test::Pair { left: 55, right: 55 }") "struct output formatting"
  let array ← IO.ofExcept (← exported.run "Test::array" #[← json "[3, 4]"])
  check (array.output == #[8,4]) "array update"
  check (array.pretty_output == some "Test::Box<Test::Numbers> { value: [8, 4] }")
    s!"generic struct/array formatting: {array.pretty_output}"
  let choice ← IO.ofExcept (← exported.run "Test::choice" #[← json "{\"Some\":[[0,7]]}"])
  check (choice.output == #[1,7,0,0]) "enum pattern and padding"
  check (choice.pretty_output == some "Test::Choice::Some([7, 0])") "enum output formatting"
  let nested ← IO.ofExcept (← exported.run "Test::nested" #[← json "{\"Wrap\":[{\"Some\":[[5,6]]}]}"])
  check (nested.output == #[1,1,5,6,0,0,0,0,0]) "nested enum encoding"
  check (nested.pretty_output == some "Test::Outer::Wrap(Test::Choice::Some([5, 6]))") "nested enum output"
  let unit ← IO.ofExcept (← exported.run "Test::unit" #[← json "{\"Unit\":[]}"])
  check (unit.output.isEmpty) "tagless unit width"
  check (unit.pretty_output == some "(Test::Unit::Unit, [Test::Unit::Unit, Test::Unit::Unit])") "zero-width arrays"
  let memory ← runFlat "Test::memory" #[4]
  check (memory.output == #[18] && memory.memory.size == 1) "interned typed ROM"
  check ((← query memory "Test::loaded" #[0]).multiplicity == 2) "pointer query cache"
  check (memory.memory[0]!.multiplicity == 3) "cached call repeated ROM load"
  let table ← runFlat "Test::table" #[1,1]
  check (table.output == #[2,1,2]) "static maps"
  check ((← query table "Test::add" #[1,1]).multiplicity == 2) "map cache counts"
  for (name, args) in [("Test::arithmetic", [12,3]), ("Test::choose", [0]), ("Test::choose", [1]), ("Test::choose", [2]), ("Test::refutable", [3])] do
    let result ← runFlat name args.toArray
    let (value, _) ← IO.ofExcept (prepared.run name (args.map fun n => .field (Nat.cast n)))
    let .field expected := value | throw (IO.userError "expected field result")
    check (result.output == #[expected.val]) s!"Rust/native evaluation disagreement for {name}"
  let lazy ← runFlat "Test::lazy" #[0]
  let deferred ← runFlat "Test::constrained" #[3]
  check (deferred.output == #[9]) "constrain_eq was checked by Rust"
  check ((prepared.run "Test::constrained" [.field 3]).toOption.isNone)
    "constrain_eq was weakened in the source semantics"
  check (lazy.output == #[7]) "inactive hint was executed"
  let secret ← runFlat "Test::secret" #[]
  check (secret.pretty_output.isNone) "opaque alias leaked through pretty IO"
  let mixed ← runFlat "Test::mixed" #[]
  check (mixed.pretty_output.isNone) "inactive opaque variant leaked through pretty IO"
  let emptySecret ← runFlat "Test::empty_secret" #[]
  check (emptySecret.pretty_output.isNone) "empty opaque array leaked through pretty IO"
  let pointer ← runFlat "Test::pointer" #[]
  check (pointer.pretty_output.isNone) "pointer leaked through pretty IO"
  for (name, args, expected) in [
      ("Test::arithmetic", #[1,0], "division by zero"),
      ("Test::refutable", #[2], "let pattern mismatch"),
      ("Test::asserted", #[3], "expected four"),
      ("Test::hinted", #[0], "division by zero"),
      ("Test::cycle", #[1], "already being evaluated"),
      ("Test::table", #[2,0], "no table entry"),
      ("Test::choice", #[3,0,0,0], "invalid enum tag"),
      ("Test::choice", #[0,0,0,1], "nonzero enum padding"),
      ("Test::fib", #[97], "noncanonical"),
      ("Test::inner", #[1], "unselected entrypoint")] do
    match ← exported.runFlat name args with
    | .ok _ => throw (IO.userError s!"unexpected execution success: {name}")
    | .error message => check ((message.splitOn expected).length > 1) s!"unexpected error: {message}"
  let large ← IO.ofExcept do
    let p ← Modules.prepare (largeFieldSource.toField (ZMod 18446744069414584321)) ["Large::identity", "Large::square"]
    p.exportExecution
  let big ← IO.ofExcept (← large.runFlat "Large::identity" #[18446744069414584320])
  check (big.output == #[18446744069414584320]) "UInt64 FFI value was rounded"
  let squared ← IO.ofExcept (← large.runFlat "Large::square" #[18446744069414584320])
  check (squared.output == #[1]) "Goldilocks field multiplication"
  AiurExecutionHintTests.run
  IO.println "Passed execution bytecode, Rust FFI, memoization, ROM, maps, structured IO and native comparison checks."

end AiurExecutionTests
