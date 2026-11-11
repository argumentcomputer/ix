import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurTableTests

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- Importing the frontend leaves these ordinary Lean identifiers available.
example (map table : Nat) : map + table = table + map := Nat.add_comm _ _

def source : Program Nat := aiur% "
enum Choice { Empty, Pair((Field, Field)) }
table pairs: (Field, Field) { (0, 0), (0, 1), (1, 0), (1, 1), }
table sums: Field { 0, 1, 1, 2, }
table products: Field { 0, 0, 0, 1, }
table xors: Field { 0, 1, 1, 0, }
map bit_add(a: Field, b: Field) -> Field = pairs => sums;
map bit_mul(a: Field, b: Field) -> Field = pairs => products;
map bit_xor(a: Field, b: Field) -> Field = pairs => xors;

table nested_inputs: ((Field, Field),) { ((2, 3),), ((5, 7),), }
table choices: Choice { Choice::Pair((3, 2)), Choice::Empty, }
map choose(p: (Field, Field)) -> Choice = nested_inputs => choices;

table enum_inputs: (Choice,) { (Choice::Empty,), (Choice::Pair((3, 2)),), }
table enum_outputs: (Field, ()) { (0, ()), (1, ()), }
map inspect(value: Choice) -> (Field, ()) = enum_inputs => enum_outputs;

table unit_inputs: () { (), }
table unit_outputs: () { (), }
map unit() -> () = unit_inputs => unit_outputs;

table empty_inputs: (Field,) { }
table empty_outputs: Field { }
map missing(x: Field) -> Field = empty_inputs => empty_outputs;

fn combined(a: Field, b: Field) -> (Field, Field, Field) {
    (bit_add(a, b), bit_mul(a, b), bit_xor(a, b))
}
fn nested() -> (Field, ()) { inspect(choose((2, 3))) }
fn lazy(x: Field) -> Field { match x { 0 => 9, _ => missing(4), } }
fn repeated() -> Field { bit_add(1, 1) + bit_add(1, 1) }
fn through_rom() -> Choice { let p = &choose((2, 3)); *p }
"

def program := source.toField Rat

def runtimeTests : List (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("direct map", eval program "bit_add" [1, 1], .ok 2),
  ("shared inputs multiply", eval program "bit_mul" [1, 1], .ok 1),
  ("shared inputs xor", eval program "bit_xor" [1, 1], .ok 0),
  ("repeated output rows", eval program "bit_add" [0, 1], .ok 1),
  ("repeated output rows second input", eval program "bit_add" [1, 0], .ok 1),
  ("ordinary calls", eval program "combined" [1, 1], .ok (.tuple [2, 1, 0])),
  ("one tuple argument", eval program "choose" [.tuple [2, 3]],
    .ok (.construct "Choice" "Pair" [.tuple [3, 2]])),
  ("enum empty result", eval program "choose" [.tuple [5, 7]], .ok (.construct "Choice" "Empty" [])),
  ("enum input", eval program "inspect" [.construct "Choice" "Pair" [.tuple [3, 2]]],
    .ok (.tuple [1, .tuple []])),
  ("nested map calls", eval program "nested" [], .ok (.tuple [1, .tuple []])),
  ("zero arguments and unit result", eval program "unit" [], .ok (.tuple [])),
  ("empty map", eval program "missing" [0], .error (.missingMapInput "missing")),
  ("absent input", eval program "bit_add" [2, 0], .error (.missingMapInput "bit_add")),
  ("wrong arity", eval program "bit_add" [.tuple [1, 1]], .error (.arityMismatch "bit_add" 2 1)),
  ("tuple remains one argument", eval program "choose" [2, 3], .error (.arityMismatch "choose" 1 2)),
  ("wrong argument type", eval program "bit_add" [.tuple [1], 0],
    .error (.argumentTypeMismatch "bit_add" .field (.tuple [.field]))),
  ("inactive map call", eval program "lazy" [0], .ok 9),
  ("active missing map call", eval program "lazy" [1], .error (.missingMapInput "missing")),
  ("same claim twice", eval program "repeated" [], .ok 4),
  ("map result stored in ROM", eval program "through_rom" [],
    .ok (.construct "Choice" "Pair" [.tuple [3, 2]])),
  ("zero fuel", eval program "bit_add" [1, 1] 0, .error .outOfFuel)
]

/-- Generators construct the same field-agnostic AST used by the string frontend. -/
def generated : Program Nat := {
  functions := []
  tables := [
    { name := "inputs", rowType := .tuple [.field, .field]
      rows := (List.range 4).flatMap fun a => (List.range 4).map fun b => .tuple [.field a, .field b] },
    { name := "outputs", rowType := .field
      rows := (List.range 4).flatMap fun a => (List.range 4).map fun b => .field (a + b) }
  ]
  maps := [⟨"add", [("a", .field), ("b", .field)], .field, "inputs", "outputs"⟩]
}

example : typecheck generated = .ok () := by decide +kernel
example : eval (generated.toField Rat) "add" [2, 3] = .ok 5 := by decide +kernel

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def collision : Program Nat := aiur% "
table inputs: (Field,) { (0,), (7,), }
table outputs: Field { 1, 1, }
map collide(x: Field) -> Field = inputs => outputs;
"
example : typecheck (collision.toField (ZMod 7)) = .error (.duplicateInput "collide" "inputs") := by decide +kernel
example : (compile (collision.toField (ZMod 7))).isOk = false := by decide +kernel
example : (run (collision.toField (ZMod 7)) "collide" [0]).isOk = false := by decide +kernel

/-- Partitioning must accept repeated first arguments, but still reject full
row collisions, including nonadjacent rows that collide only in the field. -/
def pairCollision : Program Nat := aiur% "
table inputs: (Field, Field) { (0, 0), (1, 0), (0, 1), (7, 0), }
table outputs: Field { 0, 1, 2, 3, }
map pair_lookup(a: Field, b: Field) -> Field = inputs => outputs;
"
example : typecheck pairCollision = .ok () := by decide +kernel
example : typecheck (pairCollision.toField Rat) = .ok () := by decide +kernel
example : typecheck (pairCollision.toField (ZMod 7)) =
    .error (.duplicateInput "pair_lookup" "inputs") := by decide +kernel

def system : System Rat := (compile program).toOption.getD { chips := [] }
theorem compiled : compile program = .ok system := by
  have succeeds : (compile program).isOk = true := by decide +kernel
  cases lowered : compile program with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [system, lowered, Except.toOption]

-- Tables are retained once and maps have no generated function chips.
example : system.tables.length = source.tables.length := by decide +kernel
example : system.chips.length = source.functions.length := by decide +kernel
example : system.findChip? "bit_add" = none := by decide +kernel

private def accepts (claim : Message Rat) : Bool := (system.check ⟨[]⟩ claim []).isOk

def membershipTests : List (String × Bool × Bool) := [
  ("static root needs no chip rows", accepts ⟨"bit_add", [1, 1], 2⟩, true),
  ("other operation same inputs", accepts ⟨"bit_xor", [1, 1], 0⟩, true),
  ("wrong result", accepts ⟨"bit_add", [1, 1], 0⟩, false),
  ("wrong row alignment", accepts ⟨"bit_add", [0, 0], 1⟩, false),
  ("wrong map identity", accepts ⟨"bit_mul", [1, 1], 2⟩, false),
  ("absent tuple", accepts ⟨"bit_add", [2, 0], 2⟩, false),
  ("tuple is not two arguments", accepts ⟨"bit_add", [.tuple [1, 1]], 2⟩, false),
  ("singleton output is distinct", accepts ⟨"bit_add", [1, 1], .tuple [2]⟩, false),
  ("empty static map", accepts ⟨"missing", [0], 0⟩, false),
  ("dynamic root still needs rows", accepts ⟨"repeated", [], 4⟩, false),
  ("unit static claim", accepts ⟨"unit", [], .tuple []⟩, true),
  ("repeated static claims need no provider rows",
    (system.check ⟨[]⟩ ⟨"repeated", [], 4⟩ [⟨"repeated", [4, 2, 2]⟩]).isOk, true),
  ("valid equations cannot justify absent static claims",
    (system.check ⟨[]⟩ ⟨"repeated", [], 0⟩ [⟨"repeated", [0, 0, 0]⟩]).isOk, false)
]

-- Both derivation models use an explicit, premise-free membership leaf.
def tableLeaf : Derivation system ⟨[]⟩ ⟨"bit_add", [1, 1], 2⟩ := .table (by decide +kernel)
example : MemoDerives system ⟨[]⟩ ⟨"bit_add", [1, 1], 2⟩ := ⟨tableLeaf.toMemo⟩

-- The complete source-to-circuit theorem covers map calls, inactive lookups, and ROM.
example : EncodedEntryDerives system "repeated" (entryValues []) (.field 4) := by
  have executed : run program "repeated" [] 16 = .ok (.field 4, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa [Value.mapAddress] using complete

example : EncodedEntryDerives system "lazy" (entryValues [0]) (.field 9) := by
  have executed : run program "lazy" [0] 16 = .ok (.field 9, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa [Value.mapAddress] using complete

example : EncodedEntryDerives system "through_rom" (entryValues [])
    (.construct "Choice" "Pair" [.tuple [.field 3, .field 2]]) := by
  have executed : run program "through_rom" [] 20 =
      .ok (.construct "Choice" "Pair" [.tuple [.field 3, .field 2]], [.construct "Choice" "Pair" [.tuple [.field 3, .field 2]]]) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (99 : Rat)) (by intro i j hi hj _; simp at hi hj; omega)
  simpa [Value.mapAddress] using complete

example (accepted : EncodedEntryDerives system "bit_add" (entryValues [1, 1]) (.field 0)) : False := by
  have wrong := compiler_entry_sound compiled accepted (by decide +kernel)
  have actual : EvalCall program "bit_add" [1, 1] (.field 2) := eval_spec (hints := HintProvider.unavailable) (fuel := 4) (by decide +kernel)
  have same := actual.deterministic wrong (by decide +kernel)
  simp [Value.mapAddress] at same

example (graph : MemoDerivation system ⟨[]⟩ ⟨"bit_add", [.field 1, .field 1], .field 0⟩)
    (acyclic : graph.Acyclic) : False := by
  obtain ⟨args, value, decoded, output, evaluated⟩ := memo_acyclic_sound compiled graph acyclic
  have argsEq : args = [.field 1, .field 1] := decoded.unique
    (.cons (WireValue.decode_field _ _) (.cons (WireValue.decode_field _ _) .nil))
  have resultEq : value = .field 0 := Option.some.inj (output.symm.trans (WireValue.decode_field _ _))
  subst args
  subst value
  cases evaluated with
  | intro prepared body =>
    have expected : prepareCall program "bit_add" [.field 1, .field 1] =
        .ok (([] : Environment Rat), .literal 2) := by
      simpa only [Constant.toExpr] using
        (prepareCall_map (program := program) (name := "bit_add")
          (args := ([.field 1, .field 1] : List (Value Rat))) (value := .field 2)
          (by rfl) (by decide +kernel))
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (prepared.symm.trans expected))
    have same := (ROMEvalExprWith.constant_iff (.field 2 : Constant Rat)).mp
      (by simpa only [Constant.toExpr] using body.toEvalExprWith)
    simp [Constant.toValue, Value.mapAddress] at same

run_cmd do
  let env ← Lean.getEnv
  for text in [
    "table x: (Field,) { (0,), (0,), } table y: Field { 1, 1, } map f(a: Field) -> Field = x => y;",
    "table x: (Field,) { (0,), } table y: Field { } map f(a: Field) -> Field = x => y;",
    "map f(a: Field) -> Field = absent => absent;",
    "table x: Field { (1,), }",
    "enum E { A(Field) } table x: E { E::A, }",
    "table x: Field { 0, } table x: Field { 1, }",
    "table x: () { (), } table y: Field { 0, } map f() -> Field = x => y; fn f() -> Field { 0 }",
    "table x: () { (), } table y: Field { 0, } map f() -> Field = x => y; map f() -> Field = x => y;",
    "table x: (&Field,) { (&1,), }",
    "enum E { P(&Field) } table x: E { E::P(&1), }",
    "table x: Field { 1 + 2, }",
    "table x: Field { f(), } fn f() -> Field { 1 }",
    "table x: (Field,) { (0,), } table y: Field { 1, } map f(a) -> Field = x => y;",
    "table x: (Field,) { (0,), } table y: Field { 1, } map f(a: Field) = x => y;",
    "table x: (Field,) { (0,), } table y: Field { 1, } map f(a: Field, a: Field) -> Field = x => y;",
    "table x: Field { 0, } table y: Field { 1, } map f(a: Field) -> Field = x => y;",
    "table x: (Field,) { (0,), } table y: (Field,) { (1,), } map f(a: Field) -> Field = x => y;"
  ] do
    match Frontend.ofString env text with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted table program: {text}"

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in runtimeTests do checkEqual label actual expected
  for (label, actual, expected) in membershipTests do checkEqual label actual expected
  IO.println s!"Passed {runtimeTests.length + membershipTests.length} table and map checks."

end AiurTableTests
