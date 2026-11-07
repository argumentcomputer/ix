import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurArrayTests
open Aiur
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def source : Generic.Program Nat := aiur% "
type Four<T> = [T; 4];
type Matrix<T> = [[T; 2]; 2];
type Maybe<T> = Option<T>;
enum Option<T> { None, Some(T) }
const zero = 0;
const zeros = [zero; 4];
const cell = &[zero];
const cells = [&zero; 2];
const matrix = [[1, 2]; 2];

fn identity<T>(x: T) -> T { x }
fn twice<T>(x: T) -> [T; 2] { [x; 2] }
fn first<T>(a: [T; 2]) -> T { a[0] }
fn last<T>(a: [T; 2]) -> T { a[1] }
fn pair([a, b]: [Field; 2]) -> Field { a + b }
fn singleton([x]: [Field; 1]) -> Field { x }
fn unit([]: [Field; 0]) -> Field { 9 }
fn take_two<T>(a: Four<T>) -> [T; 2] { a[..2] }
fn suffix<T>(a: Four<T>) -> [T; 2] { a[2..] }
fn full<T>(a: Four<T>) -> Four<T> { a[..] }
fn middle<T>(a: Four<T>) -> [T; 2] { a[1..3] }
fn inclusive<T>(a: Four<T>) -> [T; 2] { a[1..=2] }
fn inclusive_zero<T>(a: Four<T>) -> [T; 2] { a[..=1] }
fn at_end<T>(a: Four<T>) -> [T; 0] { a[4..4] }
fn all_slices() -> ([Field; 2], [Field; 2], [Field; 4], [Field; 2], [Field; 2], [Field; 2], [Field; 0]) {
  let a = [1, 2, 3, 4,];
  (take_two(a), suffix(a), full(a), middle(a), inclusive(a), inclusive_zero(a), at_end(a))
}
fn nested() -> Field { matrix[1][0] + [(3, 4), (5, 6)][1].0 }
fn generic_enum() -> [Field; 2] {
  match Maybe::Some(identity([7, 8])) { Maybe::Some([a, b]) => [b, a], Maybe::None => [0; 2] }
}
fn infer_empty_ctor() -> [Option<Field>; 2] { [Option::None; 2] }
fn empty() -> [Field; 0] { [] }
fn empty_repeat() -> [Field; 0] { [5; 0] }
fn simple() -> Field { pair(twice(3)) + singleton([4]) + unit([]) }
fn ordered(a: [Field; 2]) -> Field {
  match a { [0, x] => x + 10, [x, 0] => x + 20, [x, y] => x + y }
}
fn refutable(a: [Field; 2]) -> Field { let [0, x] = a; x }
fn const_match() -> Field { let ::zeros = [0, 0, 0, 0]; let ::cell = cell; 7 }
fn const_repeat() -> [&Field; 2] { cells }
fn const_pattern() -> Field { let ::cells = [&0, &0]; 11 }
fn repeated() -> [&Field; 2] { [&1; 2] }
fn separate() -> [&Field; 2] { [&1, &1] }
fn empty_effect() -> [&Field; 0] { [&1; 0] }
fn empty_error() -> [Field; 0] { [1 / 0; 0] }
fn produce() -> [Field; 3] { let p = &[1, 2, 3]; *p }
fn slice_once() -> [Field; 2] { produce()[1..] }
fn index_once() -> Field { produce()[2] }
fn slice_empty() -> [Field; 0] { produce()[1..1] }
fn slice_error() -> [Field; 0] { [1 / 0][0..0] }
fn load_array(&[a, b]: &[Field; 2]) -> Field { a + b }
fn pointers() -> Field { load_array(&[3, 4]) }
fn pointer_match(x: Field) -> Field {
  match [&x, &5] { [&0, &b] => b, [&a, &b] => a + b }
}
fn repeated_pattern(x: Field) -> Field { match [x; 3] { [0; 3] => 1, [_; 3] => 2 } }
fn shadow(zero: Field) -> [Field; 2] { let [zero, x] = [zero, ::zero]; [zero, x] }
fn inactive() -> [Field; 2] { match 0 { 0 => [3; 2], _ => [1 / 0; 2] } }
fn hinted(key: Field) -> [Option<Field>; 2] { hint::<[Option<Field>; 2]>(key) }
fn repeated_hint() -> [Field; 2] { [hint::<Field>(*&9); 2] }
fn zero_hint() -> [Field; 0] { [hint::<Field>(()); 0] }
fn empty_pointer_arg(x: [&Field; 0]) -> Field { 0 }
fn empty_pointer_internal() -> Field { empty_pointer_arg([]) }
fn static_length() -> Field { [7, 8, 9, 10, 11, 12, 13, 14][7] }
"

def runSource (name : String) (args : List (SourceValue Rat) := []) := do
  let s ← Generic.prepare (source.toField Rat)
  s.run name args

def runSpecialized (name : String) (args : List (SourceValue Rat) := []) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.run name args

def runCore (name : String) (args : List (SourceValue Rat) := []) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.coreRun name args

def checks : List (String × Except String (SourceValue Rat × Heap Rat)) := [
  ("all_slices", .ok (.tuple [
    .tuple [1, 2], .tuple [3, 4], .tuple [1, 2, 3, 4], .tuple [2, 3],
    .tuple [2, 3], .tuple [1, 2], .tuple []], [])),
  ("nested", .ok (6, [])),
  ("generic_enum", .ok (.tuple [8, 7], [])),
  ("empty", .ok (.tuple [], [])),
  ("empty_repeat", .ok (.tuple [], [])),
  ("simple", .ok (19, [])),
  ("const_match", .ok (7, [.tuple [0]])),
  ("const_repeat", .ok (.tuple [.ptr .field 0, .ptr .field 0], [0])),
  ("const_pattern", .ok (11, [0, 0])),
  ("repeated", .ok (.tuple [.ptr .field 0, .ptr .field 0], [1])),
  ("separate", .ok (.tuple [.ptr .field 0, .ptr .field 1], [1, 1])),
  ("empty_effect", .ok (.tuple [], [1])),
  ("empty_error", .error (reprStr EvalError.divisionByZero)),
  ("slice_once", .ok (.tuple [2, 3], [.tuple [1, 2, 3]])),
  ("index_once", .ok (3, [.tuple [1, 2, 3]])),
  ("slice_empty", .ok (.tuple [], [.tuple [1, 2, 3]])),
  ("slice_error", .error (reprStr EvalError.divisionByZero)),
  ("pointers", .ok (7, [.tuple [3, 4]])),
  ("inactive", .ok (.tuple [3, 3], [])),
  ("empty_pointer_internal", .ok (0, [])),
  ("zero_hint", .error (reprStr (EvalError.hint .unavailable)))
]

#guard checks.all fun (name, expected) => runSource name == expected && runSpecialized name == expected && runCore name == expected
#guard runSource "ordered" [.tuple [0, 0]] == .ok (10, [])
#guard runSource "ordered" [.tuple [3, 0]] == .ok (23, [])
#guard runSpecialized "ordered" [.tuple [3, 4]] == .ok (7, [])
#guard runSource "refutable" [.tuple [0, 8]] == .ok (8, [])
#guard runSource "refutable" [.tuple [1, 8]] == .error (reprStr EvalError.patternMismatch)
#guard runSource "pointer_match" [0] == .ok (5, [0, 5])
#guard runSpecialized "pointer_match" [3] == .ok (8, [3, 5])
#guard runSource "repeated_pattern" [0] == .ok (1, [])
#guard runSource "repeated_pattern" [7] == .ok (2, [])
#guard runSource "shadow" [6] == .ok (.tuple [6, 0], [])
#guard (runSource "empty_pointer_arg" [.tuple []]).toOption.isNone

def tables : Generic.Program Nat := aiur% "
type Pair = [Field; 2];
const key = [0, 1];
table inputs: (Pair,) { (key,), ([2; 2],) }
table outputs: Pair { [3; 2], [4, 5] }
map lookup(a: Pair) -> Pair = inputs => outputs;
fn main() -> Pair { lookup(key) }
"
#guard (do
  let s ← Generic.prepare (tables.toField Rat)
  let q ← Generic.specialize s ["main"]
  q.run "main" []) == .ok (.tuple [3, 3], [])
#guard (do
  let s ← Generic.prepare (tables.toField (ZMod 101))
  let q ← Generic.specialize s ["main"]
  return (← q.compile).system.chips.length).toOption.isSome

-- A typed provider sees the same tuple layout as the core evaluator.
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let hints := s.checkedHints fun _ key => match key with
    | .field n => .ok (.field (n + 1))
    | _ => .error .unavailable
  s.run "repeated_hint" [] (hints := hints)) == .ok (.tuple [10, 10], [9])
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let hints := s.checkedHints fun _ _ => .ok (.tuple [.field 1, .field 2])
  s.run "hinted" [0] (hints := hints)).toOption.isNone
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let option := (Generic.Instance.mk "Option" [.field]).symbol
  let value : Constant Rat := .tuple [.construct option "None" [], .construct option "Some" [8]]
  let hints := s.checkedHints fun _ _ => .ok value
  return (← s.run "hinted" [0] (hints := hints)) == (value.toValue, [])) == .ok true

-- Lengths and bounds remain natural numbers when literals change fields.
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 7))
  s.run "static_length" []) == .ok (.field 0, [])

-- Array/tuple distinction must survive table-map signature checking.
run_cmd do
  let env ← Lean.getEnv
  for code in [
    "fn f() -> [Field; 2] { [0, ()] }",
    "fn f() -> [Field; 2] { [0] }",
    "fn f() -> [Field; 2] { (0, 0) }",
    "fn f() -> (Field, Field) { [0; 2] }",
    "fn f() -> Field { [0][1] }",
    "fn f() -> Field { [0].0 }",
    "fn f() -> Field { (0,)[0] }",
    "fn f(i: Field) -> Field { [0, 1][i] }",
    "fn f() -> Field { [0, 1][1 + 0] }",
    "fn f() -> Field { [0][-1] }",
    "fn f() -> Field { [][0] }",
    "fn f() -> [Field; 1] { [0, 1][2..1] }",
    "fn f() -> [Field; 1] { [0][0..2] }",
    "fn f() -> [Field; 0] { [0][2..2] }",
    "fn f() -> [Field; 2] { [0][..=1] }",
    "fn f(n: Field) -> [Field; 1] { [0][..n] }",
    "fn f() -> [Field; 1] { (0,)[..] }",
    "fn f() -> Field { let [x, y] = [0]; x }",
    "fn f() -> Field { let [x, x] = [0, 0]; x }",
    "fn f() -> Field { let [x; 2] = [0; 2]; x }",
    "fn f() -> Field { let [x; 0] = [0; 0]; x }",
    "fn f([0]: [Field; 1]) -> Field { 0 }",
    "fn f(a: [&Field; 2]) -> Field { match a { [&0; 2] => 1, [&0, &0] => 2, _ => 3 } }",
    "fn f() -> [Field; 2] { [0; x] }",
    "fn f() -> [Field; 2] { [0; 65537] }",
    "fn f() -> [Field; 65537] { [] }",
    "const a = [a; 0];",
    "const a = [b]; const b = a;",
    "const a = [_; 3];",
    "const a = [0, ()];",
    "type Bad = [Bad; 0];",
    "enum Bad { Wrap([Bad; 0]) }",
    "enum Bad { Wrap([Bad; 2]) }",
    "enum A { Wrap([B; 0]) } enum B { Wrap(A) }",
    "table t: [&Field; 0] { [] }",
    "enum E { A, B([&Field; 0]) } table t: E { E::A }",
    "fn f() -> [&Field; 0] { hint::<[&Field; 0]>(()) }",
    "enum E { A, B([&Field; 0]) } fn f() -> E { hint::<E>(()) }",
    "table i: [Field; 2] { [0, 1] } table o: Field { 0 } map m(a: Field, b: Field) -> Field = i => o;",
    "table i: () { () } table o: [Field; 2] { [0, 1] } map m() -> (Field, Field) = i => o;",
    "table i: () { () } table o: [Field; 0] { [] } map m() -> [(); 0] = i => o;"
  ] do
    match Generic.Frontend.ofString env code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"

def duplicate : Generic.Program Nat := aiur% "
fn main(a: [Field; 2]) -> Field { match a { [0; 2] => 1, [0, 0] => 2, _ => 3 } }
"
#guard (do
  let s ← Generic.prepare (duplicate.toField Rat)
  let q ← Generic.specialize s ["main"]
  return (← q.compile).system.chips.length).toOption.isNone

def boundary : Generic.Program Nat := aiur% "
enum E { A, B([&Field; 0]) }
fn entry(x: E) -> Field { 0 }
"
#guard (do
  let s ← Generic.prepare (boundary.toField Rat)
  s.checkEntry "entry").toOption.isNone

def collision : Generic.Program Nat := aiur% "
fn main(a: [Field; 1]) -> Field { match a { [1] => 2, [102] => 3, _ => 4 } }
"
#guard (do
  let s ← Generic.prepare (collision.toField (ZMod 101))
  let q ← Generic.specialize s ["main"]
  return (← q.compile).system.chips.length).toOption.isNone

def shuffle : Generic.Program Nat := aiur% "
fn index(a: [Field; 4]) -> Field { a[2] }
fn slice(a: [Field; 4]) -> [Field; 2] { a[1..3] }
fn repeated(a: Field) -> [Field; 4] { [a; 4] }
"
-- No selector columns or lookup messages are introduced by static operations.
#guard (do
  let s ← Generic.prepare (shuffle.toField Rat)
  let q ← Generic.specialize s ["index", "slice", "repeated"]
  let chips := (← q.compile).system.chips
  return chips.map (fun (c : Circuit.Chip Rat) => (c.numVars, c.sends.length, c.memory.length))) ==
    .ok [(5, 0, 0), (6, 0, 0), (5, 0, 0)]

#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s
    ["all_slices", "nested", "generic_enum", "infer_empty_ctor", "const_match", "const_repeat",
     "const_pattern", "slice_once", "slice_empty", "repeated", "separate", "empty_effect",
     "ordered", "refutable", "pointers", "pointer_match", "hinted", "repeated_hint", "inactive"]
  return (← q.compile).system.chips.length).toOption.isSome

/-- info: 'Aiur.Generic.ArrayLowering.repeatValue_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.ArrayLowering.repeatValue_iff

def run : IO Unit := do
  for (name, expected) in checks do
    for actual in [runSource name, runSpecialized name, runCore name] do
      unless actual = expected do
        throw (IO.userError s!"array {name}: expected {repr expected}, got {repr actual}")
  IO.println s!"Passed {3 * checks.length} array execution checks."

end AiurArrayTests
