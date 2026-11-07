import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurUpdateTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- Paths and operand order survive checking and literal conversion. -/
def source : Generic.Program Nat := aiur% "
struct Point { x: Field, y: Field }
struct Box<T> { value: T }
struct State { point: Point, items: [(Field, Field); 2] }
struct Ptrs { x: &Field, y: &Field }
struct Empty {}
enum Option<T> { None, Some(T) }
type P = Point;
const origin = P { x: 1, y: 2 };

fn point() -> Point { origin with { .y = 8, .x = 7, } }
fn tuple() -> (Field, [Field; 2]) { (1, [2, 3]) with { .1[0] = 9 } }
fn array() -> [Field; 3] { [1, 2, 3] with { [2] = 9, [0] = 8 } }
fn nested() -> State {
  State { point: origin, items: [(3, 4), (5, 6)] } with { .point.x = 9, .items[1].0 = 8 }
}
fn siblings() -> Point { origin with { .x = 4, .y = 5 } }
fn changed<T>(b: Box<T>, value: T) -> Box<T> { b with { .value = value } }
fn inferred() -> Field { changed(Box { value: origin }, point()).value.y }
fn explicit() -> Field { changed::<Field>(Box { value: 1 }, 6).value }
fn generic_tuple<T>(p: (T, Field), value: T) -> (T, Field) { p with { .0 = value } }
fn generic_array<T>(a: [T; 2], value: T) -> [T; 2] { a with { [1] = value } }
fn generics() -> Field { generic_array([1, 2], generic_tuple((3, 4), 5).0)[1] }
fn alias_use() -> P { origin with { .x = 3 } }
fn immutable() -> Field { let p = origin; let q = p with { .x = 9 }; p.x * 10 + q.x }
fn swap() -> Point { let p = origin; p with { .x = p.y, .y = p.x } }
fn chain() -> Point { origin with { .x = 3 } with { .x = 4 } }
fn projection() -> Field { (origin with { .y = 7 }).y }
fn empty() -> Empty { Empty {} with {} }
fn empty_array() -> [Field; 0] { [] with {} }
fn identity<T>(value: T) -> T { value with {} }
fn no_changes() -> Field { identity(6) }
fn pointers() -> Ptrs { Ptrs { y: &2, x: &1 } with { .y = &3, .x = &4 } }
fn retained() -> Ptrs { let p = Ptrs { x: &1, y: &2 }; p with { .x = &3 } }
fn explicit_load() -> Field { let p = &origin; ((*p) with { .x = 8 }).x }
fn once() -> [Field; 2] { [*&1, *&2] with { [0] = *&3 } }
fn skip_base() -> Point { (return origin) with { .x = 1 / 0 } }
fn skip_replacement() -> Field {
  let p = Ptrs { x: &1, y: &2 } with { .x = return 7, .y = &3 }; *p.x
}
fn later_exit() -> Field {
  let p = Ptrs { x: &1, y: &2 } with { .x = &3, .y = return 8 }; *p.y
}
fn block() -> Point { 'done: { origin with { .x = break 'done point(), .y = 1 / 0 } } }
fn shadow() -> Field {
  let x = 9; let p = origin with { .x = { let x = 7; x }, .y = x }; p.x * 10 + p.y
}
fn choice(x: Field) -> Point {
  origin with { .x = match x { 0 => 8, _ => 9 } }
}
fn optional() -> Box<Option<Field>> {
  Box { value: Option::None } with { .value = Option::Some(4) }
}
fn hinted() -> [Field; 2] { hint::<[Field; 2]>(*&1) with { [1] = hint::<Field>(\"field\", *&2) } }
fn unchanged_hint() -> [Field; 2] { hint::<[Field; 2]>(()) with { [0] = 3, [1] = 4 } }
"

#guard (source.findFunction? "point").any fun f => match f.body with
  | .update [[.member y], [.member x]] [.global "origin" _, .literal 8, .literal 7] => y.name == "y" && x.name == "x"
  | _ => false
#guard (source.toField Rat).findFunction? "point" |>.any fun f => match f.body with
  | .update _ _ => true | _ => false

def point (x y : Rat) : SourceValue Rat := .construct "Point" Generic.structConstructor [.field x, .field y]
def ptrs (x y : Nat) : SourceValue Rat := .construct "Ptrs" Generic.structConstructor [.ptr .field x, .ptr .field y]
abbrev Result := Except String (SourceValue Rat × Heap Rat)
def checks : List (String × List (SourceValue Rat) × Result) := [
  ("point", [], .ok (point 7 8, [])),
  ("tuple", [], .ok (.tuple [1, .tuple [9, 3]], [])),
  ("array", [], .ok (.tuple [8, 2, 9], [])),
  ("nested", [], .ok (.construct "State" Generic.structConstructor
    [point 9 2, .tuple [.tuple [3, 4], .tuple [8, 6]]], [])),
  ("siblings", [], .ok (point 4 5, [])),
  ("inferred", [], .ok (8, [])), ("explicit", [], .ok (6, [])), ("generics", [], .ok (5, [])),
  ("alias_use", [], .ok (point 3 2, [])), ("immutable", [], .ok (19, [])),
  ("swap", [], .ok (point 2 1, [])), ("chain", [], .ok (point 4 2, [])),
  ("projection", [], .ok (7, [])), ("empty", [], .ok (.construct "Empty" Generic.structConstructor [], [])),
  ("empty_array", [], .ok (.tuple [], [])), ("no_changes", [], .ok (6, [])),
  ("pointers", [], .ok (ptrs 3 2, [2, 1, 3, 4])),
  ("retained", [], .ok (ptrs 2 1, [1, 2, 3])),
  ("explicit_load", [], .ok (8, [point 1 2])),
  ("once", [], .ok (.tuple [3, 2], [1, 2, 3])),
  ("skip_base", [], .ok (point 1 2, [])),
  ("skip_replacement", [], .ok (7, [1, 2])),
  ("later_exit", [], .ok (8, [1, 2, 3])),
  ("block", [], .ok (point 7 8, [])), ("shadow", [], .ok (79, [])),
  ("choice", [0], .ok (point 8 2, [])), ("choice", [1], .ok (point 9 2, [])),
  ("optional", [], .ok (.construct (Generic.Instance.mk "Box" [.named "Option" [.field]]).symbol
    Generic.structConstructor [.construct (Generic.Instance.mk "Option" [.field]).symbol "Some" [4]], []))
]

def checkExecutions : Except String Unit := do
  let s ← Generic.prepare (source.toField Rat)
  for (name, args, expected) in checks do
    let q ← Generic.specialize s [name]
    for (mode, actual) in [("source", s.run name args), ("specialized", q.run name args),
        ("core", q.coreRun name args)] do
      if actual != expected then throw s!"{name} ({mode}): expected {repr expected}, got {repr actual}"
    let _ ← q.compile
  let q ← Generic.specialize s ["hinted", "unchanged_hint"]
  let _ ← q.compile
  let provider := fun (channel : String) (_ : Constant Rat) =>
    (Except.ok (if channel == "field" then (9 : Constant Rat) else .tuple [3, 4]) : Except HintError (Constant Rat))
  if s.run "hinted" [] 256 (s.checkedHints provider) != .ok (.tuple [3, 9], [1, 2]) then throw "source update hints"
  if q.coreRun "hinted" [] 256 (HintProvider.checked q.program.enums provider) != .ok (.tuple [3, 9], [1, 2]) then
    throw "core update hints"
  -- Overwriting every component still evaluates the base hint.
  if (s.run "unchanged_hint" []).isOk || (q.coreRun "unchanged_hint" []).isOk then throw "base hint skipped"

#guard checkExecutions == .ok ()

run_cmd do
  let env ← Lean.getEnv
  for code in [
    "fn f() -> [Field; 2] { [1, 2] with { [2] = 9 } }",
    "fn f(i: Field) -> [Field; 2] { [1, 2] with { [i] = 9 } }",
    "fn f() -> [Field; 2] { [1, 2] with { [0] = (), } }",
    "fn f() -> [Field; 2] { [1, 2] with { [0] = 3, [0] = 4 } }",
    "fn f() -> ([Field; 2],) { ([1, 2],) with { .0 = [3, 4], .0[0] = 5 } }",
    "fn f() -> ([Field; 2],) { ([1, 2],) with { .0[0] = 5, .0 = [3, 4] } }",
    "fn f() -> (Field,) { (1,) with { .1 = 3 } }",
    "fn f() -> (Field,) { (1,) with { [0] = 3 } }",
    "fn f() -> [Field; 1] { [1] with { .0 = 3 } }",
    "fn f() -> [Field; 2] { [1, 2] with { [0..1] = [3] } }",
    "struct P { x: Field } fn f(p: P) -> P { p with { .y = 2 } }",
    "struct P { x: Field } fn f(p: P) -> P { p with { .x = 2, .x = 3 } }",
    "struct P { x: Field } fn f(p: &P) -> &P { p with { .x = 2 } }",
    "struct P { x: Field } struct S { p: &P } fn f(s: S) -> S { s with { .p.x = 2 } }",
    "enum E { X(Field) } fn f(e: E) -> E { e with { .0 = 2 } }",
    "struct A { x: Field } struct B { x: Field } struct S { a: A } fn f(s: S) -> S { s with { .a = B { x: 1 } } }",
    "fn f<T>(x: T) -> T { x with { .0 = 1 } }",
    "fn f() -> [Field; 0] { [] with { [0] = 1 } }"
  ] do
    match Generic.Frontend.ofString env code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
-- The static index 2 remains 2 even over a field where the literal 2 is zero.
def smallField : Generic.Program Nat := aiur% "fn f() -> [Field; 3] { [0; 3] with { [2] = 1 } }"
#guard (do
  let s ← Generic.prepare (smallField.toField (ZMod 2))
  let q ← Generic.specialize s ["f"]
  let _ ← q.compile
  q.coreRun "f" []) == .ok (.tuple [0, 0, 1], [])

def rowSource : Generic.Program Nat := aiur% "
fn edit(a: [Field; 3]) -> [Field; 3] { a with { [1] = a[0] + 7 } }
"

def checkRows : Except String Unit := do
  let s ← Generic.prepare (rowSource.toField Rat)
  let q ← Generic.specialize s ["edit"]
  let c ← q.compile
  let some chip := c.system.findChip? "edit" | throw "missing update chip"
  if chip.numVars != 6 then throw "static array update introduced auxiliary columns"
  let type : Aiur.Ty := .tuple [.field, .field, .field]
  let input : WireValue Rat := ⟨type, [2, 3, 4]⟩
  let output : WireValue Rat := ⟨type, [2, 9, 4]⟩
  let row : Circuit.Row Rat := ⟨"edit", [2, 3, 4, 2, 9, 4]⟩
  c.check {} ⟨"edit", [input], output⟩ [row]
  c.checkMemo {} ⟨"edit", [input], output⟩ [⟨row, 1⟩]
  -- Equations enforce both preservation and replacement, for both checkers.
  for (index, words) in [(3, [8, 9, 4]), (4, [2, 8, 4])] do
    let wrong : WireValue Rat := ⟨type, words⟩
    let bad : Circuit.Row Rat := ⟨"edit", row.values.set index 8⟩
    if (c.check {} ⟨"edit", [input], wrong⟩ [bad]).isOk then throw "wrong array update accepted"
    if (c.checkMemo {} ⟨"edit", [input], wrong⟩ [⟨bad, 1⟩]).isOk then throw "wrong memoized array update accepted"

#guard checkRows == .ok ()

/-- info: 'Aiur.Generic.UpdateLowering.expression_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.UpdateLowering.expression_iff

def run : IO Unit := do
  match checkExecutions *> checkRows with
  | .ok () => IO.println s!"Passed {3 * checks.length} update execution checks and {checks.length} compilations."
  | .error e => throw (IO.userError e)

end AiurUpdateTests
