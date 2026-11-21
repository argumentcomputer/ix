import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurStructTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

-- Declarations and named source syntax survive checking and literal conversion.
def source : Generic.Program Nat := aiur% "
struct Point { x: Field, y: Field }
struct Empty {}
struct Box<T> { value: T }
struct Pointers { first: &Field, second: &Field }
struct Node { value: Field, next: Link }
enum Link { End, Next(&Node) }
enum Option<T> { None, Some(T) }
struct Response { point: Point, answer: Option<Field> }
type P = Point;
type Wrapped<T> = Box<T>;
const origin = Point { y: 0, x: 0 };
const saved = Pointers { second: &2, first: &1 };

fn make(x: Field, y: Field) -> Point { Point { y, x } }
fn swap(Point { y, x }: Point) -> Point { Point { x: y, y: x } }
fn unwrap<T>(b: Box<T>) -> T { b.value }
fn named() -> Point { swap(make(3, 4)) }
fn field() -> Field { make(3, 4).x }
fn empty() -> Empty { Empty {} }
fn rest() -> Field { let Point { x, .., } = make(3, 4); x }
fn all_rest() -> Field { let Point { .., } = origin; 9 }
fn pattern() -> Field { let Point { y: b, x: 3 } = make(3, 4); b }
fn ordered(p: Point) -> Field {
  match p { Point { x: 0, .. } => 1, Point { y: 0, .. } => 2, _ => 3 }
}
fn generic() -> Point { unwrap(Box { value: make(1, 2) }) }
fn explicit() -> Field { Box::<Field> { value: 5 }.value }
fn alias_use() -> Field { let Wrapped { value } = Wrapped { value: P { y: 7, x: 6 } }; value.x }
fn nested() -> Field { [Box { value: (make(5, 6),) }; 2][1].value.0.y }
fn constants() -> Field { let ::origin = Point { x: 0, y: 0 }; origin.y }
fn pointers() -> Field { let Pointers { second: &b, first: &a } = saved; a * 10 + b }
fn allocate() -> Pointers { Pointers { second: &2, first: &1 } }
fn once() -> Field { (*&make(3, 4)).x }
fn early() -> Field { let p = Point { y: *&2, x: return 7 }; p.x }
fn skip() -> Field { let p = Point { x: return 8, y: 1 / 0 }; p.y }
fn block() -> Field { 'b: { let p = Point { y: *&3, x: break 'b 9 }; p.x } }
fn scope() -> Field { let x = 5; let p = Point { x: { let x = 99; return 11; }, y: x }; p.y }
fn recursive() -> Field {
  let n = Node { next: Link::Next(&Node { value: 2, next: Link::End }), value: 1 };
  match n.next { Link::End => n.value, Link::Next(p) => (*p).value }
}
fn hinted(key: Field) -> Field { hint::<Response>(key).point.y }
fn pointer_input(p: Pointers) -> Field { *p.first }
fn pointer_internal() -> Field { pointer_input(allocate()) }
"

#guard source.structs.length == 6
#guard source.aliases.length == 2
#guard source.consts.length == 2
#guard (source.findFunction? "make").any fun definition => match definition.body with
  | .record head [.var "y", .var "x"] => head.fields == ["y", "x"] && head.slots == some [some 1, some 0]
  | _ => false
#guard (source.toField Rat).structs == source.structs
#guard (source.findFunction? "field").any fun definition => match definition.body with | .member _ _ => true | _ => false

def point (x y : Rat) : SourceValue Rat := .construct "Point" Generic.structConstructor [.field x, .field y]
def ptrs : SourceValue Rat := .construct "Pointers" Generic.structConstructor [.ptr .field 1, .ptr .field 0]
abbrev Result := Except String (SourceValue Rat × Heap Rat)

def checks : List (String × List (SourceValue Rat) × Result) := [
  ("named", [], .ok (point 4 3, [])), ("field", [], .ok (3, [])),
  ("empty", [], .ok (.construct "Empty" Generic.structConstructor [], [])),
  ("rest", [], .ok (3, [])), ("all_rest", [], .ok (9, [])), ("pattern", [], .ok (4, [])),
  ("ordered", [point 0 0], .ok (1, [])), ("ordered", [point 1 0], .ok (2, [])),
  ("ordered", [point 1 2], .ok (3, [])),
  ("generic", [], .ok (point 1 2, [])), ("explicit", [], .ok (5, [])),
  ("alias_use", [], .ok (6, [])), ("nested", [], .ok (6, [])), ("constants", [], .ok (0, [])),
  ("pointers", [], .ok (12, [2, 1])), ("allocate", [], .ok (ptrs, [2, 1])),
  ("once", [], .ok (3, [point 3 4])),
  ("early", [], .ok (7, [2])), ("skip", [], .ok (8, [])),
  ("block", [], .ok (9, [3])), ("scope", [], .ok (11, [])),
  ("recursive", [], .ok (2, [.construct "Node" Generic.structConstructor
    [2, .construct "Link" "End" []]])), ("pointer_internal", [], .ok (1, [2, 1]))
]

def checkExecutions : Except String Unit := do
  let s ← Generic.prepare (source.toField Rat)
  for (name, args, expected) in checks do
    let q ← Generic.specialize s [name]
    for (mode, actual) in [("source", s.run name args), ("specialized", q.run name args),
        ("core", q.coreRun name args)] do
      if actual != expected then throw s!"{name} ({mode}): expected {repr expected}, got {repr actual}"
    let _ ← q.compile
  if (s.checkEntry "pointer_input").isOk then throw "pointer-containing entry accepted"
  let malformed : SourceValue Rat := .construct "Point" Generic.structConstructor [1]
  if (s.run "ordered" [malformed]).isOk then throw "malformed struct input accepted"

#guard checkExecutions == .ok ()

def tables : Generic.Program Nat := aiur% "
struct Point { x: Field, y: Field }
type P = Point;
const one = P { y: 2, x: 1 };
table inputs: (Field,) { (0,), (1,) }
table outputs: Point { one, Point { x: 3, y: 4 } }
map get(i: Field) -> Point = inputs => outputs;
table keys: (Point,) { (one,), (Point { y: 4, x: 3 },) }
table results: Field { 8, 9 }
map lookup(p: Point) -> Field = keys => results;
fn main(x: Field) -> Field { lookup(get(x)) }
"

#guard (do
  let s ← Generic.prepare (tables.toField Rat)
  let q ← Generic.specialize s ["main"]
  let _ ← q.compile
  if s.run "main" [0] != Except.ok (8, []) then throw "struct map source"
  if q.coreRun "main" [1] != Except.ok (9, []) then throw "struct map core"
  pure ()) == .ok ()

-- Provider values validate the entire nested nominal shape.
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["hinted"]
  let _ ← q.compile
  let value : Constant Rat := .construct "Response" Generic.structConstructor
    [.construct "Point" Generic.structConstructor [3, 4], .construct (Generic.Instance.mk "Option" [.field]).symbol "Some" [5]]
  let provider := fun (_ : String) (_ : Constant Rat) => (Except.ok value : Except HintError (Constant Rat))
  if s.run "hinted" [0] 256 (s.checkedHints provider) != Except.ok (4, []) then throw "struct hint source"
  if q.coreRun "hinted" [0] 256 (HintProvider.checked q.program.enums provider) != Except.ok (4, []) then throw "struct hint core"
  let bad : Constant Rat := .construct "Response" Generic.structConstructor
    [.construct "Point" Generic.structConstructor [3, 4], .construct (Generic.Instance.mk "Option" [.field]).symbol "Bad" []]
  let invalid := fun (_ : String) (_ : Constant Rat) => (Except.ok bad : Except HintError (Constant Rat))
  if (s.run "hinted" [0] 256 (s.checkedHints invalid)).isOk then throw "invalid nested hint accepted"
  pure ()) == .ok ()

instance : Fact (Nat.Prime 101) := ⟨by decide⟩
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["named", "recursive", "pointers", "early"]
  let _ ← q.compile
  q.coreRun "pointers" []) == .ok (12, [2, 1])

def rowSource : Generic.Program Nat := aiur% "
struct Point { x: Field, y: Field }
fn swap(p: Point) -> Point { Point { y: p.x, x: p.y } }
fn first(p: Point) -> Field { p.x }
"

def checkRows : Except String Unit := do
  let s ← Generic.prepare (rowSource.toField Rat)
  let q ← Generic.specialize s ["swap", "first"]
  let c ← q.compile
  let input : WireValue Rat := ⟨.enum "Point", [3, 4]⟩
  let output : WireValue Rat := ⟨.enum "Point", [4, 3]⟩
  let swapRow : Circuit.Row Rat := ⟨"swap", [3, 4, 4, 3, 1, 0, 1, 0, 1, 0, 1, 0]⟩
  let firstRow : Circuit.Row Rat := ⟨"first", [3, 4, 3, 1, 0, 1, 0]⟩
  c.check {} ⟨"swap", [input], output⟩ [swapRow]
  c.checkMemo {} ⟨"swap", [input], output⟩ [⟨swapRow, 1⟩]
  c.check {} ⟨"first", [input], 3⟩ [firstRow]
  c.checkMemo {} ⟨"first", [input], 3⟩ [⟨firstRow, 1⟩]
  let wrong : WireValue Rat := ⟨.enum "Point", [9, 3]⟩
  let badRow : Circuit.Row Rat := ⟨"swap", swapRow.values.set 2 9⟩
  if (c.check {} ⟨"swap", [input], wrong⟩ [badRow]).isOk then throw "wrong struct output accepted"
  let tagged : WireValue Rat := ⟨.enum "Point", [0, 3, 4]⟩
  if (c.check {} ⟨"first", [tagged], 3⟩ [firstRow]).isOk then
    throw "obsolete struct tag accepted"
  let short : WireValue Rat := ⟨.enum "Point", [3]⟩
  if (c.checkMemo {} ⟨"first", [short], 3⟩ [⟨firstRow, 1⟩]).isOk then throw "short struct root accepted"

#guard checkRows == .ok ()

def duplicate : Generic.Program Nat := aiur% "
struct S { x: Field, y: Field }
fn f(s: S) -> Field { match s { S { x: 0, y: a } => a, S { y: b, x: 0 } => b } }
"
#guard !(do
  let s ← Generic.prepare (duplicate.toField Rat)
  let q ← Generic.specialize s ["f"]
  let _ ← q.compile
  pure () : Except String Unit).isOk

run_cmd do
  let env ← Lean.getEnv
  for code in [
    "struct S { x: Field, x: Field }",
    "struct S {} enum S { A }",
    "struct S {} type S = Field;",
    "struct S { x: Missing }",
    "struct S { x: S }",
    "struct S { x: [S; 0] }",
    "struct S<T> { x: Missing<T> }",
    "struct S { x: Field } fn f() -> S { S {} }",
    "struct S { x: Field } fn f() -> S { S { x: 1, x: 2 } }",
    "struct S { x: Field } fn f() -> S { S { y: 1 } }",
    "struct S { x: Field } fn f() -> S { S { x: () } }",
    "struct S { x: Field } fn f(s: S) -> Field { s.y }",
    "struct A { x: Field } struct B { x: Field } fn f() -> A { B { x: 1 } }",
    "enum E { V(Field) } fn f() -> E { E { value: 1 } }",
    "struct S { x: Field, y: Field } fn f(s: S) -> Field { let S { x } = s; x }",
    "struct S { x: Field } fn f(s: S) -> Field { let S { x, x } = s; x }",
    "struct S { x: Field } fn f(s: S) -> Field { let S { x .. } = s; x }",
    "struct S { x: Field } const a = S { x: b }; const b = a;",
    "struct S { x: &Field } table t: S {}",
    "struct S { x: [&Field; 0] } table t: S {}",
    "struct S { x: &Field } fn f() -> S { hint::<S>(()) }",
    "struct S<T> { x: T } fn f<T>(x: T) -> S<T> { hint::<S<T>>(()) }"
  ] do
    match Generic.Frontend.ofString env code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"

/-- info: 'Aiur.Generic.StructLowering.record_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.StructLowering.record_iff
/-- info: 'Aiur.Generic.StructLowering.member_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.StructLowering.member_iff

def run : IO Unit := do
  match checkExecutions *> checkRows with
  | .ok () => IO.println s!"Passed {3 * checks.length} struct execution checks and {checks.length} compilations."
  | .error e => throw (IO.userError e)

end AiurStructTests
