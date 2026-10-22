import Aiur.Generic.Frontend
import Aiur.Generic.Specialize
import Aiur.Generic.Circuit
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurGenericTests
open Aiur
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def source : Generic.Program Nat := aiur% "
enum Option<T> { None, Some(T) }
enum List<T> { Nil, Cons(T, &List<T>) }
fn identity<T>(x: T) -> T { x }
fn swap<A, B>(p: (A, B)) -> (B, A) { (p.1, p.0) }
fn wrap<T>(x: T) -> Option<T> { Option::Some(x) }
fn unwrap<T>(x: Option<T>, fallback: T) -> T {
  match x { Option::Some(value) => value, Option::None => fallback }
}
fn main(x: Field) -> Field {
  let pair = swap((identity(x), (2, 3)));
  unwrap(wrap(pair.1), 0)
}
fn empty() -> Option<Field> { Option::None }
fn explicit(x: Field) -> Field { identity::<Field>(x) }
fn alloc<T>(x: T) -> &T { &x }
fn deref<T>(p: &T) -> T { *p }
fn cons(x: Field) -> List<Field> { List::Cons(x, alloc(List::<Field>::Nil)) }
fn nested(x: Field) -> Option<Option<Field>> { Option::Some(Option::Some(x)) }
fn read(x: Field) -> Field {
  let list = cons(x);
  let List::Cons(head, tail) = list;
  let List::Nil = deref(tail);
  head
}
fn hinted<T>(x: T) -> Field { hint::<Field>(x) }
fn hint_entry(x: Field) -> Field { hinted((x, x)) }
fn grow<T>(n: Field, x: T) -> T {
  match n { 0 => x, _ => grow(n - 1, x) }
}
fn grow_entry(n: Field) -> Field { grow(n, 9) }
"

def runSource (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  s.run name args

def runSpecialized (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.run name args

#guard runSource "main" [.field 17] == .ok (.field 17, [])
#guard runSpecialized "main" [.field 17] == .ok (.field 17, [])
#guard runSource "grow_entry" [.field 4] == .ok (.field 9, [])
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  return (← Generic.specialize s ["grow_entry"]).program.functions.length).toOption.isSome

#guard runSource "explicit" [.field 23] == .ok (.field 23, [])
#guard runSpecialized "explicit" [.field 23] == .ok (.field 23, [])
#guard (runSpecialized "read" [.field 31]).map Prod.fst == .ok (.field 31)
#guard (runSource "read" [.field 31]) == (runSpecialized "read" [.field 31])
#guard (runSpecialized "nested" [.field 7]) == (runSource "nested" [.field 7])
#guard (runSpecialized "empty" []) == (runSource "empty" [])

-- Multiple independent instances are allowed; the artifact keeps only the
-- selected public interface, even though identity is a reachable helper.
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["main"]
  return q.program.functions.any (·.name == "grow_entry")) == .ok false
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["read"]
  q.run "cons" [.field 1]).toOption.isNone
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  return (← Generic.specialize s ["identity"]).program.functions.length).toOption.isNone

def recursion : Generic.Program Nat := aiur% "
fn left<A, B>(n: Field, a: A, b: B) -> A {
  match n { 0 => a, _ => right(n - 1, b, a) }
}
fn right<A, B>(n: Field, a: A, b: B) -> B {
  match n { 0 => b, _ => left(n - 1, b, a) }
}
fn swapping<A, B>(n: Field, a: A, b: B) -> () {
  match n { 0 => (), _ => swapping(n - 1, a, b) }
}
fn good(n: Field) -> Field { left(n, 41, (2, 3)) }
fn finite(n: Field) -> () { swapping(n, 1, (2, 3)) }
fn same(n: Field) -> () { swapping(n, 1, 2) }
"

#guard (do
  let s ← Generic.prepare (recursion.toField Rat)
  let q ← Generic.specialize s ["good", "same"]
  q.run "good" [.field 10]) == .ok (.field 41, [])
#guard (do
  let s ← Generic.prepare (recursion.toField Rat)
  s.run "finite" [.field 5]) == .ok (.tuple [], [])
#guard (do
  let s ← Generic.prepare (recursion.toField Rat)
  return (← Generic.specialize s ["finite"]).program.functions.length).toOption.isSome

-- A cached f<Field> reached from f<(Field, Field)> must still be rejected.
def cached : Generic.Program Nat := { functions := [
  { name := "f", typeParams := ["T"], params := [("x", .param "T")], result := .field,
    body := .call "g" none [.literal 1] },
  { name := "g", typeParams := ["T"], params := [("x", .param "T")], result := .field,
    body := .call "f" none [.literal 1] },
  { name := "first", params := [], result := .field, body := .call "f" none [.literal 1] },
  { name := "second", params := [], result := .field,
    body := .call "f" none [.tuple [.literal 1, .literal 2]] }] }

def cacheRejected (roots : List String) : Bool :=
  match (do
    let s ← Generic.prepare (cached.toField Rat)
    return (← Generic.specialize s roots).program.functions.length) with
  | .error e => e.startsWith "recursive"
  | .ok _ => false

#guard cacheRejected ["first", "second"]
#guard cacheRejected ["second", "first"]
#guard (do
  let s ← Generic.prepare (cached.toField Rat)
  return (← Generic.specialize s ["first"]).program.functions.length).toOption.isNone

-- An ordinary bridge must not hide a change of generic arguments. The check
-- starts at every generic root, even when no public entry reaches that root.
def ordinaryBridge : Generic.Program Nat := { functions := [
  { name := "poly", typeParams := ["T"], params := [], result := .field,
    body := .call "bridge" (some []) [] },
  { name := "bridge", params := [], result := .field,
    body := .call "poly" (some [.field]) [] }] }
#guard (Generic.checkGenericCycles ordinaryBridge).toOption.isNone

-- Regression for IxVM's large monomorphic call graph: repeated call sites
-- create exponentially many paths, but cannot change any type argument.
def ordinaryFanout : Generic.Program Nat := { functions := (List.range 32).map fun i =>
  { name := s!"f{i}", params := [], result := .field,
    body := .binary .add (.call s!"f{(i+1)%32}" (some []) [])
      (.call s!"f{(i+1)%32}" (some []) []) } }
#guard Generic.checkGenericCycles ordinaryFanout == .ok ()

def mapped : Generic.Program Nat := aiur% "
enum Box<T> { New(T) }
table keys: (Box<Field>,) { (Box::New(1),), (Box::New(2),) }
table outputs: Box<(Field, Field)> { Box::New((3, 4)), Box::New((5, 6)) }
map expand(x: Box<Field>) -> Box<(Field, Field)> = keys => outputs;
fn unbox<T>(x: Box<T>) -> T { let Box::New(v) = x; v }
fn main(x: Field) -> Field { unbox(expand(Box::New(x))).1 }
"

#guard (do
  let s ← Generic.prepare (mapped.toField Rat)
  let q ← Generic.specialize s ["main"]
  q.run "main" [.field 2]) == .ok (.field 6, [])
#guard (do
  let s ← Generic.prepare (mapped.toField Rat)
  s.run "main" [.field 2]) == .ok (.field 6, [])

#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let provider := s.checkedHints (fun _ _ => .ok (.field 19))
  s.run "hint_entry" [.field 8] 100 provider) == .ok (.field 19, [])
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let provider := s.checkedHints (fun _ _ => .ok (.tuple []))
  s.run "hint_entry" [.field 8] 100 provider).toOption.isNone

-- The same monomorphic circuit compiler consumes concrete enum instances,
-- generic pointers, maps, and hints after specialization.
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["main", "read", "nested", "hint_entry"]
  let c ← q.compile
  return c.system.chips.length).toOption.isSome
#guard (do
  let s ← Generic.prepare (mapped.toField (ZMod 101))
  let q ← Generic.specialize s ["main"]
  let c ← q.compile
  return c.system.maps.length) == .ok 1

#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["read"]
  let c ← q.compile
  c.check ⟨[]⟩ ⟨"cons", [], ⟨.field, []⟩⟩ []) ==
    .error "'cons' is not a selected entrypoint"
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["read"]
  let c ← q.compile
  c.checkMemo ⟨[]⟩ ⟨"cons", [], ⟨.field, []⟩⟩ []) ==
    .error "'cons' is not a selected entrypoint"

-- Inference failures, static pointer exclusion, layout cycles, and concrete
-- hint restrictions are checked while elaborating the whole source.
run_cmd do
  let bad := [
    "fn f<T>(x: T) -> T { x + 1 }",
    "fn grow<T>(n: Field, x: T) -> T { match n { 0 => x, _ => grow(n - 1, (x, x)).0 } }",
    "fn swap<A, B>(n: Field, a: A, b: B) -> () { match n { 0 => (), _ => swap(n - 1, b, a) } }",
    "fn grow<T>(x: T) -> Field { match &x { &a => 1, _ => grow((x, x)) } } fn main() -> Field { grow(0) }",
    "fn f<T>(x: T) -> T { hint::<T>(x) }",
    "enum E<T> { A(T) } fn f<T>(x: T) -> E<T> { hint::<E<T>>(x) }",
    "fn f<T>(x: T) -> T { x } fn main() -> Field { f::<(Field, Field)>(1) }",
    "enum O<T> { None, Some(T) } fn main() -> Field { let x = O::None; 1 }",
    "enum E<T> { Loop(E<T>) }",
    "enum E<T> { Loop(&E<(T, T)>) }",
    "enum E<T> { None, Some(T) } table bad: E<&Field> {}",
    "enum E<T> { None, Some(T) } fn f() -> E<&Field> { hint::<E<&Field>>(()) }",
    "fn f<T, T>(x: T) -> T { x }",
    "fn f<T>((x, y): (T, T), x: T) -> T { x }",
    "fn f<T>(x) -> T { x }",
    "fn f<T>(x: T) { x }"
  ]
  for code in bad do
    match Generic.Frontend.ofString (← Lean.getEnv) code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"

def pointerInput : Generic.Program Nat := aiur% "
enum E<T> { None, Some(T) }
fn entry(x: E<&Field>) -> Field { 0 }
"
#guard (do
  let s ← Generic.prepare (pointerInput.toField Rat)
  return (← Generic.specialize s ["entry"]).program.functions.length).toOption.isNone

-- The equivalence theorem is usable for every selected root and every
-- successful outcome, rather than just a particular evaluator fuel bound.
example [Field F] [DecidableEq F] (s : Generic.Source F)
    (q : Generic.Specialized s roots) (selected : name ∈ roots) :
    s.EvalCall name args result ↔ q.EvalCall name args result :=
  q.evalCall_iff selected

def run : IO Unit := do
  let checks := [
    ("generic source", runSource "main" [.field 17], .ok (.field 17, [])),
    ("generic specialization", runSpecialized "main" [.field 17], .ok (.field 17, [])),
    ("ordinary generic recursion", runSource "grow_entry" [.field 4], .ok (.field 9, [])),
    ("explicit arguments", runSpecialized "explicit" [.field 23], .ok (.field 23, [])),
    ("nested generic enum", runSpecialized "nested" [.field 7], runSource "nested" [.field 7]),
    ("generic ROM", runSpecialized "read" [.field 31], runSource "read" [.field 31])
  ]
  for (name, actual, expected) in checks do
    unless actual = expected do throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")
  unless cacheRejected ["first", "second"] && cacheRejected ["second", "first"] do
    throw (IO.userError "specialization recursion check depends on traversal order")
  IO.println s!"Passed {checks.length + 2} generic execution checks."

-- Guard the proof boundary against admissions or additional axioms.
/-- info: 'Aiur.Generic.Engine.evalExpr_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Engine.evalExpr_spec
/-- info: 'Aiur.Generic.Source.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Source.run_spec
/-- info: 'Aiur.Generic.Specialized.evalFn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.evalFn_iff
/-- info: 'Aiur.Generic.Specialized.evalCall_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.evalCall_iff
/-- info: 'Aiur.Generic.Specialized.core_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.core_run_complete
/-- info: 'Aiur.Generic.Specialized.core_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.core_heap_sound
/-- info: 'Aiur.Generic.Specialized.core_memo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.core_memo_acyclic_heap_sound
/-- info: 'Aiur.Generic.Specialized.core_checker_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.core_checker_run_complete
/-- info: 'Aiur.Generic.Specialized.core_checkerMemo_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.core_checkerMemo_run_complete
/-- info: 'Aiur.Generic.Specialized.core_checker_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.core_checker_heap_sound

end AiurGenericTests
