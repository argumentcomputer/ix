import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurAliasTests
open Aiur
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def source : Generic.Program Nat := aiur% "
type Coordinates = Pair<Scalar>;
type Pair<T> = (T, T);
type Scalar = Field;
type Id<T> = T;
type Maybe<T> = Option<T>;
type Fixed = Maybe<Scalar>;
type Wrapped<T> = Box<Pair<T>>;
type Swapped<A, B> = Either<B, A>;
type Link<T> = &List<T>;
type Concrete<T> = Scalar;
enum Option<T> { None, Some(T) }
enum Box<T> { New(T) }
enum Either<A, B> { Left(A), Right(B) }
enum List<T> { Nil, Cons(T, Link<T>) }

fn identity<T>(x: T) -> T { x }
fn pair<T>(x: T) -> Pair<T> { (x, x) }
fn unwrap<T>(x: Maybe<T>, fallback: T) -> T {
  match x { Maybe::Some(v) => v, Maybe::None => fallback }
}
fn unbox<T>(Wrapped::New((a, b)): Wrapped<T>) -> T { a }
fn main(x: Id<Id<Scalar>>) -> Scalar {
  let coordinates = pair(x);
  unwrap(Maybe::Some(identity::<Scalar>(coordinates.0)), identity::<Field>(0))
}
fn explicit(x: Field) -> Field { unwrap(Maybe::<Scalar>::Some(x), 0) }
fn fixed(x: Scalar) -> Fixed { Fixed::Some(x) }
fn none() -> Fixed { Fixed::None }
fn nested(x: Scalar) -> Scalar { unbox(Wrapped::New(pair(x))) }
fn swapped(x: Scalar) -> Swapped<(Scalar, Scalar), Scalar> { Swapped::Left(x) }
fn read(x: Scalar) -> Scalar {
  let list = List::Cons(x, &List::<Scalar>::Nil);
  let List::Cons(v, tail) = list;
  let List::Nil = *tail;
  v
}
fn hinted<T>(x: T) -> Scalar { hint::<Concrete<T>>(x) }
fn hint_entry(x: Scalar) -> Scalar { hinted(x) }
fn literal() -> Scalar { 108 }
fn singleton(x: (Scalar,)) -> (Scalar,) { x }
"

-- Type metadata is normalized, while alias declarations and code remain.
#guard source.aliases.length == 10
#guard (source.findFunction? "main").map (·.params) == some [("x", .field)]
#guard (source.findFunction? "literal").map (·.body) == some (.literal 108)
#guard (source.findFunction? "singleton").map (·.result) == some (.tuple [.field])

def runSource (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  s.run name args

def runSpecialized (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.run name args

#guard runSource "main" [.field 17] == .ok (.field 17, [])
#guard runSpecialized "main" [.field 17] == .ok (.field 17, [])
#guard runSpecialized "explicit" [.field 19] == .ok (.field 19, [])
#guard runSpecialized "nested" [.field 23] == .ok (.field 23, [])
#guard runSpecialized "swapped" [.field 31] == runSource "swapped" [.field 31]
#guard runSpecialized "fixed" [.field 31] == runSource "fixed" [.field 31]
#guard runSpecialized "none" [] == runSource "none" []
#guard (runSpecialized "read" [.field 29]).map Prod.fst == .ok (.field 29)
#guard runSource "read" [.field 29] == runSpecialized "read" [.field 29]

-- Aliases do not make new specialization keys or nominal enum identities.
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["main", "explicit", "fixed", "none"]
  return (q.program.functions.filter fun (decl : Aiur.Function Rat) =>
    (Generic.Instance.ofSymbol decl.name).toOption.any (fun (key : Generic.Instance) => key.name == "identity")).length) == .ok 1
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["main", "explicit", "fixed", "none"]
  return q.program.enums.length) == .ok 1

def mapped : Generic.Program Nat := aiur% "
type Item = Box<Field>;
type Key = (Item,);
enum Box<T> { New(T) }
table keys: Key { (Item::New(1),), (Item::New(2),) }
table outputs: Item { Item::New(3), Item::New(4) }
map lookup(x: Item) -> Item = keys => outputs;
fn main(x: Field) -> Field { let Item::New(y) = lookup(Item::New(x)); y }
"

#guard (do
  let s ← Generic.prepare (mapped.toField Rat)
  let q ← Generic.specialize s ["main"]
  q.run "main" [.field 2]) == .ok (.field 4, [])
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  s.run "hint_entry" [.field 2] 100 (s.checkedHints (fun _ _ => .ok (.field 41)))) ==
    .ok (.field 41, [])
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  s.run "literal" []) == .ok (.field 7, [])
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["main", "read", "nested", "swapped", "hint_entry"]
  return (← q.compile).system.chips.length).toOption.isSome
#guard (do
  let s ← Generic.prepare (mapped.toField (ZMod 101))
  let q ← Generic.specialize s ["main"]
  return (← q.compile).system.maps.length) == .ok 1

-- The shared preparation API also expands hand-built, field-valued ASTs.
def handBuilt : Generic.Program Nat := {
  aliases := [{ name := "Scalar", target := .field }]
  functions := [{
    name := "main"
    params := [("x", .named "Scalar" [])]
    result := .named "Scalar" []
    body := .var "x"
  }]
}
#guard (do
  let s ← Generic.prepare (handBuilt.toField Rat)
  s.run "main" [.field 13]) == .ok (.field 13, [])

run_cmd do
  let bad := [
    "type A = A;",
    "type A = &A;",
    "type A<T> = A<(T, T)>;",
    "type A = B; type B = (Field, A);",
    "type A = E<A>; enum E<T> { New(T) }",
    "type Ignore<T> = Field; type A = Ignore<A>;",
    "type A = Missing;",
    "type A<T> = U;",
    "type A<T, T> = T;",
    "type Field = ();",
    "type A<Field> = Field;",
    "type T<U> = Field; fn f<T>(x: T<Field>) -> Field { x }",
    "type A = Field; type A = ();",
    "type A = Field; enum A { New }",
    "type P<T> = (T, T); fn f(x: P) -> Field { 0 }",
    "type S = Field; fn f(x: S<Field>) -> Field { x }",
    "type Ignore<T> = Field; fn f(x: Ignore<Missing>) -> Field { x }",
    "type Ignore<T> = Field; fn f() -> Field { hint::<Ignore<Missing>>(()) }",
    "type S = Field; fn f() -> S { S::Some(1) }",
    "enum O<T> { Some(T) } type A<T> = O<T>; fn f() -> A<Field> { A::<Field, Field>::Some(1) }",
    "enum O<T> { Some(T) } type Fixed = O<Field>; fn f(x: O<(Field, Field)>) -> Field { let Fixed::Some(y) = x; 0 }",
    "enum O<T> { Some(T) } type Fixed = O<Field>; fn f() -> O<(Field, Field)> { Fixed::Some((1, 2)) }",
    "type A = Field; fn f(x: (A,)) -> A { x }",
    "enum E { A } enum F { A } type X = E; fn f(x: X) -> F { x }",
    "type P = &Field; fn f() -> P { hint::<P>(()) }",
    "type I<T> = T; fn f<T>(x: T) -> T { hint::<I<T>>(x) }",
    "enum O<T> { None, Some(T) } type P = O<&Field>; table bad: P {}",
    "type P = &Field; table keys: (Field,) {} table vals: Field {} map f(x: P) -> Field = keys => vals;",
    "type Link = E; enum E { Recur(Link) }",
    "enum O<T> { None, Some(T) } type A<T> = O<T>; fn f(A::Some(x): A<Field>) -> Field { x }"
  ]
  for code in bad do
    match Generic.Frontend.ofString (← Lean.getEnv) code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"
  -- The legacy frontend must not silently discard a new declaration.
  match Frontend.ofString (← Lean.getEnv) "type A = A; fn f() -> Field { 0 }" with
  | .error _ => pure ()
  | .ok _ => throwError "legacy frontend discarded an alias declaration"

def pointerInput : Generic.Program Nat := aiur% "
type Public = Hidden;
enum Hidden { Empty, Pointer(&Field) }
fn main(x: Public) -> Field { 0 }
"
#guard (do
  let s ← Generic.prepare (pointerInput.toField Rat)
  return (← Generic.specialize s ["main"]).program.functions.length).toOption.isNone

def collidingKeys : Generic.Program Nat := aiur% "
type Scalar = Field;
table keys: (Scalar,) { (1,), (102,) }
table outputs: Scalar { 0, 1 }
map lookup(x: Scalar) -> Scalar = keys => outputs;
"
#guard (Generic.prepare (collidingKeys.toField (ZMod 101))).toOption.isNone

-- The ordering of the pass is field agnostic, including expansion errors.
example (p : Generic.Program Nat) (F : Type) [NatCast F] :
    Generic.expandAliases (p.toField F) = (Generic.expandAliases p).map (fun q => q.toField F) :=
  Generic.expandAliases_toField p F

/-- info: 'Aiur.Generic.expandAliases_toField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.expandAliases_toField

def run : IO Unit := do
  let checks := [
    ("alias inference", runSource "main" [.field 17], .ok (.field 17, [])),
    ("alias specialization", runSpecialized "main" [.field 17], .ok (.field 17, [])),
    ("alias constructor inference", runSpecialized "nested" [.field 23], .ok (.field 23, [])),
    ("alias ROM", runSpecialized "read" [.field 29], runSource "read" [.field 29])
  ]
  for (name, actual, expected) in checks do
    unless actual = expected do throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")
  IO.println s!"Passed {checks.length} alias execution checks."

end AiurAliasTests
