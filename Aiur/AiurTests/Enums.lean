import Aiur.Frontend
import Aiur.EvalCorrectness
import Aiur.Circuit.Compile
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur

namespace AiurEnumTests

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def sample : Program Nat := aiur% r#"
enum Maybe { None, Some(Field) }
enum Other { None, Some(Field) }
enum List { Nil, Cons(Field, &List) }
enum Token { Wrap(Field) }
enum Effects { Pair(&Field, &Field) }
enum Box { Empty, Full(&Field) }
enum Inner { A, B }
enum Outer { Raw(Field), Nested(Inner) }
enum Mixed { Unit(()), Nested((Field, (Maybe, Field))) }
enum Even { End, Next(&Odd) }
enum Odd { Next(Even) }

fn classify(value: Maybe) -> Field {
  match value { Maybe::None => 0, Maybe::Some(0) => 1, Maybe::Some(x) => x + 2 }
}
fn make(x: Field) -> Maybe { Maybe::Some(x) }
fn call(x: Field) -> Field { classify(make(x)) }
fn sum(xs: List) -> Field {
  match xs { List::Nil => 0, List::Cons(x, tail) => x + sum(*tail) }
}
fn list(x: Field, y: Field) -> Field {
  let tail = List::Cons(y, &List::Nil);
  sum(List::Cons(x, &tail))
}
fn parameter(Token::Wrap(x): Token) -> Field { x }
fn binding(x: Field) -> Field { let Token::Wrap(y) = Token::Wrap(x); y + 1 }
fn empty_box(value: Box) -> Field { match value { Box::Empty => 0, Box::Full(p) => *p } }
fn boxed(x: Field) -> Field { empty_box(Box::Full(&x)) }
fn nested(value: Mixed) -> Field {
  match value {
    Mixed::Unit(()) => 3,
    Mixed::Nested((x, (Maybe::Some(0), y))) => x + y,
    Mixed::Nested((_, (m, _))) => classify(m),
  }
}
fn non_tail(x: Field) -> Maybe {
  let y = match x { 0 => Maybe::None, _ => Maybe::Some(x) };
  match classify(y) { 0 => Maybe::Some(9), _ => y }
}
fn lazy(x: Field) -> Field {
  match Maybe::Some(x) { Maybe::Some(y) => y, _ => *&(1 / 0) }
}
fn partial_enum(value: Maybe) -> Field { match value { Maybe::Some(x) => x } }
fn outer(x: Field) -> Outer { Outer::Raw(x) }
fn forever(x: Field) -> Maybe { forever(x) }
fn eager() -> Maybe { Maybe::Some(1 / 0) }
fn discarded() -> Field { let _ = Maybe::Some(1 / 0); 7 }
fn effects(x: Field) -> Effects { Effects::Pair(&x, &(x + 1)) }
"#

private def ctor (name constructor : String) (args : List (SourceValue Rat) := []) : SourceValue Rat :=
  .construct name constructor args

def runtimeTests : List (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("nullary constructor", eval (sample.toField Rat) "classify" [ctor "Maybe" "None"], .ok 0),
  ("ordered constructor patterns", eval (sample.toField Rat) "classify" [ctor "Maybe" "Some" [0]], .ok 1),
  ("constructor binding", eval (sample.toField Rat) "classify" [ctor "Maybe" "Some" [5]], .ok 7),
  ("enum call result", eval (sample.toField Rat) "call" [5], .ok 7),
  ("pointer recursion", eval (sample.toField Rat) "list" [7, 8], .ok 15),
  ("irrefutable parameter", eval (sample.toField Rat) "parameter" [ctor "Token" "Wrap" [5]], .ok 5),
  ("irrefutable let", eval (sample.toField Rat) "binding" [5], .ok 6),
  ("pointer in an unselected variant", eval (sample.toField Rat) "empty_box" [ctor "Box" "Empty"],
    .error (.pointerEntryArgument 0)),
  ("pointer payload", eval (sample.toField Rat) "boxed" [5], .ok 5),
  ("unit payload", eval (sample.toField Rat) "nested" [ctor "Mixed" "Unit" [.tuple []]], .ok 3),
  ("nested constructor and tuple patterns", eval (sample.toField Rat) "nested"
    [ctor "Mixed" "Nested" [.tuple [3, .tuple [ctor "Maybe" "Some" [0], 4]]]], .ok 7),
  ("non-tail enum result", eval (sample.toField Rat) "non_tail" [0], .ok (ctor "Maybe" "Some" [9])),
  ("non-tail enum result other arm", eval (sample.toField Rat) "non_tail" [5], .ok (ctor "Maybe" "Some" [5])),
  ("inactive arm", eval (sample.toField Rat) "lazy" [5], .ok 5),
  ("partial constructor match", eval (sample.toField Rat) "partial_enum" [ctor "Maybe" "None"], .error .noMatchingArm),
  ("eager constructor argument", eval (sample.toField Rat) "eager" [], .error .divisionByZero),
  ("discarded constructor argument", eval (sample.toField Rat) "discarded" [], .error .divisionByZero),
  ("recursion fuel", eval (sample.toField Rat) "forever" [0] 20, .error .outOfFuel),
  ("nominal input types", eval (sample.toField Rat) "classify" [ctor "Other" "Some" [0]],
    .error (.argumentTypeMismatch "classify" (.enum "Maybe") (.enum "Other"))),
  ("unknown input constructor", eval (sample.toField Rat) "classify" [ctor "Maybe" "Bogus"],
    .error (.malformedValue (.enum "Maybe"))),
  ("malformed input payload", eval (sample.toField Rat) "classify" [ctor "Maybe" "Some" []],
    .error (.malformedValue (.enum "Maybe"))),
  ("pointer-bearing entry variant", eval (sample.toField Rat) "empty_box"
    [ctor "Box" "Full" [.ptr .field 0]], .error (.pointerEntryArgument 0))
]

run_cmd do
  let env ← Lean.getEnv
  for source in [
    "enum E {}",
    "enum Field { X }",
    "enum E { A, A }",
    "enum E { A } enum E { B }",
    "enum E { A(Unknown) }",
    "enum E { A(&Unknown) }",
    "enum E { Stop, Next(E) }",
    "enum E { Stop, Next((Field, E)) }",
    "enum A { X(B) } enum B { Y(A) }",
    "enum E { A(Field) } fn f() -> E { E::A }",
    "enum E { A } fn f() -> E { E::Missing }",
    "enum E { A(Field) } fn f() -> E { E::A(()) }",
    "enum E { A } enum D { A } fn f() -> E { D::A }",
    "enum E { A(Field), B } fn f(E::A(x): E) -> Field { x }",
    "enum E { A(Field, Field) } fn f(e: E) -> Field { match e { E::A(x, x) => x } }",
    "enum E { A(Field) } fn f(e: E) -> Field { e.0 }"
  ] do
    match Frontend.ofString env source with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted enum program: {source}"

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def three : Program Nat := aiur% "enum E { A, B, C } fn f() -> E { E::C }"

/-- Constructors remain nominal even when their default field tags would collide. -/
example : eval (three.toField (ZMod 2)) "f" [] = .ok (.construct "E" "C" []) := by decide +kernel

example : (Circuit.compile (three.toField (ZMod 2))).isOk = false := by decide +kernel

def two : Program Nat := aiur% "enum E { A, B(Field) } fn f() -> E { E::B(3) }"
example : (Circuit.compile (two.toField (ZMod 2))).isOk = true := by decide +kernel

private def duplicateError (result : Except Circuit.CompileError (Circuit.System F)) : Bool :=
  match result with
  | .error (.duplicatePattern name) => name == "f"
  | _ => false

def duplicates : Program Nat := aiur% "
enum E { A(Field), B }
fn f(e: E) -> Field { match e { E::A(x) => x, E::A(_) => 2, _ => 3 } }
"
example : duplicateError (Circuit.compile (duplicates.toField Rat)) = true := by decide +kernel

def collisions : Program Nat := aiur% "
enum E { A(Field) }
fn f(e: E) -> Field { match e { E::A(0) => 1, E::A(2) => 2, _ => 3 } }
"
example : (Circuit.compile (collisions.toField Rat)).isOk = true := by decide +kernel
example : duplicateError (Circuit.compile (collisions.toField (ZMod 2))) = true := by decide +kernel

def discardedArms : Program Nat := aiur% "
enum E { A(Field) }
fn f(e: E) -> Field { match e { E::A(x) => x, E::A(0) => 2, E::A(0) => 1 / 0 } }
"
example : (Circuit.compile (discardedArms.toField Rat)).isOk = true := by decide +kernel
example : eval (discardedArms.toField Rat) "f" [.construct "E" "A" [0]] = .ok 0 := by decide +kernel

example : run (sample.toField Rat) "effects" [7] 16 =
    .ok (.construct "Effects" "Pair" [.ptr .field 0, .ptr .field 1], [7, 8]) := by decide +kernel

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in runtimeTests do checkEqual label actual expected
  match Circuit.compile (sample.toField Rat) with
  | .error error => throw (IO.userError s!"enum compilation failed: {repr error}")
  | .ok _ => pure ()
  IO.println s!"Passed {runtimeTests.length} enum runtime checks and enum compilation."

end AiurEnumTests
