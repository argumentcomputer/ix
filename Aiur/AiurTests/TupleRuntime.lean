import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurTupleRuntimeTests

def sample : Program Nat := aiur% "
fn unit() -> () { () }
fn singleton(x: Field) -> (Field,) { (x,) }
fn grouped(x: Field) -> Field { (x) }
fn wide(x: Field) -> (Field, Field, Field, Field, Field) { (x, 2, 3, 4, 5) }
fn nested(x: Field) -> (Field, (Field, ()), (Field,)) { (x, (x + 1, ()), (x + 2,)) }
fn swap(p: (Field, Field)) -> (Field, Field) { match p { (x, y) => (y, x) } }
fn destructure((x, (y, z)): (Field, (Field, Field))) -> Field { x + y + z }
fn unpack(p: (Field, (Field, ()))) -> Field { let (x, (y, ())) = p; x + y }
fn shadow(x: Field) -> Field { let (x, y) = (x + 1, x + 2); x * y }
fn projection(p: (Field, (Field, Field))) -> Field { p.1.0 }
fn call_projection(p: (Field, Field)) -> Field { swap(p).0 }
fn overlap(p: (Field, Field)) -> Field {
  match p { (0, _) => 11, (_, 0) => 22, _ => 33 }
}
fn deep_match(p: (Field, (Field, Field))) -> Field {
  match p { (0, (1, x)) => x, (_, (_, 0)) => 9, _ => 7 }
}
fn partial_pair(p: (Field, Field)) -> Field { match p { (0, 0) => 1 } }
fn reduce(p: (Field, Field)) -> (Field, Field) {
  match p { (0, total) => (0, total), (n, total) => reduce((n - 1, total + n)) }
}
fn even(p: (Field, Field)) -> (Field, Field) {
  match p { (0, total) => (1, total), (n, total) => odd((n - 1, total + 1)) }
}
fn odd(p: (Field, Field)) -> (Field, Field) {
  match p { (0, total) => (0, total), (n, total) => even((n - 1, total + 1)) }
}
fn eager_tuple() -> Field { (7, 1 / 0).0 }
fn discarded_tuple() -> Field { let _ = (7, 1 / 0); 9 }
fn divide_unit(x: Field) -> () { let _ = 1 / x; () }
fn call_unit(x: Field) -> () { divide_unit(x) }
fn looping(p: (Field, Field)) -> (Field, Field) { looping(p) }
fn lazy(p: (Field, Field)) -> (Field, Field) {
  match p { (0, x) => (x, x), _ => looping((1 / 0, 0)) }
}
fn catch_all(p: (Field, Field)) -> Field {
  match p { (x, _) => x, (0, 0) => 1, (0, 0) => 2 }
}
"

def rationalTests : List (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("unit", eval (sample.toField Rat) "unit" [], .ok (.tuple [])),
  ("singleton", eval (sample.toField Rat) "singleton" [7], .ok (.tuple [7])),
  ("grouping", eval (sample.toField Rat) "grouped" [7], .ok 7),
  ("wide tuple", eval (sample.toField Rat) "wide" [7], .ok (.tuple [7, 2, 3, 4, 5])),
  ("nested tuple", eval (sample.toField Rat) "nested" [7],
    .ok (.tuple [7, .tuple [8, .tuple []], .tuple [9]])),
  ("tuple pattern", eval (sample.toField Rat) "swap" [.tuple [2, 3]], .ok (.tuple [3, 2])),
  ("parameter pattern", eval (sample.toField Rat) "destructure" [.tuple [1, .tuple [2, 3]]], .ok 6),
  ("let pattern", eval (sample.toField Rat) "unpack" [.tuple [1, .tuple [2, .tuple []]]], .ok 3),
  ("binding scope", eval (sample.toField Rat) "shadow" [2], .ok 12),
  ("nested projection", eval (sample.toField Rat) "projection" [.tuple [1, .tuple [2, 3]]], .ok 2),
  ("call projection", eval (sample.toField Rat) "call_projection" [.tuple [2, 3]], .ok 3),
  ("overlap first", eval (sample.toField Rat) "overlap" [.tuple [0, 0]], .ok 11),
  ("overlap second", eval (sample.toField Rat) "overlap" [.tuple [5, 0]], .ok 22),
  ("overlap default", eval (sample.toField Rat) "overlap" [.tuple [5, 6]], .ok 33),
  ("nested literal pattern", eval (sample.toField Rat) "deep_match" [.tuple [0, .tuple [1, 4]]], .ok 4),
  ("nested first match", eval (sample.toField Rat) "deep_match" [.tuple [0, .tuple [1, 0]]], .ok 0),
  ("nested default", eval (sample.toField Rat) "deep_match" [.tuple [2, .tuple [1, 2]]], .ok 7),
  ("partial match", eval (sample.toField Rat) "partial_pair" [.tuple [0, 1]], .error .noMatchingArm),
  ("tuple recursion", eval (sample.toField Rat) "reduce" [.tuple [4, 0]] 40, .ok (.tuple [0, 10])),
  ("mutual tuple recursion", eval (sample.toField Rat) "even" [.tuple [4, 0]] 40, .ok (.tuple [1, 4])),
  ("tuple nontermination", eval (sample.toField Rat) "looping" [.tuple [1, 2]] 10, .error .outOfFuel),
  ("strict tuple construction", eval (sample.toField Rat) "eager_tuple" [], .error .divisionByZero),
  ("strict discarded tuple", eval (sample.toField Rat) "discarded_tuple" [], .error .divisionByZero),
  ("unit call", eval (sample.toField Rat) "call_unit" [2], .ok (.tuple [])),
  ("unit call still executes", eval (sample.toField Rat) "call_unit" [0], .error .divisionByZero),
  ("inactive tuple branch", eval (sample.toField Rat) "lazy" [.tuple [0, 9]], .ok (.tuple [9, 9])),
  ("irrefutable tuple ends match", eval (sample.toField Rat) "catch_all" [.tuple [4, 0]], .ok 4),
  ("entry tuple shape", eval (sample.toField Rat) "swap" [2],
    .error (.argumentTypeMismatch "swap" (.tuple [.field, .field]) .field)),
  ("entry singleton shape", eval (sample.toField Rat) "grouped" [.tuple [2]],
    .error (.argumentTypeMismatch "grouped" .field (.tuple [.field])))
]

-- All of these fail at elaboration, before choosing a field.
run_cmd do
  let env ← Lean.getEnv
  for source in [
    "fn f(x) -> Field { x }",
    "fn f(x: Field) { x }",
    "fn f() { () }",
    "fn f(x: Nat) -> Field { x }",
    "fn f() -> Field { (1,) }",
    "fn f() -> (Field,) { (1) }",
    "fn f() -> Field { () + 1 }",
    "fn f() -> Field { -(1, 2) }",
    "fn f() -> Field { (1, 2).2 }",
    "fn f(x: Field) -> Field { x.0 }",
    "fn f() -> Field { let (x, y) = (1,); x }",
    "fn f() -> Field { let (x, x) = (1, 2); x }",
    "fn f() -> Field { match (1, 2) { (x, x) => x } }",
    "fn f() -> Field { match (1, 2) { (x,) => x } }",
    "fn f() -> Field { match (1, 2) { 0 => 1, _ => 2 } }",
    "fn f() -> Field { match 0 { 0 => 1, _ => () } }",
    "fn f() -> Field { match 0 { x => x } + x }",
    "fn f(p: (Field, Field)) -> Field { p.0 } fn g() -> Field { f((1,)) }",
    "fn f((x, y): (Field, Field), x: Field) -> Field { x }",
    "fn f((0, x): (Field, Field)) -> Field { x }"
  ] do
    match Frontend.ofString env source with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted invalid source: {source}"


def system : System Rat := (compile (sample.toField Rat)).toOption.getD { chips := [] }
theorem compiled : compile (sample.toField Rat) = .ok system := by
  have succeeds : (compile (sample.toField Rat)).isOk = true := by decide +kernel
  cases lowered : compile (sample.toField Rat) with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [system, lowered, Except.toOption]

-- A tuple-only run allocates nothing, so its completeness needs no field-capacity bound.
example : Circuit.EncodedEntryDerives system "reduce" (entryValues [.tuple [4, 0]]) (.tuple [0, 10]) := by
  have executed : run (sample.toField Rat) "reduce" [.tuple [4, 0]] 40 =
      .ok (.tuple [.field 0, .field 10], []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simp only [Value.mapAddress, List.map_cons, List.map_nil] at complete
  exact complete

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in rationalTests do
    checkEqual label actual expected
  checkEqual "tuple compiler regression" (Circuit.compile (sample.toField Rat)).isOk true
  IO.println s!"Passed {rationalTests.length + 1} tuple checks against the main API."

end AiurTupleRuntimeTests
