import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurPointerPatternTests
open Aiur
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def source : Generic.Program Nat := aiur% "
type Pair<T> = (T, T);
type Maybe<T> = Option<T>;
enum Option<T> { None, Some(T) }

fn read<T>(&x: &T) -> T { x }
fn twice(&&x: &&Field) -> Field { x }
fn simple(x: Field) -> Field { let &a = &x; a }
fn explicit(x: Field) -> Field { let a = *(&x); a }
fn call(x: Field) -> Field { read(&x) }
fn nested(x: Field) -> Field { twice(&&x) }
fn tuple(x: Field) -> Field { let (&a, (b, &c)) = (&x, (2, &(x + 3))); a + b + c }
fn aliased(x: Field) -> Field {
  let &Maybe::Some((a, b)) = &Maybe::Some((x, 3));
  a + b
}
fn once() -> Field { let &(a, b) = &(2, 3); a + b }
fn match_once(x: Field) -> Field {
  match &(x, x + 1) { &(0, _) => 0, &(a, b) => a + b }
}
fn inspect(p: &Field) -> Field { match p { &0 => 7, &1 => 8, &x => x + 10 } }
fn dispatch(x: Field) -> Field { inspect(&x) }
fn let_fail() -> Field { let &(0, x) = &(1, 2); 1 / 0 }
fn match_fail() -> Field { match &2 { &0 => 1, &1 => 2 } }
fn fallback(x: Field) -> Field {
  match (1, &5) { (x, &0) => x, _ => x }
}
fn inactive() -> Field {
  let value = Maybe::<&Field>::None;
  match value { Maybe::Some(&x) => x, Maybe::None => 17 }
}
fn guarded(value: (Field, &Field)) -> Field {
  match value { (0, &x) => x, _ => 19 }
}
fn ignore(p: &Field) -> Field { let &_ = p; 23 }
fn ignored(x: Field) -> Field { ignore(&x) }
fn unreachable() -> Field { match &1 { _ => 29, &0 => 0, &0 => 1 } }
fn overlap(x: Field, y: Field) -> Field {
  match (&x, &y) { (&0, _) => 31, (_, &0) => 37, _ => 41 }
}
fn singleton(x: Field) -> Field { let &(a,) = &(x,); a }
fn unit() -> () { let &() = &(); () }
"

def runSource (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  s.run name args

def runSpecialized (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.run name args

def runCore (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.coreRun name args

-- Check the independent implementations around ordered loads and bindings.
#guard ([
  ("simple", [.field 13]), ("nested", [.field 5]), ("tuple", [.field 5]),
  ("dispatch", [.field 0]), ("dispatch", [.field 1]), ("dispatch", [.field 2]),
  ("fallback", [.field 42]), ("overlap", [.field 0, .field 0]),
  ("overlap", [.field 1, .field 0]), ("let_fail", []), ("match_fail", [])
] : List (String × List (SourceValue Rat))).all fun (name, args) =>
  runSource name args == runCore name args

-- The basic spelling lowers to precisely the explicit load, without a helper call.
#guard (source.findFunction? "simple").map (fun d => d.body.lower []) ==
  (source.findFunction? "explicit").map (fun d => d.body.lower [])

#guard runSource "simple" [.field 13] == .ok (.field 13, [.field 13])
#guard runSource "simple" [.field 13] == runSource "explicit" [.field 13]
#guard runSpecialized "call" [.field 13] == .ok (.field 13, [.field 13])
#guard (runSource "nested" [.field 5]).map Prod.fst == .ok (.field 5)
#guard (runSource "tuple" [.field 5]).map Prod.fst == .ok (.field 15)
#guard (runSpecialized "aliased" [.field 5]).map Prod.fst == .ok (.field 8)
#guard runSource "once" [] == .ok (.field 5, [.tuple [.field 2, .field 3]])
#guard runSource "match_once" [.field 4] == .ok (.field 9, [.tuple [.field 4, .field 5]])
#guard (runSpecialized "dispatch" [.field 0]).map Prod.fst == .ok (.field 7)
#guard (runSpecialized "dispatch" [.field 1]).map Prod.fst == .ok (.field 8)
#guard (runSpecialized "dispatch" [.field 2]).map Prod.fst == .ok (.field 12)
#guard runSource "let_fail" [] == .error (reprStr EvalError.patternMismatch)
#guard runSource "match_fail" [] == .error (reprStr EvalError.noMatchingArm)
#guard (runSource "fallback" [.field 42]).map Prod.fst == .ok (.field 42)
#guard runSource "inactive" [] == .ok (.field 17, [])
#guard (runSource "ignored" [.field 1]).map Prod.fst == .ok (.field 23)
#guard (runSource "unreachable" []).map Prod.fst == .ok (.field 29)
#guard (runSource "overlap" [.field 0, .field 0]).map Prod.fst == .ok (.field 31)
#guard (runSource "overlap" [.field 1, .field 0]).map Prod.fst == .ok (.field 37)
#guard (runSource "overlap" [.field 1, .field 1]).map Prod.fst == .ok (.field 41)
#guard runSpecialized "singleton" [.field 5] == .ok (.field 5, [.tuple [.field 5]])
#guard runSpecialized "unit" [] == .ok (.tuple [], [.tuple []])

-- Probe an internal call with a deliberately dangling pointer. An earlier
-- failed field test skips the read; `&_` itself always performs a read.
def runInternal (name : String) (args : List (SourceValue Rat)) := do
  let s ← Generic.prepare (source.toField Rat)
  let (types, locals, body) ← (s.world.prepare name args).mapError reprStr
  (Generic.SourceSemantics.evalExprWith s.world Generic.SourceSemantics.unavailable types locals 100 body []).mapError reprStr

#guard runInternal "guarded" [.tuple [.field 1, .ptr .field 99]] == .ok (.field 19, [])
#guard (runInternal "guarded" [.tuple [.field 0, .ptr .field 99]]).toOption.isNone
#guard (runInternal "ignore" [.ptr .field 99]).toOption.isNone

-- Compilation uses the existing guarded ROM loads and keeps all call
-- dependencies visible, independently of native source execution.
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["simple", "call", "nested", "tuple", "aliased", "match_once",
    "dispatch", "fallback", "inactive", "ignored", "unreachable", "overlap", "singleton", "unit",
    "let_fail", "match_fail"]
  return (← q.compile).system.chips.length).toOption.isSome
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  return (← Generic.specialize s ["read"]).program.functions.length).toOption.isNone
#guard (runSource "inspect" [.ptr .field 0]).toOption.isNone
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  return (← Generic.specialize s ["ignore"]).program.functions.length).toOption.isNone

def collision : Generic.Program Nat := aiur% "
fn inspect(p: &Field) -> Field { match p { &1 => 0, &102 => 1, _ => 2 } }
fn main(x: Field) -> Field { inspect(&x) }
"
#guard (Generic.prepare (collision.toField (ZMod 101))).toOption.isNone

-- Generated temporaries also avoid names in hand-built ASTs, not just names
-- which can be written as Rust-like identifiers.
def unusualName := "$pattern___________:0"
def handBuilt : Generic.Program Nat := {
  functions := [{
    name := "main", params := [(unusualName, .field)], result := .field
    body := .matchValue (.tuple [.literal 1, .store (.literal 5)]) [
      (.tuple [.bind unusualName, .load (.literal 0)], .var unusualName),
      (.wildcard, .var unusualName)]
  }]
}
#guard (do
  let s ← Generic.prepare (handBuilt.toField Rat)
  s.run "main" [.field 42]) == .ok (.field 42, [.field 5])
#guard (do
  let s ← Generic.prepare (handBuilt.toField Rat)
  let q ← Generic.specialize s ["main"]
  q.coreRun "main" [.field 42]) == .ok (.field 42, [.field 5])

-- Keep all original arm dependencies visible to conservative specialization,
-- even though the first arm makes the growing call unreachable at runtime.
run_cmd do
  let code := "fn grow<T>(x: T) -> Field { match &x { &a => 1, _ => grow((x, x)) } } fn main() -> Field { grow(0) }"
  match Generic.Frontend.ofString (← Lean.getEnv) code with
  | .error _ => pure ()
  | .ok _ => throwError "accepted type-changing recursion in an unreachable branch"

run_cmd do
  for code in [
    "fn f(x: Field) -> Field { let &a = x; a }",
    "fn f(x: Field) -> Field { match x { &a => a } }",
    "fn f(&0: &Field) -> Field { 1 }",
    "fn f(p: &Field) -> Field { let &(a, b) = p; a }",
    "fn f(x: Field) -> Field { let (&a, a) = (&x, x); a }",
    "fn f(p: &(Field, Field)) -> Field { match p { &(0, a) => a, &(0, b) => b } }",
    "fn f(p: &Field) -> Field { match p { &0 => 1, &0 => 2, _ => 3 } }",
    "fn f(&x: &Field, x: Field) -> Field { x }"
  ] do
    match Generic.Frontend.ofString (← Lean.getEnv) code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"

def run : IO Unit := do
  let checks := [
    ("pointer let", runSource "simple" [.field 13], .ok (.field 13, [.field 13])),
    ("pointer parameter", runSpecialized "call" [.field 13], .ok (.field 13, [.field 13])),
    ("single scrutinee evaluation", runSource "match_once" [.field 4], .ok (.field 9, [.tuple [.field 4, .field 5]])),
    ("failed arm scope", runSource "fallback" [.field 42], .ok (.field 42, [.field 5]))
  ]
  for (name, actual, expected) in checks do
    unless actual = expected do throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")
  IO.println s!"Passed {checks.length} pointer-pattern execution checks."

/-- info: 'Aiur.Generic.PatternLowering.load_bind_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.PatternLowering.load_bind_iff

/-- info: 'Aiur.Generic.PatternLowering.letSteps_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.PatternLowering.letSteps_iff

/-- info: 'Aiur.Generic.PatternLowering.matchSteps_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.PatternLowering.matchSteps_iff

end AiurPointerPatternTests
