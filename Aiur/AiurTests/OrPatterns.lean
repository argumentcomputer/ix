import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurOrPatternTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def source : Generic.Program Nat := aiur% "
enum Pair<T> { Left(T, T), Right(T, T), Empty }
struct S { a: Field, b: Field }
const zero = 0;
const one = 1;
fn literals(x: Field) -> Field { match x { 0 | 1 | 2 => 10, _ => 20 } }
fn constants(x: Field) -> Field { match x { ::zero | ::one => 11, _ => 21 } }
fn overlap(x: (Field, Field, Field)) -> Field {
  let (a, 0, _) | (_, _, a) = x; a
}
fn nested(x: (Field, Field)) -> Field { let (0 | 1, a) = x; a }
fn array(x: [Field; 2]) -> Field { let [0, a] | [a, 0] = x; a }
fn repeated(x: [Field; 2]) -> Field { let [0 | 1; 2] = x; 12 }
fn generic<T>(p: Pair<T>) -> (T, T) {
  let Pair::Left(x, y) | Pair::Right(y, x) = p; (x, y)
}
fn left() -> (Field, Field) { generic(Pair::Left(3, 5)) }
fn right() -> (Field, Field) { generic(Pair::Right(3, 5)) }
fn record(s: S) -> Field { match s { S { a: 0, b: x } | S { a: x, b: 0 } => x, _ => 19 } }
fn recordEntry(a: Field, b: Field) -> Field { record(S { a, b }) }
fn loads(p: &Field) -> Field { match p { &0 | &1 => 23, _ => 29 } }
fn loadEntry(x: Field) -> Field { loads(&x) }
fn loadedTuple(x: Field) -> Field { let &(0 | 1, a) = &(x, 8); a }
fn choosePointer(p: (&Field, Field)) -> Field {
  let (a, 0) | (a, 1) = p; *a
}
fn pointerBinder(x: Field) -> Field { choosePointer((&13, x)) }
fn scrutinee() -> (Field, Field) { debug!(\"scrutinee\"); (*&1, *&8) }
fn once() -> Field { let (0, x) | (1, x) = scrutinee(); x }
fn early(x: Field) -> Field { 'done: { let 0 | 1 = x; break 'done 31; } }
fn skip() -> Field { match 0 { 0 => 37, _ => { let 0 | 1 = 2; 1 / 0 } } }
fn noMatch() -> Field { match 4 { 0 | 1 => 0, 2 | 3 => 1 } }
fn mismatch() -> Field { let 0 | 1 = 3; 0 }
fn nestedGuard(v: ((Field, &Field), Field)) -> Field {
  match v { ((1, _) | (_, &0), 0) => 41, _ => 43 }
}
fn guardedEntry(x: Field) -> Field { nestedGuard(((x, &0), 1)) }
fn badLoad(p: &Field) -> Field { match p { &0 | _ => 47 } }
fn badEntry() -> Field { badLoad(&0) }
"

#guard (source.findFunction? "overlap").any fun definition => match definition.body with
  | .letValue (.orElse _ _ _) _ _ => true
  | _ => false

def checks : List (String × List (SourceValue Rat) × SourceValue Rat × Heap Rat) := [
  ("literals", [0], 10, []), ("literals", [1], 10, []), ("literals", [2], 10, []), ("literals", [3], 20, []),
  ("constants", [1], 11, []), ("constants", [2], 21, []),
  ("overlap", [.tuple [7, 0, 9]], 7, []), ("overlap", [.tuple [7, 1, 9]], 9, []),
  ("nested", [.tuple [1, 6]], 6, []), ("array", [.tuple [0, 6]], 6, []),
  ("array", [.tuple [6, 0]], 6, []), ("repeated", [.tuple [1, 0]], 12, []),
  ("left", [], .tuple [3, 5], []), ("right", [], .tuple [5, 3], []),
  ("recordEntry", [0, 7], 7, []), ("recordEntry", [7, 0], 7, []), ("recordEntry", [7, 1], 19, []),
  ("loadEntry", [0], 23, [0]), ("loadEntry", [1], 23, [1]), ("loadEntry", [2], 29, [2]),
  ("loadedTuple", [1], 8, [.tuple [1, 8]]),
  ("pointerBinder", [0], 13, [13]), ("pointerBinder", [1], 13, [13]),
  ("once", [], 8, [1, 8]), ("early", [1], 31, []), ("skip", [], 37, []),
  ("guardedEntry", [1], 43, [0]), ("badEntry", [], 47, [0])
]

run_cmd do
  for text in [
    "fn f(x: Field) -> Field { match x { 0 | 0 => 1, _ => 2 } }",
    "fn f(x: Field) -> Field { let 0 | (1 | 0) = x; 2 }",
    "fn f(x: (Field, Field)) -> Field { let (a, 0) | (0, b) = x; a }",
    "fn f(x: (Field, Field)) -> Field { let (a, 0) | (0, _) = x; a }",
    "fn f(x: (Field, (Field,))) -> Field { let (a, _) | (_, a) = x; 1 }",
    "fn f(x: (Field, Field)) -> Field { let (a, 0) | (a, a) = x; a }",
    "fn f(x: Field) -> Field { let 0 | (0,) = x; 1 }",
    "fn f(x: [Field; 2]) -> Field { let [0 | 0, _] = x; 1 }",
    "fn f(p: &Field) -> Field { match p { &0 | &0 => 1, _ => 2 } }"
  ] do
    match Generic.Frontend.ofString (← Lean.getEnv) text with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted or-pattern: {text}"

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def collision : Generic.Program Nat := aiur% "fn f(x: Field) -> Field { match x { 0 | 7 => 1, _ => 2 } }"
#guard (Generic.prepare (collision.toField (ZMod 7))).toOption.isNone

-- The first nested alternative succeeds, then the enclosing tuple fails.
-- This must not backtrack into the alternative that dereferences the bad pointer.
def shortCircuitChecks : Except String Unit := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["guardedEntry", "badEntry"]
  let cases : List (String × List (SourceValue Rat) × Option (SourceValue Rat × Heap Rat)) := [
    ("nestedGuard", [.tuple [.tuple [1, .ptr .field 99], 1]], some (43, [])),
    ("nestedGuard", [.tuple [.tuple [1, .ptr .field 99], 0]], some (41, [])),
    ("nestedGuard", [.tuple [.tuple [0, .ptr .field 99], 1]], none),
    ("badLoad", [.ptr .field 99], none)]
  for (name, args, expected) in cases do
    let (types, locals, body) ← (s.world.prepare name args).mapError reprStr
    let actual := Generic.SourceSemantics.evalExprWith s.world Generic.SourceSemantics.unavailable types locals 1000 body []
    if actual.toOption != expected then throw s!"source short-circuit: {name}"
    let (locals, body) ← (prepareCall q.program name args).mapError reprStr
    let lowered := evalExpr q.program locals 1000 body []
    if lowered.toOption != expected then throw s!"lowered short-circuit: {name}"

#guard shortCircuitChecks == .ok ()

def run : IO Unit := do
  let .ok s := Generic.prepare (source.toField Rat) | throw (IO.userError "or-pattern source failed to check")
  for (name, args, value, heap) in checks do
    let expected := .ok (value, heap)
    unless s.run name args == expected do throw (IO.userError s!"source {name}: {repr (s.run name args)}")
    unless (s.runTraced name args).result == expected do throw (IO.userError s!"traced {name}")
    let .ok q := Generic.specialize s [name] | throw (IO.userError s!"specializing {name}: {repr ((Generic.specialize s [name]).map (fun _ => ())) }")
    unless q.coreRun name args == expected do throw (IO.userError s!"lowered {name}: {repr (q.coreRun name args)}")
    let .ok _ := q.compile | throw (IO.userError s!"compiling {name}: {repr (q.compile.map (fun _ => ())) }")
  for name in ["noMatch", "mismatch"] do
    unless (s.run name []).toOption.isNone do throw (IO.userError s!"source accepted {name}")
    let .ok q := Generic.specialize s [name] | throw (IO.userError s!"specializing {name}")
    unless (q.coreRun name []).toOption.isNone do throw (IO.userError s!"lowered accepted {name}")
    let .ok _ := q.compile | throw (IO.userError s!"compiling {name}")
  let messages := (s.runTraced "once" []).events.filter fun event => match event with | .message _ _ => true | _ => false
  unless messages == [.message "scrutinee" []] do throw (IO.userError "or-pattern evaluated scrutinee more than once")
  if let .error error := shortCircuitChecks then throw (IO.userError error)
  IO.println s!"Passed {checks.length * 3} or-pattern execution checks and {checks.length + 2} compilations."

end AiurOrPatternTests
