import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurControlTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- Keep the source exits visible through checking and field conversion. -/
def source : Generic.Program Nat := aiur% "
type Pair = (Field, Field);
const seven = 7;
enum Answer { Empty, Pair(Pair) }
fn chosen(x: Field) -> Field {
  let y = 'chosen: {
    match x { 0 => break 'chosen seven, 1 => return 20, _ => () };
    9
  };
  y + 1
}
fn shadow() -> Field {
  let x = 3;
  let y = 'b: { let x = 100; break 'b 7; };
  x + y
}
fn outer() -> Field {
  'outer: { let x = 'inner: { break 'outer 5; }; x + 100 }
}
fn same_label() -> Field {
  'b: { let x = 'b: { break 'b 5; }; break 'b (x + 1); }
}
fn precedence() -> Field { return 3 + 4 * 2; 1 / 0 }
fn return_payload() -> Field { return (return 11); }
fn break_payload() -> Field { 'b: { break 'b (return 12); } }
fn return_block() -> Field { return 'b: { break 'b 4; }; }
fn callee() -> Field { return 4; }
fn caller() -> Field { callee() + 1 }
fn caller_block() -> Field { 'b: { let x = callee(); break 'b (x + 2); } }
fn add(x: Field, y: Field) -> Field { x + y }
fn call_args() -> Field { add(*&1, { return 7; }) }
fn skip_calls() -> Field { return 8; forever() }
fn forever() -> Field { forever() }
fn skip_right() -> Field { (return 9) + 1 / 0 }
fn right_effect() -> Field { *&1 + (return 10) }
fn tuple_exit() -> Field { let x = (*&1, return 13, *&2); 0 }
fn array_exit() -> Field { let a = [*&1, return 14, *&2]; 0 }
fn repeat_exit() -> Field { let a = [return 15; 0]; 0 }
fn store_exit() -> Field { let p = &(return 16); 0 }
fn load_exit() -> Field { let x = *(return 17); 0 }
fn key_exit() -> Field { hint::<Field>({ return 18; }) }
fn skip_hint() -> Field { return 19; hint::<Field>(()) }
fn early<T>(x: T) -> T { return x; }
fn generic() -> Pair { early((2, 3)) }
fn pointer() -> Field { let p = 'b: { break 'b &5; }; let &x = p; return x; }
fn enumeration() -> Answer { return Answer::Pair((5, 6)); }
fn match_statement(x: Field) -> Field { match x { 0 => return 23, _ => return 24 }; }
fn final_let() -> () { let x = 3; }
fn hinted(x: Field) -> Field {
  let key = 'b: { match x { 0 => return 7, _ => break 'b *&3 } };
  return hint::<Field>(key);
}
fn unit() -> () { return; }
fn empty() -> () {}
fn unit_block() -> Field { 'b: { break 'b; }; 21 }
fn nested_payload() -> Field { 'a: { 'b: { break 'b (break 'a 22); } } }
fn loop(n: Field) -> Field { match n { 0 => return 0, _ => return loop(n - 1) + 1 } }
fn branch_calls(x: Field) -> Field {
  let y = 'b: { match x { 0 => return 7, _ => break 'b callee() } };
  add(y, 2)
}
"

#guard (source.findFunction? "callee").map (·.body) ==
  some (.control (.exit .function) (.literal 4))
#guard (source.findFunction? "shadow").any fun definition => Generic.ControlLower.hasControl definition.body

abbrev Result := Except String (SourceValue Rat × Heap Rat)

def checks : List (String × List (SourceValue Rat) × Result) := [
  ("chosen", [0], .ok (8, [])), ("chosen", [1], .ok (20, [])), ("chosen", [2], .ok (10, [])),
  ("shadow", [], .ok (10, [])), ("outer", [], .ok (5, [])), ("same_label", [], .ok (6, [])),
  ("precedence", [], .ok (11, [])), ("return_payload", [], .ok (11, [])),
  ("break_payload", [], .ok (12, [])), ("return_block", [], .ok (4, [])),
  ("caller", [], .ok (5, [])), ("caller_block", [], .ok (6, [])),
  ("call_args", [], .ok (7, [1])), ("skip_calls", [], .ok (8, [])),
  ("skip_right", [], .ok (9, [])), ("right_effect", [], .ok (10, [1])),
  ("tuple_exit", [], .ok (13, [1])), ("array_exit", [], .ok (14, [1])),
  ("repeat_exit", [], .ok (15, [])), ("store_exit", [], .ok (16, [])),
  ("load_exit", [], .ok (17, [])), ("key_exit", [], .ok (18, [])),
  ("skip_hint", [], .ok (19, [])), ("generic", [], .ok (.tuple [2, 3], [])),
  ("pointer", [], .ok (5, [5])), ("enumeration", [], .ok (.construct "Answer" "Pair" [.tuple [5, 6]], [])),
  ("match_statement", [0], .ok (23, [])), ("match_statement", [1], .ok (24, [])),
  ("final_let", [], .ok (.tuple [], [])),
  ("unit", [], .ok (.tuple [], [])), ("empty", [], .ok (.tuple [], [])),
  ("unit_block", [], .ok (21, [])), ("nested_payload", [], .ok (22, [])),
  ("loop", [4], .ok (4, [])),
  ("branch_calls", [0], .ok (7, [])), ("branch_calls", [1], .ok (6, []))
]

def checkExecutions : Except String Unit := do
  let s ← Generic.prepare (source.toField Rat)
  for (name, args, expected) in checks do
    let q ← Generic.specialize s [name]
    for (mode, actual) in [("source", s.run name args), ("specialized", q.run name args),
        ("core", q.coreRun name args)] do
      if actual != expected then throw s!"{name} ({mode}): expected {repr expected}, got {repr actual}"
    let _ ← q.compile

#guard checkExecutions == .ok ()

-- The dynamic hint key retains ordinary allocations; an earlier return skips it.
#guard (do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["hinted"]
  let provider : HintDispatcher Rat := fun _ key => match key with
    | .field 3 => .ok (.field (29 : Rat))
    | _ => .error HintError.unavailable
  let direct := s.checkedHints provider
  let core := HintProvider.checked q.program.enums provider
  return [s.run "hinted" [1] (hints := direct), q.run "hinted" [1] (hints := direct),
    q.coreRun "hinted" [1] (hints := core), q.coreRun "hinted" [0]]) =
      .ok [.ok (29, [3]), .ok (29, [3]), .ok (29, [3]), .ok (7, [])]

#guard (do
  let s ← Generic.prepare (source.toField Rat)
  s.run "callee" [] 0) == .error (reprStr EvalError.outOfFuel)

-- A concrete row on the return arm requires no callee proof. Its inactive
-- call output is arbitrary. On the other arm the lookup must be discharged.
def circuitSource : Generic.Program Nat := aiur% "
fn risky(x: Field) -> Field { 1 / x }
fn main(x: Field) -> Field {
  let y = 'b: { match x { 0 => return 7, _ => break 'b risky(x) } };
  y + 2
}
"

def checkRows : Except String Unit := do
  let s ← Generic.prepare (circuitSource.toField Rat)
  let q ← Generic.specialize s ["main"]
  let c ← q.compile
  let returned : Circuit.Row Rat := ⟨"main", [0, 7, 7, 1, 0, 1, 0, 123]⟩
  let resumed : Circuit.Row Rat := ⟨"main", [2, 5/2, 5/2, 0, 1/2, 0, 1, 1/2]⟩
  let callee : Circuit.Row Rat := ⟨"risky", [2, 1/2, 1/2]⟩
  c.check {} ⟨"main", [0], 7⟩ [returned]
  c.checkMemo {} ⟨"main", [0], 7⟩ [⟨returned, 1⟩]
  c.check {} ⟨"main", [2], .field (5/2)⟩ [resumed, callee]
  c.checkMemo {} ⟨"main", [2], .field (5/2)⟩ [⟨resumed, 1⟩, ⟨callee, 1⟩]
  if (c.check {} ⟨"main", [2], .field (5/2)⟩ [resumed]).isOk then throw "missing active call accepted"
  if (c.check {} ⟨"main", [0], 8⟩ [returned]).isOk then throw "incorrect return accepted"

#guard checkRows == .ok ()

instance : Fact (Nat.Prime 101) := ⟨by decide⟩
#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["chosen", "loop", "generic", "pointer", "branch_calls"]
  let _ ← q.compile
  q.coreRun "chosen" [0]) == .ok (8, [])

-- Ill-scoped exits are rejected before specialization, including unused code.
run_cmd do
  let env ← Lean.getEnv
  for code in [
    "fn f() -> Field { break 'missing 0; }",
    "fn f() -> Field { 'b: { break 'b (); 1 } }",
    "fn f() -> Field { return (); }",
    "fn f() -> () { return 0; }",
    "fn f() -> Field { return; }",
    "fn f() -> Field { 'b: { break 'b; } }",
    "fn f() -> Field { 'b: { 0 }; break 'b 1; }",
    "fn f() -> Field { 'b: { g() } } fn g() -> Field { break 'b 0; }",
    "table t: Field { return 0 }",
    "const x = return 0;",
    "fn f() -> Field { @ b: { 0 } }"
  ] do
    match Generic.Frontend.ofString env code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"

/-- info: 'Aiur.Generic.ControlLower.function_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.ControlLower.function_correct
/-- info: 'Aiur.Generic.SourceSemantics.evalFunction_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.SourceSemantics.evalFunction_spec

def run : IO Unit := do
  match checkExecutions *> checkRows with
  | .ok () => IO.println s!"Passed {3 * checks.length} control-flow execution checks and {checks.length} compilations."
  | .error e => throw (IO.userError e)

end AiurControlTests
