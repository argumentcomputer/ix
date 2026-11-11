import Aiur.Generic
import Mathlib.Algebra.Field.Rat

namespace AiurDiagnosticTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def source : Generic.Program Nat := aiur% "
type Pair<T> = (T, T);
enum Option<T> { None, Some(T) }
struct Box<T> { value: T }
fn identity<T>(x: T) -> T { let y: T = x; (y: T) }
fn annotated() -> Field {
  let (a, b): Pair<Field> = (3, 4);
  let empty: Option<Field> = Option::None;
  let box: Box<[Field; 0]> = Box { value: [] };
  let p: &Field = &a;
  identity((*p: Field)) + b
}
fn say(x: Field) -> Field { debug!(\"callee\", x); x + 1 }
fn logged() -> Field {
  debug!(\"before\");
  debug!(\"values\", say(*&1), *&2,);
  debug!(\"after\", ());
  9
}
fn escaped() -> () { debug!(\"/* kept */ // ' @ & > ..= \\\"quoted\\\" \\\\ \\n\"); }
fn early() -> Field { debug!(\"discarded\", *&1, return 7, 1 / 0); 0 }
fn block() -> Field { 'done: { debug!(\"discarded\", break 'done 8); 0 } }
fn skip() -> Field { match 0 { 0 => 5, _ => { debug!(\"inactive\"); 0 } } }
fn failing() -> Field { debug!(\"retained\", 4); 1 / 0 }
fn failure() -> Field { failing() }
fn forever() -> Field { debug!(\"loop\"); forever() }
"

#guard (source.findFunction? "identity").any fun f => match f.body with
  | .letValue _ (.builtin (.ascribe _) [_]) (.builtin (.ascribe _) [_]) => true
  | _ => false

def checks : List (String × Except String (SourceValue Rat × Heap Rat)) := [
  ("annotated", .ok (7, [3])),
  ("logged", .ok (9, [1, 2])),
  ("escaped", .ok (.tuple [], [])),
  ("early", .ok (7, [1])), ("block", .ok (8, [])), ("skip", .ok (5, []))
]

run_cmd do
  let env ← Lean.getEnv
  -- Character preprocessing must handle realistic source sizes in the
  -- elaborator's interpreter without one stack frame per character.
  let long := String.ofList (List.replicate 100000 'x')
  unless Generic.Frontend.prepareSource long == .ok long do
    throwError "large source changed during character preprocessing"
  let spaces := String.ofList (List.replicate 100004 ' ')
  unless Generic.Frontend.prepareSource ("/*" ++ long ++ "*/") == .ok spaces do
    throwError "large block comment was not masked correctly"
  for text in [
    "fn f() -> Field { let x: () = 1; 0 }",
    "fn f() -> Field { ((): Field) }",
    "fn f() -> () { let x: Missing = (); }",
    "fn f() -> Field { (1: &Field) }",
    "fn f() -> () { debug!(1); }",
    "fn f() -> () { debug!(\"unterminated); }",
    "fn f() -> () { @bad: {} }"
  ] do
    match Generic.Frontend.ofString env text with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {text}"

def run : IO Unit := do
  let .ok s := Generic.prepare (source.toField Rat) | throw (IO.userError "diagnostic source failed to check")
  for (name, expected) in checks do
    let actual := s.run name []
    unless actual == expected do throw (IO.userError s!"{name}: {repr actual}")
    let traced := s.runTraced name []
    unless traced.result == expected && traced.activeCalls.isEmpty do
      throw (IO.userError s!"traced {name}: {repr traced}")
    let .ok specialized := Generic.specialize s [name] | throw (IO.userError s!"specializing {name}")
    unless specialized.coreRun name [] == expected do throw (IO.userError s!"lowered {name}")
    let .ok _ := specialized.compile | throw (IO.userError s!"compiling {name}")
  let traced := s.runTraced "logged" []
  let expected : List (Generic.TraceEvent Rat) := [
    .enter "logged" [], .message "before" [], .enter "say" [1],
    .message "callee" [1], .leave "say" 2, .message "values" [2, 2],
    .message "after" [.tuple []], .leave "logged" 9]
  unless traced.events == expected do throw (IO.userError s!"trace order: {repr traced.events}")
  unless (s.runTraced "escaped" []).events.contains
      (.message "/* kept */ // ' @ & > ..= \"quoted\" \\ \n" []) do
    throw (IO.userError "message text was changed by frontend preprocessing")
  for name in ["early", "block", "skip"] do
    unless (s.runTraced name []).events.all (fun e => match e with | .message _ _ => false | _ => true) do
      throw (IO.userError s!"emitted incomplete or inactive message: {name}")
  let failed := s.runTraced "failure" []
  unless failed.result == s.run "failure" [] && failed.activeCalls == ["failing", "failure"] &&
      failed.events.contains (.message "retained" [4]) do
    throw (IO.userError s!"lost failure trace: {repr failed}")
  for fuel in [0, 1, 2, 10, 20] do
    unless (s.runTraced "forever" [] fuel).result == s.run "forever" [] fuel do
      throw (IO.userError "tracing changed the fuel bound")
  IO.println "Passed annotation and diagnostic checks."

end AiurDiagnosticTests
