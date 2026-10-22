import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur Aiur.Circuit

namespace AiurInputTypeTests

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def source : Program Nat := aiur% "
enum Box { Empty, Full(&Field) }
enum Outer { Raw(Field), Nested((Field, Box)) }
enum A { End, Next(B) }
enum B { Next(&A) }
enum Plain { Empty, Pair((Field, (Field,))) }

table inputs: (Plain,) { (Plain::Empty,), (Plain::Pair((3, (4,))),), }
table outputs: Field { 0, 7, }
table empty: Plain { }
map inspect(value: Plain) -> Field = inputs => outputs;

fn unbox(value: Box) -> Field { match value { Box::Empty => 0, Box::Full(p) => *p } }
fn outer(value: Outer) -> Field { match value { Outer::Raw(x) => x, _ => 0 } }
fn tuple_arg(value: (Field, Box)) -> Field { value.0 }
fn second(x: Field, value: Box) -> Field { x + unbox(value) }
fn identity(x: Field) -> Field { x }
fn read_plain(value: Plain) -> Field { inspect(value) }
fn internal(x: Field) -> Field { unbox(Box::Full(&x)) }
fn internal_empty() -> Field { unbox(Box::Empty) }
fn returned() -> Box { Box::Empty }
fn returned_pointer(x: Field) -> &Field { &x }
"

def program := source.toField Rat
def plain : SourceValue Rat := .construct "Plain" "Pair" [.tuple [3, .tuple [4]]]

def typeChecks : List (String × Bool × Bool) := [
  ("field", Ty.field.pointerFree source.enums, true),
  ("unit", (Ty.tuple []).pointerFree source.enums, true),
  ("nested tuple", (Ty.tuple [.field, .tuple [.field]]).pointerFree source.enums, true),
  ("all enum variants pointer-free", (Ty.enum "Plain").pointerFree source.enums, true),
  ("direct pointer", (Ty.ptr .field).pointerFree source.enums, false),
  ("pointer hidden in a variant", (Ty.enum "Box").pointerFree source.enums, false),
  ("transitive enum and tuple payload", (Ty.enum "Outer").pointerFree source.enums, false),
  ("mutually recursive types", (Ty.enum "A").pointerFree source.enums, false),
  ("nested pointer-bearing enum", (Ty.tuple [.tuple [.enum "Box"]]).pointerFree source.enums, false),
  ("unknown enum", (Ty.enum "Unknown").pointerFree source.enums, false)
]

def runtimeChecks : List (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("unselected pointer variant", eval program "unbox" [.construct "Box" "Empty" []],
    .error (.pointerEntryArgument 0)),
  ("transitive unselected variant", eval program "outer" [.construct "Outer" "Raw" [3]],
    .error (.pointerEntryArgument 0)),
  ("tuple containing pointer-bearing type", eval program "tuple_arg" [.tuple [3, .construct "Box" "Empty" []]],
    .error (.pointerEntryArgument 0)),
  ("offending parameter index", eval program "second" [3, .construct "Box" "Empty" []],
    .error (.pointerEntryArgument 1)),
  ("entry rejected before reading values", eval program "unbox" [], .error (.pointerEntryArgument 0)),
  ("pointer-free enum entry and map", eval program "read_plain" [plain], .ok 7),
  ("pointer-free enum map entry", eval program "inspect" [plain], .ok 7),
  ("internal pointer argument", eval program "internal" [8], .ok 8),
  ("internal empty variant", eval program "internal_empty" [], .ok 0),
  ("ordinary pointer-bearing result type", eval program "returned" [], .ok (.construct "Box" "Empty" [])),
  ("ordinary pointer result", eval program "returned_pointer" [8], .ok (.ptr .field 0)),
  ("wrong value still fails ordinary typing", eval program "identity" [.ptr .field 0],
    .error (.argumentTypeMismatch "identity" .field (.ptr .field))),
  ("enum payload still checked", eval program "read_plain" [.construct "Plain" "Empty" [.ptr .field 0]],
    .error (.malformedValue (.enum "Plain")))
]

-- No input values, execution fuel, or field operations are needed to reject this entry.
example : checkEntry source "unbox" = .error (.pointerEntryArgument 0) := by decide +kernel

-- Validate declarations even when there is no row to inspect.
def emptyPointerTable : Program Nat := {
  functions := []
  enums := source.enums
  tables := [⟨"bad", .enum "Box", []⟩]
}
example : typecheck emptyPointerTable = .error (.pointerType "table 'bad'" (.enum "Box")) := by decide +kernel
example : (compile (emptyPointerTable.toField Rat)).isOk = false := by decide +kernel
example : (eval (emptyPointerTable.toField Rat) "missing" []).isOk = false := by decide +kernel

-- Map signature checks independently enforce both sides of the same boundary.
example : checkMap source ⟨"bad", [("x", .enum "Box")], .field, "inputs", "outputs"⟩ =
    .error (.pointerType "map 'bad' inputs" (.tuple [.enum "Box"])) := by decide +kernel
example : checkMap source ⟨"bad", [], .enum "Box", "inputs", "outputs"⟩ =
    .error (.pointerType "map 'bad' result" (.enum "Box")) := by decide +kernel

run_cmd do
  let env ← Lean.getEnv
  for text in [
    "table bad: &Field { }",
    "table bad: (Field, (&Field,)) { }",
    "enum E { Empty, Full(&Field) } table bad: E { E::Empty, }",
    "enum E { Empty, Full(&Field) } table bad: E { }",
    "enum E { Empty, Full(&Field) } enum W { Unit, Wrap((Field, E)) } table bad: W { W::Unit, }",
    "enum A { End, Next(B) } enum B { Next(&A) } table bad: A { A::End, }"
  ] do
    match Frontend.ofString env text with
    | .error _ => pure ()
    | .ok _ => throwError "accepted pointer-bearing table type: {text}"

def system : System Rat := (compile program).toOption.getD { chips := [] }
theorem compiled : compile program = .ok system := by
  have succeeds : (compile program).isOk = true := by decide +kernel
  cases lowered : compile program with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [system, lowered, Except.toOption]

def badEntry : Message Rat := ⟨"unbox", [⟨.enum "Box", [0, 0]⟩], .field 0⟩
example : system.check ⟨[]⟩ badEntry [] = .error .pointerEntryArgument := by decide +kernel

-- The public predicates reject this type for every result and every proof witness.
example (args : List (SourceValue Rat)) (result : SourceValue Rat) :
    ¬ EvalCall program "unbox" args result := by
  rintro ⟨entry, _⟩
  have rejected : checkEntry program "unbox" = .error (.pointerEntryArgument 0) := by decide +kernel
  rw [rejected] at entry
  cases entry

theorem badEntry_not_public : ¬ badEntry.PublicArguments system.enums := by
  intro accepted
  have free := accepted ⟨.enum "Box", [0, 0]⟩ (by simp [badEntry])
  have rejected : (Ty.enum "Box").pointerFree system.enums = false := by decide +kernel
  change (Ty.enum "Box").pointerFree system.enums = true at free
  rw [rejected] at free
  cases free

example : ¬ EntryDerives system badEntry := fun accepted => badEntry_not_public accepted.2.1
example : ¬ MemoEntryDerives system badEntry := fun accepted => badEntry_not_public accepted.2.1

-- Pointer-free enum inputs still participate in both end-to-end completeness results.
theorem plain_derives : EncodedEntryDerives system "read_plain" (entryValues [plain]) (.field 7) := by
  have executed : Aiur.run program "read_plain" [plain] 16 = .ok (.field 7, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa [Value.mapAddress] using complete

example : EncodedMemoEntryDerives system "read_plain" (entryValues [plain]) (.field 7) := plain_derives.memo

example (accepted : EncodedEntryDerives system "read_plain" (entryValues [plain]) (.field 0)) : False := by
  have wrong := compiler_entry_sound compiled accepted (by decide +kernel)
  have actual : EvalCall program "read_plain" [plain] (.field 7) :=
    eval_spec (hints := HintProvider.unavailable) (fuel := 16) (by decide +kernel)
  have same := actual.deterministic wrong (by decide +kernel)
  simp [Value.mapAddress] at same

/-- info: 'Aiur.Value.pointerFree_of_type' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Value.pointerFree_of_type

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in typeChecks do checkEqual label actual expected
  for (label, actual, expected) in runtimeChecks do checkEqual label actual expected
  checkEqual "pointer-free root type" (system.check ⟨[]⟩ badEntry []) (.error .pointerEntryArgument)
  IO.println s!"Passed {typeChecks.length + runtimeChecks.length + 1} input type checks."

end AiurInputTypeTests
