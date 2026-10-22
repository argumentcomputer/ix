import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurRefutableLetTests

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def source : Program Nat := aiur% "
enum Outcome { Empty, Pair((Field, Field)) }
table inputs: (Field,) { (0,), (1,), }
table outputs: Outcome { Outcome::Empty, Outcome::Pair((0, 9)), }
map lookup(x: Field) -> Outcome = inputs => outputs;

fn literal(x: Field) -> Field { let 0 = x; 42 }
fn nested(p: (Field, (Field, Field))) -> Field { let (0, (x, 1)) = p; x }
fn unpack(value: Outcome) -> Field { let Outcome::Pair((0, x)) = value; x }
fn shadow(x: Field) -> Field { let (0, x) = (0, x + 1); x }
fn mapped(x: Field) -> Field { let Outcome::Pair((0, x)) = lookup(x); x }
fn allocate(x: Field) -> Field { let (0, p) = (0, &x); *p }
fn reject() -> Field { let 0 = 1; 42 }
fn skip_body() -> Field { let 0 = 1; 1 / 0 }
fn rhs_error() -> Field { let 0 = 1 / 0; 42 }
fn body_error() -> Field { let 0 = 0; 1 / 0 }
fn loop(x: Field) -> Field { loop(x) }
fn lazy(x: Field) -> Field {
  match x { 0 => 9, _ => { let 0 = 1; let p = &0; loop(*p) } }
}
fn reduced() -> Field { let 7 = 0; 4 }
"

def program := source.toField Rat

def runtimeTests : List (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("literal let succeeds", eval program "literal" [0], .ok 42),
  ("literal let fails", eval program "literal" [1], .error .patternMismatch),
  ("nested pattern binds", eval program "nested" [.tuple [0, .tuple [9, 1]]], .ok 9),
  ("nested pattern fails", eval program "nested" [.tuple [0, .tuple [9, 2]]], .error .patternMismatch),
  ("enum payload binds", eval program "unpack" [.construct "Outcome" "Pair" [.tuple [0, 8]]], .ok 8),
  ("wrong enum variant", eval program "unpack" [.construct "Outcome" "Empty" []], .error .patternMismatch),
  ("wrong enum payload", eval program "unpack" [.construct "Outcome" "Pair" [.tuple [1, 8]]],
    .error .patternMismatch),
  ("refutable binding shadows", eval program "shadow" [3], .ok 4),
  ("map output matches", eval program "mapped" [1], .ok 9),
  ("map output fails pattern", eval program "mapped" [0], .error .patternMismatch),
  ("map error precedes matching", eval program "mapped" [2], .error (.missingMapInput "lookup")),
  ("impossible let is well typed", eval program "reject" [], .error .patternMismatch),
  ("mismatch skips continuation", eval program "skip_body" [], .error .patternMismatch),
  ("RHS error precedes matching", eval program "rhs_error" [], .error .divisionByZero),
  ("matched continuation runs", eval program "body_error" [], .error .divisionByZero),
  ("inactive mismatching let", eval program "lazy" [0], .ok 9),
  ("active mismatching let", eval program "lazy" [1], .error .patternMismatch),
  ("literal before specialization", eval program "reduced" [], .error .patternMismatch)
]

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
example : eval (source.toField (ZMod 7)) "reduced" [] = .ok 4 := by decide +kernel

-- Matching never re-executes the RHS, even when it allocates a cell.
example : Aiur.run program "allocate" [8] 16 = .ok (.field 8, [.field 8]) := by decide +kernel

-- Accepting refutable lets keeps ordinary pattern typing and scope checks.
run_cmd do
  let env ← Lean.getEnv
  for text in [
    "fn f() -> Field { let (0, x) = (1, 2); missing }",
    "fn f() -> Field { let 0 = (0,); 1 }",
    "fn f() -> Field { let (0, x, x) = (0, 1, 2); x }",
    "enum E { A(Field), B } fn f() -> Field { let E::A(x, y) = E::B; x }",
    "enum E { A(Field), B } fn f() -> Field { let E::Missing = E::B; 0 }",
    "fn f(0: Field) -> Field { 1 }",
    "enum E { A(Field), B } fn f(E::A(x): E) -> Field { x }"
  ] do
    match Frontend.ofString env text with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted invalid source: {text}"

def system : System Rat := (compile program).toOption.getD { chips := [] }
theorem compiled : compile program = .ok system := by
  have succeeds : (compile program).isOk = true := by decide +kernel
  cases lowered : compile program with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [system, lowered, Except.toOption]

-- Completeness covers active enum/literal tests and the map premise supplying the value.
theorem mapped_derives : EncodedEntryDerives system "mapped" (entryValues [1]) (.field 9) := by
  have executed : Aiur.run program "mapped" [1] 16 = .ok (.field 9, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa [Value.mapAddress] using complete

example : EncodedMemoEntryDerives system "mapped" (entryValues [1]) (.field 9) := mapped_derives.memo

-- Inactive mismatches still have witnesses; their calls and ROM lookups add no premises.
example : EncodedEntryDerives system "lazy" (entryValues [0]) (.field 9) := by
  have executed : Aiur.run program "lazy" [0] 16 = .ok (.field 9, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa [Value.mapAddress] using complete

example : EncodedEntryDerives system "allocate" (entryValues [8]) (.field 8) := by
  have executed : Aiur.run program "allocate" [8] 16 = .ok (.field 8, [.field 8]) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (99 : Rat)) (by intro i j hi hj _; simp at hi hj; omega)
  simpa [Value.mapAddress] using complete

-- No result can be justified for an active mismatching let, regardless of the witness.
theorem reject_has_no_evaluation (result : SourceValue Rat) : ¬ EvalCall program "reject" [] result := by
  rintro ⟨_, heap, ⟨prepared, body⟩⟩
  have expected : prepareCall program "reject" ([] : List (SourceValue Rat)) =
      .ok ([], .letValue (.literal 0) (.literal 1) (.literal 42)) := by
    exact prepareCall_of_types («fn» := ⟨"reject", [], .field,
      .letValue (.literal 0) (.literal 1) (.literal 42)⟩)
      (by simp [program, source, Program.toField, Program.map, Program.findFunction?,
        Function.map, Expr.map, Pattern.map]) (by rfl) (by simp)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (prepared.symm.trans expected))
  cases body with
  | letValue value matched _ =>
      cases value
      simp [Pattern.bindings] at matched

theorem reject_has_no_derivation (result : Rat)
    (accepted : EncodedEntryDerives system "reject" (entryValues []) (.field result)) : False :=
  reject_has_no_evaluation _ (compiler_entry_sound compiled accepted (by simp [Value.pointerFree]))

example {rom : WireROM Rat} (valid : rom.Valid) (result : Rat)
    (graph : MemoDerivation system rom ⟨"reject", [], .field result⟩) (acyclic : graph.Acyclic) : False := by
  apply reject_has_no_derivation result
  refine ⟨[], .field result, .nil, WireValue.decode_field _ _, ?_, ?_,
    rom, valid, graph.derives_of_acyclic acyclic⟩
  · exact ⟨by simp, ⟨.field result, WireValue.decode_field _ _⟩⟩
  · simp [Message.PublicArguments]

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in runtimeTests do
    checkEqual label actual expected
  checkEqual "let RHS allocates once" (Aiur.run program "allocate" [8] 16) (.ok (.field 8, [.field 8]))
  checkEqual "let literal specializes to field" (eval (source.toField (ZMod 7)) "reduced" []) (.ok 4)
  checkEqual "refutable let compilation" (compile program).isOk true
  IO.println s!"Passed {runtimeTests.length + 3} refutable let checks."

end AiurRefutableLetTests
