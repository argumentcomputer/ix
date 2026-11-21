import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurPointerTests

def sample : Program Nat := aiur% "
fn immediate(x: Field) -> Field { *&x }
fn nested(p: &&Field) -> Field { **p }
fn nested_entry(x: Field) -> Field { nested(&&x) }
fn read_pair(p: &(Field, &Field)) -> Field { let (x, q) = *p; x + *q }
fn tuple_memory(x: Field) -> Field { read_pair(&(x, &(x + 1))) }
fn pointer_projection(p: (&Field, Field)) -> Field { *p.0 + p.1 }
fn precedence(x: Field) -> Field { x * *&x + x / *&x }
fn projection_entry(x: Field) -> Field { pointer_projection((&x, x + 1)) }
fn immutable(x: Field) -> Field { let p = &x; let x = x + 1; *p }
fn share(x: Field) -> (&Field, &Field) { (&x, &x) }
fn unit() -> () { *&() }
fn singleton(x: Field) -> (Field,) { *&(x,) }
fn heterogeneous(x: Field) -> Field {
  let a = &x;
  let b = &(x, &a, ());
  let (_, pp, ()) = *b;
  **pp
}
fn left(p: &Field, n: Field) -> Field {
  match n { 0 => *p, _ => right(p, n - 1) }
}
fn right(p: &Field, n: Field) -> Field {
  match n { 0 => *p, _ => left(p, n - 1) }
}
fn recursive(x: Field) -> Field { left(&x, 4) }
fn branch(tag: Field, x: Field) -> Field { match tag { 0 => x, _ => *&x } }
fn ordered(x: Field) -> (&Field, &Field) { (&x, &(x + 1)) }
fn forever(p: &Field) -> Field { forever(p) }
fn infinite(x: Field) -> Field { forever(&x) }
"

def rationalTests : List (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("immediate store/load", eval (sample.toField Rat) "immediate" [7], .ok 7),
  ("nested pointers", eval (sample.toField Rat) "nested_entry" [7], .ok 7),
  ("tuple cells", eval (sample.toField Rat) "tuple_memory" [7], .ok 15),
  ("pointer projection precedence", eval (sample.toField Rat) "projection_entry" [7], .ok 15),
  ("unary and binary multiplication", eval (sample.toField Rat) "precedence" [7], .ok 50),
  ("immutable allocation", eval (sample.toField Rat) "immutable" [7], .ok 7),
  ("empty tuple cell", eval (sample.toField Rat) "unit" [], .ok (.tuple [])),
  ("singleton cell", eval (sample.toField Rat) "singleton" [7], .ok (.tuple [7])),
  ("heterogeneous nested cells", eval (sample.toField Rat) "heterogeneous" [7], .ok 7),
  ("mutual recursion with pointers", eval (sample.toField Rat) "recursive" [7], .ok 7),
  ("inactive allocation", eval (sample.toField Rat) "branch" [0, 7], .ok 7),
  ("active allocation", eval (sample.toField Rat) "branch" [1, 7], .ok 7),
  ("pointer entry rejected", eval (sample.toField Rat) "nested" [.ptr (.ptr .field) 0],
    .error (.pointerEntryArgument 0)),
  ("nested pointer entry rejected", eval (sample.toField Rat) "pointer_projection"
    [.tuple [.ptr .field 0, 7]], .error (.pointerEntryArgument 0)),
  ("fuel still bounds recursion", eval (sample.toField Rat) "infinite" [7] 20, .error .outOfFuel)
]

-- Public syntax cannot inspect addresses or forge typed pointers.
run_cmd do
  let env ← Lean.getEnv
  for source in [
    "fn f(p: &Field) -> Field { p + 1 }",
    "fn f(p: &Field) -> Field { -p }",
    "fn f(p: &Field) -> Field { p * p }",
    "fn f(p: &Field) -> Field { match p { 0 => 1, _ => 2 } }",
    "fn f(p: &Field) -> Field { p.0 }",
    "fn f(p: Field) -> Field { *p }",
    "fn f() -> &Field { 0 }",
    "fn f() -> &(Field,) { &1 }",
    "fn f(p: &Field, q: &Field) -> Field { p == q }",
    "fn f(p: &Field) -> Field { p as Field }",
    "fn f(p: &Field) { *p }"
  ] do
    match Frontend.ofString env source with
    | .error _ => pure ()
    | .ok _ => throwError "accepted invalid pointer program: {source}"

example : run (sample.toField Rat) "ordered" [7] 10 =
    .ok (.tuple [.ptr .field 0, .ptr .field 1], [7, 8]) := by decide +kernel
example : run (sample.toField Rat) "branch" [0, 7] 10 = .ok (7, []) := by decide +kernel
example : EvalCall (sample.toField Rat) "tuple_memory" [7] 15 :=
  eval_spec (hints := HintProvider.unavailable) (fuel := 20) (by decide +kernel)

def sampleSystem : System Rat := (compile (sample.toField Rat)).toOption.getD { chips := [] }
theorem sample_compiled : compile (sample.toField Rat) = .ok sampleSystem := by
  have succeeds : (compile (sample.toField Rat)).isOk = true := by decide +kernel
  cases compiled : compile (sample.toField Rat) with
  | error error => simp [compiled, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [sampleSystem, compiled, Except.toOption]

-- An untaken branch's store and load require no cells at all.
example : CircuitEvaluates sampleSystem ⟨[]⟩ "branch" [.field 0, .field 7] (.field 7) := by
  have executed : run (sample.toField Rat) "branch" [.field 0, .field 7] 10 =
      .ok (.field 7, []) := by decide +kernel
  obtain ⟨_, _, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have evaluated := EvalFn.intro prepared (evalExpr_spec body)
  have romEval := evaluated.toROM (ROM.ofHeap_cells [] (fun _ => (0 : Rat)))
  have decodedEval : ROMEvalCall ((⟨[]⟩ : WireROM Rat).decode sample.enums)
      (sample.toField Rat) "branch" [.field 0, .field 7] (.field 7) := by
    simpa [ROM.ofHeap, WireROM.decode, Value.mapAddress] using romEval
  exact evaluation_complete_encoded sample_compiled decodedEval
    (.cons (WireValue.decode_field _ 0) (.cons (WireValue.decode_field _ 7) .nil))
    (WireValue.decode_field _ 7)

-- A circuit address need not equal the source allocator's location.
def roundtrip : Program Nat := aiur% "fn f(x: Field) -> Field { let p = &x; *p }"
def roundtripSystem : System Rat :=
  match Circuit.compile (roundtrip.toField Rat) with | .ok system => system | .error _ => { chips := [] }
def goodROM : WireROM Rat := ⟨[(99, 7)]⟩
def roundtripRow : Row Rat := ⟨"f", [7, 7, 99, 7]⟩

theorem roundtrip_compiled : Circuit.compile (roundtrip.toField Rat) = .ok roundtripSystem := by
  have succeeds : (compile (roundtrip.toField Rat)).isOk = true := by decide +kernel
  cases compiled : compile (roundtrip.toField Rat) with
  | error error => simp [compiled, Except.isOk, Except.toBool] at succeeds
  | ok system => simp [roundtripSystem, compiled]
example : roundtripSystem.check goodROM ⟨"f", [7], 7⟩ [roundtripRow] = .ok () := by decide +kernel
example : roundtripSystem.check ⟨[]⟩ ⟨"f", [7], 7⟩ [roundtripRow] =
    .error (.missingCell "f" 0) := by decide +kernel
example : roundtripSystem.check ⟨[(99, 7), (99, 8)]⟩ ⟨"f", [7], 7⟩ [roundtripRow] =
    .error .invalidROM := by decide +kernel
example : roundtripSystem.check ⟨[(99, 8)]⟩ ⟨"f", [7], 7⟩ [roundtripRow] =
    .error (.missingCell "f" 0) := by decide +kernel
example : roundtripSystem.check goodROM ⟨"f", [.ptr .field 99], 7⟩ [roundtripRow] =
    .error .pointerEntryArgument := by decide +kernel

-- Circuit stores may share one cell even though the source allocates twice.
def shared : Program Nat := aiur% "fn f(x: Field) -> (&Field, &Field) { (&x, &x) }"
def sharedSystem : System Rat :=
  match Circuit.compile (shared.toField Rat) with | .ok system => system | .error _ => { chips := [] }
example : run (shared.toField Rat) "f" [7] 10 =
    .ok (.tuple [.ptr .field 0, .ptr .field 1], [7, 7]) := by decide +kernel
example : sharedSystem.check goodROM ⟨"f", [7], .tuple [.ptr .field 99, .ptr .field 99]⟩
    [⟨"f", [7, 99, 99, 99, 99]⟩] = .ok () := by decide +kernel

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def finiteSystem : System (ZMod 7) :=
  match Circuit.compile (roundtrip.toField (ZMod 7)) with | .ok system => system | .error _ => { chips := [] }
theorem finite_compiled : Circuit.compile (roundtrip.toField (ZMod 7)) = .ok finiteSystem := by
  have succeeds : (compile (roundtrip.toField (ZMod 7))).isOk = true := by decide +kernel
  cases compiled : compile (roundtrip.toField (ZMod 7)) with
  | error error => simp [compiled, Except.isOk, Except.toBool] at succeeds
  | ok system => simp [finiteSystem, compiled]
example : ∃ encode : Nat → ZMod 7,
    Circuit.EncodedEntryDerives finiteSystem "f" (entryValues [3]) ((3 : SourceValue (ZMod 7)).mapAddress encode) :=
  compiler_run_complete finite_compiled
    (show run (roundtrip.toField (ZMod 7)) "f" [3] 10 = .ok (3, [3]) from by decide +kernel)
    (by decide +kernel)

-- Any accepted finite proof must return the same field value as execution.
example (accepted : Circuit.EncodedEntryDerives roundtripSystem "f" (entryValues [7]) 8) : False := by
  have wrong := compiler_entry_sound roundtrip_compiled accepted
    (by decide +kernel)
  have actual : EvalCall (roundtrip.toField Rat) "f" [7] 7 :=
    eval_spec (hints := HintProvider.unavailable) (fuel := 10) (by decide +kernel)
  have equal := actual.deterministic wrong (by decide +kernel)
  change (7 : SourceValue Rat) = Value.mapAddress (fun _ : Rat => 0) (.field 8) at equal
  simp only [Value.mapAddress] at equal
  exact (by decide +kernel : (7 : SourceValue Rat) ≠ 8) equal

-- The theorem checks include the allocation bridge, not only pure ROM semantics.
/-- info: 'Aiur.compiler_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_heap_sound
/-- info: 'Aiur.compiler_heap_complete_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_heap_complete_finite
/-- info: 'Aiur.memo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_acyclic_heap_sound
/-- info: 'Aiur.exists_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.exists_eval_iff

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in rationalTests do
    checkEqual label actual expected
  checkEqual "pointer program compiles" (Circuit.compile (sample.toField Rat)).isOk true
  checkEqual "field specialization" (eval (sample.toField (ZMod 7)) "tuple_memory" [6]) (.ok 6)
  checkEqual "shared circuit cell" (sharedSystem.check goodROM
    ⟨"f", [7], .tuple [.ptr .field 99, .ptr .field 99]⟩ [⟨"f", [7, 99, 99, 99, 99]⟩]) (.ok ())
  IO.println s!"Passed {rationalTests.length + 3} pointer runtime checks."

end AiurPointerTests
