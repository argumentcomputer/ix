import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurHintTests

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def source : Program Nat := aiur% "
enum Inner { Empty, Item(Field) }
enum Outer { Raw(Field), Nested(Inner) }
fn field(h: Field) -> Field { hint::<Field>(h) }
fn tuple(h: Field) -> (Field, Field) { hint::<(Field, Field)>(\"pair\", h) }
fn nested(h: Field) -> Outer { hint::<Outer>((h, 1)) }
fn unit() -> () { hint::<()>(()) }
fn singleton() -> (Field,) { hint::<(Field,)>(\"singleton\", ()) }
fn square_preimage(h: Field) -> () {
  let p = hint::<Field>(h);
  let 0 = p * p - h;
  ()
}
fn twice() -> (Field, Field) {
  (hint::<Field>(()), hint::<Field>(()))
}
fn lazy(x: Field) -> Field { match x { 0 => 9, _ => hint::<Field>(x) } }
fn key(x: Field) -> Field { let p = &x; *p + 1 }
fn dynamic(x: Field) -> Field { hint::<Field>(key(x)) }
fn store_hint(x: Field) -> Outer { let p = &hint::<Outer>(x); *p }
fn failed_key() -> Field { hint::<Field>(1 / 0) }
fn discarded() -> Field { let _ = hint::<Outer>(()); 7 }
"

def program := source.toField Rat

def answer (value : Constant Rat) : HintProvider Rat program.enums :=
  HintProvider.checked program.enums fun _ _ => .ok value

def keyed : HintProvider Rat program.enums := HintProvider.checked program.enums fun channel key =>
  match channel, key with
  | "", .field x => .ok (.field (x + 1))
  | "pair", .field x => .ok (.tuple [.field x, .field (x + 1)])
  | "", .tuple [.field x, .field 1] =>
      .ok (.construct "Outer" "Nested" [.construct "Inner" "Item" [.field x]])
  | "", .tuple [] => .ok (.tuple [])
  | "singleton", .tuple [] => .ok (.tuple [8])
  | _, _ => .error .unavailable

private def outer (value : Rat) : Constant Rat :=
  .construct "Outer" "Nested" [.construct "Inner" "Item" [.field value]]

private def runtimeTests : List
    (String × Except EvalError (SourceValue Rat) × Except EvalError (SourceValue Rat)) := [
  ("dynamic field key", eval program "field" [8] (hints := keyed), .ok 9),
  ("same key, different channel", eval program "tuple" [8] (hints := keyed), .ok (.tuple [8, 9])),
  ("nested enum result and tuple key", eval program "nested" [8] (hints := keyed), .ok (outer 8).toValue),
  ("unit key and result", eval program "unit" [] (hints := keyed), .ok (.tuple [])),
  ("singleton retains its shape", eval program "singleton" [] (hints := keyed), .ok (.tuple [8])),
  ("valid preimage", eval program "square_preimage" [49] (hints := answer 7), .ok (.tuple [])),
  ("another valid preimage", eval program "square_preimage" [49] (hints := answer (.field (-7))), .ok (.tuple [])),
  ("incorrect preimage", eval program "square_preimage" [49] (hints := answer 8), .error .patternMismatch),
  ("default provider is unavailable", eval program "field" [8], .error (.hint .unavailable)),
  ("provider can decline a key", eval program "field" [.field 8]
    (hints := fun _ _ _ => .error (.message "no witness")), .error (.hint (.message "no witness"))),
  ("wrong result type rejected", eval program "field" [8] (hints := answer (.tuple [1])),
    .error (.hint (.invalidValue .field (.tuple [.field])))),
  ("unknown enum constructor rejected", eval program "nested" [8]
    (hints := answer (.construct "Outer" "Missing" [])),
    .error (.hint (.invalidValue (.enum "Outer") (.enum "Outer")))),
  ("malformed nested payload rejected", eval program "nested" [8]
    (hints := answer (.construct "Outer" "Nested" [.construct "Inner" "Item" [.tuple [1, 2]]])),
    .error (.hint (.invalidValue (.enum "Outer") (.enum "Outer")))),
  ("wrong constructor arity rejected", eval program "nested" [8]
    (hints := answer (.construct "Outer" "Raw" [])),
    .error (.hint (.invalidValue (.enum "Outer") (.enum "Outer")))),
  ("fixed provider repeats an answer", eval program "twice" [] (hints := answer 3), .ok (.tuple [3, 3])),
  ("inactive hint needs no provider", eval program "lazy" [0], .ok 9),
  ("active hint needs a provider", eval program "lazy" [1], .error (.hint .unavailable)),
  ("key computation is ordinary execution", eval program "dynamic" [4] (hints := keyed), .ok 6),
  ("hinted enum can be stored and loaded", eval program "store_hint" [8] (hints := answer (outer 8)),
    .ok (outer 8).toValue),
  ("key errors precede provider invocation", eval program "failed_key" [], .error .divisionByZero),
  ("fuel exhaustion is still an error", eval program "field" [8] 0 keyed, .error .outOfFuel)
]

-- Invalid expected types are rejected statically, including unused pointer-bearing variants.
run_cmd do
  let env ← Lean.getEnv
  for text in [
    "fn f(x: Field) -> Field { hint::<Field>(&x) }",
    "fn f() -> &Field { hint::<&Field>(()) }",
    "fn f() -> (Field, &Field) { hint::<(Field, &Field)>(()) }",
    "enum E { Empty, Full(&Field) } fn f() -> E { hint::<E>(()) }",
    "enum E { Empty, Full(&Field) } enum O { Wrap(E) } fn f() -> O { hint::<O>(()) }",
    "fn f() -> Missing { hint::<Missing>(()) }",
    "fn f() -> Field { hint::<Field>(1 + (2, 3)) }",
    "fn f() -> Field { hint::<Field>(missing) }",
    "fn f() -> Field { hint::<Field>() }",
    "fn f() -> Field { other::<Field>(()) }"
  ] do
    match Frontend.ofString env text with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted invalid hint: {text}"

/-- Inspect the actual equations emitted for an internal hint, including all auxiliary columns. -/
private def hintConstraintsHold (enable : Rat) (words auxiliary : List Rat) : Bool :=
  match Compiler.lowerExpr program "test" [] (.const enable)
      (.hint (.enum "Outer") (.tuple [])) {} with
  | .error _ => false
  | .ok (_, state) =>
      let assignment := words ++ auxiliary
      decide (state.nextVar = assignment.length) && state.sends.isEmpty && state.memory.isEmpty &&
        state.constraints.toList.all (fun polynomial =>
          decide (polynomial.denote (fun id => assignment.getD id 0) = 0))

private def constraintTests : List (String × Bool) := [
  ("raw payload is not an inner tag", hintConstraintsHold 1 [0, 7, 0] [1, 0, 0, -1, 0, 1/7, 0, 1/6]),
  ("nested empty", hintConstraintsHold 1 [1, 0, 0] [0, 1, 1, 0, 1, 0, 0, -1]),
  ("nested payload", hintConstraintsHold 1 [1, 1, 8] [0, 1, 1, 0, 0, 1, 1, 0]),
  ("invalid outer tag rejected", !hintConstraintsHold 1 [2, 7, 0] [0, 1/2, 0, 1, 0, 1/7, 0, 1/6]),
  ("invalid inner tag rejected", !hintConstraintsHold 1 [1, 7, 0] [0, 1, 1, 0, 0, 1/7, 0, 1/6]),
  ("outer padding constrained", !hintConstraintsHold 1 [0, 7, 2] [1, 0, 0, -1, 0, 1/7, 0, 1/6]),
  ("inner padding constrained", !hintConstraintsHold 1 [1, 0, 5] [0, 1, 1, 0, 1, 0, 0, -1]),
  ("inactive hint permits arbitrary data columns", hintConstraintsHold 0 [2, 7, 5]
    [0, 1/2, 0, 1, 0, 1/7, 0, 1/6])
]

-- A stateless provider does not make the logical relation functional.
example : EvalCall program "field" [8] (.field 3) :=
  eval_spec (hints := answer 3) (by decide +kernel : eval program "field" [8] 16 (answer 3) = .ok 3)

example : EvalCall program "field" [8] (.field 4) :=
  eval_spec (hints := answer 4) (by decide +kernel : eval program "field" [8] 16 (answer 4) = .ok 4)

-- Logical choices for identical requests can differ within a single evaluation.
example : EvalExpr program []
    (.tuple [.hint .field (.tuple []) "choose", .hint .field (.tuple []) "choose"]) [] (.tuple [1, 2]) [] := by
  have choose (x : Rat) : EvalExpr program [] (.hint .field (.tuple []) "choose") [] (.field x) [] := by
    simpa [Constant.toValue, Value.mapAddress] using
      (EvalExpr.hint (program := program) (locals := []) (before := []) (after := [])
        (type := .field) (channel := "choose") (.tuple .nil) (value := (.field x : Constant Rat))
        (by simp [Value.WellTyped, Value.hasType, Value.type]))
  exact .tuple (.cons (choose 1) (.cons (choose 2) .nil))

def system : System Rat := (compile program).toOption.getD { chips := [] }
theorem compiled : compile program = .ok system := by
  have succeeds : (compile program).isOk = true := by decide +kernel
  cases lowered : compile program with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [system, lowered, Except.toOption]

theorem nested_derives : EncodedEntryDerives system "nested" (entryValues [8]) (outer 8).toValue := by
  have executed : Aiur.run program "nested" [8] 16 keyed = .ok ((outer 8).toValue, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa only [Constant.toValue_mapAddress] using complete

example : EncodedMemoEntryDerives system "nested" (entryValues [8]) (outer 8).toValue := nested_derives.memo

example (accepted : EncodedEntryDerives system "nested" (entryValues [8]) (outer 8).toValue) :
    EvalCall program "nested" [8] (outer 8).toValue := by
  simpa only [Constant.toValue_mapAddress] using
    compiler_entry_sound compiled accepted (Constant.toValue_pointerFree (outer 8))

example {rom : WireROM Rat} (valid : rom.Valid)
    (graph : MemoDerivation system rom
      ⟨"nested", [.field 8], ⟨.enum "Outer", [1, 1, 8]⟩⟩) (acyclic : graph.Acyclic) :
    EvalCall program "nested" [8] (outer 8).toValue := by
  obtain ⟨value, heap, evaluated, related⟩ := memo_acyclic_heap_sound compiled valid
    (args := [8]) (by decide +kernel) graph acyclic
    (by simp [DecodesValues, entryValues]; decide +kernel) (show
      (⟨.enum "Outer", [1, 1, 8]⟩ : WireValue Rat).decode program.enums = some (outer 8).toValue by
        decide +kernel)
  have same := related.pointerFree_eq (Constant.toValue_pointerFree (outer 8))
  simp only [Constant.toValue_mapAddress] at same
  subst value
  exact ⟨by decide +kernel, heap, evaluated⟩

example : EncodedEntryDerives system "lazy" (entryValues [0]) (.field 9) := by
  have executed : Aiur.run program "lazy" [0] 16 = .ok (.field 9, []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simpa [Value.mapAddress] using complete

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : eval (source.toField (ZMod 7)) "square_preimage" [2] 16
    (HintProvider.checked source.enums fun _ _ => .ok 3) = .ok (.tuple []) := by decide +kernel

example : ∃ encode : Nat → ZMod 7,
    EncodedMemoEntryDerives
      ((compile (source.toField (ZMod 7))).toOption.getD { chips := [] })
      "square_preimage" (entryValues [2]) ((.tuple [] : SourceValue (ZMod 7)).mapAddress encode) := by
  have lowered : compile (source.toField (ZMod 7)) =
      .ok ((compile (source.toField (ZMod 7))).toOption.getD { chips := [] }) := by
    have ok : (compile (source.toField (ZMod 7))).isOk = true := by decide +kernel
    cases h : compile (source.toField (ZMod 7)) <;>
      simp_all [Except.isOk, Except.toBool, Except.toOption]
  exact memo_run_complete lowered
    (hints := HintProvider.checked source.enums fun _ _ => .ok 3) (fuel := 16) (heap := [])
    (by decide +kernel) (by simp)

/-- info: 'Aiur.eval_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.eval_spec

def run : IO Unit := do
  for (label, actual, expected) in runtimeTests do
    unless actual = expected do throw (IO.userError s!"hint check {label}: {repr actual}, expected {repr expected}")
  for (label, passed) in constraintTests do
    unless passed do throw (IO.userError s!"hint constraint check failed: {label}")
  unless (compile program).isOk do throw (IO.userError "hint compilation failed")
  unless Aiur.run program "dynamic" [4] 16 keyed = .ok (.field 6, [.field 4]) do
    throw (IO.userError "key computation lost its allocation")
  IO.println s!"Passed {runtimeTests.length + constraintTests.length + 2} hint checks."

end AiurHintTests
