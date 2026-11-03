import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurEnumProofTests

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def source : Program Nat := aiur% "
enum List { Nil, Cons(Field, &List) }
enum Outcome { Empty, Pair((Field, Field)) }
fn sum(xs: List) -> Field {
  match xs { List::Nil => 0, List::Cons(x, tail) => x + sum(*tail) }
}
fn main(x: Field) -> Field { sum(List::Cons(x, &List::Nil)) }
fn wrap(x: Field) -> Outcome { Outcome::Pair((x, x + 1)) }
"

def system : System Rat := (compile (source.toField Rat)).toOption.getD { chips := [] }
theorem compiled : compile (source.toField Rat) = .ok system := by
  have succeeds : (compile (source.toField Rat)).isOk = true := by decide +kernel
  cases lowered : compile (source.toField Rat) with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [system, lowered, Except.toOption]

-- A recursive enum crosses a call boundary and ROM; address 99 represents source location 0.
example : EncodedEntryDerives system "main" (entryValues [7]) 7 := by
  have executed : run (source.toField Rat) "main" [7] 32 =
      .ok (.field 7, [.construct "List" "Nil" []]) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (99 : Rat)) (by intro i j hi hj _; simp at hi hj; omega)
  simp only [Value.mapAddress, List.map_cons, List.map_nil] at complete
  exact complete

-- A nominal result with a tuple payload is covered by the same theorem.
example : EncodedEntryDerives system "wrap" (entryValues [7])
    (.construct "Outcome" "Pair" [.tuple [7, 8]]) := by
  have executed : run (source.toField Rat) "wrap" [7] 16 =
      .ok (.construct "Outcome" "Pair" [.tuple [.field 7, .field 8]], []) := by decide +kernel
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  have complete := compiler_heap_complete compiled entry (.intro prepared (evalExpr_spec body))
    (fun _ => (0 : Rat)) (by simp)
  simp only [Value.mapAddress, List.map_cons, List.map_nil] at complete
  exact complete

-- Well-formedness of an alternative result does not make it a true root claim.
example (accepted : EncodedEntryDerives system "wrap" (entryValues [7])
    (.construct "Outcome" "Empty" [])) : False := by
  have wrong := compiler_entry_sound compiled accepted (by decide +kernel)
  have actual : EvalCall (source.toField Rat) "wrap" [7]
      (.construct "Outcome" "Pair" [.tuple [7, 8]]) := eval_spec (hints := HintProvider.unavailable) (fuel := 16) (by decide +kernel)
  have same := actual.deterministic wrong (by decide +kernel)
  simp [Value.mapAddress] at same

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def finiteSystem : System (ZMod 7) := (compile (source.toField (ZMod 7))).toOption.getD { chips := [] }
theorem finite_compiled : compile (source.toField (ZMod 7)) = .ok finiteSystem := by
  have succeeds : (compile (source.toField (ZMod 7))).isOk = true := by decide +kernel
  cases lowered : compile (source.toField (ZMod 7)) with
  | error error => simp [lowered, Except.isOk, Except.toBool] at succeeds
  | ok chips => simp [finiteSystem, lowered, Except.toOption]

example : ∃ encode : Nat → ZMod 7, EncodedEntryDerives finiteSystem "main" (entryValues [3])
    ((3 : SourceValue (ZMod 7)).mapAddress encode) :=
  compiler_run_complete finite_compiled
    (show run (source.toField (ZMod 7)) "main" [3] 32 =
      .ok (3, [.construct "List" "Nil" []]) from by decide +kernel) (by decide +kernel)

example : ∃ encode : Nat → ZMod 7, EncodedMemoEntryDerives finiteSystem "main" (entryValues [3])
    ((3 : SourceValue (ZMod 7)).mapAddress encode) :=
  memo_run_complete finite_compiled
    (show run (source.toField (ZMod 7)) "main" [3] 32 =
      .ok (3, [.construct "List" "Nil" []]) from by decide +kernel) (by decide +kernel)

-- These guard the full enum proofs against admitted steps or additional axioms.
/-- info: 'Aiur.compiler_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_correct
/-- info: 'Aiur.memo_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_complete
/-- info: 'Aiur.memo_acyclic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_acyclic_sound

end AiurEnumProofTests
