import Aiur.Generic.Runtime
import Aiur.Generic.TraceFacts

namespace Aiur.Generic

structure ExecutionTrace (F : Type) where
  result : Except String (SourceValue F × Heap F)
  events : List (TraceEvent F)
  deriving Repr

/-- Active calls, innermost first. On failure their unmatched entry events give
a call trace; a normally completed execution leaves this list empty. -/
def ExecutionTrace.activeCalls (execution : ExecutionTrace F) : List String :=
  execution.events.foldl (fun stack event => match event with
    | .enter name _ => name :: stack
    | .leave _ _ => stack.drop 1
    | .message _ _ => stack) []

def Source.runTraced [Field F] [DecidableEq F] (s : Source F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : s.HintProvider := SourceSemantics.unavailable) : ExecutionTrace F :=
  match s.checkEntry name with
  | .error error => ⟨.error error, []⟩
  | .ok () => match s.world.prepare name args with
    | .error error => ⟨.error (reprStr error), [.enter name args]⟩
    | .ok (types, locals, body) =>
        let (result, events) := Traced.finishFunction
          (Traced.evalWithTrace s.world hints types locals fuel body) [] [.enter name args]
        let events := match result with
          | .ok (value, _) => TraceEvent.leave name value :: events
          | .error _ => events
        ⟨result.mapError reprStr, events.reverse⟩

/-- Exact erasure, for failures as well as successes. Logging does not change
fuel consumption, hint requests, return values, or allocations. -/
theorem Source.runTraced_result [Field F] [DecidableEq F] (s : Source F) (name args fuel)
    (hints : s.HintProvider) :
    (s.runTraced name args fuel hints).result = s.run name args fuel hints := by
  cases entry : s.checkEntry name with
  | error error => simp [Source.runTraced, Source.run, entry, bind, Except.bind]
  | ok unit =>
      cases unit
      cases prepared : s.world.prepare name args with
      | error error => simp [Source.runTraced, Source.run, entry, prepared, Except.mapError, bind, Except.bind]
      | ok triple =>
          rcases triple with ⟨types, locals, body⟩
          have same := Traced.agrees_finish (Traced.eval_agrees s.world hints types locals fuel body)
            [] [.enter name args]
          cases traced : Traced.finishFunction
              (Traced.evalWithTrace s.world hints types locals fuel body) [] [.enter name args] with
          | mk outcome events =>
              rw [traced] at same
              simp only [Prod.fst] at same
              simp [Source.runTraced, Source.run, entry, prepared, traced, Except.mapError,
                bind, Except.bind, SourceSemantics.evalFunctionWith, ← same]

theorem Source.runTraced_spec [Field F] [DecidableEq F] {s : Source F}
    {hints : s.HintProvider} {name args fuel result heap}
    (run : (s.runTraced name args fuel hints).result = .ok (result, heap)) :
    s.checkEntry name = .ok () ∧ SourceSemantics.EvalFn s.world name args [] result heap := by
  rw [Source.runTraced_result] at run
  exact Source.run_spec run

end Aiur.Generic
