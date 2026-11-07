import IxCC.Aiur.CounterAnalysis.Machine
import IxCC.Aiur.OracleEval.Local

namespace IxCC.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open OracleEval (Values)

def initialState (inputSize : Nat) : UnitCounter.State :=
  { values := (Array.range inputSize).map (some ∘ UnitCounter.affVar) }

theorem prepare_spec {toplevel : Toplevel} {maxValues maxReplies maxReplyFields maxObservationFields self : Nat}
    {function : Function} {inputs : Values} {replies : List Values} {task : OracleEval.Task} {state : OracleEval.State}
    (lookup : toplevel.functions[self]? = some function)
    (success : OracleEval.prepare toplevel maxValues maxReplies maxReplyFields maxObservationFields self inputs replies =
      .ok (task, state)) :
    inputs.length = function.layout.inputSize ∧ task = OracleEval.start function.body ∧
      state = { values := inputs.toArray, replies, remainingFields := maxObservationFields } := by
  rw [OracleEval.prepare] at success
  split at success
  · cases success
  · split at success
    · cases success
    · rw [lookup] at success
      simp only [bind, Except.bind] at success
      split at success
      · cases success
      next same =>
        cases success
        exact ⟨by simpa using same, rfl, rfl⟩

theorem check_runFunction {toplevel : Toplevel} {self depth : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {inputs : Values} {replies : List Values}
    {limits : OracleEval.Limits} {result : OracleEval.Result}
    (lookup : toplevel.functions[self]? = some function)
    (checked : UnitCounter.check depth self candidate (initialState function.layout.inputSize) function.body = true)
    (bound : candidate.mode = .input → candidate.column < function.layout.inputSize)
    (success : OracleEval.runFunction toplevel limits self inputs replies = .ok result) :
    CounterRelation self candidate inputs result.outputs result.demands := by
  unfold OracleEval.runFunction at success
  obtain ⟨⟨task, state⟩, prepared, success⟩ := bind_success success
  obtain ⟨arity, rfl, rfl⟩ := prepare_spec lookup prepared
  have sound : Invariant self candidate inputs.toArray (initialState function.layout.inputSize)
      { values := inputs.toArray, replies, remainingFields := limits.maxObservationFields } := by
    simpa only [arity, initialState] using Invariant.initial self candidate inputs replies limits.maxObservationFields
  have relation := run_sound (by simpa only [List.size_toArray, arity] using bound)
    (check_accepted checked) sound success
  simpa only [List.toList_toArray] using relation

/-- Universal soundness of the pinned abstract checker against actual local
bytecode replay, for any accepted candidate and any successful body witness. -/
theorem check_body {toplevel : Toplevel} {self depth : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {inputs outputs : Values} {demands : List Message}
    {advice : List OracleEval.AdviceObservation}
    (lookup : toplevel.functions[self]? = some function)
    (checked : UnitCounter.check depth self candidate (initialState function.layout.inputSize) function.body = true)
    (bound : candidate.mode = .input → candidate.column < function.layout.inputSize)
    (body : OracleEval.Body toplevel self inputs outputs demands advice) :
    CounterRelation self candidate inputs outputs demands := by
  obtain ⟨limits, replies, result, success, rfl, rfl, _⟩ := body
  exact check_runFunction lookup checked bound success

end IxCC.Aiur.CounterAnalysis
