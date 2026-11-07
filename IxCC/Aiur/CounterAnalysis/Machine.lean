import IxCC.Aiur.CounterAnalysis.Control

namespace IxCC.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open OracleEval (Values)

def ProgressSound (self : Nat) (candidate : UnitCounter.Certificate) (inputs : Array G) :
    OracleEval.Progress → Prop
  | .done result => CounterRelation self candidate inputs.toList result.outputs result.demands
  | .more task continuations state => continuations = [] ∧ ∃ abstractState,
      TaskAccepted self candidate abstractState task ∧ Invariant self candidate inputs abstractState state

theorem finish_return_spec {selector : Nat} {outputs : Values} {state : OracleEval.State} {result : OracleEval.Result}
    (success : OracleEval.finish (.returned selector outputs) state = .ok result) :
    result.outputs = outputs ∧ result.demands = state.demandsRev.reverse := by
  unfold OracleEval.finish at success
  split at success
  · cases success; exact ⟨rfl, rfl⟩
  · cases success

theorem step_sound {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractState : UnitCounter.State} {state : OracleEval.State} {task : OracleEval.Task}
    {toplevel : Toplevel} {maxValues : Nat} {progress : OracleEval.Progress}
    (bound : candidate.mode = .input → candidate.column < inputs.size)
    (accepted : TaskAccepted self candidate abstractState task)
    (sound : Invariant self candidate inputs abstractState state)
    (success : OracleEval.step toplevel maxValues task [] state = .ok progress) :
    ProgressSound self candidate inputs progress := by
  cases task with
  | ops operations control =>
    obtain ⟨finalState, folded, depth, checked⟩ := accepted
    cases operations with
    | nil =>
      have equal : abstractState = finalState := Option.some.inj folded
      subst finalState
      cases success
      exact ⟨rfl, abstractState, ⟨depth, checked⟩, sound⟩
    | cons op rest =>
      rw [List.foldlM_cons] at folded
      obtain ⟨nextAbstract, abstractStep, folded⟩ := Option.bind_eq_some_iff.mp folded
      simp only [OracleEval.step] at success
      obtain ⟨nextState, concreteStep, success⟩ := bind_success success
      cases success
      exact ⟨rfl, nextAbstract, ⟨finalState, folded, depth, checked⟩,
        evalOp_invariant bound sound abstractStep concreteStep⟩
  | control control =>
    obtain ⟨depth, checked⟩ := accepted
    cases control with
    | «return» selector indices =>
      simp only [OracleEval.step] at success
      obtain ⟨outputs, reads, success⟩ := bind_success success
      obtain ⟨result, finished, success⟩ := bind_success success
      cases success
      obtain ⟨resultOutputs, resultDemands⟩ := finish_return_spec finished
      change CounterRelation self candidate inputs.toList result.outputs result.demands
      rw [resultOutputs, resultDemands]
      exact return_relation sound checked (readMany_spec reads)
    | «match» index cases fallback =>
      simp only [OracleEval.step] at success
      obtain ⟨scrutinee, _, success⟩ := bind_success success
      obtain ⟨block, selected, success⟩ := bind_success success
      cases success
      exact ⟨rfl, abstractState, selectBranch_checked checked selected, sound⟩
    | «yield» | matchContinue => cases checked

/-- A successful local machine execution satisfies the checked relation on
every constrained self-call demand. No assumption is made about its replies. -/
theorem run_sound {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractState : UnitCounter.State} {state : OracleEval.State} {task : OracleEval.Task}
    {toplevel : Toplevel} {maxValues fuel : Nat} {result : OracleEval.Result}
    (bound : candidate.mode = .input → candidate.column < inputs.size)
    (accepted : TaskAccepted self candidate abstractState task)
    (sound : Invariant self candidate inputs abstractState state)
    (success : OracleEval.run toplevel maxValues fuel task [] state = .ok result) :
    CounterRelation self candidate inputs.toList result.outputs result.demands := by
  induction fuel generalizing abstractState state task with
  | zero => cases success
  | succ fuel ih =>
    rw [OracleEval.run] at success
    obtain ⟨progress, step, success⟩ := bind_success success
    have next := step_sound bound accepted sound step
    cases progress with
    | done actual => cases success; exact next
    | more task continuations state =>
      obtain ⟨rfl, abstractState, accepted, sound⟩ := next
      exact ih accepted sound success

end IxCC.Aiur.CounterAnalysis
