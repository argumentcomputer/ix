import Ix.Compiler.IxIR2.CreditResources

/-! Public successful-main refinement for both credit policies. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso)
open CallReuse.Sim (MapRel)

/-- Budget-independent observations of a completed execution. -/
structure OutcomeRel (mapping : Array Nat) (logical physical : Result) : Prop where
  heap : HeapRel mapping logical.store physical.store
  value : RValIso (MapRel mapping) logical.value physical.value
  counters : CounterLaw logical.store.snapshot physical.store.snapshot 0
  accounted : physical.store.live + physical.store.heap.frees = physical.store.heap.allocs

structure ResultRel (mapping : Array Nat) (logical physical : Result) : Prop
    extends OutcomeRel mapping logical physical where
  control : logical.controlRemaining = physical.controlRemaining
  traversal : logical.heapRemaining = physical.heapRemaining

theorem OutcomeRel.logicalReuses {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) : logical.store.heap.reuses = 0 := by
  have events := related.heap.events
  have allocs := related.counters.allocs
  change logical.store.heap.allocs + logical.store.heap.reuses =
    physical.store.heap.allocs + physical.store.heap.reuses at events
  change logical.store.heap.allocs = physical.store.heap.allocs + physical.store.heap.reuses at allocs
  omega

theorem OutcomeRel.logicalAccounting {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) :
    logical.store.live + logical.store.heap.frees = logical.store.heap.allocs := by
  have allocs := related.counters.allocs
  have frees := related.counters.frees
  have live := related.counters.live
  have physical := related.accounted
  dsimp only [Store.snapshot, Store.counters] at allocs frees live
  omega

theorem main_shape {policy : CreditPolicy} {context : Context} {program : Program}
    {interpretation : Interpretation} {controlFuel heapFuel : Nat} {result : Result}
    (run : Policy.runMain policy context interpretation program controlFuel heapFuel = .ok result) :
    program.main.signature.params.size = 0 ∧ program.main.blocks.isEmpty = false := by
  by_cases arity : program.main.signature.params.size = 0
  · refine ⟨arity, ?_⟩
    cases empty : program.main.blocks.isEmpty with
    | false => rfl
    | true => simp [Policy.runMain, Policy.runFunction, enterFunction, arity, empty,
        bind, Except.bind] at run
  · simp [Policy.runMain, Policy.runFunction, enterFunction, Ne.symm arity,
      bind, Except.bind] at run

/-- A successful logical main executes physically with the same control and
traversal budgets. The theorem covers the whole instruction language and
derives all heap, continuation, reservation, and cost facts internally. -/
theorem runMain_refines {policy : CreditPolicy} {context : Context} {program : Program}
    {controlFuel heapFuel : Nat} {logical : Result}
    (run : Policy.runMain policy context .logical program controlFuel heapFuel = .ok logical) :
    ∃ mapping physical,
      Policy.runMain policy context .physical program controlFuel heapFuel = .ok physical ∧
      ResultRel mapping logical physical := by
  obtain ⟨arity, nonempty⟩ := main_shape run
  rw [Policy.runMain_eq_runMachine arity nonempty] at run
  obtain ⟨count, budget, steps⟩ := Policy.runMachine_steps run
  obtain ⟨mapping, target, targetSteps, machines, accounted, counters⟩ := prefix_resources steps
  rcases target with ⟨store, fuel, control⟩
  have controls := machines.control
  dsimp only at controls
  cases controls with
  | halted values =>
      refine ⟨mapping, ⟨store, _, logical.controlRemaining, fuel⟩, ?_,
        ⟨⟨machines.heap, values, counters, accounted⟩, rfl, machines.fuel⟩⟩
      rw [Policy.runMain_eq_runMachine arity nonempty, budget, targetSteps.runMachine]
      simp only [Policy.runMachine]

/-- Legacy v0 clients obtain the same full-credit guarantee for the original
runner. This strictly extends the credit-free interpretation bridge. -/
theorem runMain_v0_refines {context : Context} {program : Program}
    {controlFuel heapFuel : Nat} {logical : Result}
    (run : Eval.runMain context .logical program controlFuel heapFuel = .ok logical) :
    ∃ mapping physical,
      Eval.runMain context .physical program controlFuel heapFuel = .ok physical ∧
      ResultRel mapping logical physical := by
  have policyRun : Policy.runMain .callLocalV0 context .logical program controlFuel heapFuel = .ok logical :=
    (Policy.runMain_v0 ..).trans run
  simpa only [Policy.runMain_v0] using runMain_refines policyRun

end Ix.Compiler.IxIR2.CreditRefinement
