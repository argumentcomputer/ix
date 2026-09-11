import Ix.Compiler.IxIR2.CreditReclamation
import Ix.Compiler.IxIR2.CallEvalFuel

/-!
# General logical/physical credit refinement

The execution bridge covers both credit policies and every instruction,
including branches, loops, borrowed arguments, PAPs, scalar externs, and
continuation-owned caller credits. Successful logical execution supplies a
physical execution with the same budgets. Independent successful budgets
give the same heap/value observations.

The checked entry point fixes the exact program, schemas, and credit policy.
Validation acceptance is not a proof of semantic root ownership: the owned
endpoint states that additional assumption explicitly. No optimizer-specific
step, progress, target-heap, or resource premise is required.
-/

namespace Ix.Compiler.IxIR2.Eval.Policy

theorem Steps.deterministic {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {count : Nat} {before left right : Machine}
    (one : Steps policy context interpretation count before left)
    (two : Steps policy context interpretation count before right) : left = right := by
  induction one generalizing right with
  | refl => cases two; rfl
  | cons running head tail ih =>
      cases two with
      | cons _ otherHead otherTail =>
          have same := head.deterministic otherHead
          subst same
          exact ih otherTail

theorem Steps.take {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {count prefixLength : Nat} {before after : Machine}
    (steps : Steps policy context interpretation count before after) (bound : prefixLength ≤ count) :
    ∃ middle, Steps policy context interpretation prefixLength before middle ∧
      Steps policy context interpretation (count - prefixLength) middle after := by
  induction steps generalizing prefixLength with
  | refl =>
      have zero : prefixLength = 0 := by omega
      subst prefixLength
      exact ⟨_, .refl _, .refl _⟩
  | @cons count before middle after frame stack running head tail ih =>
      cases prefixLength with
      | zero => exact ⟨before, .refl _, .cons running head tail⟩
      | succ prefixLength =>
          obtain ⟨target, front, back⟩ := ih (prefixLength := prefixLength) (by omega)
          exact ⟨target, .cons running head front, by simpa using back⟩

end Ix.Compiler.IxIR2.Eval.Policy

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RootOwnership)

/-- Any physical prefix of a successful logical main has its corresponding
logical prefix. Reservations include every suspended caller frame. -/
theorem runMain_prefix_resources {policy : CreditPolicy} {context : Context} {program : Program}
    {controlFuel heapFuel count : Nat} {logical : Result} {physicalPrefix : Machine}
    (run : Policy.runMain policy context .logical program controlFuel heapFuel = .ok logical)
    (prefixRun : Policy.Steps policy context .physical count
      (initialMachine program.main #[] heapFuel) physicalPrefix) :
    ∃ mapping logicalPrefix,
      Policy.Steps policy context .logical count
        (initialMachine program.main #[] heapFuel) logicalPrefix ∧
      MachineRel mapping logicalPrefix physicalPrefix ∧ physicalPrefix.AllocationAccounting ∧
      CounterLaw logicalPrefix.store.snapshot physicalPrefix.store.snapshot physicalPrefix.presentCredits := by
  obtain ⟨arity, nonempty⟩ := main_shape run
  rw [Policy.runMain_eq_runMachine arity nonempty] at run
  obtain ⟨total, _, logicalSteps⟩ := Policy.runMachine_steps run
  obtain ⟨_, matched, matchedSteps, related, _, _⟩ := prefix_resources logicalSteps
  rcases matched with ⟨store, fuel, control⟩
  have controls := related.control
  dsimp only at controls
  cases controls with
  | halted values =>
      obtain ⟨suffix, length, _⟩ := prefixRun.cancelPrefixToHalted matchedSteps rfl
      obtain ⟨left, leftPrefix, _⟩ := logicalSteps.take (prefixLength := count) (by omega)
      obtain ⟨mapping, right, rightPrefix, machines, accounted, counters⟩ := prefix_resources leftPrefix
      have same := rightPrefix.deterministic prefixRun
      subst right
      exact ⟨mapping, left, leftPrefix, machines, accounted, counters⟩

/-- Successful runs may choose control and traversal budgets independently.
Their semantic observations do not depend on those choices. -/
theorem runMain_refines_independent {policy : CreditPolicy} {context : Context} {program : Program}
    {logicalControl logicalHeap physicalControl physicalHeap : Nat} {logical physical : Result}
    (leftRun : Policy.runMain policy context .logical program logicalControl logicalHeap = .ok logical)
    (rightRun : Policy.runMain policy context .physical program physicalControl physicalHeap = .ok physical) :
    ∃ mapping, OutcomeRel mapping logical physical := by
  obtain ⟨arity, nonempty⟩ := main_shape leftRun
  obtain ⟨mapping, target, targetRun, related⟩ := runMain_refines leftRun
  obtain ⟨stores, values⟩ := Policy.runMain_success_unique arity nonempty targetRun rightRun
  refine ⟨mapping, ?_⟩
  exact ⟨stores ▸ related.heap, values ▸ related.value,
    stores ▸ related.counters, stores ▸ related.accounted⟩

/-- The exact checked program and policy execute with the matching physical
result. Acceptance is retained at the API boundary; the operational theorem
is stronger and does not require it. -/
theorem checked_runMain_refines {policy : CreditPolicy} {limits : Validate.Limits}
    {validation : Validate.Context} {program : Program}
    (_checked : Validate.CheckedWithPolicy policy limits validation program)
    {oracle : Ixon.Address → List RVal → Option RVal} {controlFuel heapFuel : Nat} {logical : Result}
    (run : Policy.runMain policy (Context.ofProgram program validation.schemas oracle)
      .logical program controlFuel heapFuel = .ok logical) :
    ∃ mapping physical,
      Policy.runMain policy (Context.ofProgram program validation.schemas oracle)
        .physical program controlFuel heapFuel = .ok physical ∧
      ResultRel mapping logical physical :=
  runMain_refines run

/-- Owned checked programs preserve root ownership and reclaim both actual
heaps completely. The reclamation budget is constructed from the logical
ownership premise and the allocation order derived by execution. -/
theorem checked_runMain_owned {policy : CreditPolicy} {limits : Validate.Limits}
    {validation : Validate.Context} {program : Program}
    (checked : Validate.CheckedWithPolicy policy limits validation program)
    {oracle : Ixon.Address → List RVal → Option RVal} {controlFuel heapFuel : Nat} {logical : Result}
    (run : Policy.runMain policy (Context.ofProgram program validation.schemas oracle)
      .logical program controlFuel heapFuel = .ok logical)
    (owned : RootOwnership logical.store.heap [⟨program.main.signature.result, logical.value⟩]) :
    ∃ mapping physical,
      Policy.runMain policy (Context.ofProgram program validation.schemas oracle)
        .physical program controlFuel heapFuel = .ok physical ∧
      ResultRel mapping logical physical ∧
      RootOwnership physical.store.heap [⟨program.main.signature.result, physical.value⟩] ∧
      ∃ fuel left right,
        reclaim program.main.signature.result fuel logical.store logical.value = .ok (left, 0) ∧
        reclaim program.main.signature.result fuel physical.store physical.value = .ok (right, 0) ∧
        ReclamationRel mapping left right := by
  obtain ⟨mapping, physical, physicalRun, related⟩ := checked_runMain_refines checked run
  exact ⟨mapping, physical, physicalRun, related, related.toOutcomeRel.ownership owned,
    related.toOutcomeRel.reclamation owned⟩

end Ix.Compiler.IxIR2.CreditRefinement
