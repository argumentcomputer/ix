import Ix.Compiler.IxIR2.CreditSimulation
import Ix.Compiler.IxIR2.LowerSim

/-!
# Owned results and complete reclamation

Successful execution and counter refinement need no optimizer-specific
ownership history. Complete reclamation has an explicit domain: the logical
result owns the remaining heap. Allocation order is derived by the execution
bridge, and release fuel is constructed internally from that ownership fact.
-/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim (RootOwnership HeapIso HasWorld LiveRVal RValIso)
open Ix.Compiler.IxIR1.Reclamation (AllocationOrderInvariant)
open CallReuse.Sim (MapRel)

theorem live_of_world {store : IxIR1.Store} {world : Owned} {value : RVal}
    (valid : HasWorld store world value) : LiveRVal store value := by
  cases value with
  | lit => trivial
  | erased => trivial
  | loc location =>
      obtain ⟨box, found, _⟩ := valid
      exact ⟨box, found⟩

/-- The allocation-history relation restricts to the established finite
live-heap bijection at every closed logical endpoint. -/
def OutcomeRel.ownedIso {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) {world : Owned}
    (owned : RootOwnership logical.store.heap [⟨world, logical.value⟩]) :
    HeapIso logical.store.heap physical.store.heap :=
  related.heap.heap.toHeapIso owned.storeClosed

theorem OutcomeRel.ownedValue {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) {world : Owned}
    (owned : RootOwnership logical.store.heap [⟨world, logical.value⟩]) :
    RValIso (related.ownedIso owned).locRel logical.value physical.value :=
  related.heap.heap.toHeapIso_value owned.storeClosed related.value
    (live_of_world (owned.roots_world ⟨world, logical.value⟩ (by simp)))

theorem OutcomeRel.ownership {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) {world : Owned}
    (owned : RootOwnership logical.store.heap [⟨world, logical.value⟩]) :
    RootOwnership physical.store.heap [⟨world, physical.value⟩] := by
  have roots : IxIR1.Sim.RootsIso (related.ownedIso owned).locRel
      [⟨world, logical.value⟩] [⟨world, physical.value⟩] :=
    .cons ⟨rfl, related.ownedValue owned⟩ .nil
  exact (related.ownedIso owned).rootOwnership roots owned

theorem OutcomeRel.valueGraph {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) {world : Owned}
    (owned : RootOwnership logical.store.heap [⟨world, logical.value⟩])
    {functions : IxIR1.Sim.FunctionRel} {value : IxIR0.Value}
    (graph : IxIR1.Sim.ValueGraph functions logical.store.heap value logical.value) :
    IxIR1.Sim.ValueGraph functions physical.store.heap value physical.value :=
  graph.transport (related.ownedIso owned) (related.ownedValue owned)

def reclaim (world : Owned) (fuel : Nat) (store : Store) (value : RVal) :
    Except Error (Store × Nat) :=
  match world with
  | .shared => releaseShared fuel store value
  | .unique => dropUnique fuel store value

theorem reclaim_passive {world : Owned} {fuel remaining : Nat} {store output : Store} {value : RVal}
    (run : reclaim world fuel store value = .ok (output, remaining)) :
    passiveCounters output = passiveCounters store := by
  cases world with
  | shared => exact releaseWork_passive run
  | unique => exact dropWork_passive run

theorem reclaim_balance {world : Owned} {fuel remaining : Nat} {store output : Store} {value : RVal}
    (run : reclaim world fuel store value = .ok (output, remaining)) : HeapBalance store output := by
  cases world with
  | shared => exact releaseShared_heapBalance run
  | unique => exact dropUnique_heapBalance run

theorem HeapRel.reclaim {mapping : Array Nat} {left right output : Store}
    (state : HeapRel mapping left right) {world : Owned} {fuel remaining : Nat}
    {leftValue rightValue : RVal} (values : RValIso (MapRel mapping) leftValue rightValue)
    (run : reclaim world fuel left leftValue = .ok (output, remaining)) :
    ∃ target, reclaim world fuel right rightValue = .ok (target, remaining) ∧
      HeapRel mapping output target := by
  cases world with
  | shared => exact state.releaseWork (.cons values .nil) run
  | unique => exact state.dropWork (.cons values .nil) run

/-- The existing ownership progress proof supplies a finite release budget.
The bridge from IxIR₁ destruction is used only for its identical heap rules;
all actual IxIR₂ diagnostics and costs are retained by heap congruence. -/
theorem reclaim_progress {store : Store} {value : RVal} {world : Owned}
    (owned : RootOwnership store.heap [⟨world, value⟩])
    (ordered : AllocationOrderInvariant store.heap) :
    ∃ fuel output, reclaim world fuel store value = .ok (output, 0) ∧ output.live = 0 := by
  let bare : Store := { heap := store.heap }
  have stores : Lower.Sim.StoreRel store.heap bare := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have same : ReuseSim.HeapContentsEq bare store := ⟨rfl⟩
  cases world with
  | shared =>
      obtain ⟨sourceFuel, sourceOut, sourceRun, sourceEmpty⟩ :=
        IxIR1.Reclamation.shared_reclamation (ctx := { decls := fun _ => none }) owned ordered
      have positive : Lower.Sim.PositiveSharedRC store.heap := fun found _ => ordered.rc_pos found
      obtain ⟨fuel, bareOut, bareRun, related, _⟩ :=
        Lower.Sim.dropVal_simulates_releaseSharedWork positive stores sourceRun
      obtain ⟨output, run, contents⟩ := same.releaseShared bareRun
      refine ⟨fuel, output, run, ?_⟩
      have bareEmpty : bareOut.live = 0 := by
        change bareOut.heap.live = 0
        rw [related.heap]
        exact sourceEmpty
      rw [Store.live_eq_countP, ← contents.nodes, ← Store.live_eq_countP]
      exact bareEmpty
  | unique =>
      obtain ⟨sourceFuel, sourceOut, sourceRun, sourceEmpty⟩ :=
        IxIR1.Reclamation.unique_reclamation (ctx := { decls := fun _ => none }) owned ordered
      obtain ⟨fuel, bareOut, bareRun, related⟩ :=
        Lower.Sim.dropUVal_simulates_dropUniqueWork stores sourceRun
      obtain ⟨output, run, contents⟩ := same.dropUnique bareRun
      refine ⟨fuel, output, run, ?_⟩
      have bareEmpty : bareOut.live = 0 := by
        change bareOut.heap.live = 0
        rw [related.heap]
        exact sourceEmpty
      rw [Store.live_eq_countP, ← contents.nodes, ← Store.live_eq_countP]
      exact bareEmpty

structure ReclamationRel (mapping : Array Nat) (logical physical : Store) : Prop where
  heap : HeapRel mapping logical physical
  logicalEmpty : logical.live = 0
  physicalEmpty : physical.live = 0
  logicalFreed : logical.heap.allocs = logical.heap.frees
  physicalFreed : physical.heap.allocs = physical.heap.frees
  counters : CounterLaw logical.snapshot physical.snapshot 0

/-- Both actual heaps reclaim completely, with the same independent release
budget and the same comparative allocation, free, RC, and peak observations. -/
theorem OutcomeRel.reclamation {mapping : Array Nat} {logical physical : Result}
    (related : OutcomeRel mapping logical physical) {world : Owned}
    (owned : RootOwnership logical.store.heap [⟨world, logical.value⟩]) :
    ∃ fuel left right,
      reclaim world fuel logical.store logical.value = .ok (left, 0) ∧
      reclaim world fuel physical.store physical.value = .ok (right, 0) ∧
      ReclamationRel mapping left right := by
  obtain ⟨fuel, left, leftRun, leftEmpty⟩ := reclaim_progress owned related.heap.ordered
  obtain ⟨right, rightRun, heap⟩ := related.heap.reclaim related.value leftRun
  have rightEmpty := heap.heap.right_empty leftEmpty
  have leftBalance := reclaim_balance leftRun
  have rightBalance := reclaim_balance rightRun
  have leftInitial := related.logicalAccounting
  have rightInitial := related.accounted
  unfold HeapBalance at leftBalance rightBalance
  have leftAccount : left.live + left.heap.frees = left.heap.allocs := by omega
  have rightAccount : right.live + right.heap.frees + 0 = right.heap.allocs := by omega
  have noReuses : left.heap.reuses = 0 :=
    (congrArg Counters.reuses (reclaim_passive leftRun)).trans related.logicalReuses
  exact ⟨fuel, left, right, leftRun, rightRun,
    ⟨heap, leftEmpty, rightEmpty, by omega, by omega,
      heap.counterLaw leftAccount noReuses rightAccount⟩⟩

end Ix.Compiler.IxIR2.CreditRefinement
