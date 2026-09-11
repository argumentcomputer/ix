import Ix.Compiler.IxIR2.Borrow.OpenCheck
import Ix.Compiler.IxIR2.CreditReclamation

namespace Ix.Compiler.IxIR2.Borrow.Open

open Eval
open Ix.Compiler.IxIR1.Sim (RootOwnership)
open Ix.Compiler.IxIR1.Reclamation (AllocationOrderInvariant)

theorem Entry.readWork_eq {beforeContext afterContext schema} (entry : Entry beforeContext afterContext schema) :
    entry.beforeBody.readWork = entry.afterBody.readWork := by
  simp only [Body.readWork, entry.sameKind]

/-- Reusable function and continuation preservation. The only operational
premise is the ordinary final heap release; `Entry.total` constructs that
release internally for owned, allocation-ordered runtime inputs. -/
theorem Entry.steps {beforeContext afterContext schema} (entry : Entry beforeContext afterContext schema)
    (mode : Interpretation) (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store output : Store} {location rc fuel remaining : Nat}
    (view : major.At schema store location rc) (positive : 0 < rc)
    (released : releaseShared fuel store (.loc location) = .ok (output, remaining)) (exit : Exit) :
    Steps beforeContext mode (entry.beforeBody.ownedCost major.fieldCost)
      (start entry.before location store (fuel + 2 * entry.beforeBody.readWork) exit)
      (finish (bump output (2 * entry.beforeBody.readWork)) remaining (major.result schema) exit) ∧
    Steps afterContext mode (entry.afterBody.readCost major.fieldCost + 3)
      (start (ownedWrapper entry.summary.borrowed entry.before) location store
        (fuel + entry.beforeBody.readWork) exit)
      (finish output remaining (major.result schema) exit) := by
  refine ⟨entry.beforeBody.ownedSteps mode distinct major view positive released exit, ?_⟩
  rw [entry.readWork_eq]
  exact wrapper entry.afterAt (by rw [entry.afterBody.signature]; rfl) entry.afterBody.nonempty
    mode major released exit (fun caller rest => entry.afterBody.borrowedSteps mode distinct major view fuel (.resume caller rest))

/-- Every borrowed prefix preserves the exact caller store. In particular,
the caller retains all ownership, refcounts, and constructor views required
by a later take/reset, after the borrowed activation has returned. -/
theorem Entry.lenderLifetime {beforeContext afterContext schema} (entry : Entry beforeContext afterContext schema)
    (mode : Interpretation) (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (view : major.At schema store location rc)
    (fuel : Nat) (exit : Exit) {count : Nat} {middle : Machine}
    (path : Steps afterContext mode count
      (start entry.after location store (fuel + entry.afterBody.readWork) exit) middle)
    (bound : count ≤ entry.afterBody.readCost major.fieldCost) : middle.store = store :=
  (entry.afterBody.borrowedSteps mode distinct major view fuel exit).prefix path bound

structure Input (schema : Schema) (major : Major) (store : Store) (location rc : Nat) : Prop where
  view : major.At schema store location rc
  owned : RootOwnership store.heap [⟨.shared, .loc location⟩]
  ordered : AllocationOrderInvariant store.heap
  accounted : store.heap.allocs = store.live + store.heap.frees
  peak : store.live ≤ store.peakLiveNodes

def FullyReleased (store : Store) : Prop :=
  store.live = 0 ∧ store.heap.allocs = store.heap.frees ∧ store.heap.nodes.all Option.isNone = true

theorem fullyReleased_of_zero {before output : Store}
    (accounted : before.heap.allocs = before.live + before.heap.frees)
    (balanced : HeapBalance before output) (empty : output.live = 0) : FullyReleased output := by
  have frees : output.heap.allocs = output.heap.frees := by
    unfold HeapBalance at balanced
    omega
  refine ⟨empty, frees, ?_⟩
  have none := Array.countP_eq_zero.mp ((Store.live_eq_countP output).symm.trans empty)
  rw [Array.all_eq_true']
  intro slot member
  have absent := none slot member
  cases slot <;> simp_all

theorem FullyReleased.bump {store : Store} (released : FullyReleased store) (count : Nat) :
    FullyReleased (bump store count) := released

theorem released_peak {store output : Store} {fuel remaining : Nat} {value : RVal}
    (released : releaseShared fuel store value = .ok (output, remaining)) :
    output.peakLiveNodes = store.peakLiveNodes :=
  congrArg Counters.peakLiveNodes (CreditRefinement.releaseWork_passive released)

/-- The ownership and allocation-order invariants construct deep-release fuel
for every admitted heap, including arbitrary shared descendants. There is no
finite input matrix, source replay, or caller simulation obligation here. -/
theorem Entry.total {beforeContext afterContext schema} (entry : Entry beforeContext afterContext schema)
    (mode : Interpretation) (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (input : Input schema major store location rc) (exit : Exit) :
    ∃ fuel output,
      Steps beforeContext mode (entry.beforeBody.ownedCost major.fieldCost)
        (start entry.before location store (fuel + 2 * entry.beforeBody.readWork) exit)
        (finish (bump output (2 * entry.beforeBody.readWork)) 0 (major.result schema) exit) ∧
      Steps afterContext mode (entry.afterBody.readCost major.fieldCost + 3)
        (start (ownedWrapper entry.summary.borrowed entry.before) location store
          (fuel + entry.beforeBody.readWork) exit)
        (finish output 0 (major.result schema) exit) ∧
      FullyReleased output ∧ FullyReleased (bump output (2 * entry.beforeBody.readWork)) ∧
      output.peakLiveNodes = store.peakLiveNodes ∧
      (bump output (2 * entry.beforeBody.readWork)).heap.rcops =
        output.heap.rcops + 2 * entry.beforeBody.readWork := by
  obtain ⟨fuel, output, released, empty⟩ := CreditRefinement.reclaim_progress input.owned input.ordered
  have positive := RootOwnership.shared_rc_pos input.view input.owned
  have paths := entry.steps mode distinct major input.view positive released exit
  have clean := fullyReleased_of_zero input.accounted (releaseShared_heapBalance released) empty
  exact ⟨fuel, output, paths.1, paths.2, clean, clean.bump _, released_peak released, rfl⟩

theorem Certificate.strictImprovement {limits validation baseline}
    (certificate : Certificate limits validation baseline)
    (mode : Interpretation) (major : Major) {store : Store} {location rc : Nat}
    (input : Input certificate.schema major store location rc) (exit : Exit) :
    ∃ fuel output,
      Steps (context validation baseline) mode (certificate.entry.beforeBody.ownedCost major.fieldCost)
        (start certificate.entry.before location store (fuel + 2) exit)
        (finish (bump output 2) 0 (major.result certificate.schema) exit) ∧
      Steps (context validation certificate.rewrite.program) mode
        (certificate.entry.afterBody.readCost major.fieldCost + 3)
        (start (ownedWrapper certificate.entry.summary.borrowed certificate.entry.before) location store (fuel + 1) exit)
        (finish output 0 (major.result certificate.schema) exit) ∧
      FullyReleased output ∧ FullyReleased (bump output 2) ∧
      output.peakLiveNodes = store.peakLiveNodes ∧
      output.heap.rcops < (bump output 2).heap.rcops := by
  obtain ⟨fuel, output, before, after, clean, beforeClean, peak, _⟩ :=
    certificate.entry.total mode certificate.distinct major input exit
  have work : certificate.entry.beforeBody.readWork = 1 := by
    simp [Body.readWork, certificate.improvement]
  refine ⟨fuel, output, ?_, ?_, clean, ?_, peak, ?_⟩
  · simpa [work] using before
  · simpa [work] using after
  · simpa [work] using beforeClean
  · simp [bump]

theorem Certificate.controlCost {limits validation baseline}
    (certificate : Certificate limits validation baseline) (major : Major) :
    certificate.entry.afterBody.readCost major.fieldCost + 3 =
      certificate.entry.beforeBody.ownedCost major.fieldCost + 1 := by
  have kind : certificate.entry.afterBody.isTwice = true :=
    certificate.entry.sameKind.symm.trans certificate.improvement
  simp only [Body.readCost, Body.ownedCost, certificate.improvement, kind, ↓reduceIte]
  rw [certificate.entry.sameDepth]
  omega

theorem initial_eq_start (definition : Function) (location fuel : Nat) (store : Store)
    (peak : store.live ≤ store.peakLiveNodes) :
    initialMachine definition #[.loc location] fuel store = start definition location store fuel .halt := by
  change (Machine.mk { store with peakLiveNodes := max store.peakLiveNodes store.live } fuel
    (.running { definition, values := #[.loc location] } [])) = _
  rw [Nat.max_eq_left peak]
  rfl

/-- The public runner executes exactly the two certified open functions.
Fuel is constructed from the input ownership invariant and each structural
control cost, rather than guessed by the selecting compiler. -/
theorem Certificate.runFunctions {limits validation baseline}
    (certificate : Certificate limits validation baseline)
    (mode : Interpretation) (major : Major) {store : Store} {location rc : Nat}
    (input : Input certificate.schema major store location rc) :
    ∃ fuel output,
      runFunction (context validation baseline) mode certificate.entry.before #[.loc location]
        (certificate.entry.beforeBody.ownedCost major.fieldCost) (fuel + 2) store =
        .ok {
          store := bump output 2, value := .lit (.nat (major.result certificate.schema))
          controlRemaining := 0, heapRemaining := 0 } ∧
      runFunction (context validation certificate.rewrite.program) mode
        (ownedWrapper certificate.entry.summary.borrowed certificate.entry.before) #[.loc location]
        (certificate.entry.afterBody.readCost major.fieldCost + 3) (fuel + 1) store =
        .ok {
          store := output, value := .lit (.nat (major.result certificate.schema))
          controlRemaining := 0, heapRemaining := 0 } ∧
      FullyReleased output ∧ FullyReleased (bump output 2) ∧
      output.peakLiveNodes = store.peakLiveNodes := by
  obtain ⟨fuel, output, before, after, clean, beforeClean, peak, _⟩ :=
    certificate.strictImprovement mode major input .halt
  refine ⟨fuel, output, ?_, ?_, clean, beforeClean, peak⟩
  · rw [runFunction_eq_runMachine (by rw [certificate.entry.beforeBody.signature]; rfl)
        certificate.entry.beforeBody.nonempty, initial_eq_start _ _ _ _ input.peak]
    exact before.runMachine_halted
  · have arity : (#[.loc location] : Array RVal).size =
        (ownedWrapper certificate.entry.summary.borrowed certificate.entry.before).signature.params.size := by
      change 1 = certificate.entry.before.signature.params.size
      rw [certificate.entry.beforeBody.signature]
      rfl
    rw [runFunction_eq_runMachine arity (by rfl), initial_eq_start _ _ _ _ input.peak]
    exact after.runMachine_halted

end Ix.Compiler.IxIR2.Borrow.Open
