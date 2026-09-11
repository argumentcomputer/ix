import Ix.Compiler.UniqueReuse.TargetSteps

namespace Ix.Compiler.UniqueReuse.Target

open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval

def inPlace (reuse : Bool) (mode : Interpretation) : Bool := reuse && mode == .physical
def freshPerCons (reuse : Bool) (mode : Interpretation) : Nat := if inPlace reuse mode then 0 else 1
def reusesPerCons (reuse : Bool) (mode : Interpretation) : Nat := if inPlace reuse mode then 1 else 0
def consControl (reuse : Bool) : Nat := if reuse then 4 else 5

structure ConsResult (schema : Schema) (physical : Bool) (before after : Store)
    (head : Nat) (tailValues accValues : List Nat) (tail accumulator : RVal) : Prop where
  owned : RootOwnership after.heap [⟨.unique, tail⟩, ⟨.unique, accumulator⟩]
  tailAt : ListAt schema after.heap tailValues tail
  accAt : ListAt schema after.heap (head :: accValues) accumulator
  allocs : after.heap.allocs = before.heap.allocs + (if physical then 0 else 1)
  frees : after.heap.frees = before.heap.frees + (if physical then 0 else 1)
  reuses : after.heap.reuses = before.heap.reuses + (if physical then 1 else 0)
  rcops : after.heap.rcops = before.heap.rcops
  live : after.live = before.live
  peak : after.peakLiveNodes = before.peakLiveNodes
  attempts : after.resetAttempts = before.resetAttempts
  hot : after.hotResets = before.hotResets
  cold : after.coldResets = before.coldResets
  payload : after.reusedPayloadUnits = before.reusedPayloadUnits + (if physical then 2 else 0)

private theorem freshConsResult {schema : Schema} {store : Store} {location head : Nat}
    {tail acc : RVal} {tailValues accValues : List Nat}
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (taken : TakenCons schema store.heap location head tail acc tailValues accValues)
    (peak : store.live ≤ store.peakLiveNodes) :
    let allocated := (store.kill location).allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), acc])
    ConsResult schema false store allocated.1 head tailValues accValues tail (.loc allocated.2) := by
  obtain ⟨owned, tailAt, accAt⟩ := taken.allocate
  have live := Store.live_kill found
  refine ⟨owned, tailAt, accAt, rfl, rfl, ?_, rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp; rfl
  · rw [Store.live_allocNode]; omega
  · rw [Store.peakLive_allocNode, Store.live_allocNode]
    change max store.peakLiveNodes ((store.kill location).live + 1) = _
    rw [live, Nat.max_eq_left peak]
  · simp; rfl

private theorem physicalConsResult {schema : Schema} {store : Store} {location head : Nat}
    {tail acc : RVal} {tailValues accValues : List Nat}
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (taken : TakenCons schema store.heap location head tail acc tailValues accValues)
    (peak : store.live ≤ store.peakLiveNodes) :
    ConsResult schema true store (reuseAt store location (.ctorN (consId schema) #[.lit (.nat head), acc]) 2)
      head tailValues accValues tail (.loc location) := by
  obtain ⟨owned, tailAt, accAt⟩ := taken.reuse found
  refine ⟨owned, tailAt, accAt, ?_, ?_, rfl, rfl, reuseAt_live found _ 2,
    reuseAt_peak found _ 2 peak, rfl, rfl, rfl, rfl⟩ <;> simp [reuseAt, reuseNodeStore] <;> rfl

theorem consSteps (ctx : Context) (mode : Interpretation) (schema : Schema) (reuse : Bool)
    (store : Store) (fuel location head : Nat) (tail acc : RVal) (tailValues accValues : List Nat)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (taken : TakenCons schema store.heap location head tail acc tailValues accValues)
    (peak : store.live ≤ store.peakLiveNodes) :
    ∃ output value,
      Steps ctx mode (consControl reuse) (loop schema reuse store fuel acc (.loc location))
        (loop schema reuse output fuel value tail) ∧
      ConsResult schema (inPlace reuse mode) store output head tailValues accValues tail value := by
  let allocated := (store.kill location).allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), acc])
  have fields := consFields (store := store.kill location) taken.accAt head
  cases reuse with
  | false =>
      exact ⟨allocated.1, .loc allocated.2,
        consBaselineSteps ctx mode schema store fuel location head tail acc schemas found fields,
        freshConsResult found taken peak⟩
  | true =>
      cases mode with
      | logical =>
          exact ⟨allocated.1, .loc allocated.2,
            consLogicalSteps ctx schema store fuel location head tail acc schemas found fields,
            freshConsResult found taken peak⟩
      | physical =>
          have accAt : ListAt schema (store.reserve location).heap accValues acc :=
            taken.accAt.mono (before := store.heap.kill location)
              (after := (store.reserve location).heap) (fun kept => kept)
          exact ⟨reuseAt store location (.ctorN (consId schema) #[.lit (.nat head), acc]) 2, .loc location,
            consPhysicalSteps ctx schema store fuel location head tail acc schemas found
              (consFields (store := store.reserve location) accAt head),
            physicalConsResult found taken peak⟩

structure LoopResult (schema : Schema) (reuse : Bool) (mode : Interpretation) (before after : Store)
    (values accValues : List Nat) (value : RVal) : Prop where
  owned : RootOwnership after.heap [⟨.unique, value⟩]
  list : ListAt schema after.heap (values.reverse ++ accValues) value
  allocs : after.heap.allocs = before.heap.allocs + freshPerCons reuse mode * values.length
  frees : after.heap.frees = before.heap.frees + freshPerCons reuse mode * values.length + 1
  reuses : after.heap.reuses = before.heap.reuses + reusesPerCons reuse mode * values.length
  rcops : after.heap.rcops = before.heap.rcops
  live : after.live + 1 = before.live
  peak : after.peakLiveNodes = before.peakLiveNodes
  attempts : after.resetAttempts = before.resetAttempts
  hot : after.hotResets = before.hotResets
  cold : after.coldResets = before.coldResets
  payload : after.reusedPayloadUnits = before.reusedPayloadUnits + 2 * reusesPerCons reuse mode * values.length

theorem loopSteps (ctx : Context) (mode : Interpretation) (schema : Schema) (reuse : Bool)
    (values : List Nat) (store : Store) (fuel : Nat) (major acc : RVal) (accValues : List Nat)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (owned : RootOwnership store.heap [⟨.unique, major⟩, ⟨.unique, acc⟩])
    (input : ListAt schema store.heap values major) (accAt : ListAt schema store.heap accValues acc)
    (peak : store.live ≤ store.peakLiveNodes) :
    ∃ output value,
      Steps ctx mode (consControl reuse * values.length + 4) (loop schema reuse store fuel acc major)
        { store := output, heapFuel := fuel, control := .halted value } ∧
      LoopResult schema reuse mode store output values accValues value := by
  induction values generalizing store major acc accValues with
  | nil =>
      cases input with
      | @nil location found =>
          obtain ⟨afterOwned, afterList⟩ := nilConsumed found owned accAt
          refine ⟨store.kill location, acc, ?_, afterOwned, ?_, ?_, ?_, ?_, rfl,
            Store.live_kill found, rfl, rfl, rfl, rfl, ?_⟩
          · simpa using nilSteps ctx mode schema reuse store fuel location acc schemas found (listWorld afterList)
          · simpa using afterList
          · simp [Store.kill, IxIR1.Store.kill]
          · simp [Store.kill, IxIR1.Store.kill]
          · simp [Store.kill, IxIR1.Store.kill]
          · simp [Store.kill]
  | cons head tail ih =>
      cases input with
      | @cons _ _ location tailValue found next =>
          have taken := consTaken found owned next accAt
          obtain ⟨middle, accumulator, first, middleResult⟩ := consSteps ctx mode schema reuse store fuel
            location head tailValue acc tail accValues schemas found taken peak
          obtain ⟨output, value, rest, result⟩ := ih middle tailValue accumulator (head :: accValues)
            middleResult.owned middleResult.tailAt middleResult.accAt
            (by rw [middleResult.live, middleResult.peak]; exact peak)
          refine ⟨output, value, ?_, result.owned, ?_, ?_, ?_, ?_, result.rcops.trans middleResult.rcops,
            ?_, result.peak.trans middleResult.peak, result.attempts.trans middleResult.attempts,
            result.hot.trans middleResult.hot, result.cold.trans middleResult.cold, ?_⟩
          · have count : consControl reuse * (head :: tail).length + 4 =
                consControl reuse + (consControl reuse * tail.length + 4) := by
              simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]
            rw [count]
            exact first.trans rest
          · simpa [List.reverse_cons, List.append_assoc] using result.list
          · rw [result.allocs, middleResult.allocs]
            simp [freshPerCons, Nat.mul_add, Nat.add_assoc, Nat.add_comm]
          · rw [result.frees, middleResult.frees]
            simp [freshPerCons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          · rw [result.reuses, middleResult.reuses]
            simp [reusesPerCons, Nat.mul_add, Nat.add_assoc, Nat.add_comm]
          · rw [result.live, middleResult.live]
          · rw [result.payload, middleResult.payload]
            cases h : inPlace reuse mode <;>
              simp [reusesPerCons, h, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

end Ix.Compiler.UniqueReuse.Target
