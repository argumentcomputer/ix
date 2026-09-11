import Ix.Compiler.UniqueReuse.Heap
import Ix.Compiler.IxIR1.Mono
import Ix.Compiler.IxIR2.HeapAccounting
import Ix.Compiler.IxIR2.LowerSim

/-! Complete unique-list release, including heaps whose links were reversed
in place. Finite list views and exact owner counts replace an allocation-order
premise; reuse need not preserve the original order of heap locations. -/

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema)

private theorem consReleaseReady {store : Store} {schema : Schema} {location head : Nat}
    {tail : RVal} {values : List Nat} {rest : List Root}
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (owned : RootOwnership store (⟨.unique, .loc location⟩ :: rest))
    (next : ListAt schema store values tail) :
    RootOwnership (store.kill location) (⟨.unique, tail⟩ :: rest) ∧
      ListAt schema (store.kill location) values tail := by
  have killed : RootOwnership (store.kill location)
      (⟨.unique, .lit (.nat head)⟩ :: ⟨.unique, tail⟩ :: rest) := owned.killUniqueOne found
  have ready := killed.dropNoLocation rfl
  exact ⟨ready, next.ofRestricts (StoreGraphRestricts.kill found) ready
    (ready.roots_world ⟨.unique, tail⟩ (by simp))⟩

structure Released1 (before after : Store) (count : Nat) (rest : List Root) : Prop where
  owned : RootOwnership after rest
  allocs : after.allocs = before.allocs
  frees : after.frees = before.frees + count
  reuses : after.reuses = before.reuses
  rcops : after.rcops = before.rcops

theorem release1 (ctx : Ctx) {schema : Schema} {store : Store} {value : RVal}
    {rest : List Root} {values : List Nat}
    (owned : RootOwnership store (⟨.unique, value⟩ :: rest))
    (list : ListAt schema store values value) :
    ∃ output, dropUVal ctx (3 * values.length + 2) store value = .ok output ∧
      Released1 store output (values.length + 1) rest := by
  induction values generalizing store value with
  | nil =>
      cases list with
      | nil found =>
          refine ⟨store.kill _, ?_, owned.killUniqueOne found, rfl, ?_, rfl, rfl⟩
          · simp [dropUVal, found, dropManyU]
          · simp [Store.kill]
  | cons head tail ih =>
      cases list with
      | @cons _ _ location tailValue found next =>
          obtain ⟨ready, tailAt⟩ := consReleaseReady found owned next
          obtain ⟨output, run, result⟩ := ih ready tailAt
          refine ⟨output, ?_, result.owned, result.allocs, ?_, result.reuses, result.rcops⟩
          · have count : 3 * (head :: tail).length + 2 = (3 * tail.length + 2) + 3 := by simp; omega
            rw [count]
            rw [dropUVal.eq_def]
            simp only [found]
            change dropManyU ctx ((3 * tail.length + 2) + 2) (store.kill location)
              [.lit (.nat head), tailValue] = .ok output
            rw [dropManyU.eq_def]
            simp only [dropUVal, bind, Except.bind]
            rw [dropManyU.eq_def]
            simp only [run, bind, Except.bind, dropManyU]
          · simpa [Store.kill, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result.frees

theorem Released1.live {ctx : Ctx} {fuel : Nat} {before after : Store} {value : RVal}
    {count : Nat} {rest : List Root} (released : Released1 before after count rest)
    (run : dropUVal ctx fuel before value = .ok after) : after.live + count = before.live := by
  have operation : runOp ctx (fuel + 1) ⟨0, .unique, false, .ret .erased⟩ before [value]
      (.dropU (.var 0)) = .ok (after, .erased) := by
    cases value with
    | loc location => exact runOp_dropU rfl run
    | lit literal => cases fuel <;> simp_all [dropUVal, runOp, resolveAtom]
    | erased => cases fuel <;> simp_all [dropUVal, runOp, resolveAtom]
  have balance := (IxIR1.Reclamation.runOp_footprint operation).live_balance
  rw [released.allocs, released.frees] at balance
  omega

structure Released2 (before after : IxIR2.Eval.Store) (count : Nat) (rest : List Root) : Prop where
  owned : RootOwnership after.heap rest
  allocs : after.heap.allocs = before.heap.allocs
  frees : after.heap.frees = before.heap.frees + count
  reuses : after.heap.reuses = before.heap.reuses
  rcops : after.heap.rcops = before.heap.rcops
  peak : after.peakLiveNodes = before.peakLiveNodes
  attempts : after.resetAttempts = before.resetAttempts
  hot : after.hotResets = before.hotResets
  cold : after.coldResets = before.coldResets
  payload : after.reusedPayloadUnits = before.reusedPayloadUnits

theorem release2 {schema : Schema} {store : IxIR2.Eval.Store} {value : RVal}
    {rest : List Root} {values : List Nat}
    (owned : RootOwnership store.heap (⟨.unique, value⟩ :: rest))
    (list : ListAt schema store.heap values value) :
    ∃ output, IxIR2.Eval.dropUnique (2 * values.length + 1) store value = .ok (output, 0) ∧
      Released2 store output (values.length + 1) rest := by
  induction values generalizing store value with
  | nil =>
      cases list with
      | nil found =>
          refine ⟨store.kill _, ?_, owned.killUniqueOne found, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · simp [IxIR2.Eval.dropUnique, IxIR2.Eval.dropUniqueWork, IxIR2.Eval.Store.get?, found]
          · simp [IxIR2.Eval.Store.kill, Store.kill]
  | cons head tail ih =>
      cases list with
      | @cons _ _ location tailValue found next =>
          obtain ⟨ready, tailAt⟩ := consReleaseReady found owned next
          obtain ⟨output, run, result⟩ := ih (store := store.kill location) ready tailAt
          refine ⟨output, ?_, result.owned, result.allocs, ?_, result.reuses, result.rcops,
            result.peak, result.attempts, result.hot, result.cold, result.payload⟩
          · have count : 2 * (head :: tail).length + 1 = (2 * tail.length + 1) + 2 := by simp; omega
            rw [count]
            simpa [IxIR2.Eval.dropUnique, IxIR2.Eval.dropUniqueWork, IxIR2.Eval.Store.get?,
              found, List.append_nil] using run
          · simpa [IxIR2.Eval.Store.kill, Store.kill, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result.frees

theorem Released2.live {fuel remaining : Nat} {before after : IxIR2.Eval.Store} {value : RVal}
    {count : Nat} {rest : List Root} (released : Released2 before after count rest)
    (run : IxIR2.Eval.dropUnique fuel before value = .ok (after, remaining)) :
    after.live + count = before.live := by
  have balance := IxIR2.Eval.dropUnique_heapBalance run
  unfold IxIR2.Eval.HeapBalance at balance
  rw [released.allocs, released.frees] at balance
  omega

theorem release2_complete {schema : Schema} {store : IxIR2.Eval.Store} {value : RVal} {values : List Nat}
    (owned : RootOwnership store.heap [⟨.unique, value⟩])
    (list : ListAt schema store.heap values value) (live : store.live = values.length + 1) :
    ∃ output, IxIR2.Eval.dropUnique (2 * values.length + 1) store value = .ok (output, 0) ∧
      output.live = 0 ∧ Released2 store output (values.length + 1) [] := by
  obtain ⟨output, run, result⟩ := release2 owned list
  have balance := result.live run
  exact ⟨output, run, by omega, result⟩

end Ix.Compiler.UniqueReuse
