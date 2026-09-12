import Compilatrix.X86.PhysicalHeapObserve

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (Store)

def freeState (state : State) (index : Nat) (consume : Bool) : State :=
  let state := counter (tag state index 0) 3 (· + 1)
  if consume then counter state 9 (· - 1) else state

theorem freeState_cell (state : State) (index : Nat) (consume : Bool) (other field : Nat) :
    (freeState state index consume).words (cellSlot other field) = (tag state index 0).words (cellSlot other field) := by
  cases consume <;> simp [freeState, counter,
    cellSlot_ne_header other (field := field) (by decide : 3 < headerWords),
    cellSlot_ne_header other (field := field) (by decide : 9 < headerWords)]

theorem freeState_heap (state : State) {index : Nat} (bound : index < capacity) (consume : Bool)
    {slot : Nat} (above : heapWords ≤ slot) : (freeState state index consume).words slot = state.words slot := by
  cases consume <;> simp only [freeState, Bool.false_eq_true, ↓reduceIte]
  · rw [counter_heap _ (by decide) _ above, tag_heap _ bound _ above]
  · rw [counter_heap _ (by decide) _ above, counter_heap _ (by decide) _ above, tag_heap _ bound _ above]

theorem kill_counters (store : Store) (location field : Nat) (lower : 2 ≤ field) (upper : field ≤ 8) :
    counters (store.kill location) field = counters store field + (if field = 3 then 1 else 0) := by
  have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem HeapAt.kill {schemas constructors offset store reserved outReserved location consume} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words)
    (above : offset ≤ location) (bound : location < store.heap.nodes.size)
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (count : outReserved.length + (if consume then 1 else 0) = reserved.length) :
    HeapAt schemas constructors offset (store.kill location) outReserved (freeState state (location - offset) consume).words := by
  apply related.patch (location := location) above (by simpa [Store.kill, IxIR1.Store.kill] using related.extent)
    (by simpa [Store.kill, IxIR1.Store.kill] using related.bounded)
  · intro other small different
    simpa [Store.kill, IxIR1.Store.kill] using small
  · intro other different
    simp [Store.kill, IxIR1.Store.kill, Store.get?, IxIR1.Store.get?, Ne.symm different]
  · intro other lower different field small
    rw [freeState_cell, tag_other _ _ _ (other := other - offset) (by omega) small]
  · exact kept
  · have missing : (store.kill location).get? location = none := by
      simp [Store.kill, IxIR1.Store.kill, Store.get?, IxIR1.Store.get?, bound]
    rw [missing]
    exact .inl (by rw [freeState_cell]; simp [tag])
  · cases consume <;> simp [freeState, counter, tag_header _ _ _ (by decide : 0 < headerWords),
      Store.kill, IxIR1.Store.kill, related.cursor]
  · intro field lower upper
    have small : field < headerWords := by simp only [headerWords]; omega
    have different : field ≠ 9 := by omega
    rw [kill_counters store location field lower upper]
    by_cases three : field = 3
    · subst field
      cases consume <;> simp [freeState, counter, tag_header _ _ _ (by decide : 3 < headerWords),
        related.statistics 3 (by omega) (by omega), UInt64.ofNat_add]
    · cases consume <;> simp [freeState, counter, different, three, tag_header _ _ _ small,
        related.statistics field lower upper]
  · cases consume with
    | false => simpa [freeState, counter, tag_header _ _ _ (by decide : 9 < headerWords), related.reservations] using congrArg UInt64.ofNat count.symm
    | true =>
        change outReserved.length + 1 = reserved.length at count
        simp [freeState, counter, tag_header _ _ _ (by decide : 9 < headerWords), related.reservations,
          ← count, UInt64.ofNat_add]

theorem releaseReservation_kill {store output : Store} {location : Nat}
    (released : store.releaseReservation location = .ok output) : output = store.kill location := by
  unfold Store.releaseReservation at released
  split at released
  · rename_i found
    cases released
    have unchanged : store.heap.nodes.setIfInBounds location none = store.heap.nodes := by
      apply Array.ext_getElem?
      intro other
      by_cases same : location = other
      · subst other
        simp [(Array.getElem?_eq_some_iff.mp found).1, (Array.getElem?_eq_some_iff.mp found).2]
      · simp [same]
    simp [Store.kill, IxIR1.Store.kill, unchanged]
  · contradiction

end Compilatrix.X86.PhysicalHeap
