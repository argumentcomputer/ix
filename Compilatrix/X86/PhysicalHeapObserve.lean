import Compilatrix.X86.PhysicalHeapAlloc

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (Store)

theorem HeapAt.observe {schemas constructors offset store output reserved before after}
    (related : HeapAt schemas constructors offset store reserved before)
    (nodes : output.heap.nodes = store.heap.nodes)
    (cells : ∀ index field, field < cellWords → after (cellSlot index field) = before (cellSlot index field))
    (cursor : after 0 = before 0) (reservations : after 9 = before 9)
    (statistics : ∀ field, 2 ≤ field → field ≤ 8 → after field = UInt64.ofNat (counters output field)) :
    HeapAt schemas constructors offset output reserved after := by
  have get : ∀ location, output.get? location = store.get? location := by simp [Store.get?, IxIR1.Store.get?, nodes]
  refine ⟨by simpa [nodes] using related.extent, by simpa [nodes] using related.bounded,
    fun location lower => (get location).trans (related.offsetDead location lower),
    cursor.trans (by simpa [nodes] using related.cursor), statistics,
    reservations.trans related.reservations, ?_, ?_⟩
  · intro location box found
    obtain ⟨above, content⟩ := related.live location box ((get location).symm.trans found)
    exact ⟨above, content.words (cells _)⟩
  · intro location above below missing
    rw [cells _ 0 (by decide)]
    exact related.dead location above (by simpa [nodes] using below) ((get location).symm.trans missing)

theorem HeapAt.rcTick {schemas constructors offset store reserved} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words) :
    HeapAt schemas constructors offset store.rcTick reserved (counter state 5 (· + 1)).words := by
  apply related.observe (output := store.rcTick) rfl
  · intro index field small
    simp [counter, cellSlot_ne_header index (field := field) (by decide : 5 < headerWords)]
  · simp [counter]
  · simp [counter]
  · intro field lower upper
    have atField := related.statistics field lower upper
    have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [counter, atField, counters, Store.rcTick, IxIR1.Store.rcTick, UInt64.ofNat_add]

theorem HeapAt.resetTicks {schemas constructors offset store reserved} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words) :
    HeapAt schemas constructors offset store.tickResetAttempt.tickHotReset reserved
      (counter (counter state 6 (· + 1)) 7 (· + 1)).words := by
  apply related.observe (output := store.tickResetAttempt.tickHotReset) rfl
  · intro index field small
    simp [counter, cellSlot_ne_header index (field := field) (by decide : 6 < headerWords),
      cellSlot_ne_header index (field := field) (by decide : 7 < headerWords)]
  · simp [counter]
  · simp [counter]
  · intro field lower upper
    have atField := related.statistics field lower upper
    have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [counter, atField, counters,
        Store.tickResetAttempt, Store.tickHotReset, UInt64.ofNat_add]

theorem tag_other (state : State) (index : Nat) (word : Word) {other field : Nat}
    (different : other ≠ index) (small : field < cellWords) :
    (tag state index word).words (cellSlot other field) = state.words (cellSlot other field) := by
  have differentField : cellSlot other field ≠ cellSlot index 0 := by
    intro equal
    exact different (cellSlot_injective small (by decide) equal).1
  simp [tag, differentField]

theorem tag_header (state : State) (index : Nat) (word : Word) {field : Nat}
    (bound : field < headerWords) : (tag state index word).words field = state.words field := by
  simp [tag, Ne.symm (cellSlot_ne_header index (field := 0) bound)]

theorem tag_heap (state : State) {index : Nat} (bound : index < capacity) (word : Word)
    {slot : Nat} (above : heapWords ≤ slot) : (tag state index word).words slot = state.words slot := by
  have bound := cellSlot_bound bound (by decide : 0 < cellWords)
  simp [tag, show slot ≠ cellSlot index 0 by omega]

theorem HeapAt.reserve {schemas constructors offset store reserved outReserved location box} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words)
    (found : store.get? location = some box)
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (member : location ∈ outReserved) (count : outReserved.length = reserved.length + 1) :
    HeapAt schemas constructors offset (store.reserve location) outReserved
      (counter (tag state (location - offset) 1) 9 (· + 1)).words := by
  have above := (related.live location box found).1
  have atSlot := IxIR1.Sim.nodes_get?_of_get? found
  have bound := (Array.getElem?_eq_some_iff.mp atSlot).1
  apply related.patch (location := location) above (by simpa [Store.reserve] using related.extent)
    (by simpa [Store.reserve] using related.bounded)
  · intro other small different
    simpa [Store.reserve] using small
  · intro other different
    simp [Store.reserve, Store.get?, IxIR1.Store.get?, Array.getElem?_setIfInBounds, different, Ne.symm different]
  · intro other lower different field small
    simp [counter, cellSlot_ne_header (other - offset) (field := field) (by decide : 9 < headerWords),
      tag_other state (location - offset) 1 (other := other - offset) (by omega) small]
  · exact kept
  · have missing : (store.reserve location).get? location = none := by
      simp [Store.reserve, Store.get?, IxIR1.Store.get?, Array.getElem?_setIfInBounds, bound]
    rw [missing]
    exact .inr ⟨by simp [counter, tag, cellSlot_ne_header (location - offset) (field := 0) (by decide : 9 < headerWords)], member⟩
  · simp [counter, tag_header _ _ _ (by decide : 0 < headerWords), Store.reserve, related.cursor]
  · intro field lower upper
    have small : field < headerWords := by simp only [headerWords]; omega
    have different : field ≠ 9 := by omega
    have countersSame : counters (store.reserve location) field = counters store field := by
      have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    simp [counter, different, tag_header _ _ _ small, countersSame, related.statistics field lower upper]
  · simp [counter, tag_header _ _ _ (by decide : 9 < headerWords), related.reservations, count, UInt64.ofNat_add]

end Compilatrix.X86.PhysicalHeap
