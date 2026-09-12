import Compilatrix.X86.PhysicalHeapScopeUpdate
import Compilatrix.IxIR2.HeapAccounting

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (Store)

theorem cellSlot_injective {left right field other : Nat} (small : field < cellWords) (otherSmall : other < cellWords)
    (equal : cellSlot left field = cellSlot right other) : left = right ∧ field = other := by
  simp only [cellSlot, headerWords, cellWords] at *
  omega

theorem cellSlot_ne_header (index : Nat) {field header : Nat} (bound : header < headerWords) : cellSlot index field ≠ header := by
  simp only [cellSlot, headerWords] at *
  omega

theorem frameSlot_above_heap {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region)
    (separate : heapWords ≤ frame.stackIndex) {index : Nat} (bound : index < Scalar.maxLocals) :
    heapWords ≤ frame.localIndex index := by
  simp only [Scalar.Frame.localIndex, Scalar.Frame.stackIndex, Scalar.maxLocals] at *
  omega

theorem frameSlot_ne_cell {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region)
    (separate : heapWords ≤ frame.stackIndex) {index cell field : Nat}
    (localBound : index < Scalar.maxLocals) (cellBound : cell < capacity) (fieldBound : field < cellWords) :
    frame.localIndex index ≠ cellSlot cell field := by
  have above := frameSlot_above_heap frame separate localBound
  have below := cellSlot_bound cellBound fieldBound
  omega

theorem NodeAt.words {schemas constructors before after index box}
    (related : NodeAt schemas constructors before index box)
    (same : ∀ field < cellWords, after (cellSlot index field) = before (cellSlot index field)) :
    NodeAt schemas constructors after index box := by
  rcases related with ⟨related⟩
  exact ⟨{ related with
    tag := (same 0 (by decide)).trans related.tag
    first := (same 1 (by decide)).trans related.first
    second := (same 2 (by decide)).trans related.second
    padding := (same 3 (by decide)).trans related.padding }⟩

theorem HeapAt.words {schemas constructors offset store reserved before after}
    (related : HeapAt schemas constructors offset store reserved before)
    (same : ∀ index < heapWords, after index = before index) :
    HeapAt schemas constructors offset store reserved after := by
  refine ⟨related.extent, related.bounded, related.offsetDead,
    (same 0 (by decide)).trans related.cursor,
    fun field lower upper => (same field (by simp only [heapWords, headerWords, cellWords, capacity]; omega)).trans
      (related.statistics field lower upper), (same 9 (by decide)).trans related.reservations, ?_, ?_⟩
  · intro location box found
    obtain ⟨above, cell⟩ := related.live location box found
    have bound := (Array.getElem?_eq_some_iff.mp (IxIR1.Sim.nodes_get?_of_get? found)).1
    exact ⟨above, cell.words (fun field fieldBound => same _ (cellSlot_bound (by have := related.bounded; omega) fieldBound))⟩
  · intro location above below missing
    rw [same _ (cellSlot_bound (by have := related.bounded; omega) (by decide : 0 < cellWords))]
    exact related.dead location above below missing

theorem HeapAt.setReg {schemas constructors offset store reserved} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words) (register : GPR) (word : Word) :
    HeapAt schemas constructors offset store reserved (state.setReg register word).words := related

theorem HeapAt.setStack {schemas constructors offset store reserved} {state : State} {layout : HeapArena.Layout}
    (frame : Scalar.Frame layout.region) (separate : heapWords ≤ frame.stackIndex)
    (related : HeapAt schemas constructors offset store reserved state.words) {index : Nat}
    (bound : index < Scalar.maxLocals) (word : Word) :
    HeapAt schemas constructors offset store reserved (state.setWord (frame.localIndex index) word).words := by
  apply related.words
  intro slot small
  have above := frameSlot_above_heap frame separate bound
  simp [show slot ≠ frame.localIndex index by omega]

/-- One physical cell changes. Statistics and the cursor are checked
separately, while every other live or reserved cell retains its contents. -/
theorem HeapAt.patch {schemas constructors offset store reserved before after output outReserved location}
    (related : HeapAt schemas constructors offset store reserved before)
    (above : offset ≤ location)
    (extent : offset ≤ output.heap.nodes.size)
    (bounded : output.heap.nodes.size - offset ≤ capacity)
    (oldIndex : ∀ other < output.heap.nodes.size, other ≠ location → other < store.heap.nodes.size)
    (nodes : ∀ other, other ≠ location → output.get? other = store.get? other)
    (words : ∀ other, offset ≤ other → other ≠ location → ∀ field < cellWords,
      after (cellSlot (other - offset) field) = before (cellSlot (other - offset) field))
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (changed : match output.get? location with
      | some box => NodeAt schemas constructors after (location - offset) box
      | none => after (cellSlot (location - offset) 0) = 0 ∨
          (after (cellSlot (location - offset) 0) = 1 ∧ location ∈ outReserved))
    (cursor : after 0 = UInt64.ofNat (32 * (output.heap.nodes.size - offset)))
    (statistics : ∀ field, 2 ≤ field → field ≤ 8 → after field = UInt64.ofNat (counters output field))
    (reservations : after 9 = UInt64.ofNat outReserved.length) :
    HeapAt schemas constructors offset output outReserved after := by
  refine ⟨extent, bounded, ?_, cursor, statistics, reservations, ?_, ?_⟩
  · intro other lower
    rw [nodes other (by omega)]
    exact related.offsetDead other lower
  · intro other box found
    by_cases same : other = location
    · subst other
      rw [found] at changed
      exact ⟨above, changed⟩
    · rw [nodes other same] at found
      obtain ⟨lower, cell⟩ := related.live other box found
      exact ⟨lower, cell.words (words other lower same)⟩
  · intro other lower upper missing
    by_cases same : other = location
    · subst other
      simpa only [missing] using changed
    · have oldMissing := missing
      rw [nodes other same] at oldMissing
      have old := related.dead other lower (oldIndex other upper same) oldMissing
      rw [words other lower same 0 (by decide)]
      rcases old with free | ⟨reservedTag, member⟩
      · exact .inl free
      · exact .inr ⟨reservedTag, kept other same member⟩

end Compilatrix.X86.PhysicalHeap
