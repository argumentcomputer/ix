import Compilatrix.X86.PhysicalHeapFree

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (Store)

def reuseState (state : State) (index : Nat) (ctor : Constructor) : State :=
  counter (counter (counter (writeCell state index ctor) 4 (· + 1))
    8 (· + UInt64.ofNat ctor.schema.fields.size)) 9 (· - 1)

theorem reuseState_cell (state : State) (index : Nat) (ctor : Constructor) (other field : Nat) :
    (reuseState state index ctor).words (cellSlot other field) = (writeCell state index ctor).words (cellSlot other field) := by
  simp [reuseState, counter,
    cellSlot_ne_header other (field := field) (by decide : 4 < headerWords),
    cellSlot_ne_header other (field := field) (by decide : 8 < headerWords),
    cellSlot_ne_header other (field := field) (by decide : 9 < headerWords)]

theorem reuseState_heap (state : State) {index : Nat} (bound : index < capacity) (ctor : Constructor)
    {slot : Nat} (above : heapWords ≤ slot) : (reuseState state index ctor).words slot = state.words slot := by
  rw [reuseState, counter_heap _ (by decide) _ above, counter_heap _ (by decide) _ above,
    counter_heap _ (by decide) _ above, writeCell_heap _ bound _ above]

theorem reuse_parts {store output : Store} {location units : Nat} {world : Ixon.Owned} {node : IxIR1.Node}
    (reused : store.reuseReservation location world node units = .ok output) :
    store.heap.nodes[location]? = some none ∧
    output.heap.nodes = store.heap.nodes.setIfInBounds location (some ⟨world, 1, node⟩) ∧
    ∀ field, 2 ≤ field → field ≤ 8 → counters output field = counters store field +
      (if field = 4 then 1 else if field = 8 then units else 0) := by
  unfold Store.reuseReservation at reused
  split at reused
  · rename_i found
    cases reused
    refine ⟨found, rfl, ?_⟩
    intro field lower upper
    have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · contradiction

theorem HeapAt.reuse {schemas constructors offset store output reserved outReserved location world ctor}
    {state : State} {fields : Array Word}
    (related : HeapAt schemas constructors offset store reserved state.words)
    (accepted : ConstructorAt schemas constructors world ctor)
    (above : offset ≤ location)
    (reused : store.reuseReservation location world (.ctorN ctor.cid (fields.map PhysicalScalar.rval))
      ctor.schema.fields.size = .ok output)
    (arity : fields.size = ctor.schema.fields.size)
    (first : state.registers .r8 = fields[0]?.getD 0) (second : state.registers .r9 = fields[1]?.getD 0)
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (count : outReserved.length + 1 = reserved.length) :
    HeapAt schemas constructors offset output outReserved (reuseState state (location - offset) ctor).words := by
  obtain ⟨emptySlot, nodes, statistics⟩ := reuse_parts reused
  have bound := (Array.getElem?_eq_some_iff.mp emptySlot).1
  have size : output.heap.nodes.size = store.heap.nodes.size := by simp [nodes]
  apply related.patch (location := location) above (by simpa [size] using related.extent)
    (by simpa [size] using related.bounded)
  · intro other small different
    simpa [size] using small
  · intro other different
    simp [Store.get?, IxIR1.Store.get?, nodes, Ne.symm different]
  · intro other lower different field small
    rw [reuseState_cell, writeCell_other _ _ _ (other := other - offset) (by omega) small]
  · exact kept
  · have found : output.get? location = some ⟨world, 1, .ctorN ctor.cid (fields.map PhysicalScalar.rval)⟩ := by
      simp [Store.get?, IxIR1.Store.get?, nodes, bound]
    rw [found]
    exact (accepted.node state _ fields arity first second).words (fun field _ => reuseState_cell _ _ _ _ field)
  · simp [reuseState, counter, writeCell_header _ _ _ (by decide : 0 < headerWords), size, related.cursor]
  · intro field lower upper
    have atField := related.statistics field lower upper
    rw [statistics field lower upper]
    have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [reuseState, counter, writeCell_header _ _ _ (by decide : 2 < headerWords),
        writeCell_header _ _ _ (by decide : 3 < headerWords), writeCell_header _ _ _ (by decide : 4 < headerWords),
        writeCell_header _ _ _ (by decide : 5 < headerWords), writeCell_header _ _ _ (by decide : 6 < headerWords),
        writeCell_header _ _ _ (by decide : 7 < headerWords), writeCell_header _ _ _ (by decide : 8 < headerWords),
        atField, UInt64.ofNat_add]
  · simp [reuseState, counter, writeCell_header _ _ _ (by decide : 9 < headerWords),
      related.reservations, ← count, UInt64.ofNat_add]

end Compilatrix.X86.PhysicalHeap
