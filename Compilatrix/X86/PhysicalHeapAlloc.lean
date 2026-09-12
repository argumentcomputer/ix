import Compilatrix.X86.PhysicalHeapConstructor

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (Store)

def allocationState (state : State) (index : Nat) (ctor : Constructor) : State :=
  counter (counter (writeCell state index ctor) 0 (· + 32)) 2 (· + 1)

theorem allocationState_cell (state : State) (index : Nat) (ctor : Constructor) (other field : Nat) :
    (allocationState state index ctor).words (cellSlot other field) = (writeCell state index ctor).words (cellSlot other field) := by
  simp [allocationState, counter, cellSlot_ne_header other (field := field) (by decide : 0 < headerWords),
    cellSlot_ne_header other (field := field) (by decide : 2 < headerWords)]

theorem allocationState_heap (state : State) {index : Nat} (bound : index < capacity) (ctor : Constructor)
    {slot : Nat} (above : heapWords ≤ slot) : (allocationState state index ctor).words slot = state.words slot := by
  rw [allocationState, counter_heap _ (by decide) _ above, counter_heap _ (by decide) _ above,
    writeCell_heap _ bound _ above]

theorem alloc_counters (store : Store) (world : Ixon.Owned) (node : IxIR1.Node) (field : Nat)
    (lower : 2 ≤ field) (upper : field ≤ 8) :
    counters (store.allocNode world node).1 field = counters store field + (if field = 2 then 1 else 0) := by
  have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem HeapAt.alloc {schemas constructors offset store reserved world ctor} {state : State} {fields : Array Word}
    (related : HeapAt schemas constructors offset store reserved state.words)
    (accepted : ConstructorAt schemas constructors world ctor)
    (arity : fields.size = ctor.schema.fields.size)
    (first : state.registers .r8 = fields[0]?.getD 0) (second : state.registers .r9 = fields[1]?.getD 0)
    (room : store.heap.nodes.size - offset < capacity) :
    HeapAt schemas constructors offset (store.allocNode world (.ctorN ctor.cid (fields.map PhysicalScalar.rval))).1
      reserved (allocationState state (store.heap.nodes.size - offset) ctor).words := by
  let output := (store.allocNode world (.ctorN ctor.cid (fields.map PhysicalScalar.rval))).1
  have size : output.heap.nodes.size = store.heap.nodes.size + 1 := by simp [output, IxIR1.Store.allocNode]
  have above := related.extent
  have nextIndex : output.heap.nodes.size - offset = store.heap.nodes.size - offset + 1 := by omega
  apply related.patch (output := output) (location := store.heap.nodes.size) above (by omega) (by omega)
  · intro other bound different
    omega
  · intro other different
    change (store.heap.allocNode world (.ctorN ctor.cid (fields.map PhysicalScalar.rval))).1.get? other = store.heap.get? other
    simp only [IxIR1.Store.allocNode, IxIR1.Store.get?, Array.getElem?_push]
    split <;> first | rfl | simp_all
  · intro other lower different field small
    rw [allocationState_cell, writeCell_other _ _ _ (by omega) small]
  · intro other different member
    exact member
  · have found := IxIR1.Sim.HeapIso.get?_allocNode_new store.heap world (.ctorN ctor.cid (fields.map PhysicalScalar.rval))
    change output.get? store.heap.nodes.size = some _ at found
    change match output.get? store.heap.nodes.size with | some box => _ | none => _
    rw [found]
    exact (accepted.node state _ fields arity first second).words (fun field _ => allocationState_cell _ _ _ _ field)
  · change (allocationState state (store.heap.nodes.size - offset) ctor).words 0 = UInt64.ofNat (32 * (output.heap.nodes.size - offset))
    rw [nextIndex]
    simp [allocationState, counter, writeCell_header _ _ _ (by decide : 0 < headerWords), related.cursor,
      Nat.mul_add, UInt64.ofNat_add, UInt64.ofNat_mul]
  · intro field lower upper
    have small : field < headerWords := by simp only [headerWords]; omega
    have nonzero : field ≠ 0 := by omega
    rw [alloc_counters store world _ field lower upper]
    by_cases two : field = 2
    · subst field
      simp [allocationState, counter, writeCell_header _ _ _ (by decide : 2 < headerWords),
        related.statistics 2 (by omega) (by omega), UInt64.ofNat_add]
    · simp [allocationState, counter, two, nonzero, writeCell_header _ _ _ small,
        related.statistics field lower upper]
  · simp [allocationState, counter, writeCell_header _ _ _ (by decide : 9 < headerWords), related.reservations]

end Compilatrix.X86.PhysicalHeap
