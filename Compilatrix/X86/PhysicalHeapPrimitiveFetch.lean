import Compilatrix.X86.PhysicalHeapCapture

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros HeapPrimitives
open IxIR2.Eval (Store RVal Credit)

theorem ScopeAt.counter {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex) {field : Nat} (bound : field < headerWords) (change : Word → Word) :
    ScopeAt layout offset used frame scope values credits (HeapMacros.counter state field change) :=
  related.heap separate (fun _ above => counter_heap state bound change above)

theorem ScopeAt.tag {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex) {index : Nat} (bound : index < capacity) (word : Word) :
    ScopeAt layout offset used frame scope values credits (HeapMacros.tag state index word) :=
  related.heap separate (fun _ above => tag_heap state bound word above)

theorem ScopeAt.sharedReset {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex) (world : Ixon.Owned) :
    ScopeAt layout offset used frame scope values credits (HeapPrimitives.sharedReset world state) := by
  cases world with
  | unique => exact related
  | shared => exact (related.counter separate (by decide) (· + 1)).counter separate (by decide) (· + 1)

theorem ScopeAt.sharedRelease {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex) (world : Ixon.Owned) :
    ScopeAt layout offset used frame scope values credits (HeapPrimitives.sharedRelease world state) := by
  cases world with
  | unique => exact related
  | shared => exact related.counter separate (by decide) (· + 1)

theorem primitive_fetch {schemas constructors layout offset store reserved frame scope nextScope values credits state source operand field location box cid fields value}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (selected : scope.node source = .ok operand)
    (resolved : IxIR2.Eval.resolveAtom values source = .ok (.loc location))
    (found : store.get? location = some box)
    (node : box.node = .ctorN cid fields) (fieldAt : fields[field]? = some value) (small : field < 2)
    (pushed : scope.pushValue .scalar = .ok nextScope) :
    let after := fetch frame state (location - offset) operand field scope.values.size
    Executes layout frame (.fetch operand field scope.values.size) state after ∧
      HeapAt schemas constructors offset store reserved after.words ∧
      ScopeAt layout offset (store.heap.nodes.size - offset) frame nextScope (values.push value) credits after := by
  obtain ⟨actual, atActual, above, below, pointer⟩ := locals.node selected
  have same : actual = location := IxIR1.RVal.loc.inj (Except.ok.inj (atActual.symm.trans resolved))
  subst actual
  have allocated : location - offset < capacity := by have := heap.bounded; have := heap.extent; omega
  have represented := (heap.live location box found).2.field node fieldAt small (layout := layout)
    (offset := offset) (used := store.heap.nodes.size - offset)
  have room := pushValue_room pushed
  have localBound : scope.values.size < Scalar.maxLocals := by simp only [maxValues, Scalar.maxLocals] at *; omega
  refine ⟨.fetch state _ operand field _ allocated pointer, heap.setStack frame separate localBound _, ?_⟩
  have loaded := (locals.setReg .rax (HeapCopies.atomValue frame state operand)).setReg .rax (state.words (cellSlot (location - offset) (field + 1)))
  simpa [fetch, load, State.setReg_setReg] using loaded.saveValue pushed represented

end Compilatrix.X86.PhysicalHeap
