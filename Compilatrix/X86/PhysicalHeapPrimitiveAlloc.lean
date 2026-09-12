import Compilatrix.X86.PhysicalHeapFields

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros HeapPrimitives
open IxIR2.Eval (Store RVal Credit)

theorem pushValue_room {scope : Scope} {kind next} (pushed : scope.pushValue kind = .ok next) : scope.values.size < maxValues := by
  unfold Scope.pushValue at pushed
  split at pushed <;> first | assumption | contradiction

theorem primitive_alloc {schemas constructors layout offset store reserved frame scope nextScope values credits state world ctor}
    {operands : Array Scalar.Atom}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (accepted : ConstructorAt schemas constructors world ctor)
    (arity : operands.size = ctor.schema.fields.size)
    (pushed : scope.pushValue .node = .ok nextScope)
    (room : store.heap.nodes.size - offset < capacity) :
    let words := operands.map (HeapCopies.atomValue frame state)
    let output := (store.allocNode world (.ctorN ctor.cid (words.map PhysicalScalar.rval))).1
    let after := allocate layout frame state (store.heap.nodes.size - offset) ctor operands scope.values.size
    HeapAt schemas constructors offset output reserved after.words ∧
      ScopeAt layout offset (output.heap.nodes.size - offset) frame nextScope
        (values.push (.loc store.heap.nodes.size)) credits after := by
  let words := operands.map (HeapCopies.atomValue frame state)
  let prepared := (fields frame state operands).setReg .rax (layout.pointer (store.heap.nodes.size - offset))
  let middle := allocationState prepared (store.heap.nodes.size - offset) ctor
  have preparedHeap : HeapAt schemas constructors offset store reserved prepared.words := heap
  have storedHeap := preparedHeap.alloc accepted (fields := words) (by simpa [words] using arity)
    (by simpa [prepared, words] using (fields_registers frame state operands).1)
    (by simpa [prepared, words] using (fields_registers frame state operands).2) room
  have preparedLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits prepared :=
    locals.words (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have middleLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits middle :=
    preparedLocals.heap separate (fun _ above => allocationState_heap prepared room ctor above)
  have enough := pushValue_room pushed
  have localBound : scope.values.size < Scalar.maxLocals := by simp only [maxValues, Scalar.maxLocals] at *; omega
  have result : middle.registers .rax = layout.pointer (store.heap.nodes.size - offset) := by
    simp [middle, allocationState, prepared]
  have nextSize : (store.allocNode world (.ctorN ctor.cid (words.map PhysicalScalar.rval))).1.heap.nodes.size - offset =
      store.heap.nodes.size - offset + 1 := by
    have := heap.extent
    simp only [Store.allocNode_heap, IxIR1.Store.allocNode, Array.size_push]
    omega
  have increased := middleLocals.grow (by omega : store.heap.nodes.size - offset ≤ store.heap.nodes.size - offset + 1)
  have node : ValueAt layout offset (store.heap.nodes.size - offset + 1) .node (.loc store.heap.nodes.size)
      (middle.registers .rax) := by
    rw [result]
    exact .node _ heap.extent (by have := heap.extent; omega)
  refine ⟨storedHeap.setStack frame separate localBound _, ?_⟩
  have resultLocals := increased.saveValue pushed node
  simpa only [allocate, allocationState, middle, prepared, words, Store.allocNode_heap, IxIR1.Store.allocNode, Array.size_push,
    show store.heap.nodes.size + 1 - offset = store.heap.nodes.size - offset + 1 by have := heap.extent; omega] using resultLocals

theorem primitive_move {schemas constructors layout offset store reserved frame scope consumed nextScope values credits state source kind operand}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (taken : scope.take source = .ok (kind, operand, consumed))
    (pushed : consumed.pushValue kind = .ok nextScope) :
    ∃ value, IxIR2.Eval.resolveAtom values source = .ok value ∧
      HeapAt schemas constructors offset store reserved (save frame (load frame state operand) scope.values.size).words ∧
      ScopeAt layout offset (store.heap.nodes.size - offset) frame nextScope (values.push value) credits
        (save frame (load frame state operand) scope.values.size) := by
  obtain ⟨peeked, remaining⟩ := locals.take taken
  obtain ⟨value, resolved, represented⟩ := locals.peek peeked
  have size : consumed.values.size = scope.values.size := remaining.valueSize.trans locals.valueSize.symm
  have enough := pushValue_room pushed
  have bound : scope.values.size < Scalar.maxLocals := by simp only [maxValues, Scalar.maxLocals] at *; omega
  refine ⟨value, resolved, heap.setStack frame separate bound _, ?_⟩
  have loaded := remaining.setReg .rax (HeapCopies.atomValue frame state operand)
  simpa only [size, HeapPrimitives.load] using loaded.saveValue pushed (by simpa [load] using represented)

end Compilatrix.X86.PhysicalHeap
