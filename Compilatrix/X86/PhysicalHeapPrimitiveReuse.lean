import Compilatrix.X86.PhysicalHeapPrimitiveReserve

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros HeapPrimitives
open IxIR2.Eval (Store RVal Credit)

theorem ScopeAt.takeCreditLocation {layout offset used frame scope values credits state index id consumed credit location}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.takeCredit index = .ok (id, consumed))
    (found : credits[index]? = some (some credit))
    (present : credit.presence = .present (some location)) :
    ScopeAt layout offset used frame consumed values (credits.setIfInBounds index none) state ∧
      offset ≤ location ∧ location < offset + used ∧
      state.words (frame.localIndex (creditBase + index)) = layout.pointer (location - offset) := by
  obtain ⟨actual, actualAt, ⟨represented⟩, remaining⟩ := related.takeCredit selected
  have same := Option.some.inj (Option.some.inj (actualAt.symm.trans found))
  subst actual
  have locationEq : represented.location = location := by
    exact Option.some.inj (IxIR2.Eval.CreditPresence.present.inj (represented.presence.symm.trans present))
  exact ⟨remaining, locationEq ▸ represented.above, locationEq ▸ represented.below, locationEq ▸ represented.pointer⟩

theorem primitive_reuse {schemas constructors layout offset store output reserved outReserved frame scope consumed nextScope values credits state world ctor index credit location}
    {operands : Array Scalar.Atom}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (accepted : ConstructorAt schemas constructors world ctor)
    (arity : operands.size = ctor.schema.fields.size)
    (taken : scope.takeCredit index = .ok (ctor.schema.layout, consumed))
    (pushed : consumed.pushValue .node = .ok nextScope)
    (found : credits[index]? = some (some credit))
    (present : credit.presence = .present (some location))
    (reused : store.reuseReservation location world
      (.ctorN ctor.cid ((operands.map (HeapCopies.atomValue frame state)).map PhysicalScalar.rval))
      ctor.schema.fields.size = .ok output)
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (count : outReserved.length + 1 = reserved.length) :
    let after := reuse frame state (location - offset) ctor index operands scope.values.size
    Executes layout frame (.reuse world ctor index operands scope.values.size) state after ∧
      HeapAt schemas constructors offset output outReserved after.words ∧
      ScopeAt layout offset (output.heap.nodes.size - offset) frame nextScope (values.push (.loc location))
        (credits.setIfInBounds index none) after := by
  obtain ⟨remaining, above, below, pointer⟩ := locals.takeCreditLocation taken found present
  have allocated : location - offset < capacity := by have := heap.bounded; have := heap.extent; omega
  let words := operands.map (HeapCopies.atomValue frame state)
  let prepared := creditState frame (fields frame state operands) index
  let middle := reuseState prepared (location - offset) ctor
  have preparedHeap : HeapAt schemas constructors offset store reserved prepared.words := heap
  have middleHeap : HeapAt schemas constructors offset output outReserved middle.words :=
    preparedHeap.reuse accepted above reused (fields := words) (by simpa [words] using arity)
      (by simpa [prepared, creditState, words] using (fields_registers frame state operands).1)
      (by simpa [prepared, creditState, words] using (fields_registers frame state operands).2) kept count
  have preparedLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame consumed values
      (credits.setIfInBounds index none) prepared := remaining.words (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have middleLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame consumed values
      (credits.setIfInBounds index none) middle :=
    preparedLocals.heap separate (fun _ upper => reuseState_heap prepared allocated ctor upper)
  have valueSize : consumed.values.size = scope.values.size := remaining.valueSize.trans locals.valueSize.symm
  have room := pushValue_room pushed
  have localBound : scope.values.size < Scalar.maxLocals := by simp only [maxValues, Scalar.maxLocals] at *; omega
  have nodes := (reuse_parts reused).2.1
  have size : output.heap.nodes.size = store.heap.nodes.size := by simp [nodes]
  have result : middle.registers .rax = layout.pointer (location - offset) := by
    simp [middle, reuseState, prepared, creditState, fields, pointer]
  have node : ValueAt layout offset (store.heap.nodes.size - offset) .node (.loc location) (middle.registers .rax) := by
    rw [result]
    exact .node _ above below
  refine ⟨.reuse state _ world ctor index operands _ allocated pointer, middleHeap.setStack frame separate localBound _, ?_⟩
  simpa only [reuse, reuseState, middle, prepared, valueSize, size] using middleLocals.saveValue pushed node

end Compilatrix.X86.PhysicalHeap
