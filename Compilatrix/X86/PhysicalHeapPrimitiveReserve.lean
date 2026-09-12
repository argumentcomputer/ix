import Compilatrix.X86.PhysicalHeapPrimitiveFetch

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros HeapPrimitives
open IxIR2.Eval (Store RVal Credit)

def resetStore (world : Ixon.Owned) (store : Store) : Store :=
  if world == .shared then store.tickResetAttempt.tickHotReset else store

@[simp] theorem resetStore_nodes (world : Ixon.Owned) (store : Store) : (resetStore world store).heap.nodes = store.heap.nodes := by
  cases world <;> rfl

theorem HeapAt.sharedReset {schemas constructors offset store reserved} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words) (world : Ixon.Owned) :
    HeapAt schemas constructors offset (resetStore world store) reserved (HeapPrimitives.sharedReset world state).words := by
  cases world with
  | unique => exact related
  | shared => exact related.resetTicks

theorem ScopeAt.takeNode {layout offset used frame scope values credits state source operand consumed location}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.take source = .ok (.node, operand, consumed))
    (resolved : IxIR2.Eval.resolveAtom values source = .ok (.loc location)) :
    ScopeAt layout offset used frame consumed values credits state ∧
      offset ≤ location ∧ location < offset + used ∧
      HeapCopies.atomValue frame state operand = layout.pointer (location - offset) := by
  obtain ⟨peeked, remaining⟩ := related.take selected
  obtain ⟨value, atValue, represented⟩ := related.peek peeked
  have equal := Except.ok.inj (atValue.symm.trans resolved)
  subst value
  obtain ⟨actual, equal, above, below, pointer⟩ := represented.node_value
  cases equal
  exact ⟨remaining, above, below, pointer⟩

theorem HeapAt.constructorFields {schemas constructors offset store reserved words world ctor location box fields}
    (heap : HeapAt schemas constructors offset store reserved words)
    (accepted : ConstructorAt schemas constructors world ctor)
    (view : IxIR2.Eval.ConstructorView store location world ctor.cid box fields) :
    ∃ nativeFields : Array Word, fields = nativeFields.map PhysicalScalar.rval ∧
      nativeFields.size = ctor.schema.fields.size ∧
      ∀ field (bound : field < nativeFields.size), words (cellSlot (location - offset) (field + 1)) = nativeFields[field] := by
  obtain ⟨found, worldAt, nodeAt⟩ := view.parts
  rcases (heap.live location box found).2 with ⟨content⟩
  have equal := content.node.symm.trans nodeAt
  simp only [IxIR1.Node.ctorN.injEq] at equal
  have schemaAt : schemas world ctor.cid = some content.schema := by
    simpa only [worldAt, equal.1] using content.schemaAt
  have schemaEq := Option.some.inj (schemaAt.symm.trans accepted.schema)
  exact ⟨content.fields, equal.2.symm, content.arity.trans (congrArg (fun schema => schema.fields.size) schemaEq), fun _ bound => content.fieldWord bound⟩

theorem primitive_reserve {schemas constructors layout offset store reserved outReserved frame scope consumed fieldScope nextScope values credits state world ctor source operand location box physicalFields}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (accepted : ConstructorAt schemas constructors world ctor)
    (taken : scope.take source = .ok (.node, operand, consumed))
    (fieldsPushed : consumed.pushFields ctor.schema.fields.size = .ok fieldScope)
    (creditPushed : fieldScope.pushCredit ctor.schema.layout = .ok nextScope)
    (resolved : IxIR2.Eval.resolveAtom values source = .ok (.loc location))
    (view : IxIR2.Eval.ConstructorView store location world ctor.cid box physicalFields)
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (member : location ∈ outReserved) (count : outReserved.length = reserved.length + 1) :
    let after := reserve frame state (location - offset) world ctor operand scope.values.size scope.credits.size
    let output := resetStore world (store.reserve location)
    Executes layout frame (.reserve world ctor operand scope.values.size scope.credits.size) state after ∧
      HeapAt schemas constructors offset output outReserved after.words ∧
      ScopeAt layout offset (output.heap.nodes.size - offset) frame nextScope (values ++ physicalFields)
        (credits.push (some ⟨ctor.schema.layout, .present (some location)⟩)) after := by
  obtain ⟨remaining, above, below, pointer⟩ := locals.takeNode taken resolved
  obtain ⟨nativeFields, fieldsEq, arity, fieldWords⟩ := heap.constructorFields accepted view
  have sameSize : consumed.values.size = scope.values.size := remaining.valueSize.trans locals.valueSize.symm
  have room : scope.values.size + ctor.schema.fields.size ≤ maxValues := by
    unfold Scope.pushFields at fieldsPushed
    split at fieldsPushed
    · simpa only [sameSize] using ‹consumed.values.size + ctor.schema.fields.size ≤ maxValues›
    · contradiction
  have creditRoom : fieldScope.credits.size < maxCredits := by
    unfold Scope.pushCredit at creditPushed
    split at creditPushed <;> first | assumption | contradiction
  have allocated : location - offset < capacity := by have := heap.bounded; have := heap.extent; omega
  let loaded := load frame state operand
  let captured := captureFields frame loaded (location - offset) ctor.schema.fields.size scope.values.size
  let reservedState := counter (tag captured (location - offset) 1) 9 (· + 1)
  let observed := sharedReset world reservedState
  have loadedHeap : HeapAt schemas constructors offset store reserved loaded.words := heap
  have capturedHeap : HeapAt schemas constructors offset store reserved captured.words :=
    loadedHeap.captureFields (index := location - offset) (count := ctor.schema.fields.size) (destination := scope.values.size) separate (by simp only [maxValues, Scalar.maxLocals] at *; omega) accepted.small
  have capturedLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame consumed values credits captured := by
    simpa only [sameSize, captured, loaded, load] using (remaining.setReg .rax (HeapCopies.atomValue frame state operand)).captureFields
      (index := location - offset) (count := ctor.schema.fields.size) (by omega) accepted.small
  have fieldsLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame fieldScope (values ++ physicalFields) credits captured := by
    have native : ∀ field (bound : field < nativeFields.size), captured.words (frame.localIndex (consumed.values.size + field)) = nativeFields[field] := by
      intro field bound
      rw [sameSize]
      change (captureFields frame loaded (location - offset) ctor.schema.fields.size scope.values.size).words _ = _
      rw [captureFields_at frame loaded _ _ _ separate allocated (by simp only [maxValues, Scalar.maxLocals] at *; omega)
        accepted.small (by omega)]
      exact fieldWords field bound
    simpa only [← fieldsEq] using capturedLocals.pushFields (words := nativeFields) (by simpa only [arity] using fieldsPushed) native
  have savedHeap : HeapAt schemas constructors offset (resetStore world (store.reserve location)) outReserved observed.words :=
    (capturedHeap.reserve view.parts.1 kept member count).sharedReset world
  have observedLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame fieldScope (values ++ physicalFields) credits observed :=
    ((fieldsLocals.tag separate allocated 1).counter separate (by decide) (· + 1)).sharedReset separate world
  have creditSize : fieldScope.credits.size = scope.credits.size := observedLocals.creditSize.trans locals.creditSize.symm
  have localBound : creditBase + scope.credits.size < Scalar.maxLocals := by
    simp only [creditBase, maxCredits, Scalar.maxLocals] at *
    omega
  have result : observed.registers .rax = layout.pointer (location - offset) := by
    simp [observed, reservedState, captured, loaded, load, pointer]
  have credit : CreditAt layout offset (store.heap.nodes.size - offset) ctor.schema.layout
      ⟨ctor.schema.layout, .present (some location)⟩ (observed.registers .rax) := by
    exact ⟨⟨location, above, below, rfl, rfl, result⟩⟩
  have storedLocals := observedLocals.storeFreshCredit (observed.registers .rax) creditRoom
  have finalLocals := storedLocals.pushCredit creditPushed (by simpa using credit)
  refine ⟨.reserve state _ world ctor operand _ _ allocated pointer, savedHeap.setStack frame separate localBound _, ?_⟩
  simpa only [reserve, creditSize, resetStore_nodes, Store.reserve, Array.size_setIfInBounds,
    captured, loaded, reservedState, observed, save] using finalLocals

end Compilatrix.X86.PhysicalHeap
