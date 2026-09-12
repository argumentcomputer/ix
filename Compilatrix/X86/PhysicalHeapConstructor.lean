import Compilatrix.X86.PhysicalHeapMemoryUpdate

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (Store)

structure ConstructorAt (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (world : Ixon.Owned) (ctor : Constructor) : Prop where
  schema : schemas world ctor.cid = some ctor.schema
  small : ctor.schema.fields.size ≤ 2
  tag : ∃ index, index < maxConstructors ∧ constructors[index]? = some ctor.cid ∧
    ctor.tag = UInt64.ofNat (index + 2)

theorem constructor_sound {schemas constructors world cid ctor}
    (selected : constructor schemas constructors world cid = .ok ctor) :
    ctor.cid = cid ∧ ConstructorAt schemas constructors world ctor := by
  cases schemaAt : schemas world cid with
  | none => simp [constructor, schemaAt] at selected
  | some schema =>
      by_cases small : schema.fields.size ≤ 2
      · cases registered : constructors.findIdx? (· == cid) with
        | none => simp [constructor, schemaAt, registered, show ¬schema.fields.size > 2 by omega, throw] at selected
        | some index =>
            by_cases bound : index < maxConstructors
            · simp only [constructor, schemaAt, registered, show ¬schema.fields.size > 2 by omega,
                show ¬index >= maxConstructors by omega, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at selected
              subst ctor
              obtain ⟨lt, found, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp registered
              exact ⟨rfl, ⟨schemaAt, small, index, bound, by simpa [lt, beq_iff_eq] using found, rfl⟩⟩
            · simp [constructor, schemaAt, registered, show ¬schema.fields.size > 2 by omega, show index >= maxConstructors by omega, bind, Except.bind, throw] at selected
      · simp [constructor, schemaAt, show schema.fields.size > 2 by omega, bind, Except.bind, throw] at selected

theorem writeCell_at (state : State) (index : Nat) (ctor : Constructor) :
    (writeCell state index ctor).words (cellSlot index 0) = ctor.tag ∧
    (writeCell state index ctor).words (cellSlot index 1) = state.registers .r8 ∧
    (writeCell state index ctor).words (cellSlot index 2) = state.registers .r9 ∧
    (writeCell state index ctor).words (cellSlot index 3) = 0 := by
  simp [writeCell, tag, cellSlot]

theorem writeCell_other (state : State) (index : Nat) (ctor : Constructor) {other field : Nat}
    (different : other ≠ index) (small : field < cellWords) :
    (writeCell state index ctor).words (cellSlot other field) = state.words (cellSlot other field) := by
  have differentField : ∀ target < cellWords, cellSlot other field ≠ cellSlot index target := by
    intro target targetBound equal
    exact different (cellSlot_injective small targetBound equal).1
  simp [writeCell, tag, differentField 0 (by decide), differentField 1 (by decide),
    differentField 2 (by decide), differentField 3 (by decide)]

theorem writeCell_header (state : State) (index : Nat) (ctor : Constructor) {field : Nat}
    (bound : field < headerWords) : (writeCell state index ctor).words field = state.words field := by
  simp [writeCell, tag, Ne.symm (cellSlot_ne_header index (field := 0) bound),
    Ne.symm (cellSlot_ne_header index (field := 1) bound), Ne.symm (cellSlot_ne_header index (field := 2) bound),
    Ne.symm (cellSlot_ne_header index (field := 3) bound)]

theorem ConstructorAt.node {schemas constructors world ctor} (accepted : ConstructorAt schemas constructors world ctor)
    (state : State) (index : Nat) (fields : Array Word)
    (arity : fields.size = ctor.schema.fields.size)
    (first : state.registers .r8 = fields[0]?.getD 0) (second : state.registers .r9 = fields[1]?.getD 0) :
    NodeAt schemas constructors (writeCell state index ctor).words index
      ⟨world, 1, .ctorN ctor.cid (fields.map PhysicalScalar.rval)⟩ := by
  obtain ⟨constructorIndex, bound, registered, tag⟩ := accepted.tag
  have contents := writeCell_at state index ctor
  exact ⟨{
    constructorIndex := constructorIndex
    cid := ctor.cid
    fields := fields
    schema := ctor.schema
    schemaAt := accepted.schema
    arity := arity
    registered := registered
    constructorBound := bound
    small := arity.symm ▸ accepted.small
    unique := rfl
    node := rfl
    tag := contents.1.trans tag
    first := contents.2.1.trans first
    second := contents.2.2.1.trans second
    padding := contents.2.2.2
  }⟩

theorem ScopeAt.heap {layout offset used frame scope values credits state after}
    (related : ScopeAt layout offset used frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (same : ∀ index, heapWords ≤ index → after.words index = state.words index) :
    ScopeAt layout offset used frame scope values credits after := by
  apply related.words
  · intro index kind active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    apply same
    apply frameSlot_above_heap frame separate
    have := related.valueBound
    simp only [maxValues, Scalar.maxLocals] at *
    omega
  · intro index id active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    apply same
    apply frameSlot_above_heap frame separate
    have := related.creditBound
    simp only [maxCredits, creditBase, Scalar.maxLocals] at *
    omega

theorem counter_heap (state : State) {field : Nat} (bound : field < headerWords) (change : Word → Word)
    {index : Nat} (above : heapWords ≤ index) : (counter state field change).words index = state.words index := by
  have different : index ≠ field := by simp only [headerWords, heapWords, capacity, cellWords] at *; omega
  simp [counter, different]

theorem writeCell_heap (state : State) {index : Nat} (bound : index < capacity) (ctor : Constructor)
    {slot : Nat} (above : heapWords ≤ slot) : (writeCell state index ctor).words slot = state.words slot := by
  have different : ∀ field < cellWords, slot ≠ cellSlot index field := by
    intro field small
    have := cellSlot_bound bound small
    omega
  simp [writeCell, tag, different 0 (by decide), different 1 (by decide),
    different 2 (by decide), different 3 (by decide)]

end Compilatrix.X86.PhysicalHeap
