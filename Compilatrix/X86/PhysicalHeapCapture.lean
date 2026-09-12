import Compilatrix.X86.PhysicalHeapPrimitiveAlloc

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (RVal Credit)

theorem NodeAt.field {schemas constructors words index box cid values field value}
    (related : NodeAt schemas constructors words index box)
    (node : box.node = .ctorN cid values) (found : values[field]? = some value) (small : field < 2)
    {layout : HeapArena.Layout} {offset used : Nat} :
    ValueAt layout offset used .scalar value (words (cellSlot index (field + 1))) := by
  rcases related with ⟨related⟩
  have same := related.node.symm.trans node
  simp only [IxIR1.Node.ctorN.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  simp only [Array.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨word, found, rfl⟩ := found
  have fieldCases : field = 0 ∨ field = 1 := by omega
  rcases fieldCases with rfl | rfl
  · simpa [related.first, found, PhysicalScalar.rval] using (ValueAt.scalar (layout := layout) (offset := offset) (used := used) word)
  · simpa [related.second, found, PhysicalScalar.rval] using (ValueAt.scalar (layout := layout) (offset := offset) (used := used) word)

theorem ScopeAt.pushFields {layout offset used frame scope values credits state next} {words : Array Word}
    (related : ScopeAt layout offset used frame scope values credits state)
    (pushed : scope.pushFields words.size = .ok next)
    (represented : ∀ index (bound : index < words.size), state.words (frame.localIndex (scope.values.size + index)) = words[index]) :
    ScopeAt layout offset used frame next (values ++ words.map PhysicalScalar.rval) credits state := by
  unfold Scope.pushFields at pushed
  split at pushed
  · rename_i room
    cases pushed
    refine ⟨by simpa [Scope.bounded] using And.intro room related.creditBound,
      by simp [related.valueSize], related.creditSize, ?_, related.credits⟩
    intro index kind active
    by_cases old : index < scope.values.size
    · have active : scope.values[index]? = some (some kind) := by simpa [Array.getElem?_append, old] using active
      obtain ⟨value, found, representedValue⟩ := related.values index kind active
      refine ⟨value, ?_, representedValue⟩
      simpa [Array.getElem?_append, ← related.valueSize, old] using found
    · have below := (Array.getElem?_eq_some_iff.mp active).1
      simp only [Array.size_append, Array.size_replicate] at below
      have bound : index - scope.values.size < words.size := by omega
      have position : index = scope.values.size + (index - scope.values.size) := by omega
      have kindEq : kind = .scalar := by
        simpa [Array.getElem?_append, old, Array.getElem?_replicate, bound] using active.symm
      subst kind
      refine ⟨PhysicalScalar.rval words[index - scope.values.size], ?_, ?_⟩
      · simp [Array.getElem?_append, ← related.valueSize, old, bound]
      · have native := represented (index - scope.values.size) bound
        rw [← position] at native
        rw [native]
        exact .scalar _
  · contradiction

theorem captureFields_old {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region) (state : State)
    (index count destination : Nat) {slot : Nat}
    (different : slot ≠ frame.localIndex destination)
    (nextDifferent : slot ≠ frame.localIndex (destination + 1)) :
    (captureFields frame state index count destination).words slot = state.words slot := by
  cases count with
  | zero => rfl
  | succ count => cases count <;> simp [captureFields, capture, different, nextDifferent]

theorem ScopeAt.captureFields {layout offset used frame scope values credits state index count}
    (related : ScopeAt layout offset used frame scope values credits state)
    (room : scope.values.size + count ≤ maxValues) (small : count ≤ 2) :
    ScopeAt layout offset used frame scope values credits (HeapMacros.captureFields frame state index count scope.values.size) := by
  by_cases zero : count = 0
  · subst count; exact related
  apply related.words
  · intro slot kind active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    have different : ∀ delta ≤ 1, frame.localIndex slot ≠ frame.localIndex (scope.values.size + delta) := by
      intro delta deltaBound equal
      have := frame.enough
      simp only [Scalar.Frame.localIndex, maxValues] at *
      omega
    exact captureFields_old frame state _ _ _ (by simpa using different 0 (by omega)) (different 1 (by omega))
  · intro slot id active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    have creditBound := related.creditBound
    have different : ∀ delta < count, frame.localIndex (creditBase + slot) ≠ frame.localIndex (scope.values.size + delta) := by
      intro delta deltaBound equal
      have := frame.enough
      simp only [Scalar.Frame.localIndex, maxValues, creditBase, maxCredits] at *
      omega
    by_cases two : count = 2
    · exact captureFields_old frame state _ _ _ (by simpa using different 0 (by omega)) (different 1 (by omega))
    · have one : count = 1 := by omega
      subst count
      have differentZero : frame.localIndex (creditBase + slot) ≠ frame.localIndex scope.values.size := by
        simpa using different 0 (by omega)
      simp [HeapMacros.captureFields, capture, differentZero]

theorem HeapAt.captureFields {schemas constructors offset store reserved index count destination} {layout : HeapArena.Layout}
    {frame : Scalar.Frame layout.region} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words)
    (separate : heapWords ≤ frame.stackIndex)
    (room : destination + count ≤ Scalar.maxLocals) (small : count ≤ 2) :
    HeapAt schemas constructors offset store reserved (HeapMacros.captureFields frame state index count destination).words := by
  have cases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact related
  · exact related.setStack frame separate (by omega) _
  · exact (related.setStack frame separate (by omega) _).setStack frame separate (by omega) _

theorem captureFields_at {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region) (state : State)
    (index count destination : Nat) (separate : heapWords ≤ frame.stackIndex) (allocated : index < capacity)
    (room : destination + count ≤ Scalar.maxLocals) (small : count ≤ 2) {field : Nat} (bound : field < count) :
    (captureFields frame state index count destination).words (frame.localIndex (destination + field)) =
      state.words (cellSlot index (field + 1)) := by
  have cases : count = 1 ∧ field = 0 ∨ count = 2 ∧ field = 0 ∨ count = 2 ∧ field = 1 := by omega
  have distinct : destination + 2 ≤ Scalar.maxLocals → frame.localIndex destination ≠ frame.localIndex (destination + 1) := by
    intro enough same
    have same := frame.local_injective (by omega) (by omega) same
    omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [captureFields, capture]
  · simp [captureFields, capture, distinct room]
  · have separateCell := frameSlot_ne_cell frame separate (index := destination) (by omega) allocated (by decide : 2 < cellWords)
    simp [captureFields, capture, Ne.symm separateCell]

theorem NodeData.fieldWord {schemas constructors words index box}
    (related : NodeData schemas constructors words index box) {field : Nat} (bound : field < related.fields.size) :
    words (cellSlot index (field + 1)) = related.fields[field] := by
  have small := related.small
  have cases : field = 0 ∨ field = 1 := by omega
  rcases cases with rfl | rfl
  · simpa [Array.getElem?_eq_getElem bound] using related.first
  · simpa [Array.getElem?_eq_getElem bound] using related.second


end Compilatrix.X86.PhysicalHeap
