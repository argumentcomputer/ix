import Compilatrix.X86.PhysicalHeapScope

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (RVal Credit)

theorem ScopeAt.valueBound {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state) : scope.values.size ≤ maxValues :=
  by
  have bound := related.bounded
  simp only [Scope.bounded, Bool.and_eq_true, decide_eq_true_eq] at bound
  exact bound.1

theorem ScopeAt.creditBound {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state) : scope.credits.size ≤ maxCredits :=
  by
  have bound := related.bounded
  simp only [Scope.bounded, Bool.and_eq_true, decide_eq_true_eq] at bound
  exact bound.2

theorem ScopeAt.storeFreshValue {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state) (word : Word)
    (room : scope.values.size < maxValues) :
    ScopeAt layout offset used frame scope values credits
      (state.setWord (frame.localIndex scope.values.size) word) := by
  apply related.words
  · intro index kind active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    have different : frame.localIndex index ≠ frame.localIndex scope.values.size := by
      intro same
      have := frame.local_injective (by simp only [maxValues, Scalar.maxLocals] at *; omega)
        (by simp only [maxValues, Scalar.maxLocals] at *; omega) same
      omega
    simp [different]
  · intro index id active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    have creditBound := related.creditBound
    have different : frame.localIndex (creditBase + index) ≠ frame.localIndex scope.values.size := by
      intro same
      have := frame.local_injective (by simp only [creditBase, maxCredits, Scalar.maxLocals] at *; omega)
        (by simp only [maxValues, Scalar.maxLocals] at *; omega) same
      simp only [creditBase, maxValues] at *
      omega
    simp [different]

theorem ScopeAt.pushValue {layout offset used frame scope values credits state kind next value}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.pushValue kind = .ok next)
    (represented : ValueAt layout offset used kind value (state.words (frame.localIndex scope.values.size))) :
    ScopeAt layout offset used frame next (values.push value) credits state := by
  unfold Scope.pushValue at selected
  split at selected
  · rename_i room
    cases selected
    have bounded : ({ scope with values := scope.values.push (some kind) } : Scope).bounded = true := by
      simp only [Scope.bounded, Array.size_push, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, related.creditBound⟩
    refine ⟨bounded, by simp [related.valueSize], related.creditSize, ?_, related.credits⟩
    intro index actual active
    by_cases old : index < scope.values.size
    · have active : scope.values[index]? = some (some actual) := by
        simpa [Array.getElem?_push, old, Nat.ne_of_lt old] using active
      obtain ⟨existing, found, relatedValue⟩ := related.values index actual active
      exact ⟨existing, by simp [Array.getElem?_push, ← related.valueSize, old, Nat.ne_of_lt old, (Array.getElem?_eq_some_iff.mp found).2], relatedValue⟩
    · have indexEq : index = scope.values.size := by
        have := (Array.getElem?_eq_some_iff.mp active).1
        simp only [Array.size_push] at this
        omega
      subst index
      simp only [Array.getElem?_push_size, Option.some.injEq] at active
      subst actual
      exact ⟨value, by simp [related.valueSize], represented⟩
  · contradiction

theorem ScopeAt.saveValue {layout offset used frame scope values credits state kind next value}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.pushValue kind = .ok next)
    (represented : ValueAt layout offset used kind value (state.registers .rax)) :
    ScopeAt layout offset used frame next (values.push value) credits (HeapPrimitives.save frame state scope.values.size) := by
  have room : scope.values.size < maxValues := by
    unfold Scope.pushValue at selected
    split at selected <;> first | assumption | contradiction
  exact (related.storeFreshValue _ room).pushValue selected (by simpa [HeapPrimitives.save] using represented)

theorem ScopeAt.clearCredit {layout offset used frame scope values credits state} (index : Nat)
    (related : ScopeAt layout offset used frame scope values credits state) :
    ScopeAt layout offset used frame { scope with credits := scope.credits.setIfInBounds index none }
      values (credits.setIfInBounds index none) state := by
  refine ⟨by simpa [Scope.bounded] using related.bounded, related.valueSize,
    by simpa using related.creditSize, related.values, ?_⟩
  intro slot id active
  by_cases same : slot = index
  · subst slot
    simp [Array.getElem?_setIfInBounds] at active
  · have active : scope.credits[slot]? = some (some id) := by
      simpa [Array.getElem?_setIfInBounds, same, Ne.symm same] using active
    obtain ⟨credit, found, represented⟩ := related.credits slot id active
    exact ⟨credit, by simpa [Array.getElem?_setIfInBounds, same, Ne.symm same] using found, represented⟩

theorem ScopeAt.takeCredit {layout offset used frame scope values credits state index id next}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.takeCredit index = .ok (id, next)) :
    ∃ credit, credits[index]? = some (some credit) ∧
      CreditAt layout offset used id credit (state.words (frame.localIndex (creditBase + index))) ∧
      ScopeAt layout offset used frame next values (credits.setIfInBounds index none) state := by
  simp only [Scope.takeCredit] at selected
  split at selected
  · rename_i actual active
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at selected
    rcases selected with ⟨rfl, rfl⟩
    obtain ⟨credit, found, represented⟩ := related.credits index actual active
    exact ⟨credit, found, represented, related.clearCredit index⟩
  · contradiction

theorem ScopeAt.storeFreshCredit {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state) (word : Word)
    (room : scope.credits.size < maxCredits) :
    ScopeAt layout offset used frame scope values credits
      (state.setWord (frame.localIndex (creditBase + scope.credits.size)) word) := by
  apply related.words
  · intro index kind active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    have valueBound := related.valueBound
    have different : frame.localIndex index ≠ frame.localIndex (creditBase + scope.credits.size) := by
      intro same
      have := frame.local_injective (by simp only [maxValues, Scalar.maxLocals] at *; omega)
        (by simp only [creditBase, maxCredits, Scalar.maxLocals] at *; omega) same
      simp only [creditBase, maxValues] at *
      omega
    simp [different]
  · intro index id active
    have bound := (Array.getElem?_eq_some_iff.mp active).1
    have different : frame.localIndex (creditBase + index) ≠ frame.localIndex (creditBase + scope.credits.size) := by
      intro same
      have := frame.local_injective (by simp only [creditBase, maxCredits, Scalar.maxLocals] at *; omega)
        (by simp only [creditBase, maxCredits, Scalar.maxLocals] at *; omega) same
      omega
    simp [different]

theorem ScopeAt.pushCredit {layout offset used frame scope values credits state id next credit}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.pushCredit id = .ok next)
    (represented : CreditAt layout offset used id credit (state.words (frame.localIndex (creditBase + scope.credits.size)))) :
    ScopeAt layout offset used frame next values (credits.push (some credit)) state := by
  unfold Scope.pushCredit at selected
  split at selected
  · rename_i room
    cases selected
    have bounded : ({ scope with credits := scope.credits.push (some id) } : Scope).bounded = true := by
      simp only [Scope.bounded, Array.size_push, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨related.valueBound, by omega⟩
    refine ⟨bounded, related.valueSize, by simp [related.creditSize], related.values, ?_⟩
    intro index actual active
    by_cases old : index < scope.credits.size
    · have active : scope.credits[index]? = some (some actual) := by
        simpa [Array.getElem?_push, old, Nat.ne_of_lt old] using active
      obtain ⟨existing, found, relatedCredit⟩ := related.credits index actual active
      exact ⟨existing, by simp [Array.getElem?_push, ← related.creditSize, old, Nat.ne_of_lt old, (Array.getElem?_eq_some_iff.mp found).2], relatedCredit⟩
    · have indexEq : index = scope.credits.size := by
        have := (Array.getElem?_eq_some_iff.mp active).1
        simp only [Array.size_push] at this
        omega
      subst index
      simp only [Array.getElem?_push_size, Option.some.injEq] at active
      subst actual
      exact ⟨credit, by simp [related.creditSize], represented⟩
  · contradiction

end Compilatrix.X86.PhysicalHeap
