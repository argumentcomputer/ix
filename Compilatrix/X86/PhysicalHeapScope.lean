import Compilatrix.X86.PhysicalHeapMemory

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (RVal Credit)

/-- Only available owners are related. Consumed physical registers keep their
old bits, but the selector cannot use those registers again. -/
structure ScopeAt (layout : HeapArena.Layout) (offset used : Nat)
    (frame : Scalar.Frame layout.region) (scope : Scope) (values : Array RVal)
    (credits : Array (Option Credit)) (state : State) : Prop where
  bounded : scope.bounded = true
  valueSize : scope.values.size = values.size
  creditSize : scope.credits.size = credits.size
  values : ∀ index kind, scope.values[index]? = some (some kind) →
    ∃ value, values[index]? = some value ∧
      ValueAt layout offset used kind value (state.words (frame.localIndex index))
  credits : ∀ index id, scope.credits[index]? = some (some id) →
    ∃ credit, credits[index]? = some (some credit) ∧
      CreditAt layout offset used id credit (state.words (frame.localIndex (creditBase + index)))

theorem ScopeAt.grow {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state)
    {larger : Nat} (bound : used ≤ larger) : ScopeAt layout offset larger frame scope values credits state := by
  refine ⟨related.bounded, related.valueSize, related.creditSize, ?_, ?_⟩
  · intro index kind active
    obtain ⟨value, found, represented⟩ := related.values index kind active
    exact ⟨value, found, represented.grow bound⟩
  · intro index id active
    obtain ⟨credit, found, represented⟩ := related.credits index id active
    exact ⟨credit, found, represented.grow bound⟩

theorem ScopeAt.words {layout offset used frame scope values credits state after}
    (related : ScopeAt layout offset used frame scope values credits state)
    (sameValue : ∀ index kind, scope.values[index]? = some (some kind) →
      after.words (frame.localIndex index) = state.words (frame.localIndex index))
    (sameCredit : ∀ index id, scope.credits[index]? = some (some id) →
      after.words (frame.localIndex (creditBase + index)) = state.words (frame.localIndex (creditBase + index))) :
    ScopeAt layout offset used frame scope values credits after := by
  refine ⟨related.bounded, related.valueSize, related.creditSize, ?_, ?_⟩
  · intro index kind active
    rw [sameValue index kind active]
    exact related.values index kind active
  · intro index id active
    rw [sameCredit index id active]
    exact related.credits index id active

theorem ScopeAt.setReg {layout offset used frame scope values credits state}
    (related : ScopeAt layout offset used frame scope values credits state) (register : GPR) (word : Word) :
    ScopeAt layout offset used frame scope values credits (state.setReg register word) :=
  related.words (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem ScopeAt.peek {layout offset used frame scope values credits state source kind operand}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.peek source = .ok (kind, operand)) :
    ∃ value, IxIR2.Eval.resolveAtom values source = .ok value ∧
      ValueAt layout offset used kind value (HeapCopies.atomValue frame state operand) := by
  cases source with
  | reg index =>
      simp only [Scope.peek] at selected
      split at selected
      · rename_i actual found
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at selected
        rcases selected with ⟨rfl, rfl⟩
        obtain ⟨value, valueAt, represented⟩ := related.values index actual found
        exact ⟨value, by simp [IxIR2.Eval.resolveAtom, valueAt], represented⟩
      · contradiction
  | erased =>
      simp only [Scope.peek, Except.ok.injEq, Prod.mk.injEq] at selected
      rcases selected with ⟨rfl, rfl⟩
      exact ⟨.erased, rfl, .erased⟩
  | lit literal =>
      cases literal with
      | nat number =>
          simp only [Scope.peek] at selected
          split at selected
          · rename_i word encoded
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at selected
            rcases selected with ⟨rfl, rfl⟩
            rw [← ExactNat.encode_some_iff.mp encoded]
            exact ⟨_, rfl, .scalar word⟩
          · contradiction
      | _ => contradiction

theorem ScopeAt.scalar {layout offset used frame scope values credits state source operand}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.scalar source = .ok operand) :
    IxIR2.Eval.resolveAtom values source = .ok (PhysicalScalar.rval (HeapCopies.atomValue frame state operand)) := by
  unfold Scope.scalar at selected
  cases found : scope.peek source with
  | error error => simp [found, bind, Except.bind] at selected
  | ok result =>
      rcases result with ⟨kind, actual⟩
      cases kind <;> simp only [found, bind, Except.bind] at selected
      · simp only [pure, Except.pure, Except.ok.injEq] at selected
        subst actual
        obtain ⟨value, resolved, represented⟩ := related.peek found
        exact resolved.trans (congrArg Except.ok represented.scalar_value)
      all_goals contradiction

theorem ScopeAt.node {layout offset used frame scope values credits state source operand}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.node source = .ok operand) :
    ∃ location, IxIR2.Eval.resolveAtom values source = .ok (.loc location) ∧
      offset ≤ location ∧ location < offset + used ∧
      HeapCopies.atomValue frame state operand = layout.pointer (location - offset) := by
  unfold Scope.node at selected
  cases found : scope.peek source with
  | error error => simp [found, bind, Except.bind] at selected
  | ok result =>
      rcases result with ⟨kind, actual⟩
      cases kind <;> simp only [found, bind, Except.bind] at selected
      case node =>
        simp only [pure, Except.pure, Except.ok.injEq] at selected
        subst actual
        obtain ⟨value, resolved, represented⟩ := related.peek found
        obtain ⟨location, rfl, above, below, pointer⟩ := represented.node_value
        exact ⟨location, resolved, above, below, pointer⟩
      all_goals contradiction

theorem ScopeAt.clearValue {layout offset used frame scope values credits state} (index : Nat)
    (related : ScopeAt layout offset used frame scope values credits state) :
    ScopeAt layout offset used frame { scope with values := scope.values.setIfInBounds index none } values credits state := by
  refine ⟨by simpa [Scope.bounded] using related.bounded, by simpa using related.valueSize, related.creditSize, ?_, related.credits⟩
  intro slot kind active
  by_cases same : slot = index
  · subst slot
    simp [Array.getElem?_setIfInBounds] at active
  · apply related.values slot kind
    simpa [Array.getElem?_setIfInBounds, same, Ne.symm same] using active

theorem ScopeAt.take {layout offset used frame scope values credits state source kind operand next}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.take source = .ok (kind, operand, next)) :
    scope.peek source = .ok (kind, operand) ∧
      ScopeAt layout offset used frame next values credits state := by
  unfold Scope.take at selected
  cases found : scope.peek source with
  | error error => simp [found, bind, Except.bind] at selected
  | ok result =>
      rcases result with ⟨actual, value⟩
      cases actual <;> cases source <;>
        simp only [found, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at selected
      all_goals rcases selected with ⟨rfl, rfl, rfl⟩
      all_goals first | exact ⟨rfl, related⟩ | exact ⟨rfl, related.clearValue _⟩

end Compilatrix.X86.PhysicalHeap
