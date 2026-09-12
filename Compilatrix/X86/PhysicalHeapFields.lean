import Compilatrix.X86.PhysicalHeapReuse

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros
open IxIR2.Eval (RVal Credit)

theorem ScopeAt.scalars {layout offset used frame scope values credits state arguments operands}
    (related : ScopeAt layout offset used frame scope values credits state)
    (small : arguments.size ≤ 2)
    (selected : arguments.mapM scope.scalar = .ok operands) :
    operands.size = arguments.size ∧
      IxIR2.Eval.resolveAtoms values arguments =
        .ok ((operands.map (HeapCopies.atomValue frame state)).map PhysicalScalar.rval) := by
  rcases Scalar.array_le_two arguments small with rfl | ⟨first, rfl⟩ | ⟨first, second, rfl⟩
  · simp [Functor.map, Except.map, pure, Except.pure, Array.mapM_eq_mapM_toList] at selected
    subst operands
    exact ⟨rfl, by simp [IxIR2.Eval.resolveAtoms, pure, Except.pure]⟩
  · cases found : scope.scalar first with
    | error error => simp [Functor.map, Except.map, pure, Except.pure, Array.mapM_eq_mapM_toList, found, bind, Except.bind] at selected
    | ok operand =>
        simp [Functor.map, Except.map, pure, Except.pure, Array.mapM_eq_mapM_toList, found, bind, Except.bind] at selected
        subst operands
        exact ⟨rfl, by simp [IxIR2.Eval.resolveAtoms, Functor.map, Except.map, pure, Except.pure, bind, Except.bind, related.scalar found]⟩
  · cases firstAt : scope.scalar first with
    | error error => simp [Functor.map, Except.map, pure, Except.pure, Array.mapM_eq_mapM_toList, firstAt, bind, Except.bind] at selected
    | ok left =>
        cases secondAt : scope.scalar second with
        | error error => simp [Functor.map, Except.map, pure, Except.pure, Array.mapM_eq_mapM_toList, firstAt, secondAt, bind, Except.bind] at selected
        | ok right =>
            simp [Functor.map, Except.map, pure, Except.pure, Array.mapM_eq_mapM_toList, firstAt, secondAt, bind, Except.bind] at selected
            subst operands
            exact ⟨rfl, by simp [IxIR2.Eval.resolveAtoms, Functor.map, Except.map, pure, Except.pure, bind, Except.bind, related.scalar firstAt, related.scalar secondAt]⟩

theorem fieldValue_map {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) (index : Nat) :
    fieldValue frame state arguments index = (arguments.map (HeapCopies.atomValue frame state))[index]?.getD 0 := by
  cases found : arguments[index]? <;> simp [fieldValue, Array.getElem?_map, found, HeapCopies.atomValue]

theorem fields_registers {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) :
    (HeapMacros.fields frame state arguments).registers .r8 = (arguments.map (HeapCopies.atomValue frame state))[0]?.getD 0 ∧
    (HeapMacros.fields frame state arguments).registers .r9 = (arguments.map (HeapCopies.atomValue frame state))[1]?.getD 0 := by
  simp [HeapMacros.fields, fieldValue_map]

end Compilatrix.X86.PhysicalHeap
