import Ix.Compiler.X86.ScalarFunctions

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem array_le_two {α : Type} (array : Array α) (bound : array.size ≤ 2) :
    array = #[] ∨ (∃ first, array = #[first]) ∨ (∃ first second, array = #[first, second]) := by
  rcases array with ⟨list⟩
  cases list with
  | nil => exact .inl rfl
  | cons first rest =>
      cases rest with
      | nil => exact .inr (.inl ⟨first, rfl⟩)
      | cons second rest =>
          cases rest with
          | nil => exact .inr (.inr ⟨first, second, rfl⟩)
          | cons third rest => simp at bound

theorem mapped_arguments {values supplied : Array Word} {arguments : Array Atom}
    (small : arguments.size ≤ 2) (mapped : arguments.mapM (Atom.eval values) = some supplied) :
    supplied.size ≤ 2 ∧
    (arguments[0]?.getD (Atom.constant 0)).eval values = some (supplied[0]?.getD 0) ∧
    (arguments[1]?.getD (Atom.constant 0)).eval values = some (supplied[1]?.getD 0) := by
  rcases array_le_two arguments small with rfl | ⟨first, rfl⟩ | ⟨first, second, rfl⟩
  · simp [Array.mapM_eq_mapM_toList] at mapped
    subst supplied
    simp [Atom.eval]
  · cases evaluated : first.eval values with
    | none => simp [Array.mapM_eq_mapM_toList, evaluated] at mapped
    | some value =>
        simp [Array.mapM_eq_mapM_toList, evaluated] at mapped
        subst supplied
        simp [evaluated, show Atom.eval values (.constant 0) = some 0 from rfl]
  · cases left : first.eval values with
    | none => simp [Array.mapM_eq_mapM_toList, left] at mapped
    | some a =>
        cases right : second.eval values with
        | none => simp [Array.mapM_eq_mapM_toList, left, right] at mapped
        | some b =>
            simp [Array.mapM_eq_mapM_toList, left, right] at mapped
            subst supplied
            simp [left, right]

def argumentsState (state : State) (supplied : Array Word) : State :=
  (state.setReg .rdi (supplied[0]?.getD 0)).setReg .rsi (supplied[1]?.getD 0)

theorem arguments_preserves {layout : Layout} (frame : Frame layout) (locals : Nat) (state : State) (supplied : Array Word) :
    Preserves frame locals state (argumentsState state supplied) :=
  (Preserves.setReg _ _ _ _ _ (by simp)).trans (Preserves.setReg _ _ _ _ _ (by simp))

theorem arguments_ready (state : State) (supplied : Array Word) (small : supplied.size ≤ 2) :
    ArgumentsAt supplied (argumentsState state supplied) := by
  refine ⟨small, fun index bound => ?_⟩
  have alternatives : index = 0 ∨ index = 1 := by omega
  rcases alternatives with rfl | rfl <;> simp [argumentsState, Array.getElem?_eq_getElem bound]

theorem arguments_safeTrace {layout : Layout} {frame : Frame layout} {values supplied : Array Word}
    {state : State} {returns : List ReturnFrame} {rootTop : Nat} {holes : Stream.Holes} {arguments : Array Atom}
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state) (valid : HolesIn layout rootTop holes)
    (small : arguments.size ≤ 2) (mapped : arguments.mapM (Atom.eval values) = some supplied) :
    SafeTrace layout returns [load .rdi (arguments[0]?.getD (.constant 0)), load .rsi (arguments[1]?.getD (.constant 0))]
      state holes (argumentsState state supplied) holes := by
  have found := mapped_arguments small mapped
  have preserved := Preserves.setReg frame values.size state .rdi (supplied[0]?.getD 0) (by simp)
  exact (load_safeTrace framed valuesAt valid .rdi found.2.1).append
    (load_safeTrace (preserved.1.framed framed) (preserved.values valuesAt) valid .rsi found.2.2)

end Ix.Compiler.X86.Scalar
