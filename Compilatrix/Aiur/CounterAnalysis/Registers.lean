import Compilatrix.Aiur.CounterAnalysis.Affine
import Compilatrix.Aiur.CounterAnalysis.Effects

namespace Compilatrix.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode

def Extends (before after : Array G) : Prop :=
  ∀ (index : Nat) (value : G), before[index]? = some value → after[index]? = some value

theorem Extends.refl (values : Array G) : Extends values values := fun _ _ read => read

theorem Extends.trans {first second third : Array G}
    (left : Extends first second) (right : Extends second third) : Extends first third :=
  fun index value read => right index value (left index value read)

theorem extends_append (values outputs : Array G) : Extends values (values ++ outputs) := by
  intro index value read
  have bound := (Array.getElem?_eq_some_iff.mp read).1
  rw [Array.getElem?_append_left bound, read]

theorem ReadList.length_eq {values : Array G} {indices : List Nat} {inputs : OracleEval.Values}
    (reads : ReadList values indices inputs) : inputs.length = indices.length := by
  induction reads <;> simp_all

theorem ReadList.get {values : Array G} {indices : List Nat} {inputs : OracleEval.Values}
    (reads : ReadList values indices inputs) {column index : Nat} (selected : indices[column]? = some index) :
    ∃ value, inputs[column]? = some value ∧ values[index]? = some value := by
  induction reads generalizing column with
  | nil => simp at selected
  | @cons head value tail inputs read rest ih =>
      cases column with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; cases selected; exact ⟨value, rfl, read⟩
      | succ column => exact ih selected

theorem Reads.get {values : Array G} {indices : Array Nat} {inputs : OracleEval.Values}
    (reads : Reads values indices inputs) {column index : Nat} (selected : indices[column]? = some index) :
    ∃ value, inputs[column]? = some value ∧ values[index]? = some value :=
  ReadList.get reads (by simpa using selected)

/-- All known analyzer entries denote the corresponding concrete register.
Both arrays have equal size, including unknown outputs. -/
def Registers (abstractValues : Array (Option UnitCounter.Affine)) (values : Array G) : Prop :=
  abstractValues.size = values.size ∧
    ∀ (index : Nat) (expression : UnitCounter.Affine), abstractValues[index]? = some (some expression) →
      ∃ value, values[index]? = some value ∧ Denotes values expression value

theorem Registers.get {abstractValues : Array (Option UnitCounter.Affine)} {values : Array G}
    (sound : Registers abstractValues values) {index : Nat} {value : G} (read : values[index]? = some value) :
    ValueSound values ((abstractValues[index]?).getD none) value := by
  intro expression known
  have present : abstractValues[index]? = some (some expression) := by
    cases found : abstractValues[index]? <;> simp_all
  obtain ⟨actual, actualRead, denotes⟩ := sound.2 index expression present
  have equal := Option.some.inj (actualRead.symm.trans read)
  cases equal
  exact denotes

theorem Registers.append {abstractValues added : Array (Option UnitCounter.Affine)} {values outputs : Array G}
    (sound : Registers abstractValues values) (sameSize : added.size = outputs.size)
    (newSound : ∀ (index : Nat) (expression : UnitCounter.Affine), added[index]? = some (some expression) →
      ∃ value, outputs[index]? = some value ∧ Denotes (values ++ outputs) expression value) :
    Registers (abstractValues ++ added) (values ++ outputs) := by
  refine ⟨by simp [sound.1, sameSize], ?_⟩
  intro index expression known
  by_cases old : index < abstractValues.size
  · rw [Array.getElem?_append_left old] at known
    obtain ⟨value, read, denotes⟩ := sound.2 index expression known
    exact ⟨value, extends_append values outputs index value read, denotes_extend (extends_append values outputs) denotes⟩
  · rw [Array.getElem?_append_right (by omega)] at known
    obtain ⟨value, read, denotes⟩ := newSound _ expression known
    refine ⟨value, ?_, denotes⟩
    rw [Array.getElem?_append_right (by have := sound.1; omega), ← sound.1]
    exact read

theorem Registers.unknown {abstractValues : Array (Option UnitCounter.Affine)} {values outputs : Array G}
    (sound : Registers abstractValues values) :
    Registers (abstractValues ++ Array.replicate outputs.size none) (values ++ outputs) := by
  apply sound.append (by simp)
  intro index expression known
  simp only [Array.getElem?_replicate] at known
  split at known <;> cases known

theorem Registers.push {abstractValues : Array (Option UnitCounter.Affine)} {values : Array G}
    (sound : Registers abstractValues values) (expression : Option UnitCounter.Affine) (value : G)
    (newSound : ValueSound values expression value) :
    Registers (abstractValues.push expression) (values.push value) := by
  rw [Array.push_eq_append, Array.push_eq_append]
  apply sound.append (by rfl)
  intro index affine known
  cases index with
  | zero =>
      simp at known
      exact ⟨value, rfl, denotes_extend (extends_append values #[value]) (newSound affine known)⟩
  | succ index => simp at known

theorem Registers.initial (values : Array G) :
    Registers ((Array.range values.size).map (some ∘ UnitCounter.affVar)) values := by
  refine ⟨by simp, ?_⟩
  intro index expression known
  simp only [Array.getElem?_map, Array.getElem?_range] at known
  split at known
  next bound =>
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq] at known
    cases known
    exact ⟨values[index], Array.getElem?_eq_getElem bound,
      denotes_variable values index values[index] (Array.getElem?_eq_getElem bound)⟩
  next bound => simp at known

theorem Registers.marker {abstractValues : Array (Option UnitCounter.Affine)} {values outputs : Array G}
    (sound : Registers abstractValues values) (column : Nat) :
    Registers (abstractValues ++ (Array.range outputs.size).map (fun index =>
      if index == column then some (UnitCounter.affVar (abstractValues.size + column)) else none))
      (values ++ outputs) := by
  apply sound.append (by simp)
  intro index expression known
  simp only [Array.getElem?_map, Array.getElem?_range] at known
  split at known
  next bound =>
    simp only [Option.map_some, Option.some.injEq] at known
    by_cases selected : index = column
    · subst index
      simp only [BEq.rfl, ↓reduceIte, Option.some.injEq] at known
      cases known
      refine ⟨outputs[column], Array.getElem?_eq_getElem bound, denotes_variable _ _ _ ?_⟩
      rw [sound.1, Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact Array.getElem?_eq_getElem bound
    · simp [selected] at known
  next bound => simp at known

end Compilatrix.Aiur.CounterAnalysis
