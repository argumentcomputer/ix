import Aiur.Generic.AST
import Mathlib.Data.List.Forall2

namespace Aiur.Generic

/-- Binding layouts determine names even for unchecked patterns. -/
theorem reorderBindings_names {names positions} {bindings result : List (String × V)}
    (ordered : reorderBindings names positions bindings = some result) :
    result.map Prod.fst = names := by
  induction names generalizing positions result with
  | nil => cases positions <;> simp_all [reorderBindings]
  | cons name names ih =>
      cases positions with
      | nil => simp [reorderBindings] at ordered
      | cons index positions =>
          cases found : bindings[index]? with
          | none => simp [reorderBindings, found] at ordered
          | some pair =>
              cases tail : reorderBindings names positions bindings with
              | none => simp [reorderBindings, found, tail] at ordered
              | some rest =>
                  simp [reorderBindings, found, tail] at ordered
                  subst result
                  simp only [List.map_cons, ih tail]

/-- Pattern renaming changes names, while recorded positions stay fixed. -/
theorem reorderBindings_rename (rename : String → String) (names positions)
    (bindings : List (String × V)) :
    reorderBindings (names.map rename) positions
        (bindings.map fun pair => (rename pair.1, pair.2)) =
      (reorderBindings names positions bindings).map
        (List.map fun pair => (rename pair.1, pair.2)) := by
  induction names generalizing positions with
  | nil => cases positions <;> rfl
  | cons name names ih =>
      cases positions with
      | nil => rfl
      | cons index positions =>
          simp only [List.map_cons, reorderBindings, List.getElem?_map, ih]
          cases bindings[index]? <;> cases reorderBindings names positions bindings <;> rfl

/-- Changing only selected output names commutes with gathering values. -/
theorem reorderBindings_mapNames (rename : String → String) (names positions)
    (bindings : List (String × V)) :
    reorderBindings (names.map rename) positions bindings =
      (reorderBindings names positions bindings).map
        (List.map fun pair => (rename pair.1, pair.2)) := by
  induction names generalizing positions with
  | nil => cases positions <;> rfl
  | cons name names ih =>
      cases positions with
      | nil => rfl
      | cons index positions =>
          simp only [List.map_cons, reorderBindings, ih]
          cases bindings[index]? <;> cases reorderBindings names positions bindings <;> rfl

/-- Applying a value operation commutes with positional binding alignment. -/
theorem reorderBindings_mapValues (f : V → W) (names positions)
    (bindings : List (String × V)) :
    reorderBindings names positions (bindings.map fun pair => (pair.1, f pair.2)) =
      (reorderBindings names positions bindings).map
        (List.map fun pair => (pair.1, f pair.2)) := by
  induction names generalizing positions with
  | nil => cases positions <;> rfl
  | cons name names ih =>
      cases positions with
      | nil => rfl
      | cons index positions =>
          simp only [reorderBindings, List.getElem?_map, ih]
          cases bindings[index]? <;> cases reorderBindings names positions bindings <;> rfl

theorem reorderBindings_good {P : V → Prop} {names positions}
    {bindings result : List (String × V)}
    (good : ∀ b ∈ bindings, P b.2)
    (ordered : reorderBindings names positions bindings = some result) :
    ∀ b ∈ result, P b.2 := by
  induction names generalizing positions result with
  | nil =>
      cases positions <;> simp_all [reorderBindings]
  | cons name names ih =>
      cases positions with
      | nil => simp [reorderBindings] at ordered
      | cons index positions =>
          cases found : bindings[index]? with
          | none => simp [reorderBindings, found] at ordered
          | some pair =>
              cases tail : reorderBindings names positions bindings with
              | none => simp [reorderBindings, found, tail] at ordered
              | some rest =>
                  simp [reorderBindings, found, tail] at ordered
                  subst result
                  intro b member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact good pair (List.mem_of_getElem? found)
                  · exact ih tail b member

end Aiur.Generic
