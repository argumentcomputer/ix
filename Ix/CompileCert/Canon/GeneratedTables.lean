import Ix.Compile.Canon.NameTable

namespace Ix.Compile.Canon

theorem nameLookup_some_mem {α : Type} {entries : List (Ix.Name × α)}
    {query : Lean.Name} {value : α} (found : nameLookup entries query = some value) :
    ∃ name, (name,value) ∈ entries ∧ keyName name = query := by
  induction entries with
  | nil => cases found
  | cons pair rest ih =>
    obtain ⟨name,stored⟩ := pair
    simp only [nameLookup] at found
    split at found
    · rename_i equal
      cases found
      exact ⟨name,List.mem_cons_self,equal⟩
    · obtain ⟨name,member,equal⟩ := ih found
      exact ⟨name,List.mem_cons_of_mem _ member,equal⟩

theorem nameLookup_filter_other {α : Type} (entries : List (Ix.Name × α))
    (removed query : Lean.Name) (different : removed ≠ query) :
    nameLookup (entries.filter fun pair => decide (keyName pair.1 ≠ removed)) query =
      nameLookup entries query := by
  induction entries with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨name,value⟩ := pair
    simp only [decide_not] at ih
    by_cases matchesRemoved : keyName name = removed
    · simp [nameLookup, matchesRemoved, different, ih]
    · simp [nameLookup, matchesRemoved, ih]

theorem NameTable.get?_insert {α : Type} (table : NameTable α)
    (name query : Ix.Name) (value : α) :
    (table.insert name value).get? query =
      if keyName name = keyName query then some value else table.get? query := by
  unfold insert
  split
  · simp [get?, nameLookup]
  · by_cases same : keyName name = keyName query
    · simp [get?, nameLookup, same]
    · simp only [get?, nameLookup, same, ↓reduceIte]
      simpa only [decide_not] using nameLookup_filter_other table.entries _ _ same

theorem NameTable.get?_insert_self {α : Type} (table : NameTable α)
    (name : Ix.Name) (value : α) :
    (table.insert name value).get? name = some value := by
  simp [get?_insert]

theorem NameTable.contains_insert {α : Type} (table : NameTable α)
    (name query : Ix.Name) (value : α) :
    (table.insert name value).contains query =
      (decide (keyName name = keyName query) || table.contains query) := by
  unfold contains
  rw [get?_insert]
  split <;> simp_all

theorem NameTable.contains_insert_mono {α : Type} (table : NameTable α)
    (name query : Ix.Name) (value : α) (found : table.contains query = true) :
    (table.insert name value).contains query = true := by
  simp [contains_insert, found]

theorem NameTable.contains_insert_self {α : Type} (table : NameTable α)
    (name : Ix.Name) (value : α) : (table.insert name value).contains name = true := by
  simp [contains_insert]

end Ix.Compile.Canon
