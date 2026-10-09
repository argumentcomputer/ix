import Ix.Compile.Canon.FreshNames

namespace Ix.Compile.Canon

theorem keyName_mkStr (parent : Ix.Name) (label : String) :
    keyName (Ix.Name.mkStr parent label) = .str (keyName parent) label := rfl


theorem keyName_mkNat (parent : Ix.Name) (index : Nat) :
    keyName (Ix.Name.mkNat parent index) = .num (keyName parent) index := rfl


theorem nameNumeralBound_le {n : Lean.Name} {ns : List Lean.Name} (h : n ∈ ns) :
    nameNumeralBound n ≤ numeralBound ns := by
  induction ns with
  | nil => simp at h
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)


theorem nameNumeralBound_prefix {p n : Lean.Name} (h : p.isPrefixOf n = true) :
    nameNumeralBound p ≤ nameNumeralBound n := by
  induction n with
  | anonymous =>
    have : p = .anonymous := by simpa [Lean.Name.isPrefixOf] using h
    subst p
    exact Nat.le_refl _
  | str n s ih =>
    have h : p = .str n s ∨ p.isPrefixOf n = true := by
      simpa [Lean.Name.isPrefixOf] using h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact ih h
  | num n k ih =>
    have h : p = .num n k ∨ p.isPrefixOf n = true := by
      simpa [Lean.Name.isPrefixOf] using h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih h) (Nat.le_max_left _ _)


theorem freshFamily_preserves {names : List Lean.Name} {parent : Ix.Name} {label : String}
    (h : familyFree names (keyName (Ix.Name.mkStr parent label)) = true) :
    freshFamily names parent label = Ix.Name.mkStr parent label := by
  simp [freshFamily, h]


theorem freshFamily_free (names : List Lean.Name) (parent : Ix.Name) (label : String)
    (n : Lean.Name) (hn : n ∈ names) :
    (keyName (freshFamily names parent label)).isPrefixOf n = false := by
  unfold freshFamily
  dsimp only
  split
  · rename_i h
    have hfree := (List.all_eq_true.mp h) n hn
    simpa using hfree
  · apply Bool.eq_false_iff.mpr
    intro h
    have bound := nameNumeralBound_prefix h
    have upper := nameNumeralBound_le hn
    simp only [keyName_mkStr, keyName_mkNat, nameNumeralBound] at bound
    omega



theorem freshCtorFamily_preserves {forbidden : List Lean.Name} {aux candidate : Ix.Name}
    {index : Nat} {ctorRoots : List Lean.Name} (h : ctorFamilyFree forbidden aux candidate ctorRoots = true) :
    freshCtorFamily forbidden aux candidate index ctorRoots = candidate := by
  simp [freshCtorFamily, h]


theorem freshCtorFamily_free (forbidden : List Lean.Name) (aux candidate : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) (n : Lean.Name) (hn : n ∈ forbidden) :
    (keyName (freshCtorFamily forbidden aux candidate index ctorRoots)).isPrefixOf n = false := by
  unfold freshCtorFamily
  split
  · rename_i h
    have free : familyFree (keyName aux :: forbidden) (keyName candidate) = true := by
      cases hf : familyFree (keyName aux :: forbidden) (keyName candidate) with
      | false => simp [ctorFamilyFree, hf] at h
      | true => rfl
    exact by simpa [familyFree] using (List.all_eq_true.mp free) n (List.mem_cons_of_mem _ hn)
  · apply Bool.eq_false_iff.mpr
    intro h
    have bound := nameNumeralBound_prefix h
    have upper := nameNumeralBound_le
      (show n ∈ keyName aux :: auxSuffixFamilies aux ++ ctorRoots ++ forbidden by simp [hn])
    simp only [keyName_mkStr, keyName_mkNat, nameNumeralBound] at bound
    omega


end Ix.Compile.Canon
