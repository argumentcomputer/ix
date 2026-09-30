import Compilatrix.Src.NatMap

/-! # Lookups after an insertion into a `NatMap` -/

namespace Compilatrix.Src.NatMap

variable {α : Type}

theorem get?_parts (m : NatMap α) (k : Nat) :
    m.get? k = if k == 0 then m.parts.1 else if k % 2 == 0 then m.parts.2.1.get? (k / 2)
      else m.parts.2.2.get? (k / 2) := by
  cases m with
  | leaf => simp [get?, parts]
  | node v z o => rfl

theorem get?_setF : ∀ (fuel : Nat) (m : NatMap α) (k : Nat) (x : Option α) (k' : Nat),
    k < fuel → (setF fuel m k x).get? k' = if k' = k then x else m.get? k'
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, m, k, x, k', h => by
    rw [get?_parts m k']
    unfold setF
    obtain ⟨v, z, o⟩ := m.parts
    dsimp only
    by_cases hk : k = 0
    · subst hk
      simp only [BEq.rfl, ↓reduceIte, get?]
      by_cases hk' : k' = 0
      · simp [hk']
      · simp [hk']
    · have hk0 : (k == 0) = false := by simpa using hk
      by_cases he : k % 2 = 0
      · have he' : (k % 2 == 0) = true := by simpa using he
        simp only [hk0, he', Bool.false_eq_true, ↓reduceIte, get?]
        rw [get?_setF fuel z (k / 2) x (k' / 2) (by omega)]
        by_cases hk' : k' = 0
        · simp [hk', Ne.symm hk]
        · by_cases he2 : k' % 2 = 0
          · have : (k' / 2 = k / 2) ↔ k' = k := by omega
            simp [hk', he2, this]
          · have : k' ≠ k := by omega
            simp [hk', he2, this]
      · have he' : (k % 2 == 0) = false := by simpa using he
        simp only [hk0, he', Bool.false_eq_true, ↓reduceIte, get?]
        rw [get?_setF fuel o (k / 2) x (k' / 2) (by omega)]
        by_cases hk' : k' = 0
        · simp [hk', Ne.symm hk]
        · by_cases he2 : k' % 2 = 0
          · have : k' ≠ k := by omega
            simp [hk', he2, this]
          · have : (k' / 2 = k / 2) ↔ k' = k := by omega
            simp [hk', he2, this]

theorem get?_insert (m : NatMap α) (k : Nat) (x : α) (k' : Nat) :
    (m.insert k x).get? k' = if k' = k then some x else m.get? k' :=
  get?_setF (k + 1) m k (some x) k' (Nat.lt_succ_self k)

theorem get?_insert_self (m : NatMap α) (k : Nat) (x : α) : (m.insert k x).get? k = some x := by
  simp [get?_insert]

theorem get?_insert_ne (m : NatMap α) {k k' : Nat} (x : α) (h : k' ≠ k) :
    (m.insert k x).get? k' = m.get? k' := by
  simp [get?_insert, h]

end Compilatrix.Src.NatMap
