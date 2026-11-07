import IxCC.Src.NatMap

/-! # Lookups after an insertion into a `NatMap` -/

namespace IxCC.Src.NatMap

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

/-! ## Every entry is listed -/

theorem mem_entriesAux_of_acc : ∀ (m : NatMap α) (k w : Nat) (acc : List (Nat × α))
    (x : Nat × α), x ∈ acc → x ∈ entriesAux m k w acc
  | .leaf, _, _, _, _, h => h
  | .node v z o, k, w, acc, x, h => by
    unfold entriesAux
    have h' := mem_entriesAux_of_acc z k (2 * w) _ x
      (mem_entriesAux_of_acc o (k + w) (2 * w) acc x h)
    cases v with
    | none => exact h'
    | some y => exact List.mem_cons_of_mem _ h'

theorem mem_entriesAux : ∀ (m : NatMap α) (j k w : Nat) (acc : List (Nat × α)) (x : α),
    m.get? j = some x → (k + w * j, x) ∈ entriesAux m k w acc
  | .leaf, _, _, _, _, _, h => by simp [get?] at h
  | .node v z o, j, k, w, acc, x, h => by
    unfold entriesAux
    simp only [get?] at h
    by_cases hj : j = 0
    · subst hj
      simp only [BEq.rfl, ↓reduceIte] at h
      subst h
      simp
    · have hj' : (j == 0) = false := by simpa using hj
      simp only [hj', Bool.false_eq_true, ↓reduceIte] at h
      by_cases he : j % 2 = 0
      · have he' : (j % 2 == 0) = true := by simpa using he
        simp only [he', ↓reduceIte] at h
        have hmem := mem_entriesAux z (j / 2) k (2 * w) (entriesAux o (k + w) (2 * w) acc) x h
        have hk : k + 2 * w * (j / 2) = k + w * j := by
          generalize hq : j / 2 = q at *
          have hjq : j = 2 * q := by omega
          subst hjq
          rw [Nat.mul_assoc, Nat.mul_left_comm]
        rw [hk] at hmem
        cases v with
        | none => exact hmem
        | some y => exact List.mem_cons_of_mem _ hmem
      · have he' : (j % 2 == 0) = false := by simpa using he
        simp only [he', Bool.false_eq_true, ↓reduceIte] at h
        have hmem := mem_entriesAux_of_acc z k (2 * w) _ _
          (mem_entriesAux o (j / 2) (k + w) (2 * w) acc x h)
        have hk : k + w + 2 * w * (j / 2) = k + w * j := by
          generalize hq : j / 2 = q at *
          have hjq : j = 2 * q + 1 := by omega
          subst hjq
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm w 2 q]
          omega
        rw [hk] at hmem
        cases v with
        | none => exact hmem
        | some y => exact List.mem_cons_of_mem _ hmem

theorem mem_toList {m : NatMap α} {j : Nat} {x : α} (h : m.get? j = some x) :
    (j, x) ∈ m.toList := by
  have := mem_entriesAux m j 0 1 [] x h
  rwa [Nat.zero_add, Nat.one_mul] at this

/-! ## Building from a list -/

theorem get?_foldl_insert {f : NatMap α → Nat × α → NatMap α}
    (hf : ∀ m p, f m p = m.insert p.1 p.2) :
    ∀ (xs : List (Nat × α)) (m : NatMap α), (xs.map (·.1)).Nodup →
      (∀ k, k ∉ xs.map (·.1) → (xs.foldl f m).get? k = m.get? k) ∧
        ∀ k x, (k, x) ∈ xs → (xs.foldl f m).get? k = some x
  | [], _, _ => ⟨fun _ _ => rfl, fun _ _ h => by cases h⟩
  | (k₀, x₀) :: xs, m, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨h₁, h₂⟩ := get?_foldl_insert hf xs (f m (k₀, x₀)) hn.2
    rw [List.foldl_cons]
    refine ⟨fun k hk => ?_, fun k x hk => ?_⟩
    · rw [List.map_cons, List.mem_cons, not_or] at hk
      rw [h₁ k hk.2, hf, get?_insert_ne _ _ hk.1]
    · rcases List.mem_cons.1 hk with e | hk
      · cases e
        rw [h₁ _ hn.1, hf, get?_insert_self]
      · exact h₂ k x hk

theorem get?_ofList {xs : List (Nat × α)} (hn : (xs.map (·.1)).Nodup) {k : Nat} {x : α}
    (h : (k, x) ∈ xs) : (ofList xs).get? k = some x :=
  (get?_foldl_insert (fun _ _ => rfl) xs .leaf hn).2 k x h

end IxCC.Src.NatMap
