import Ix.Compile.Verify.UniformRevisible

/-!
# Stage 4: the tie order of sets

`setPrec` on strictly increasing sets: `a` precedes `b` exactly when the
smallest term of their symmetric difference is in `b`. It is a strict total
order on such sets, and it is monotone under unions of sets from disjoint
universes.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact

/-- `z` is the first difference of `X` and `Y`, and it is in `Y`. -/
def FirstIn (X Y : List Nat) (z : Nat) : Prop :=
  z ∈ Y ∧ z ∉ X ∧ ∀ u, u < z → (u ∈ X ↔ u ∈ Y)

theorem lexLt_iff : ∀ (X Y : List Nat), X.Pairwise (· < ·) → Y.Pairwise (· < ·) →
    (List.compareLex compareDesc X Y = .lt ↔ ∃ z, FirstIn X Y z)
  | [], [], _, _ => by simp [List.compareLex_nil_nil, FirstIn]
  | [], y :: ys, _, hY => by
    rw [List.compareLex_nil_cons]
    simp only [true_iff]
    refine ⟨y, List.mem_cons_self, by simp, fun u hu => ?_⟩
    simp only [List.not_mem_nil, false_iff, List.mem_cons, not_or]
    refine ⟨by omega, fun hm => ?_⟩
    have := (List.pairwise_cons.mp hY).1 u hm
    omega
  | x :: xs, [], _, _ => by
    rw [List.compareLex_cons_nil]
    simp [FirstIn]
  | x :: xs, y :: ys, hX, hY => by
    rw [List.compareLex_cons_cons]
    have hXs := (List.pairwise_cons.mp hX)
    have hYs := (List.pairwise_cons.mp hY)
    rw [show compareDesc x y = compare y x from rfl]
    rcases Nat.lt_trichotomy y x with hyx | rfl | hxy
    · rw [Nat.compare_eq_lt.mpr hyx]
      simp only [Ordering.lt_then, true_iff]
      refine ⟨y, List.mem_cons_self, fun hm => ?_, fun u hu => ?_⟩
      · rcases List.mem_cons.mp hm with h | h
        · omega
        · have := hXs.1 y h; omega
      · constructor
        · intro hm
          rcases List.mem_cons.mp hm with h | h
          · omega
          · have := hXs.1 u h; omega
        · intro hm
          rcases List.mem_cons.mp hm with h | h
          · omega
          · have := hYs.1 u h; omega
    · rw [Nat.compare_eq_eq.mpr rfl, Ordering.eq_then, lexLt_iff xs ys hXs.2 hYs.2]
      constructor
      · rintro ⟨z, hz, hzx, hagree⟩
        refine ⟨z, List.mem_cons_of_mem _ hz, fun hm => ?_, fun u hu => ?_⟩
        · rcases List.mem_cons.mp hm with h | h
          · have := hYs.1 z hz; omega
          · exact hzx h
        · simp only [List.mem_cons]
          by_cases hux : u = y
          · simp [hux]
          · simp only [hux, false_or]; exact hagree u hu
      · rintro ⟨z, hz, hzx, hagree⟩
        have hzy : z ≠ y := fun h => hzx (h ▸ List.mem_cons_self)
        refine ⟨z, ?_, fun h => hzx (List.mem_cons_of_mem _ h), fun u hu => ?_⟩
        · rcases List.mem_cons.mp hz with h | h
          · exact absurd h hzy
          · exact h
        · have := hagree u hu
          simp only [List.mem_cons] at this
          by_cases hux : u = y
          · subst hux
            constructor
            · intro h; have := hXs.1 u h; omega
            · intro h; have := hYs.1 u h; omega
          · simpa [hux] using this
    · rw [Nat.compare_eq_gt.mpr hxy]
      simp only [Ordering.gt_then]
      simp only [reduceCtorEq, false_iff, not_exists]
      rintro z ⟨hz, hzx, hagree⟩
      have hyz : y ≤ z := by
        rcases List.mem_cons.mp hz with h | h
        · omega
        · have := hYs.1 z h; omega
      have := (hagree x (by omega)).mp List.mem_cons_self
      rcases List.mem_cons.mp this with h | h
      · omega
      · have := hYs.1 x h; omega

/-! ## The tie order on sorted sets -/

/-- `X` strictly precedes `Y`: the first difference is in `Y`. -/
def PrecL (X Y : List Nat) : Prop := ∃ z, FirstIn X Y z

/-- `X` precedes `Y` or has the same terms. -/
def LeL (X Y : List Nat) : Prop := (∀ u, u ∈ X ↔ u ∈ Y) ∨ PrecL X Y

/-- Sorted lists with the same terms are equal. -/
theorem sorted_eq_of_mem {X Y : List Nat} (hX : X.Pairwise (· < ·)) (hY : Y.Pairwise (· < ·))
    (h : ∀ u, u ∈ X ↔ u ∈ Y) : X = Y := by
  apply List.Perm.eq_of_pairwise (le := fun a b => a < b) (fun a b _ _ h1 h2 => by omega) hX hY
  exact (List.perm_ext_iff_of_nodup (hX.imp Nat.ne_of_lt) (hY.imp Nat.ne_of_lt)).mpr h

theorem precL_irrefl (X : List Nat) : ¬ PrecL X X := fun ⟨_, h1, h2, _⟩ => h2 h1

theorem precL_trans {X Y Z : List Nat} (h1 : PrecL X Y) (h2 : PrecL Y Z) : PrecL X Z := by
  obtain ⟨a, haY, haX, hXY⟩ := h1
  obtain ⟨b, hbZ, hbY, hYZ⟩ := h2
  rcases Nat.lt_trichotomy a b with hab | rfl | hba
  · refine ⟨a, (hYZ a hab).mp haY, haX, fun u hu => (hXY u hu).trans (hYZ u (by omega))⟩
  · exact absurd haY hbY
  · refine ⟨b, hbZ, fun hbX => hbY ((hXY b hba).mp hbX), fun u hu =>
      (hXY u (by omega)).trans (hYZ u hu)⟩

theorem leL_refl (X : List Nat) : LeL X X := Or.inl fun _ => Iff.rfl

/-- The tie order depends only on membership. -/
theorem precL_congr {X X' Y Y' : List Nat} (hX : ∀ u, u ∈ X ↔ u ∈ X') (hY : ∀ u, u ∈ Y ↔ u ∈ Y')
    (h : PrecL X Y) : PrecL X' Y' := by
  obtain ⟨z, hzY, hzX, hag⟩ := h
  exact ⟨z, (hY z).mp hzY, fun h => hzX ((hX z).mpr h), fun u hu =>
    ((hX u).symm.trans (hag u hu)).trans (hY u)⟩

theorem leL_trans {X Y Z : List Nat} (h1 : LeL X Y) (h2 : LeL Y Z) : LeL X Z := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl fun u => (h1 u).trans (h2 u)
  · exact Or.inr (precL_congr (fun u => (h1 u).symm) (fun _ => Iff.rfl) h2)
  · exact Or.inr (precL_congr (fun _ => Iff.rfl) h2 h1)
  · exact Or.inr (precL_trans h1 h2)

theorem leL_congr {X X' Y Y' : List Nat} (hX : ∀ u, u ∈ X ↔ u ∈ X') (hY : ∀ u, u ∈ Y ↔ u ∈ Y')
    (h : LeL X Y) : LeL X' Y' := by
  rcases h with h | h
  · exact Or.inl fun u => ((hX u).symm.trans (h u)).trans (hY u)
  · exact Or.inr (precL_congr hX hY h)

/-- **The tie order is total** on sorted lists. -/
theorem precL_total {X Y : List Nat} (hX : X.Pairwise (· < ·)) (hY : Y.Pairwise (· < ·))
    (hne : X ≠ Y) : PrecL X Y ∨ PrecL Y X := by
  have hd : ∃ u, ¬ (u ∈ X ↔ u ∈ Y) := Classical.byContradiction fun h => by
    apply hne
    apply sorted_eq_of_mem hX hY
    intro u
    exact Classical.byContradiction fun hu => h ⟨u, hu⟩
  obtain ⟨z, hz, hmin⟩ := exists_min_nat (fun u => ¬ (u ∈ X ↔ u ∈ Y)) hd
  have hagree : ∀ u, u < z → (u ∈ X ↔ u ∈ Y) := fun u hu =>
    Classical.byContradiction fun h => hmin u hu h
  by_cases hzY : z ∈ Y
  · left; exact ⟨z, hzY, fun hzX => hz ⟨fun _ => hzY, fun _ => hzX⟩, hagree⟩
  · right
    have hzX : z ∈ X := Classical.byContradiction fun hzX => hz ⟨fun h => absurd h hzX, fun h => absurd h hzY⟩
    exact ⟨z, hzX, hzY, fun u hu => (hagree u hu).symm⟩

theorem leL_total {X Y : List Nat} (hX : X.Pairwise (· < ·)) (hY : Y.Pairwise (· < ·)) :
    LeL X Y ∨ PrecL Y X := by
  by_cases h : X = Y
  · exact Or.inl (Or.inl fun u => by rw [h])
  · rcases precL_total hX hY h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- **Monotonicity under unions of disjoint universes.** -/
theorem precL_union {X1 Y1 X2 Y2 X Y : List Nat}
    (hdisj : ∀ a, (a ∈ X1 ∨ a ∈ Y1) → ¬ (a ∈ X2 ∨ a ∈ Y2))
    (hX : ∀ u, u ∈ X ↔ u ∈ X1 ∨ u ∈ X2) (hY : ∀ u, u ∈ Y ↔ u ∈ Y1 ∨ u ∈ Y2)
    (h1 : (∀ u, u ∈ X1 ↔ u ∈ Y1) ∨ PrecL X1 Y1) (h2 : (∀ u, u ∈ X2 ↔ u ∈ Y2) ∨ PrecL X2 Y2) :
    (∀ u, u ∈ X ↔ u ∈ Y) ∨ PrecL X Y := by
  -- the first difference of a side, if any
  have side1 : ∀ z, FirstIn X1 Y1 z → (∀ u, u < z → ((u ∈ X2 ↔ u ∈ Y2))) → FirstIn X Y z := by
    intro z ⟨hzY, hzX, hag⟩ hag2
    refine ⟨(hY z).mpr (Or.inl hzY), fun h => ?_, fun u hu => ?_⟩
    · rcases (hX z).mp h with h | h
      · exact hzX h
      · exact hdisj z (Or.inr hzY) (Or.inl h)
    · rw [hX, hY, hag u hu, hag2 u hu]
  have side2 : ∀ z, FirstIn X2 Y2 z → (∀ u, u < z → ((u ∈ X1 ↔ u ∈ Y1))) → FirstIn X Y z := by
    intro z ⟨hzY, hzX, hag⟩ hag1
    refine ⟨(hY z).mpr (Or.inr hzY), fun h => ?_, fun u hu => ?_⟩
    · rcases (hX z).mp h with h | h
      · exact hdisj z (Or.inl h) (Or.inr hzY)
      · exact hzX h
    · rw [hX, hY, hag1 u hu, hag u hu]
  rcases h1 with h1 | ⟨z1, hz1⟩ <;> rcases h2 with h2 | ⟨z2, hz2⟩
  · left; intro u; rw [hX, hY, h1 u, h2 u]
  · right; exact ⟨z2, side2 z2 hz2 (fun u _ => h1 u)⟩
  · right; exact ⟨z1, side1 z1 hz1 (fun u _ => h2 u)⟩
  · right
    rcases Nat.lt_or_ge z1 z2 with h | h
    · exact ⟨z1, side1 z1 hz1 (fun u hu => hz2.2.2 u (by omega))⟩
    · rcases Nat.lt_or_ge z2 z1 with h' | h'
      · exact ⟨z2, side2 z2 hz2 (fun u hu => hz1.2.2 u (by omega))⟩
      · have : z1 = z2 := by omega
        subst this
        exact absurd (Or.inr hz2.1) (hdisj z1 (Or.inr hz1.1))

/-! ## `setPrec` on sorted arrays -/

theorem setPrec_iff {a b : Array Nat} (ha : a.toList.Pairwise (· < ·)) (hb : b.toList.Pairwise (· < ·)) :
    setPrec a b = true ↔ PrecL a.toList b.toList := by
  unfold setPrec
  rw [Array.compareLex_eq_compareLex_toList]
  have h := lexLt_iff a.toList b.toList ha hb
  unfold PrecL
  rw [← h]
  cases List.compareLex compareDesc a.toList b.toList <;> decide

end Ix.Compile.Verify.UniformModel
