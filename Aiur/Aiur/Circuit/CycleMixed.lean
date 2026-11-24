import Aiur.Circuit.CycleLength

/-!
# Cycles over counted and sized nodes

`CycleLength.no_cycle` excludes cycles when every edge lowers a rank or lowers a field-valued
depth by a small positive step. Here an edge that keeps the rank joins two nodes of one kind:

* *counted* nodes carry a field value that the edge lowers by a small positive step, or keeps
  while lowering a natural `order`;
* the other nodes carry a natural `size` that the edge lowers, or does not raise while lowering
  `order`.

A closed walk keeps its rank, so it stays within one kind. Among counted nodes the steps sum
to zero in the field: either some step is positive, and the sum is a positive integer at most
`N · B`, or every edge lowers `order`. Among the others `(size, order)` falls lexicographically.
-/

namespace Aiur.Circuit.CycleLength

variable {V : Type}

/-- No cycle when every edge lowers the rank, or keeps it between two counted nodes with a
small field step (or an `order` step at the same field value), or keeps it between two
uncounted nodes whose `(size, order)` falls. -/
theorem no_cycle_mixed {F : Type} [Field F] [DecidableEq V] {edge : V → V → Prop}
    {rows : Finset V} {N B : Nat} (source : ∀ u v, edge u v → u ∈ rows) (card : rows.card ≤ N)
    (rank : V → Nat) (counted : V → Prop) (depth : V → F) (size order : V → Nat)
    (step : ∀ u v, edge u v → rank v < rank u ∨ rank v = rank u ∧
      ((counted u ∧ counted v ∧
          ((∃ s : Nat, 0 < s ∧ s ≤ B ∧ depth v + (s : F) = depth u) ∨
            (depth v = depth u ∧ order v < order u))) ∨
        (¬ counted u ∧ ¬ counted v ∧
          (size v < size u ∨ (size v ≤ size u ∧ order v < order u)))))
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * B → (n : F) ≠ 0) (u : V) :
    ¬ Relation.TransGen edge u u := by
  intro cycle
  obtain ⟨w, length, positive, short, closed, walk⟩ := short_cycle source cycle
  have climb : ∀ i k, i + k ≤ length → rank (w (i + k)) ≤ rank (w i) := by
    intro i k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
        intro bound
        have previous := ih (by omega)
        show rank (w (i + k + 1)) ≤ rank (w i)
        rcases step _ _ (walk (i + k) (by omega)) with lower | ⟨same, _⟩ <;> omega
  -- The walk returns to its rank, so no step lowers it.
  have flat : ∀ i < length,
      (counted (w i) ∧ counted (w (i + 1)) ∧
        ((∃ s : Nat, 0 < s ∧ s ≤ B ∧ depth (w (i + 1)) + (s : F) = depth (w i)) ∨
          (depth (w (i + 1)) = depth (w i) ∧ order (w (i + 1)) < order (w i)))) ∨
      (¬ counted (w i) ∧ ¬ counted (w (i + 1)) ∧
        (size (w (i + 1)) < size (w i) ∨
          (size (w (i + 1)) ≤ size (w i) ∧ order (w (i + 1)) < order (w i)))) := by
    intro i inside
    rcases step _ _ (walk i inside) with lower | ⟨_, steps⟩
    · have first := climb 0 i (by omega)
      have last := climb (i + 1) (length - (i + 1)) (by omega)
      rw [show i + 1 + (length - (i + 1)) = length by omega, closed] at last
      simp only [Nat.zero_add] at first
      omega
    · exact steps
  -- Each edge joins two nodes of one kind, so the walk stays within the kind of its start.
  have kind : ∀ m ≤ length, (counted (w m) ↔ counted (w 0)) := by
    intro m bound
    induction m with
    | zero => exact Iff.rfl
    | succ m ih =>
        have previous := ih (by omega)
        rcases flat m (by omega) with ⟨here, next, _⟩ | ⟨here, next, _⟩
        · exact ⟨fun _ => previous.mp here, fun _ => next⟩
        · exact ⟨fun holds => absurd holds next, fun holds => absurd (previous.mpr holds) here⟩
  by_cases start : counted (w 0)
  · -- Counted nodes: the steps sum to zero in the field, and a zero sum means `order` fell throughout.
    have total : ∀ m ≤ length, ∃ sum : Nat, sum ≤ m * B ∧
        depth (w m) + (sum : F) = depth (w 0) ∧ (sum = 0 → order (w m) + m ≤ order (w 0)) := by
      intro m bound
      induction m with
      | zero => exact ⟨0, by simp, by simp, fun _ => le_rfl⟩
      | succ m ih =>
          obtain ⟨sum, high, equal, ordered⟩ := ih (by omega)
          rcases flat m (by omega) with ⟨_, _, lowered⟩ | ⟨uncounted, _⟩
          · rcases lowered with ⟨s, positive, small, lowered⟩ | ⟨same, lower⟩
            · refine ⟨sum + s, ?_, ?_, by omega⟩
              · calc sum + s ≤ m * B + B := Nat.add_le_add high small
                  _ = (m + 1) * B := by ring
              · rw [← equal, ← lowered]
                push_cast
                ring
            · refine ⟨sum, ?_, by rw [same, equal], fun zero => ?_⟩
              · calc sum ≤ m * B := high
                  _ ≤ (m + 1) * B := Nat.mul_le_mul_right B (Nat.le_succ m)
              · have := ordered zero
                omega
          · exact absurd ((kind m (by omega)).mpr start) uncounted
    obtain ⟨sum, high, equal, ordered⟩ := total length le_rfl
    rw [closed] at equal ordered
    by_cases zero : sum = 0
    · have := ordered zero
      omega
    · apply characteristic sum (by omega)
        (high.trans (Nat.mul_le_mul_right B (short.trans card)))
      simpa using equal
  · -- Uncounted nodes: `size` never rises, and while it holds `order` falls.
    have total : ∀ m ≤ length, size (w m) ≤ size (w 0) ∧
        (size (w m) = size (w 0) → order (w m) + m ≤ order (w 0)) := by
      intro m bound
      induction m with
      | zero => exact ⟨le_rfl, fun _ => le_rfl⟩
      | succ m ih =>
          obtain ⟨below, ordered⟩ := ih (by omega)
          rcases flat m (by omega) with ⟨here, _⟩ | ⟨_, _, lower | ⟨same, lower⟩⟩
          · exact absurd ((kind m (by omega)).mp here) start
          · exact ⟨by omega, fun equal => by omega⟩
          · refine ⟨by omega, fun equal => ?_⟩
            have := ordered (by omega)
            omega
    have last := (total length le_rfl).2
    rw [closed] at last
    have := last rfl
    omega

end Aiur.Circuit.CycleLength
