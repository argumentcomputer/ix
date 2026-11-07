/-! Finite-relation lemmas used by the Aiur trace argument. The pigeonhole
bound concerns distinct trace rows, not the potentially much larger unfolded
derivation tree. -/

namespace IxCC.Aiur.Finite

/-- Two of the first `n + 1` values of a sequence in `Fin n` agree. -/
theorem exists_repeat (n : Nat) : ∀ (f : Nat → Fin n),
    ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  induction n with
  | zero => intro f; exact (f 0).elim0
  | succ n ih =>
    intro f
    by_cases hit : ∃ k, 0 < k ∧ k ≤ n + 1 ∧ f k = f 0
    · obtain ⟨k, hk, hkn, hfk⟩ := hit
      exact ⟨0, k, hk, hkn, hfk.symm⟩
    · have hit : ∀ k, 0 < k → k ≤ n + 1 → f k ≠ f 0 := by
        intro k hk hkn h
        exact hit ⟨k, hk, hkn, h⟩
      let c := (f 0).val
      have shrink : ∀ k, 0 < k → k ≤ n + 1 → (f k).val ≠ c := by
        intro k hk hkn h
        exact hit k hk hkn (Fin.ext h)
      have hn : 0 < n := by
        apply Classical.byContradiction
        intro h0
        have h0 : n = 0 := by omega
        subst h0
        exact hit 1 (by omega) (by omega)
          (Fin.ext (by have := (f 1).isLt; have := (f 0).isLt; omega))
      let g : Nat → Fin n := fun k =>
        if h : (f (k + 1)).val < c then ⟨(f (k + 1)).val, by omega⟩
        else ⟨(f (k + 1)).val - 1, by
          have := (f (k + 1)).isLt
          omega⟩
      obtain ⟨i, j, hij, hjn, hg⟩ := ih g
      refine ⟨i + 1, j + 1, by omega, by omega, ?_⟩
      have hi := shrink (i + 1) (by omega) (by omega)
      have hj := shrink (j + 1) (by omega) (by omega)
      apply Fin.ext
      simp only [g] at hg
      split at hg <;> split at hg <;> simp only [Fin.mk.injEq] at hg <;> omega

theorem wellFounded_of_noChain {α : Type} (r : α → α → Prop)
    (noChain : ∀ f : Nat → α, (∀ i, r (f (i + 1)) (f i)) → False) : WellFounded r := by
  classical
  refine ⟨fun x => ?_⟩
  apply Classical.byContradiction
  intro hx
  have pick : ∀ y : {y // ¬ Acc r y}, ∃ z : {z // ¬ Acc r z}, r z.1 y.1 := by
    intro ⟨y, hy⟩
    apply Classical.byContradiction
    intro hnone
    apply hy
    constructor
    intro z hz
    apply Classical.byContradiction
    intro hz'
    exact hnone ⟨⟨z, hz'⟩, hz⟩
  let next : {y // ¬ Acc r y} → {y // ¬ Acc r y} := fun y => Classical.choose (pick y)
  have hnext : ∀ y, r (next y).1 y.1 := fun y => Classical.choose_spec (pick y)
  let chain : Nat → {y // ¬ Acc r y} := fun i => Nat.rec ⟨x, hx⟩ (fun _ y => next y) i
  exact noChain (fun i => (chain i).1) (fun i => hnext (chain i))

theorem wellFounded_of_noShortCycle {n : Nat} (r : Fin n → Fin n → Prop)
    (noCycle : ∀ (walk : Nat → Fin n) (length : Nat),
      0 < length → length ≤ n →
      (∀ i, i < length → r (walk (i + 1)) (walk i)) → walk length ≠ walk 0) :
    WellFounded r := by
  apply wellFounded_of_noChain
  intro sequence edges
  obtain ⟨i, j, before, bounded, repeated⟩ := exists_repeat n sequence
  apply noCycle (fun k => sequence (i + k)) (j - i) (by omega) (by omega)
  · intro k _
    simpa [Nat.add_assoc] using edges (i + k)
  · have finish : i + (j - i) = j := by omega
    simpa [finish] using repeated.symm

end IxCC.Aiur.Finite
