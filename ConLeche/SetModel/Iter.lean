module

public import ConLeche.SetModel.TaggedSum

@[expose] public section

/-!
# The ω-iterate of a set functor (task #188)

The one place iteration survives in the recursive-type model: the
carrier is the Knaster–Tarski least pre-fixed point
(`ConLeche/SetTheory/Derive/Lfp.lean`), and every law about it assumes a
CLOSED MEMBER of the universe exists.  For a *finitary* tower functor
that witness is the ω-iterate

    iterF Φ 0 = ∅,   iterF Φ (n+1) = Φ (iterF Φ n),   iterU Φ = ⋃ₙ iterF Φ n

— a countable union of members of `univ w`, hence a member (`ω ∈ univ
w` at `w ≥ 1`, `omega_mem_univ_succ`; at `w = 0` truth values), and
closed under `Φ` whenever every member of `Φ (iterU Φ)` already lies in
some `Φ (iterF Φ n)` (`iterU_closed_of` — the finitary condition,
discharged for the tower functor in `ConLeche/Semantics/Tower/FixLeaf.lean`
by bounding the ranks of a tuple's finitely many recursive fields).
The union is also where the recursor's semantic fixed point is built
by rank recursion.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The finite iterates of a set functor from the empty set. -/
noncomputable def iterF (Φ : V → V) : Nat → V
  | 0 => empty
  | n + 1 => Φ (iterF Φ n)

@[simp] theorem iterF_zero (Φ : V → V) : iterF Φ 0 = empty := rfl
@[simp] theorem iterF_succ (Φ : V → V) (n : Nat) : iterF Φ (n + 1) = Φ (iterF Φ n) := rfl

/-- The union of a countable family `f 0 ∪ f 1 ∪ …` (the ω-indexed union
through the tag fibre). -/
noncomputable def natUnion (f : Nat → V) : V :=
  sUnion (image (natFibre f) omega)

theorem mem_natUnion {f : Nat → V} {x : V} : x ∈ˢ natUnion f ↔ ∃ n, x ∈ˢ f n := by
  unfold natUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem f hk
    rw [hfib] at hxy
    exact ⟨n, hxy⟩
  · rintro ⟨n, hn⟩
    exact ⟨natFibre f (vnat n), mem_image.mpr ⟨vnat n, vnat_mem_omega n, rfl⟩,
      by rw [natFibre_vnat]; exact hn⟩

/-- **Formation** (graph regime): a countable union of members of a
positive level is a member. -/
theorem natUnion_mem_univ_pos {w : Nat} (hw : w ≠ 0) {f : Nat → V}
    (h : ∀ n, f n ∈ˢ (univ w : V)) : natUnion f ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  unfold natUnion
  refine (univ_isTGUniverse (Nat.succ_ne_zero w')).famUnion_mem (omega_mem_univ_succ w') ?_
  intro k hk
  obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem f hk
  rw [hfib]
  exact h n

/-- **Formation** (squash regime): a union of truth values is a truth
value. -/
theorem natUnion_mem_univZero {f : Nat → V} (h : ∀ n, f n ∈ˢ (univZero : V)) :
    natUnion f ∈ˢ (univZero : V) := by
  rw [mem_univZero]
  intro x hx
  obtain ⟨n, hn⟩ := mem_natUnion.mp hx
  exact (mem_univZero.mp (h n)) x hn

/-- The ω-iterate: the union of the finite iterates. -/
noncomputable def iterU (Φ : V → V) : V := natUnion (iterF Φ)

theorem mem_iterU {Φ : V → V} {x : V} : x ∈ˢ iterU Φ ↔ ∃ n, x ∈ˢ iterF Φ n :=
  mem_natUnion

/-- **Closure** under a finitary functor: if every member of
`Φ (iterU Φ)` lies in some finite stage's image, the ω-iterate is
closed. -/
theorem iterU_closed_of {Φ : V → V}
    (hfin : ∀ x, x ∈ˢ Φ (iterU Φ) → ∃ n, x ∈ˢ Φ (iterF Φ n)) :
    Φ (iterU Φ) ⊆ˢ iterU Φ := by
  intro x hx
  obtain ⟨n, hn⟩ := hfin x hx
  exact mem_iterU.mpr ⟨n + 1, hn⟩

end ConLeche.SetTheory.Tower
