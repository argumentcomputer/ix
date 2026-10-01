module

public import ConLeche.SetTheory.Core

@[expose] public section

/-!
# The empty set, derived

The transitivity clause in `IsTGUniverse` makes this cheap —
`univChain 1` is inhabited (by `univChain 0`) and transitive, so
regularity's `∈`-minimal member of it has no members at all.

Also here: the small consequences of regularity everything downstream
wants — `x ∉ x` and the impossibility of membership 2-cycles.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

theorem empty_exists : ∃ e : V, ∀ z, ¬ z ∈ˢ e := by
  obtain ⟨htrans, -, -, -⟩ := univChain_tg (V := V) 1
  obtain ⟨y, hy, hmin⟩ :=
    regularity (univChain (V := V) 1) ⟨univChain 0, univChain_mem 0⟩
  exact ⟨y, fun z hz => hmin ⟨z, hz, htrans y z hy hz⟩⟩

/-- The empty set. -/
noncomputable def empty : V := Classical.choose empty_exists

theorem not_mem_empty (z : V) : ¬ z ∈ˢ (empty : V) :=
  Classical.choose_spec empty_exists z

theorem eq_empty {x : V} (h : ∀ z, ¬ z ∈ˢ x) : x = empty :=
  ext fun z => ⟨fun hz => absurd hz (h z), fun hz => absurd hz (not_mem_empty z)⟩

theorem eq_empty_iff {x : V} : x = empty ↔ ∀ z, ¬ z ∈ˢ x :=
  ⟨fun h z => h ▸ not_mem_empty z, eq_empty⟩

theorem ne_empty_of_mem {x z : V} (h : z ∈ˢ x) : x ≠ empty :=
  fun he => not_mem_empty z (he ▸ h)

theorem nonempty_of_ne_empty {x : V} (h : x ≠ empty) : ∃ z, z ∈ˢ x :=
  Classical.byContradiction fun hn => h (eq_empty fun z hz => hn ⟨z, hz⟩)

theorem empty_subset (x : V) : (empty : V) ⊆ˢ x :=
  fun z hz => absurd hz (not_mem_empty z)

/-- No set is a member of itself (regularity at `{x}`). -/
theorem not_mem_self (x : V) : ¬ x ∈ˢ x := by
  intro hx
  obtain ⟨y, hy, hmin⟩ := regularity (upair x x) ⟨x, mem_upair.mpr (Or.inl rfl)⟩
  have hyx : y = x := by rcases mem_upair.mp hy with h | h <;> exact h
  subst hyx
  exact hmin ⟨y, hx, mem_upair.mpr (Or.inl rfl)⟩

/- Interface operators are opaque from here on (as the legacy class
projections were): consumers reason only through the laws, never by
unfolding.  Everything above this line may use the definition. -/
attribute [irreducible] empty

/-- No membership 2-cycles (regularity at `{a, b}`). -/
theorem no_two_cycle {a b : V} (hab : a ∈ˢ b) (hba : b ∈ˢ a) : False := by
  obtain ⟨y, hy, hmin⟩ := regularity (upair a b) ⟨a, mem_upair.mpr (Or.inl rfl)⟩
  rcases mem_upair.mp hy with h | h <;> subst h
  · exact hmin ⟨b, hba, mem_upair.mpr (Or.inr rfl)⟩
  · exact hmin ⟨a, hab, mem_upair.mpr (Or.inl rfl)⟩

end ConLeche.SetTheory
