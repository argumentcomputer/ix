module

public import ConLeche.SetTheory.Derive.Graphs

@[expose] public section

/-!
# Choice: the global selector, and the eighth axiom as a theorem

A first-order development of Tarski–Grothendieck set theory asserts (or
derives from Axiom A) an axiom of choice, because it cannot reach the
meta-level.  Here the meta-logic is Lean with `Classical.choice`, so
choice over `V` is *derived*:

* `schoice : V → V` — a global selector, `schoice A ∈ A` whenever `A`
  is inhabited (Lean-level choice on the membership predicate);
* `set_choice` — the Jech-form statement (*Set Theory*, §5): every
  family has a *set* choice function, obtained as the replacement
  graph of `schoice`, spelled through `kpair` as a single-valued set
  of ordered pairs.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- Global choice: a uniform selection from nonempty sets.  On sets
without members (and only there) it returns the set itself. -/
noncomputable def schoice (A : V) : V :=
  if h : ∃ x, x ∈ˢ A then Classical.choose h else A

theorem schoice_mem {A x : V} (hx : x ∈ˢ A) : schoice A ∈ˢ A := by
  unfold schoice
  rw [dif_pos ⟨x, hx⟩]
  exact Classical.choose_spec (⟨x, hx⟩ : ∃ x, x ∈ˢ A)

/-- The axiom of choice, Jech-form, as a theorem: every family `X` has
a set-level choice function — a single-valued set of pairs, total on
`X`, selecting a member from every inhabited `A ∈ X`. -/
theorem set_choice (X : V) :
    ∃ f : V,
      (∀ A c, kpair A c ∈ˢ f → A ∈ˢ X) ∧
      (∀ A, A ∈ˢ X → ∃ c, kpair A c ∈ˢ f ∧ ∀ c', kpair A c' ∈ˢ f → c' = c) ∧
      (∀ A c, kpair A c ∈ˢ f → (∃ x, x ∈ˢ A) → c ∈ˢ A) := by
  refine ⟨graph schoice X, ?_, ?_, ?_⟩
  · intro A c hp
    obtain ⟨A', hA', hp'⟩ := mem_graph.mp hp
    obtain ⟨rfl, -⟩ := kpair_inj hp'
    exact hA'
  · intro A hA
    refine ⟨schoice A, mem_graph.mpr ⟨A, hA, rfl⟩, ?_⟩
    intro c' hc'
    obtain ⟨A', -, hp'⟩ := mem_graph.mp hc'
    obtain ⟨rfl, rfl⟩ := kpair_inj hp'
    rfl
  · intro A c hp ⟨x, hx⟩
    obtain ⟨A', -, hp'⟩ := mem_graph.mp hp
    obtain ⟨rfl, rfl⟩ := kpair_inj hp'
    exact schoice_mem hx

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] schoice

end ConLeche.SetTheory
