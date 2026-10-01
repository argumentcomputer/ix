module

public import ConLeche.SetTheory.Derive.Pair

@[expose] public section

/-!
# Grothendieck universes: the diagonal argument and the closure laws

The engine room, recovering the Grothendieck-universe closure laws
(SGA 4, Exp. I, Appendix) from the Axiom-A matrix `IsTGUniverse`
(Tarski 1938) — applied downstream to the chain members `univChain n`.
The inaccessibility clause offers, for any subset `S ⊆ u`, the
disjunction `S ≈ u ∨ S ∈ u`; the single lemma `covered_mem` turns it
into a closure property by refuting the first disjunct with Cantor's
diagonal whenever `S` is covered by a function from a *member* of `u`.
Everything else — pairing, power, binary union, replacement images,
`⋃` of a member — reduces to it (`⋃` via a two-step surjection
argument ending in a membership 2-cycle).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section IsTGUniverse

variable {U : V} (hU : IsTGUniverse (Mem (V := V)) U)

include hU

theorem _root_.ConLeche.IsTGUniverse.transitive : ∀ {y z : V}, y ∈ˢ U → z ∈ˢ y → z ∈ˢ U :=
  fun {y z} hy hz => hU.1 y z hy hz

theorem _root_.ConLeche.IsTGUniverse.mem_of_subset_mem : ∀ {y z : V}, y ∈ˢ U → z ⊆ˢ y → z ∈ˢ U :=
  fun {y z} hy hz => hU.2.1 y z hy hz

theorem _root_.ConLeche.IsTGUniverse.subset_of_mem {y : V} (hy : y ∈ˢ U) : y ⊆ˢ U :=
  fun _ hz => hU.transitive hy hz

theorem _root_.ConLeche.IsTGUniverse.power_mem {y : V} (hy : y ∈ˢ U) : power y ∈ˢ U := by
  obtain ⟨p, hp, hsub⟩ := hU.2.2.1 y hy
  exact hU.mem_of_subset_mem hp fun z hz => hsub z (mem_power.mp hz)

/-- Cantor's diagonal, in the form everything downstream uses: a subset
of `U` covered by the image of a *member* of `U` is itself a member.
The equinumerosity disjunct is refuted by diagonalizing the covering
composed with the would-be surjection onto `U`. -/
theorem _root_.ConLeche.IsTGUniverse.covered_mem {I S : V} {F : V → V}
    (hI : I ∈ˢ U) (hS : S ⊆ˢ U)
    (hcov : ∀ b, b ∈ˢ S → ∃ x, x ∈ˢ I ∧ F x = b) : S ∈ˢ U := by
  rcases hU.2.2.2 S hS with ⟨f, -, -, hsurj⟩ | hmem
  · -- `f : S ↠ U`; diagonalize `x ↦ f (F x) : I ↠ U` at
    -- `D := {x ∈ I : x ∉ f (F x)}`.
    exfalso
    have hDU : sep I (fun x => ¬ x ∈ˢ f (F x)) ∈ˢ U :=
      hU.mem_of_subset_mem hI sep_subset
    obtain ⟨b, hbS, hfb⟩ := hsurj _ hDU
    obtain ⟨j, hjI, hFj⟩ := hcov b hbS
    have hGj : f (F j) = sep I (fun x => ¬ x ∈ˢ f (F x)) := by rw [hFj, hfb]
    have hiff : j ∈ˢ sep I (fun x => ¬ x ∈ˢ f (F x)) ↔
        ¬ j ∈ˢ sep I (fun x => ¬ x ∈ˢ f (F x)) := by
      constructor
      · intro hj
        have := (mem_sep.mp hj).2
        rwa [hGj] at this
      · intro hn
        exact mem_sep.mpr ⟨hjI, by rwa [hGj]⟩
    rcases Classical.em (j ∈ˢ sep I (fun x => ¬ x ∈ˢ f (F x))) with hj | hj
    · exact hiff.mp hj hj
    · exact hj (hiff.mpr hj)
  · exact hmem

/-- Replacement closure: the image of a member under a fibre-wise
member-valued function is a member. -/
theorem _root_.ConLeche.IsTGUniverse.image_mem {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U) : image F A ∈ˢ U :=
  hU.covered_mem hA
    (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact hF w hw)
    (fun b hb => by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hb
      exact ⟨w, hw, rfl⟩)

theorem _root_.ConLeche.IsTGUniverse.empty_mem {y : V} (hy : y ∈ˢ U) : (empty : V) ∈ˢ U :=
  hU.mem_of_subset_mem hy (empty_subset y)

open Classical in
/-- Pairing closure, via `covered_mem` from the two-element member
`power (power ∅) = {∅, {∅}}`. -/
theorem _root_.ConLeche.IsTGUniverse.upair_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : upair a b ∈ˢ U := by
  have h2 : power (power (empty : V)) ∈ˢ U :=
    (hU.empty_mem hy |> hU.power_mem) |> hU.power_mem
  refine hU.covered_mem (F := fun x => if x = empty then a else b) h2 ?_ ?_
  · intro z hz
    rcases mem_upair.mp hz with h | h <;> subst h <;> assumption
  · intro z hz
    rcases mem_upair.mp hz with h | h <;> subst h
    · exact ⟨empty, mem_power.mpr (empty_subset _), by simp⟩
    · refine ⟨power empty, mem_power.mpr (Subset.refl _), ?_⟩
      have hne : power (empty : V) ≠ empty :=
        ne_empty_of_mem (mem_power.mpr (Subset.refl _))
      simp [hne]

theorem _root_.ConLeche.IsTGUniverse.sing_mem {a y : V} (hy : y ∈ˢ U) (ha : a ∈ˢ U) :
    sing a ∈ˢ U := hU.upair_mem hy ha ha

/-- `⋃` closure.  A surjection `f : ⋃s ↠ U` would make `U` the union
of the member `S = {f-image of w : w ∈ s}`, putting `S ∈ U ⊆ ⋃S` — a
2-cycle. -/
theorem _root_.ConLeche.IsTGUniverse.sUnion_mem {s : V} (hs : s ∈ˢ U) : sUnion s ∈ˢ U := by
  have hsub : sUnion s ⊆ˢ U := fun z hz => by
    obtain ⟨y, hy, hzy⟩ := mem_sUnion.mp hz
    exact hU.transitive (hU.transitive hs hy) hzy
  rcases hU.2.2.2 (sUnion s) hsub with ⟨f, hinto, -, hsurj⟩ | hmem
  · exfalso
    -- For each `w ∈ s`, the `f`-image of `w` is a member of `U` …
    have himg : ∀ w, w ∈ˢ s → image f w ∈ˢ U := fun w hw =>
      hU.image_mem (hU.transitive hs hw) fun x hx =>
        hinto x (mem_sUnion.mpr ⟨w, hw, hx⟩)
    -- … so the set of all these images is a member too …
    have hS : image (fun w => image f w) s ∈ˢ U :=
      hU.image_mem hs fun w hw => himg w hw
    -- … but `U ⊆ ⋃(that set)`, giving `S ∈ U ⊆ ⋃S`: a 2-cycle.
    obtain ⟨x, hx, hfx⟩ := hsurj _ hS
    obtain ⟨w, hw, hxw⟩ := mem_sUnion.mp hx
    have : image (fun w => image f w) s ∈ˢ image f w :=
      hfx ▸ mem_image.mpr ⟨x, hxw, rfl⟩
    exact no_two_cycle this (mem_image.mpr ⟨w, hw, rfl⟩)
  · exact hmem

theorem _root_.ConLeche.IsTGUniverse.binUnion_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : binUnion a b ∈ˢ U :=
  hU.sUnion_mem (hU.upair_mem hy ha hb)

theorem _root_.ConLeche.IsTGUniverse.kpair_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : kpair a b ∈ˢ U :=
  hU.upair_mem hy (hU.sing_mem hy ha) (hU.upair_mem hy ha hb)

theorem _root_.ConLeche.IsTGUniverse.sep_mem {a : V} {p : V → Prop} (ha : a ∈ˢ U) :
    sep a p ∈ˢ U :=
  hU.mem_of_subset_mem ha sep_subset

/-- Union of a member-indexed family of members. -/
theorem _root_.ConLeche.IsTGUniverse.famUnion_mem {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U) :
    sUnion (image F A) ∈ˢ U :=
  hU.sUnion_mem (hU.image_mem hA hF)

end IsTGUniverse

/-- Chain membership generalizes along the ordering, by transitivity
of the higher universe. -/
theorem univChain_mem_of_lt {m n : Nat} (h : m < n) :
    (univChain m : V) ∈ˢ univChain n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact (univChain_tg (n + 1)).transitive (univChain_mem n) (ih h')
    · exact univChain_mem m

end ConLeche.SetTheory
