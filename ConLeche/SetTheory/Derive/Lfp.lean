module

public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# Least pre-fixed points inside a universe (task #188)

The carrier of a directly installed **recursive** inductive type is the
Knaster–Tarski least pre-fixed point of its constructor-tower functor,
taken *inside* a universe:

    lfpSet w F = ⋂ { X ∈ univ w | F X ⊆ X }

where `F` is a set-level function (a graph over `univ w`, so `F X` is
`app F X`).  The intersection is realised as a separation over a
(classically chosen) closed member — `{x ∈ L₀ | x lies in every
`F`-closed member of `univ w`}` — so it is a set, and a *subset of a
member* of `univ w`, hence a member.  When NO closed member exists the
definition returns the empty set instead.  That junk value is what
makes the operator **total** at the type `(Sort w → Sort w) → Sort w`:
`lfpSet w F ∈ univ w` for every `F` (`lfpSet_mem_univ`), so the basis
constant `lfp` needs no certificate argument.  Every LAW below assumes
a closed member exists (`∃ L, IsClosedIn w F L`) — the semantic side
exhibits one (the ω-iterate of a finitary tower functor,
`ConLeche/SetModel/Iter.lean`).

Under that hypothesis and monotonicity the standard facts hold: the
least pre-fixed point is a fixed point (`lfpSet_closed`,
`lfpSet_fixed`), and it is contained in every closed member
(`lfpSet_subset`) — which IS structural induction (`lfpSet_induction`):
a property closed under the functor holds on the whole carrier.  No
rank, no ordinal, no iteration is consulted by the recursor's laws.

The RECURSOR of a recursive type needs no operator of its own: it is a
fixed point of its one-step unfolding, selected by the basis
`Classical.choice` from the (spelled) sigma type of fixed points
(`ConLeche/Semantics/Tower/FixRec.lean`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Universe helpers -/

/-- A subset of a member of `univ w` is a member: at `w = 0` members of
`univZero` are the subsets of `unitSet`; above, the Grothendieck
clause. -/
theorem univ_mem_of_subset_mem {w : Nat} {y z : V} (hy : y ∈ˢ (univ w : V)) (hz : z ⊆ˢ y) :
    z ∈ˢ (univ w : V) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [univ_zero] at hy ⊢
    rw [mem_univZero] at hy ⊢
    exact hz.trans hy
  · exact (univ_isTGUniverse (Nat.pos_iff_ne_zero.mp hw)).mem_of_subset_mem hy hz

/-- Separation stays inside every level. -/
theorem univ_sep_mem {w : Nat} {a : V} {p : V → Prop} (ha : a ∈ˢ (univ w : V)) :
    sep a p ∈ˢ (univ w : V) :=
  univ_mem_of_subset_mem ha sep_subset

/-! ## The least pre-fixed point -/

/-- An `F`-closed member of `univ w`: a pre-fixed point of `app F`. -/
def IsClosedIn (w : Nat) (F X : V) : Prop :=
  X ∈ˢ (univ w : V) ∧ app F X ⊆ˢ X

open Classical in
/-- **The least pre-fixed point of `F` inside `univ w`** — the
intersection of the `F`-closed members of `univ w` when there is one
(separated from a chosen closed member), the empty set otherwise (see
the module docstring). -/
noncomputable def lfpSet (w : Nat) (F : V) : V :=
  if h : ∃ L, IsClosedIn w F L then
    sep (Classical.choose h) (fun x => ∀ X, IsClosedIn w F X → x ∈ˢ X)
  else empty

theorem lfpSet_of_not {w : Nat} {F : V} (h : ¬ ∃ L, IsClosedIn w F L) :
    lfpSet w F = empty := by
  unfold lfpSet; exact dif_neg h

theorem mem_lfpSet {w : Nat} {F x : V} (h : ∃ L, IsClosedIn w F L) :
    x ∈ˢ lfpSet w F ↔ ∀ X, IsClosedIn w F X → x ∈ˢ X := by
  unfold lfpSet
  rw [dif_pos h, mem_sep]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩

/-- **Leastness**: the least pre-fixed point lies in every closed
member. -/
theorem lfpSet_subset {w : Nat} {F X : V} (hX : IsClosedIn w F X) : lfpSet w F ⊆ˢ X :=
  fun _x hx => (mem_lfpSet ⟨X, hX⟩).mp hx X hX

/-- **Formation, unconditional**: the least pre-fixed point is a member
of the universe — a subset of a closed member when there is one, the
empty set otherwise. -/
theorem lfpSet_mem_univ (w : Nat) (F : V) : lfpSet w F ∈ˢ (univ w : V) := by
  by_cases h : ∃ L, IsClosedIn w F L
  · obtain ⟨L, hL⟩ := h
    exact univ_mem_of_subset_mem hL.1 (lfpSet_subset hL)
  · rw [lfpSet_of_not h]; exact empty_mem_univ w

/-- Monotonicity of a set-level functor on the universe. -/
def MonoIn (w : Nat) (F : V) : Prop :=
  ∀ X Y, X ∈ˢ (univ w : V) → Y ∈ˢ (univ w : V) → X ⊆ˢ Y → app F X ⊆ˢ app F Y

/-- The functor maps the universe into itself. -/
def MapsIn (w : Nat) (F : V) : Prop :=
  ∀ X, X ∈ˢ (univ w : V) → app F X ∈ˢ (univ w : V)

/-- **Closure**: the least pre-fixed point is a pre-fixed point. -/
theorem lfpSet_closed {w : Nat} {F : V} (h : ∃ L, IsClosedIn w F L)
    (hmono : MonoIn w F) : app F (lfpSet w F) ⊆ˢ lfpSet w F := by
  intro x hx
  rw [mem_lfpSet h]
  intro X hX
  exact hX.2 x (hmono _ _ (lfpSet_mem_univ w F) hX.1 (lfpSet_subset hX) x hx)

/-- **The fixed-point equation's other half**: the least pre-fixed
point is a post-fixed point, because its image is itself closed. -/
theorem lfpSet_fixed {w : Nat} {F : V} (h : ∃ L, IsClosedIn w F L)
    (hmono : MonoIn w F) (hmaps : MapsIn w F) : lfpSet w F ⊆ˢ app F (lfpSet w F) := by
  refine lfpSet_subset ⟨hmaps _ (lfpSet_mem_univ w F), ?_⟩
  exact hmono _ _ (hmaps _ (lfpSet_mem_univ w F)) (lfpSet_mem_univ w F)
    (lfpSet_closed h hmono)

/-- The fixed-point equation. -/
theorem lfpSet_eq {w : Nat} {F : V} (h : ∃ L, IsClosedIn w F L)
    (hmono : MonoIn w F) (hmaps : MapsIn w F) : app F (lfpSet w F) = lfpSet w F :=
  Subset.antisymm (lfpSet_closed h hmono) (lfpSet_fixed h hmono hmaps)

/-- **Structural induction**: a property closed under the functor on
the carrier holds on the whole carrier — the members of the carrier
satisfying it form a closed member of the universe, in which the
carrier lies by leastness. -/
theorem lfpSet_induction {w : Nat} {F : V} (h : ∃ L, IsClosedIn w F L)
    (hmono : MonoIn w F) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ app F (sep (lfpSet w F) P) → P x) :
    ∀ x, x ∈ˢ lfpSet w F → P x := by
  intro x hx
  have hS : IsClosedIn w F (sep (lfpSet w F) P) := by
    refine ⟨univ_sep_mem (lfpSet_mem_univ w F), fun y hy => ?_⟩
    rw [mem_sep]
    refine ⟨?_, hP y hy⟩
    exact lfpSet_closed h hmono y
      (hmono _ _ (univ_sep_mem (lfpSet_mem_univ w F)) (lfpSet_mem_univ w F) sep_subset y hy)
  exact (mem_sep.mp (lfpSet_subset hS x hx)).2

end ConLeche.SetTheory
