module

public import ConLeche.SetTheory.Derive.Graphs
public import ConLeche.SetTheory.Derive.Omega

@[expose] public section

/-!
# The universe tower

`univ 0` is the set of truth values (`univZero`, the `U₀` of Mario
Carneiro, *The Type Theory of Lean*, master's thesis, Carnegie Mellon
University, 2019);
`univ (n+1)` is the chain universe `univChain (n+2)`.  The tower
starts two levels up the chain so that every positive level has the
inductive set `univChain 1` as a member — which is what puts `ω`
inside every positive level (a bare universe need not contain `ω`;
`V_ω` is one — and `univChain 0` need not be inhabited, the empty set
satisfying `IsTGUniverse` vacuously, so `univChain 1` is the first chain
member known to be inductive).  `univ 0 ∈ univ 1` because `univZero`
is built from `∅` by pairing/power closure inside the inhabited
universe `univChain 1 ∈ univChain 2`.  Cumulativity holds because
positive levels are transitive and each level is a member of the
next.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The universe tower interpreting `Sort n`. -/
noncomputable def univ : Nat → V
  | 0 => univZero
  | n + 1 => univChain (n + 2)

theorem univ_zero : (univ 0 : V) = univZero := by rfl

/-- Positive levels are Grothendieck universes. -/
theorem univ_isTGUniverse {n : Nat} (hn : n ≠ 0) :
    IsTGUniverse (Mem (V := V)) (univ n) := by
  match n, hn with
  | m + 1, _ => exact univChain_tg _

theorem univChain_one_mem_univ_succ (n : Nat) :
    (univChain 1 : V) ∈ˢ univ (n + 1) :=
  univChain_mem_of_lt (Nat.succ_lt_succ n.succ_pos)

theorem univ_mem_univ (n : Nat) : (univ n : V) ∈ˢ univ (n + 1) := by
  match n with
  | 0 =>
    exact (univChain_tg 2).transitive (univChain_mem 1)
      ((univChain_tg 1).univZero_mem (univChain_mem 0))
  | m + 1 => exact univChain_mem (m + 2)

theorem univ_subset_succ (n : Nat) : (univ n : V) ⊆ˢ univ (n + 1) :=
  (univ_isTGUniverse (Nat.succ_ne_zero n)).subset_of_mem (univ_mem_univ n)

theorem univ_mono {m n : Nat} (h : m ≤ n) : (univ m : V) ⊆ˢ univ n := by
  induction n with
  | zero => cases Nat.le_zero.mp h; exact Subset.refl _
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (univ_subset_succ n)
    · exact Subset.refl _

/-- **The universe tower is injective.**  `univ u ∈ˢ univ (u+1) ⊆ˢ univ v`
whenever `u < v`, so an equality of two levels' universes would put a set
inside itself, against regularity (`not_mem_self`).

Note what this does *not* say, and what nothing can: the tower is
**cumulative** (`univ_mono`), so a *membership* `x ∈ˢ univ u` fixes only
a lower bound on `u` and two memberships of one value never determine a
level.  Injectivity of `univ` itself is the only handle on levels the
tower offers, and every consumer that needs "the sort is `u`" has to
reach it through an equality of universes, not through a typing. -/
theorem univ_inj {u v : Nat} (h : (univ u : V) = univ v) : u = v := by
  rcases Nat.lt_trichotomy u v with hlt | heq | hgt
  · exact absurd (h ▸ univ_mono (V := V) hlt _ (univ_mem_univ u))
      (not_mem_self (univ v : V))
  · exact heq
  · exact absurd (h ▸ univ_mono (V := V) hgt _ (univ_mem_univ v))
      (not_mem_self (univ u : V))

theorem omega_mem_univ_succ (n : Nat) : (omega : V) ∈ˢ univ (n + 1) :=
  (univ_isTGUniverse (Nat.succ_ne_zero n)).omega_mem (univChain_one_mem_univ_succ n)

theorem empty_mem_univ : ∀ n : Nat, (empty : V) ∈ˢ univ n
  | 0 => mem_univZero.mpr (empty_subset _)
  | n + 1 =>
    (univ_isTGUniverse (Nat.succ_ne_zero n)).empty_mem (univChain_one_mem_univ_succ n)

theorem unitSet_mem_univ : ∀ n : Nat, (unitSet : V) ∈ˢ univ n
  | 0 => mem_univZero.mpr (Subset.refl _)
  | n + 1 =>
    (univ_isTGUniverse (Nat.succ_ne_zero n)).unitSet_mem (univChain_one_mem_univ_succ n)

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] univ

end ConLeche.SetTheory
