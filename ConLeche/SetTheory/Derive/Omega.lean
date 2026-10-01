module

public import ConLeche.SetTheory.Derive.Universe

@[expose] public section

/-!
# Infinity, derived: the finite ordinals

Infinity is derived from the universe chain + Replacement: an
*inhabited* Grothendieck universe is an inductive *set* — it contains
`∅` and is closed under the von Neumann successor `n ↦ n ∪ {n}`
(von Neumann 1923) by the pairing/union closures — so `ω` can be
separated out of one as the members of *every* inductive set.
Leastness is then definitional.  The inductive universe used is
`univChain 1`: it is inhabited by `univChain 0` (note `univChain 0`
itself need not be — the empty set satisfies `IsTGUniverse`
vacuously).

`vnat : Nat → V` names the members of `ω` from the meta-level; every
member of `ω` is a unique `vnat k` (`mem_omega_iff`, `vnat_inj`),
which is what makes recursion on `ω` cheap in `Derive/Natrec.lean`.

`ω` itself is a *member* of any universe that has the inductive
universe `univChain 1` as a member — arranged for the tower in
`Derive/Univ.lean`.  (Mere universehood does not suffice: `V_ω` is a
Tarski universe without `ω`.)
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The von Neumann successor `n ∪ {n}`. -/
noncomputable def vsucc (n : V) : V := binUnion n (sing n)

theorem mem_vsucc {z n : V} : z ∈ˢ vsucc n ↔ z ∈ˢ n ∨ z = n := by
  rw [vsucc, mem_binUnion, mem_sing]

theorem self_mem_vsucc (n : V) : n ∈ˢ vsucc n := mem_vsucc.mpr (Or.inr rfl)

theorem vsucc_ne_empty (n : V) : vsucc n ≠ empty :=
  ne_empty_of_mem (self_mem_vsucc n)

/-- An inductive set: contains `∅`, closed under the successor. -/
def Inductive (I : V) : Prop :=
  (empty : V) ∈ˢ I ∧ ∀ n, n ∈ˢ I → vsucc n ∈ˢ I

/-- An inhabited Grothendieck universe is an inductive set. -/
theorem _root_.ConLeche.IsTGUniverse.inductive_self {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : Inductive U :=
  ⟨hU.empty_mem hy, fun _n hn =>
    hU.binUnion_mem hy hn (hU.sing_mem hy hn)⟩

theorem univChain_one_inductive : Inductive (univChain 1 : V) :=
  (univChain_tg 1).inductive_self (univChain_mem 0)

/-- The finite ordinals: the members of every inductive set, separated
from the inductive universe `univChain 1`. -/
noncomputable def omega : V :=
  sep (univChain 1) (fun n => ∀ I : V, Inductive I → n ∈ˢ I)

theorem mem_omega {n : V} : n ∈ˢ (omega : V) ↔ ∀ I : V, Inductive I → n ∈ˢ I := by
  rw [omega, mem_sep]
  exact ⟨fun h => h.2, fun h => ⟨h _ univChain_one_inductive, h⟩⟩

theorem omega_subset_inductive {I : V} (hI : Inductive I) : (omega : V) ⊆ˢ I :=
  fun _ hn => mem_omega.mp hn I hI

theorem omega_inductive : Inductive (omega : V) := by
  constructor
  · exact mem_omega.mpr fun I hI => hI.1
  · intro n hn
    exact mem_omega.mpr fun I hI => hI.2 n (mem_omega.mp hn I hI)

theorem empty_mem_omega : (empty : V) ∈ˢ omega := omega_inductive.1

theorem vsucc_mem_omega {n : V} (hn : n ∈ˢ (omega : V)) : vsucc n ∈ˢ (omega : V) :=
  omega_inductive.2 n hn

/-- The `k`-th von Neumann natural. -/
noncomputable def vnat : Nat → V
  | 0 => empty
  | k + 1 => vsucc (vnat k)

theorem vnat_mem_omega : ∀ k, (vnat k : V) ∈ˢ omega
  | 0 => empty_mem_omega
  | k + 1 => vsucc_mem_omega (vnat_mem_omega k)

/-- Every finite ordinal is named by a meta-level natural. -/
theorem mem_omega_iff {n : V} : n ∈ˢ (omega : V) ↔ ∃ k, n = vnat k := by
  constructor
  · intro hn
    have hind : Inductive (sep (omega : V) (fun n => ∃ k, n = vnat k)) := by
      constructor
      · exact mem_sep.mpr ⟨empty_mem_omega, 0, rfl⟩
      · intro m hm
        obtain ⟨hmo, k, rfl⟩ := mem_sep.mp hm
        exact mem_sep.mpr ⟨vsucc_mem_omega hmo, k + 1, rfl⟩
    exact (mem_sep.mp (omega_subset_inductive hind n hn)).2
  · rintro ⟨k, rfl⟩
    exact vnat_mem_omega k

theorem vnat_mem_vnat_of_lt : ∀ {k l : Nat}, k < l → (vnat k : V) ∈ˢ vnat l := by
  intro k l hkl
  induction l with
  | zero => exact absurd hkl (Nat.not_lt_zero k)
  | succ l ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hkl with h | rfl
    · exact mem_vsucc.mpr (Or.inl (ih h))
    · exact self_mem_vsucc _

theorem vnat_inj {k l : Nat} (h : (vnat k : V) = vnat l) : k = l := by
  rcases Nat.lt_trichotomy k l with hlt | heq | hgt
  · exact absurd (h ▸ vnat_mem_vnat_of_lt (V := V) hlt) (not_mem_self _)
  · exact heq
  · exact absurd (h ▸ vnat_mem_vnat_of_lt (V := V) hgt) (not_mem_self _)

theorem omega_subset_univChain_one : (omega : V) ⊆ˢ univChain 1 := sep_subset

/-- `ω` is a member of any universe having the inductive universe
`univChain 1` as a member. -/
theorem _root_.ConLeche.IsTGUniverse.omega_mem {U : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (h1 : (univChain 1 : V) ∈ˢ U) :
    (omega : V) ∈ˢ U :=
  hU.mem_of_subset_mem h1 omega_subset_univChain_one

/- Opaque interface operator (see `Derive/Empty.lean`).  `vsucc` stays
reducible: `Derive/Natrec.lean` computes with it through `vnat`. -/
attribute [irreducible] omega

end ConLeche.SetTheory
