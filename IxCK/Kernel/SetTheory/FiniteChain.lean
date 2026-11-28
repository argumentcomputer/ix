module

public import IxCK.Kernel.SetTheory.Core

@[expose] public section

/-!
# Finite Grothendieck-universe chains in Lean's universe hierarchy

`Ix.Kernel.SetTheory V` (`IxCK/Kernel/SetTheory/Core.lean`) asks for the six ZF⁻
axioms (extensionality, pairing, union, power set, regularity, Lean-level
replacement) together with an ω-chain `univChain : Nat → V` of Grothendieck
universes (`IsTGUniverse`).  By Gödel's second incompleteness theorem (and
Carneiro 2019, *The Type Theory of Lean*, §1.2), an ω-chain inside a single
type `V` has the full consistency strength of Lean itself and cannot be
constructed unconditionally inside Lean.  (`Models/SetTheory` constructs it
conditionally on Mathlib's `ZFSet` from `ω` strongly inaccessible cardinals.)

Every **finite** prefix of that interface, however, is unconditionally
inhabited inside Lean's own universe hierarchy, using only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and zero external
dependencies:

* `PSet.{u}` and its bisimulation quotient `VSet.{u} : Type (u + 1)` form
  Aczel's pure-Lean model of the six ZF⁻ axioms (`VSet.ext`, `VSet.upair`,
  `VSet.sUnion`, `VSet.power`, `VSet.regularity`, `VSet.image`).
* The universe-lifting embedding `VSet.lift : VSet.{u} → VSet.{u + 1}` turns
  the entire universe `VSet.{u}` into a single set `VSet.univSet.{u} : VSet.{u + 1}`
  satisfying all four clauses of `Ix.Kernel.IsTGUniverse`
  (`VSet.isTGUniverse_univSet`), and `VSet.lift` preserves `IsTGUniverse`
  (`VSet.isTGUniverse_lift`).
* `FiniteSetTheory n V` is the exact `n`-universe truncation of
  `Ix.Kernel.SetTheory V` (`univChain : Fin n → V`).  Every `SetTheory V`
  restricts to `FiniteSetTheory n V` (`FiniteSetTheory.ofSetTheory`), and
  `FiniteSetTheory.liftStep` lifts any `n`-chain in `VSet.{u}` to an
  `(n + 1)`-chain in `VSet.{u + 1}` by appending `VSet.univSet.{u}`,
  inhabiting `FiniteSetTheory n VSet.{u + n}` for every concrete `n`
  (`finiteSetTheory0`, `finiteSetTheory1`, `finiteSetTheory2`,
  `finiteSetTheory3`, `finiteSetTheory4`, ...).
* Finally, assuming an ω-chain of Grothendieck universes in `VSet.{u}`
  (`VSet.OmegaUniverses`), `VSet.setTheoryOfOmegaUniverses` directly supplies
  an `Ix.Kernel.SetTheory VSet.{u}` instance without requiring Mathlib.
-/

namespace Ix.Kernel

universe u v w

/-! ## Aczel's pure-Lean set model `VSet` -/

/-- Aczel's pre-sets at universe `u`: well-founded trees whose branching types
live in `Type u`. -/
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

/-- The indexing type of a pre-set. -/
def Idx : PSet.{u} → Type u
  | .mk α _ => α

/-- The element family of a pre-set. -/
def Func : (x : PSet.{u}) → x.Idx → PSet.{u}
  | .mk _ A => A

/-- Bisimulation (extensional equivalence) of pre-sets. -/
def Equiv : PSet.{u} → PSet.{u} → Prop
  | .mk _ A, .mk _ B =>
      (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))

theorem Equiv.refl : ∀ x : PSet.{u}, Equiv x x
  | .mk _ A => ⟨fun a => ⟨a, Equiv.refl (A a)⟩, fun a => ⟨a, Equiv.refl (A a)⟩⟩

theorem Equiv.symm : ∀ {x y : PSet.{u}}, Equiv x y → Equiv y x
  | .mk _ _, .mk _ _, ⟨h1, h2⟩ =>
      ⟨fun b => let ⟨a, ha⟩ := h2 b; ⟨a, Equiv.symm ha⟩,
       fun a => let ⟨b, hb⟩ := h1 a; ⟨b, Equiv.symm hb⟩⟩

theorem Equiv.trans : ∀ {x y z : PSet.{u}}, Equiv x y → Equiv y z → Equiv x z
  | .mk _ _, .mk _ _, .mk _ _, ⟨h1, h2⟩, ⟨h3, h4⟩ =>
      ⟨fun a =>
        let ⟨b, hab⟩ := h1 a
        let ⟨c, hbc⟩ := h3 b
        ⟨c, Equiv.trans hab hbc⟩,
       fun c =>
        let ⟨b, hbc⟩ := h4 c
        let ⟨a, hab⟩ := h2 b
        ⟨a, Equiv.trans hab hbc⟩⟩

/-- Pre-set membership: `x` is bisimilar to a child of `y`. -/
def Mem (x : PSet.{u}) : PSet.{u} → Prop
  | .mk _ B => ∃ b, Equiv x (B b)

theorem Mem.congr_left {x x' y : PSet.{u}} (h : Equiv x x') : Mem x y ↔ Mem x' y := by
  cases y with
  | mk β B =>
    exact ⟨fun ⟨b, hb⟩ => ⟨b, Equiv.trans (Equiv.symm h) hb⟩,
           fun ⟨b, hb⟩ => ⟨b, Equiv.trans h hb⟩⟩

theorem Mem.congr_right {x y y' : PSet.{u}} (h : Equiv y y') : Mem x y ↔ Mem x y' := by
  cases y with
  | mk β B =>
    cases y' with
    | mk γ C =>
      exact ⟨fun ⟨b, hb⟩ => let ⟨c, hc⟩ := h.1 b; ⟨c, Equiv.trans hb hc⟩,
             fun ⟨c, hc⟩ => let ⟨b, hb⟩ := h.2 c; ⟨b, Equiv.trans hc (Equiv.symm hb)⟩⟩

theorem Equiv.of_mem {x y : PSet.{u}} (h : ∀ z, Mem z x ↔ Mem z y) : Equiv x y := by
  cases x with
  | mk α A =>
    cases y with
    | mk β B =>
      exact ⟨fun a => (h (A a)).mp ⟨a, Equiv.refl _⟩,
             fun b => let ⟨a, ha⟩ := (h (B b)).mpr ⟨b, Equiv.refl _⟩; ⟨a, Equiv.symm ha⟩⟩

instance setoid : Setoid PSet.{u} where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- Lift a pre-set up one Lean universe level. -/
def lift : PSet.{u} → PSet.{u + 1}
  | .mk α A => .mk (ULift.{u + 1} α) (fun a => lift (A a.down))

theorem Equiv.lift_iff : ∀ {x y : PSet.{u}}, Equiv x y ↔ Equiv x.lift y.lift
  | .mk _ _, .mk _ _ => by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun ⟨a⟩ => let ⟨b, hb⟩ := h1 a; ⟨⟨b⟩, Equiv.lift_iff.mp hb⟩,
             fun ⟨b⟩ => let ⟨a, ha⟩ := h2 b; ⟨⟨a⟩, Equiv.lift_iff.mp ha⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun a => let ⟨⟨b⟩, hb⟩ := h1 ⟨a⟩; ⟨b, Equiv.lift_iff.mpr hb⟩,
             fun b => let ⟨⟨a⟩, ha⟩ := h2 ⟨b⟩; ⟨a, Equiv.lift_iff.mpr ha⟩⟩

end PSet

/-- Pure-Lean ZF⁻ sets at universe `u`: `PSet.{u}` modulo bisimulation. -/
def VSet : Type (u + 1) := Quotient PSet.setoid.{u}

namespace VSet

/-- Quotient constructor from a pre-set. -/
def mk (x : PSet.{u}) : VSet.{u} := Quotient.mk PSet.setoid x

/-- Set membership in `VSet.{u}`. -/
def Mem (x y : VSet.{u}) : Prop :=
  Quotient.liftOn₂ x y PSet.Mem fun _ _ _ _ h1 h2 =>
    propext ((PSet.Mem.congr_left h1).trans (PSet.Mem.congr_right h2))

/-- Extensionality in `VSet.{u}`. -/
theorem ext {x y : VSet.{u}} (h : ∀ z, Mem z x ↔ Mem z y) : x = y := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) h
  exact Quotient.sound (PSet.Equiv.of_mem fun z => hab (mk z))

/-- Chosen pre-set representative of a `VSet.{u}` (via `Classical.choice`). -/
noncomputable def rep (x : VSet.{u}) : PSet.{u} :=
  Classical.choose (Quotient.exists_rep x)

theorem mk_rep (x : VSet.{u}) : mk (rep x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

/-- Construct a `VSet.{u}` from any `Type u`-indexed family of sets. -/
noncomputable def ofFam (α : Type u) (f : α → VSet.{u}) : VSet.{u} :=
  mk (.mk α fun a => rep (f a))

theorem mem_ofFam {α : Type u} {f : α → VSet.{u}} {z : VSet.{u}} :
    Mem z (ofFam α f) ↔ ∃ a : α, z = f a := by
  refine Quotient.inductionOn z fun x => ?_
  change (∃ a : α, PSet.Equiv x (rep (f a))) ↔ ∃ a : α, mk x = f a
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (Quotient.sound ha).trans (mk_rep (f a))⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Quotient.exact (ha.trans (mk_rep (f a)).symm)⟩

/-- Chosen `Type u` indexing type of a set's elements. -/
noncomputable def Idx (x : VSet.{u}) : Type u :=
  (rep x).Idx

/-- Chosen enumeration of a set's elements over `x.Idx`. -/
noncomputable def elem (x : VSet.{u}) : x.Idx → VSet.{u} :=
  fun i => mk ((rep x).Func i)

theorem mem_iff_exists_elem {z x : VSet.{u}} :
    Mem z x ↔ ∃ i : x.Idx, z = x.elem i := by
  refine Quotient.inductionOn z fun w => ?_
  change Mem (mk w) x ↔ ∃ i : x.Idx, mk w = x.elem i
  have h1 : Mem (mk w) x ↔ Mem (mk w) (mk (rep x)) := by rw [mk_rep x]
  rw [h1]
  change PSet.Mem w (rep x) ↔ ∃ i : (rep x).Idx, mk w = mk ((rep x).Func i)
  cases rep x with
  | mk α A =>
    change (∃ a : α, PSet.Equiv w (A a)) ↔ ∃ a : α, mk w = mk (A a)
    exact ⟨fun ⟨a, ha⟩ => ⟨a, Quotient.sound ha⟩, fun ⟨a, ha⟩ => ⟨a, Quotient.exact ha⟩⟩

theorem elem_mem (x : VSet.{u}) (i : x.Idx) : Mem (x.elem i) x :=
  mem_iff_exists_elem.mpr ⟨i, rfl⟩

/-! ### The six ZF⁻ axioms on `VSet` -/

/-- The empty set in `VSet.{u}`. -/
noncomputable def empty : VSet.{u} := ofFam PEmpty PEmpty.elim

theorem not_mem_empty (z : VSet.{u}) : ¬ Mem z empty := by
  rw [empty, mem_ofFam]
  rintro ⟨a, -⟩
  exact PEmpty.elim a

/-- Unordered pair `{a, b}` in `VSet.{u}`. -/
noncomputable def upair (a b : VSet.{u}) : VSet.{u} :=
  ofFam (ULift.{u} Bool) fun c => if c.down then a else b

theorem mem_upair {z a b : VSet.{u}} : Mem z (upair a b) ↔ z = a ∨ z = b := by
  rw [upair, mem_ofFam]
  constructor
  · rintro ⟨⟨c⟩, rfl⟩
    cases c <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨true⟩, rfl⟩
    · exact ⟨⟨false⟩, rfl⟩

/-- Singleton `{a}` in `VSet.{u}`. -/
noncomputable def sing (a : VSet.{u}) : VSet.{u} := upair a a

theorem mem_sing {z a : VSet.{u}} : Mem z (sing a) ↔ z = a := by
  rw [sing, mem_upair]
  exact ⟨fun h => h.elim id id, Or.inl⟩

/-- Union `⋃ x` in `VSet.{u}`. -/
noncomputable def sUnion (x : VSet.{u}) : VSet.{u} :=
  ofFam (Σ i : x.Idx, (x.elem i).Idx) fun p => (x.elem p.1).elem p.2

theorem mem_sUnion {z x : VSet.{u}} : Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y := by
  rw [sUnion, mem_ofFam]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨x.elem i, elem_mem x i, elem_mem (x.elem i) j⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨i, rfl⟩ := mem_iff_exists_elem.mp hy
    obtain ⟨j, rfl⟩ := mem_iff_exists_elem.mp hz
    exact ⟨⟨i, j⟩, rfl⟩

/-- Binary union `a ∪ b` in `VSet.{u}`. -/
noncomputable def binUnion (a b : VSet.{u}) : VSet.{u} := sUnion (upair a b)

theorem mem_binUnion {z a b : VSet.{u}} : Mem z (binUnion a b) ↔ Mem z a ∨ Mem z b := by
  rw [binUnion, mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    rcases mem_upair.mp hy with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨a, mem_upair.mpr (Or.inl rfl), hz⟩
    · exact ⟨b, mem_upair.mpr (Or.inr rfl), hz⟩

/-- Separation `{z ∈ x | p z}` in `VSet.{u}`. -/
noncomputable def sep (x : VSet.{u}) (p : VSet.{u} → Prop) : VSet.{u} :=
  ofFam {i : x.Idx // p (x.elem i)} fun j => x.elem j.1

theorem mem_sep {z x : VSet.{u}} {p : VSet.{u} → Prop} :
    Mem z (sep x p) ↔ Mem z x ∧ p z := by
  rw [sep, mem_ofFam]
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    exact ⟨elem_mem x i, hi⟩
  · rintro ⟨hz, hp⟩
    obtain ⟨i, rfl⟩ := mem_iff_exists_elem.mp hz
    exact ⟨⟨i, hp⟩, rfl⟩

/-- Power set `𝒫 x` in `VSet.{u}`. -/
noncomputable def power (x : VSet.{u}) : VSet.{u} :=
  ofFam (x.Idx → Prop) fun p => ofFam {i : x.Idx // p i} fun j => x.elem j.1

theorem mem_power {z x : VSet.{u}} : Mem z (power x) ↔ ∀ w, Mem w z → Mem w x := by
  rw [power, mem_ofFam]
  constructor
  · rintro ⟨p, rfl⟩ w hw
    obtain ⟨⟨i, _⟩, rfl⟩ := mem_ofFam.mp hw
    exact elem_mem x i
  · intro hsub
    refine ⟨fun i => Mem (x.elem i) z, ext fun w => ?_⟩
    rw [mem_ofFam]
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := mem_iff_exists_elem.mp (hsub w hw)
      exact ⟨⟨i, hw⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact hi

/-- Replacement image `{f w | w ∈ a}` in `VSet.{u}` for any Lean function `f`. -/
noncomputable def image (f : VSet.{u} → VSet.{u}) (a : VSet.{u}) : VSet.{u} :=
  ofFam a.Idx fun i => f (a.elem i)

theorem mem_image {f : VSet.{u} → VSet.{u}} {a z : VSet.{u}} :
    Mem z (image f a) ↔ ∃ w, Mem w a ∧ z = f w := by
  rw [image, mem_ofFam]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨a.elem i, elem_mem a i, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := mem_iff_exists_elem.mp hw
    exact ⟨i, rfl⟩

/-- Well-foundedness of `VSet.Mem`, proved by structural recursion on `PSet`. -/
private theorem acc_mk : ∀ x : PSet.{u}, Acc Mem (mk x)
  | .mk _ A => Acc.intro _ fun y hy => by
    refine Quotient.inductionOn y (fun z hz => ?_) hy
    obtain ⟨a, ha⟩ := hz
    have heq : mk z = mk (A a) := Quotient.sound ha
    change Acc Mem (mk z)
    rw [heq]
    exact acc_mk (A a)

theorem mem_wf : WellFounded Mem.{u} :=
  ⟨fun x => Quotient.inductionOn x acc_mk⟩

/-- Regularity (foundation) in `VSet.{u}`. -/
theorem regularity (x : VSet.{u}) (h : ∃ y, Mem y x) :
    ∃ y, Mem y x ∧ ¬ ∃ z, Mem z y ∧ Mem z x := by
  obtain ⟨y₀, hy₀⟩ := h
  suffices ∀ y, Mem y x → ∃ m, Mem m x ∧ ¬ ∃ z, Mem z m ∧ Mem z x from this y₀ hy₀
  intro y
  induction y using mem_wf.induction with
  | h y ih =>
    intro hy
    by_cases hsub : ∃ z, Mem z y ∧ Mem z x
    · obtain ⟨z, hzy, hzx⟩ := hsub
      exact ih z hzy hzx
    · exact ⟨y, hy, hsub⟩

theorem not_mem_self (x : VSet.{u}) : ¬ Mem x x := by
  intro hx
  obtain ⟨y, hy, hmin⟩ := regularity (sing x) ⟨x, mem_sing.mpr rfl⟩
  obtain rfl := mem_sing.mp hy
  exact hmin ⟨y, hx, mem_sing.mpr rfl⟩

theorem no_two_cycle {a b : VSet.{u}} (hab : Mem a b) (hba : Mem b a) : False := by
  obtain ⟨y, hy, hmin⟩ := regularity (upair a b) ⟨a, mem_upair.mpr (Or.inl rfl)⟩
  rcases mem_upair.mp hy with rfl | rfl
  · exact hmin ⟨b, hba, mem_upair.mpr (Or.inr rfl)⟩
  · exact hmin ⟨a, hab, mem_upair.mpr (Or.inl rfl)⟩

theorem no_three_cycle {a b c : VSet.{u}} (hab : Mem a b) (hbc : Mem b c) (hca : Mem c a) :
    False := by
  let t := binUnion (upair a b) (sing c)
  have ha : Mem a t := mem_binUnion.mpr (Or.inl (mem_upair.mpr (Or.inl rfl)))
  have hb : Mem b t := mem_binUnion.mpr (Or.inl (mem_upair.mpr (Or.inr rfl)))
  have hc : Mem c t := mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))
  obtain ⟨y, hy, hmin⟩ := regularity t ⟨a, ha⟩
  rcases mem_binUnion.mp hy with hy' | hy'
  · rcases mem_upair.mp hy' with rfl | rfl
    · exact hmin ⟨c, hca, hc⟩
    · exact hmin ⟨a, hab, ha⟩
  · obtain rfl := mem_sing.mp hy'
    exact hmin ⟨b, hbc, hb⟩

/-! ### Cantor-Schröder-Bernstein (pure Lean) -/

private inductive CSBReach {α : Type v} {β : Type w} (f : α → β) (g : β → α) : α → Prop
  | base {x : α} : (∀ b : β, g b ≠ x) → CSBReach f g x
  | step {x : α} : CSBReach f g x → CSBReach f g (g (f x))

/-- Cantor-Schröder-Bernstein: mutual injections yield a bijection. -/
private theorem csb {α : Type v} {β : Type w} {f : α → β} {g : β → α}
    (hf : ∀ x y, f x = f y → x = y) (hg : ∀ a b, g a = g b → a = b) :
    ∃ h : α → β, (∀ x y, h x = h y → x = y) ∧ (∀ b, ∃ x, h x = b) := by
  classical
  have hpre : ∀ x : α, ¬ CSBReach f g x → ∃ b : β, g b = x := by
    intro x hnx
    apply Classical.byContradiction
    intro hne
    exact hnx (CSBReach.base fun b hb => hne ⟨b, hb⟩)
  let h : α → β := fun x =>
    if hx : CSBReach f g x then f x else Classical.choose (hpre x hx)
  refine ⟨h, ?_, ?_⟩
  · intro x y hxy
    dsimp only [h] at hxy
    split at hxy <;> split at hxy
    · exact hf x y hxy
    · rename_i hx hny
      have hgy : g (Classical.choose (hpre y hny)) = y := Classical.choose_spec (hpre y hny)
      rw [← hxy] at hgy
      exact absurd (hgy ▸ CSBReach.step hx) hny
    · rename_i hnx hy
      have hgx : g (Classical.choose (hpre x hnx)) = x := Classical.choose_spec (hpre x hnx)
      rw [hxy] at hgx
      exact absurd (hgx ▸ CSBReach.step hy) hnx
    · rename_i hnx hny
      have hgx : g (Classical.choose (hpre x hnx)) = x := Classical.choose_spec (hpre x hnx)
      have hgy : g (Classical.choose (hpre y hny)) = y := Classical.choose_spec (hpre y hny)
      rw [← hgx, ← hgy, hxy]
  · intro b
    by_cases hgb : CSBReach f g (g b)
    · generalize hgb_eq : g b = y at hgb
      cases hgb with
      | base hno => exact absurd hgb_eq (hno b)
      | @step x hx =>
        refine ⟨x, ?_⟩
        dsimp only [h]
        rw [dif_pos hx]
        exact hg _ _ hgb_eq.symm
    · refine ⟨g b, ?_⟩
      dsimp only [h]
      rw [dif_neg hgb]
      exact hg _ _ (Classical.choose_spec (hpre (g b) hgb))

/-! ### Von Neumann ordinals inside `VSet.{u}` -/

/-- A transitive set: members of members are members. -/
def IsTrans (x : VSet.{u}) : Prop :=
  ∀ y z, Mem y x → Mem z y → Mem z x

/-- A von Neumann ordinal: transitive and linearly ordered by `Mem`. -/
def IsOrd (x : VSet.{u}) : Prop :=
  IsTrans x ∧ ∀ y z, Mem y x → Mem z x → Mem y z ∨ y = z ∨ Mem z y

/-- Von Neumann ordinals in `VSet.{u}`. -/
abbrev VOrd := {x : VSet.{u} // IsOrd x}

/-- Every member of a von Neumann ordinal is a von Neumann ordinal. -/
theorem isOrd_mem {α β : VSet.{u}} (hα : IsOrd α) (hβ : Mem β α) : IsOrd β := by
  refine ⟨?_, ?_⟩
  · intro y z hy hz
    have hyα : Mem y α := hα.1 β y hβ hy
    have hzα : Mem z α := hα.1 y z hyα hz
    rcases hα.2 z β hzα hβ with h | rfl | h
    · exact h
    · exact absurd hz (fun h1 => no_two_cycle hy h1)
    · exact absurd h (fun h1 => no_three_cycle h1 hz hy)
  · intro y z hy hz
    exact hα.2 y z (hα.1 β y hβ hy) (hα.1 β z hβ hz)

/-- Trichotomy for von Neumann ordinals. -/
theorem isOrd_trichotomy {α β : VSet.{u}} (hα : IsOrd α) (hβ : IsOrd β) :
    Mem α β ∨ α = β ∨ Mem β α := by
  by_cases heq : α = β
  · exact Or.inr (Or.inl heq)
  · -- Consider `α \ β` and `β \ α`.
    have hdiff : ∀ {a b : VSet.{u}}, IsOrd a → IsOrd b → (∀ x, Mem x a → Mem x b) →
        a ≠ b → Mem a b := by
      intro a b ha hb hsub hne
      have hex : ∃ y, Mem y (sep b fun z => ¬ Mem z a) := by
        apply Classical.byContradiction
        intro hno
        apply hne
        refine ext fun z => ⟨hsub z, fun hzb => ?_⟩
        apply Classical.byContradiction
        intro hza
        exact hno ⟨z, mem_sep.mpr ⟨hzb, hza⟩⟩
      obtain ⟨m, hm, hmin⟩ := regularity (sep b fun z => ¬ Mem z a) hex
      obtain ⟨hmb, hma⟩ := mem_sep.mp hm
      have heqm : a = m := by
        refine ext fun x => ⟨?_, ?_⟩
        · intro hxa
          rcases hb.2 x m (hsub x hxa) hmb with hxm | rfl | hmx
          · exact hxm
          · exact absurd hxa hma
          · exact absurd (ha.1 x m hxa hmx) hma
        · intro hxm
          have hxb : Mem x b := hb.1 m x hmb hxm
          apply Classical.byContradiction
          intro hxna
          exact hmin ⟨x, hxm, mem_sep.mpr ⟨hxb, hxna⟩⟩
      rw [heqm]
      exact hmb
    by_cases hab : ∀ x, Mem x α → Mem x β
    · exact Or.inl (hdiff hα hβ hab heq)
    · by_cases hba : ∀ x, Mem x β → Mem x α
      · exact Or.inr (Or.inr (hdiff hβ hα hba (Ne.symm heq)))
      · exfalso
        have hex1 : ∃ y, Mem y (sep α fun z => ¬ Mem z β) := by
          apply Classical.byContradiction
          intro hno
          apply hab
          intro x hxa
          apply Classical.byContradiction
          intro hxb
          exact hno ⟨x, mem_sep.mpr ⟨hxa, hxb⟩⟩
        have hex2 : ∃ y, Mem y (sep β fun z => ¬ Mem z α) := by
          apply Classical.byContradiction
          intro hno
          apply hba
          intro x hxb
          apply Classical.byContradiction
          intro hxa
          exact hno ⟨x, mem_sep.mpr ⟨hxb, hxa⟩⟩
        obtain ⟨m₁, hm₁, hmin₁⟩ := regularity (sep α fun z => ¬ Mem z β) hex1
        obtain ⟨m₂, hm₂, hmin₂⟩ := regularity (sep β fun z => ¬ Mem z α) hex2
        obtain ⟨hm₁α, hm₁nβ⟩ := mem_sep.mp hm₁
        obtain ⟨hm₂β, hm₂nα⟩ := mem_sep.mp hm₂
        have hm₁eq : m₁ = m₂ := by
          refine ext fun x => ⟨?_, ?_⟩
          · intro hxm₁
            have hxα : Mem x α := hα.1 m₁ x hm₁α hxm₁
            have hxβ : Mem x β := Classical.byContradiction fun h =>
              hmin₁ ⟨x, hxm₁, mem_sep.mpr ⟨hxα, h⟩⟩
            rcases hβ.2 x m₂ hxβ hm₂β with h | rfl | h
            · exact h
            · exact absurd hxα hm₂nα
            · exact absurd (hα.1 x m₂ hxα h) hm₂nα
          · intro hxm₂
            have hxβ : Mem x β := hβ.1 m₂ x hm₂β hxm₂
            have hxα : Mem x α := Classical.byContradiction fun h =>
              hmin₂ ⟨x, hxm₂, mem_sep.mpr ⟨hxβ, h⟩⟩
            rcases hα.2 x m₁ hxα hm₁α with h | rfl | h
            · exact h
            · exact absurd hxβ hm₁nβ
            · exact absurd (hβ.1 x m₁ hxβ h) hm₁nβ
        rw [hm₁eq] at hm₁α
        exact hm₂nα hm₁α

/-- Successor ordinal `α ∪ {α}`. -/
noncomputable def ordSucc (α : VOrd.{u}) : VOrd.{u} :=
  ⟨binUnion α.1 (sing α.1), by
    refine ⟨?_, ?_⟩
    · intro y z hy hz
      rcases mem_binUnion.mp hy with hy | hy
      · exact mem_binUnion.mpr (Or.inl (α.2.1 y z hy hz))
      · rw [mem_sing.mp hy] at hz
        exact mem_binUnion.mpr (Or.inl hz)
    · intro y z hy hz
      rcases mem_binUnion.mp hy with hy | hy <;> rcases mem_binUnion.mp hz with hz | hz
      · exact α.2.2 y z hy hz
      · rw [mem_sing.mp hz]; exact Or.inl hy
      · rw [mem_sing.mp hy]; exact Or.inr (Or.inr hz)
      · rw [mem_sing.mp hy, mem_sing.mp hz]; exact Or.inr (Or.inl rfl)⟩

theorem mem_ordSucc_iff {x : VSet.{u}} {α : VOrd.{u}} :
    Mem x (ordSucc α).1 ↔ Mem x α.1 ∨ x = α.1 := by
  show Mem x (binUnion α.1 (sing α.1)) ↔ Mem x α.1 ∨ x = α.1
  rw [mem_binUnion, mem_sing]

theorem self_mem_ordSucc (α : VOrd.{u}) : Mem α.1 (ordSucc α).1 :=
  mem_ordSucc_iff.mpr (Or.inr rfl)

/-- Supremum of a `Type u`-indexed family of von Neumann ordinals. -/
noncomputable def ordSup {ι : Type u} (f : ι → VOrd.{u}) : VOrd.{u} :=
  ⟨sUnion (ofFam ι fun i => (f i).1), by
    refine ⟨?_, ?_⟩
    · intro y z hy hz
      obtain ⟨w, hw, hyw⟩ := mem_sUnion.mp hy
      obtain ⟨i, rfl⟩ := mem_ofFam.mp hw
      exact mem_sUnion.mpr ⟨(f i).1, mem_ofFam.mpr ⟨i, rfl⟩, (f i).2.1 y z hyw hz⟩
    · intro y z hy hz
      obtain ⟨w₁, hw₁, hyw₁⟩ := mem_sUnion.mp hy
      obtain ⟨i₁, rfl⟩ := mem_ofFam.mp hw₁
      obtain ⟨w₂, hw₂, hzw₂⟩ := mem_sUnion.mp hz
      obtain ⟨i₂, rfl⟩ := mem_ofFam.mp hw₂
      exact isOrd_trichotomy (isOrd_mem (f i₁).2 hyw₁) (isOrd_mem (f i₂).2 hzw₂)⟩

theorem mem_ordSup_iff {ι : Type u} {f : ι → VOrd.{u}} {z : VSet.{u}} :
    Mem z (ordSup f).1 ↔ ∃ i : ι, Mem z (f i).1 := by
  show Mem z (sUnion (ofFam ι fun i => (f i).1)) ↔ ∃ i : ι, Mem z (f i).1
  rw [mem_sUnion]
  constructor
  · rintro ⟨w, hw, hzw⟩
    obtain ⟨i, rfl⟩ := mem_ofFam.mp hw
    exact ⟨i, hzw⟩
  · rintro ⟨i, hi⟩
    exact ⟨(f i).1, mem_ofFam.mpr ⟨i, rfl⟩, hi⟩

theorem subset_ordSup {ι : Type u} (f : ι → VOrd.{u}) (i : ι) {z : VSet.{u}}
    (hz : Mem z (f i).1) : Mem z (ordSup f).1 :=
  mem_ordSup_iff.mpr ⟨i, hz⟩

/-- Maximum of two von Neumann ordinals. -/
noncomputable def ordMax (α β : VOrd.{u}) : VOrd.{u} :=
  ⟨binUnion α.1 β.1, by
    refine ⟨?_, ?_⟩
    · intro y z hy hz
      rcases mem_binUnion.mp hy with hy | hy
      · exact mem_binUnion.mpr (Or.inl (α.2.1 y z hy hz))
      · exact mem_binUnion.mpr (Or.inr (β.2.1 y z hy hz))
    · intro y z hy hz
      have hyo : IsOrd y := by
        rcases mem_binUnion.mp hy with hy | hy
        · exact isOrd_mem α.2 hy
        · exact isOrd_mem β.2 hy
      have hzo : IsOrd z := by
        rcases mem_binUnion.mp hz with hz | hz
        · exact isOrd_mem α.2 hz
        · exact isOrd_mem β.2 hz
      exact isOrd_trichotomy hyo hzo⟩

theorem ordMax_eq_left_or_right (α β : VOrd.{u}) :
    ordMax α β = α ∨ ordMax α β = β := by
  rcases isOrd_trichotomy α.2 β.2 with h | h | h
  · right
    apply Subtype.ext
    refine ext fun z => ⟨?_, fun hz => mem_binUnion.mpr (Or.inr hz)⟩
    intro hz
    rcases mem_binUnion.mp hz with hz | hz
    · exact β.2.1 α.1 z h hz
    · exact hz
  · left
    apply Subtype.ext
    refine ext fun z => ⟨?_, fun hz => mem_binUnion.mpr (Or.inl hz)⟩
    intro hz
    rcases mem_binUnion.mp hz with hz | hz
    · exact hz
    · rw [← h] at hz; exact hz
  · left
    apply Subtype.ext
    refine ext fun z => ⟨?_, fun hz => mem_binUnion.mpr (Or.inl hz)⟩
    intro hz
    rcases mem_binUnion.mp hz with hz | hz
    · exact hz
    · exact α.2.1 β.1 z h hz

theorem left_le_ordMax (α β : VOrd.{u}) :
    Mem α.1 (ordMax α β).1 ∨ α = ordMax α β := by
  rcases isOrd_trichotomy α.2 (ordMax α β).2 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Subtype.ext h)
  · exfalso
    rcases ordMax_eq_left_or_right α β with hm | hm
    · rw [hm] at h; exact not_mem_self α.1 h
    · rw [hm] at h
      have hsub : Mem β.1 (ordMax α β).1 := by
        show Mem β.1 (binUnion α.1 β.1)
        exact mem_binUnion.mpr (Or.inl h)
      rw [hm] at hsub
      exact not_mem_self β.1 hsub

theorem right_le_ordMax (α β : VOrd.{u}) :
    Mem β.1 (ordMax α β).1 ∨ β = ordMax α β := by
  rcases isOrd_trichotomy β.2 (ordMax α β).2 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Subtype.ext h)
  · exfalso
    rcases ordMax_eq_left_or_right α β with hm | hm
    · rw [hm] at h
      have hsub : Mem α.1 (ordMax α β).1 := by
        show Mem α.1 (binUnion α.1 β.1)
        exact mem_binUnion.mpr (Or.inr h)
      rw [hm] at hsub
      exact not_mem_self α.1 hsub
    · rw [hm] at h; exact not_mem_self β.1 h

/-- Order relation on `VOrd.{u}`. -/
def VOrd.Lt (α β : VOrd.{u}) : Prop := Mem α.1 β.1

theorem vord_wf : WellFounded VOrd.Lt.{u} :=
  InvImage.wf Subtype.val mem_wf

/-- Burali-Forti: no `VSet.{u}` contains every von Neumann ordinal of `VSet.{u}`. -/
theorem buraliForti : ¬ ∃ x : VSet.{u}, ∀ α : VOrd.{u}, Mem α.1 x := by
  rintro ⟨x, hx⟩
  let Ω : VSet.{u} := sep x IsOrd
  have hΩ : IsOrd Ω := by
    refine ⟨?_, ?_⟩
    · intro y z hy hz
      have hyo : IsOrd y := (mem_sep.mp hy).2
      have hzo : IsOrd z := isOrd_mem hyo hz
      exact mem_sep.mpr ⟨hx ⟨z, hzo⟩, hzo⟩
    · intro y z hy hz
      exact isOrd_trichotomy (mem_sep.mp hy).2 (mem_sep.mp hz).2
  exact not_mem_self Ω (mem_sep.mpr ⟨hx ⟨Ω, hΩ⟩, hΩ⟩)

/-! ### Rank, von Neumann stages, well-ordering of sets, and Gödel pairing -/

/-- Von Neumann rank of a pre-set. -/
noncomputable def prank : PSet.{u} → VOrd.{u}
  | .mk _ A => ordSup fun a => ordSucc (prank (A a))

theorem prank_congr : ∀ {x y : PSet.{u}}, PSet.Equiv x y → prank x = prank y
  | .mk _ A, .mk _ B, ⟨h1, h2⟩ => by
    apply Subtype.ext
    refine ext fun z => ?_
    change Mem z (ordSup fun a => ordSucc (prank (A a))).1 ↔
      Mem z (ordSup fun b => ordSucc (prank (B b))).1
    rw [mem_ordSup_iff, mem_ordSup_iff]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hab⟩ := h1 a
      exact ⟨b, prank_congr hab ▸ ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, hab⟩ := h2 b
      exact ⟨a, (prank_congr hab).symm ▸ hb⟩

/-- Von Neumann rank of a `VSet.{u}`. -/
noncomputable def vrank (x : VSet.{u}) : VOrd.{u} :=
  Quotient.lift prank (fun _ _ h => prank_congr h) x

theorem vrank_lt_of_mem {y x : VSet.{u}} (hy : Mem y x) :
    Mem (vrank y).1 (vrank x).1 := by
  refine Quotient.inductionOn₂ y x (fun a b hab => ?_) hy
  cases b with
  | mk β B =>
    obtain ⟨i, hi⟩ := hab
    have hEq : prank a = prank (B i) := prank_congr hi
    unfold vrank
    change Mem (prank a).1 (ordSup fun j => ordSucc (prank (B j))).1
    rw [hEq]
    exact subset_ordSup (fun j => ordSucc (prank (B j))) i (self_mem_ordSucc _)

/-- Cumulative von Neumann stage `V_α` inside `VSet.{u}`: `V_α = ⋃_{β ∈ α} 𝒫(V_β)`. -/
noncomputable def vonNeumann : VOrd.{u} → VSet.{u} :=
  vord_wf.fix fun α rec =>
    sUnion (ofFam α.1.Idx fun i =>
      power (rec ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩ (elem_mem α.1 i)))

theorem vonNeumann_eq (α : VOrd.{u}) :
    vonNeumann α =
      sUnion (ofFam α.1.Idx fun i =>
        power (vonNeumann ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩)) :=
  vord_wf.fix_eq _ α

theorem mem_vonNeumann_iff {α : VOrd.{u}} {x : VSet.{u}} :
    Mem x (vonNeumann α) ↔
      ∃ β : VOrd.{u}, Mem β.1 α.1 ∧ ∀ w, Mem w x → Mem w (vonNeumann β) := by
  rw [vonNeumann_eq α, mem_sUnion]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨i, rfl⟩ := mem_ofFam.mp hs
    exact ⟨⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩, elem_mem α.1 i, mem_power.mp hxs⟩
  · rintro ⟨β, hβα, hsub⟩
    obtain ⟨i, hi⟩ := mem_iff_exists_elem.mp hβα
    refine ⟨power (vonNeumann ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩),
      mem_ofFam.mpr ⟨i, rfl⟩, mem_power.mpr ?_⟩
    have hβeq : (⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩ : VOrd.{u}) = β :=
      Subtype.ext hi.symm
    rw [hβeq]
    exact hsub

theorem vonNeumann_mono {α β : VOrd.{u}} (h : ∀ z, Mem z α.1 → Mem z β.1) {x : VSet.{u}}
    (hx : Mem x (vonNeumann α)) : Mem x (vonNeumann β) := by
  obtain ⟨γ, hγα, hsub⟩ := mem_vonNeumann_iff.mp hx
  exact mem_vonNeumann_iff.mpr ⟨γ, h γ.1 hγα, hsub⟩

/-- Every set lies in `V_{rank(x) + 1}`. -/
theorem mem_vonNeumann_succ_vrank (x : VSet.{u}) :
    Mem x (vonNeumann (ordSucc (vrank x))) := by
  induction x using mem_wf.induction with
  | h x ih =>
    refine mem_vonNeumann_iff.mpr ⟨vrank x, self_mem_ordSucc (vrank x), fun y hy => ?_⟩
    have hsub : ∀ z, Mem z (ordSucc (vrank y)).1 → Mem z (vrank x).1 := by
      intro z hz
      have hlt : Mem (vrank y).1 (vrank x).1 := vrank_lt_of_mem hy
      rcases mem_ordSucc_iff.mp hz with hz | rfl
      · exact (vrank x).2.1 (vrank y).1 z hlt hz
      · exact hlt
    exact vonNeumann_mono hsub (ih y hy)

open Classical in
/-- Transfinite enumeration of a set `A : VSet.{u}` by von Neumann ordinals. -/
private noncomputable def enumSet (A : VSet.{u}) : VOrd.{u} → Option VSet.{u} :=
  vord_wf.fix fun α rec =>
    if h : ∃ x, Mem x A ∧ ∀ (β : VOrd.{u}) (hβ : Mem β.1 α.1), rec β hβ ≠ some x then
      some (Classical.choose h)
    else none

open Classical in
private theorem enumSet_eq (A : VSet.{u}) (α : VOrd.{u}) :
    enumSet A α =
      if h : ∃ x, Mem x A ∧ ∀ β : VOrd.{u}, Mem β.1 α.1 → enumSet A β ≠ some x then
        some (Classical.choose h)
      else none :=
  vord_wf.fix_eq _ α

private theorem enumSet_inj (A : VSet.{u}) {α β : VOrd.{u}} {x : VSet.{u}}
    (hα : enumSet A α = some x) (hβ : enumSet A β = some x) : α = β := by
  rcases isOrd_trichotomy α.2 β.2 with hlt | heq | hgt
  · exfalso
    rw [enumSet_eq A β] at hβ
    split at hβ
    · rename_i h
      have hspec := Classical.choose_spec h
      have hxeq : Classical.choose h = x := Option.some.inj hβ
      rw [hxeq] at hspec
      exact hspec.2 α hlt hα
    · cases hβ
  · exact Subtype.ext heq
  · exfalso
    rw [enumSet_eq A α] at hα
    split at hα
    · rename_i h
      have hspec := Classical.choose_spec h
      have hxeq : Classical.choose h = x := Option.some.inj hα
      rw [hxeq] at hspec
      exact hspec.2 β hgt hβ
    · cases hα

/-- Every set `A : VSet.{u}` injects into `VOrd.{u}` (via `Classical.choice` and Burali-Forti). -/
private theorem exists_inj_to_vord (A : VSet.{u}) :
    ∃ f : VSet.{u} → VOrd.{u}, ∀ x y, Mem x A → Mem y A → f x = f y → x = y := by
  have hcov : ∀ x, Mem x A → ∃ α : VOrd.{u}, enumSet A α = some x := by
    intro x hxA
    apply Classical.byContradiction
    intro hno
    have hall : ∀ α : VOrd.{u}, ∃ y, Mem y A ∧ enumSet A α = some y := by
      intro α
      have hex : ∃ y, Mem y A ∧ ∀ β : VOrd.{u}, Mem β.1 α.1 → enumSet A β ≠ some y :=
        ⟨x, hxA, fun β _ hβ => hno ⟨β, hβ⟩⟩
      refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, ?_⟩
      rw [enumSet_eq A α, dif_pos hex]
    classical
    let inv : VSet.{u} → VSet.{u} := fun y =>
      if h : ∃ α : VOrd.{u}, enumSet A α = some y then (Classical.choose h).1 else empty
    apply buraliForti.{u}
    refine ⟨image inv A, fun α => ?_⟩
    obtain ⟨y, hyA, hαy⟩ := hall α
    refine mem_image.mpr ⟨y, hyA, ?_⟩
    have hex : ∃ β : VOrd.{u}, enumSet A β = some y := ⟨α, hαy⟩
    have hinv : inv y = (Classical.choose hex).1 := dif_pos hex
    rw [hinv]
    exact congrArg Subtype.val (enumSet_inj A hαy (Classical.choose_spec hex))
  classical
  let f : VSet.{u} → VOrd.{u} := fun x =>
    if hx : Mem x A then Classical.choose (hcov x hx) else ⟨empty, ⟨fun _ _ h => absurd h (not_mem_empty _), fun _ _ h => absurd h (not_mem_empty _)⟩⟩
  refine ⟨f, fun x y hx hy hxy => ?_⟩
  have hfx : f x = Classical.choose (hcov x hx) := dif_pos hx
  have hfy : f y = Classical.choose (hcov y hy) := dif_pos hy
  have hspecx : enumSet A (f x) = some x := hfx ▸ Classical.choose_spec (hcov x hx)
  have hspecy : enumSet A (f y) = some y := hfy ▸ Classical.choose_spec (hcov y hy)
  rw [hxy] at hspecx
  exact Option.some.inj (hspecx.symm.trans hspecy)

/-- Gödel's well-ordering on pairs of ordinals: compare by `(max a b, a, b)`. -/
private def PairLt (p q : VOrd.{u} × VOrd.{u}) : Prop :=
  Mem (ordMax p.1 p.2).1 (ordMax q.1 q.2).1 ∨
  (ordMax p.1 p.2 = ordMax q.1 q.2 ∧
    (Mem p.1.1 q.1.1 ∨ (p.1 = q.1 ∧ Mem p.2.1 q.2.1)))

private theorem pairLt_wf : WellFounded PairLt.{u} := by
  constructor
  intro ⟨a, b⟩
  -- Triple nested well-founded induction on `(ordMax a b, a, b)`.
  suffices ∀ (m : VOrd.{u}) (a b : VOrd.{u}), ordMax a b = m → Acc PairLt (a, b) from
    this (ordMax a b) a b rfl
  intro m
  induction m using vord_wf.induction with
  | h m ihm =>
    intro a
    induction a using vord_wf.induction with
    | h a iha =>
      intro b
      induction b using vord_wf.induction with
      | h b ihb =>
        intro hm
        refine Acc.intro (a, b) fun ⟨a', b'⟩ hlt => ?_
        rcases hlt with hmax | ⟨hmax, ha | ⟨rfl, hb⟩⟩
        · rw [hm] at hmax
          exact ihm (ordMax a' b') hmax a' b' rfl
        · exact iha a' ha b' (hmax.trans hm)
        · exact ihb b' hb (hmax.trans hm)

private theorem pairLt_trichotomy (p q : VOrd.{u} × VOrd.{u}) :
    PairLt p q ∨ p = q ∨ PairLt q p := by
  rcases isOrd_trichotomy (ordMax p.1 p.2).2 (ordMax q.1 q.2).2 with h | h | h
  · exact Or.inl (Or.inl h)
  · have hm : ordMax p.1 p.2 = ordMax q.1 q.2 := Subtype.ext h
    rcases isOrd_trichotomy p.1.2 q.1.2 with ha | ha | ha
    · exact Or.inl (Or.inr ⟨hm, Or.inl ha⟩)
    · have ha' : p.1 = q.1 := Subtype.ext ha
      rcases isOrd_trichotomy p.2.2 q.2.2 with hb | hb | hb
      · exact Or.inl (Or.inr ⟨hm, Or.inr ⟨ha', hb⟩⟩)
      · exact Or.inr (Or.inl (Prod.ext ha' (Subtype.ext hb)))
      · exact Or.inr (Or.inr (Or.inr ⟨hm.symm, Or.inr ⟨ha'.symm, hb⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hm.symm, Or.inl ha⟩))
  · exact Or.inr (Or.inr (Or.inl h))

private theorem pairLt_components_lt {p q : VOrd.{u} × VOrd.{u}} (h : PairLt p q) :
    Mem p.1.1 (ordSucc (ordMax q.1 q.2)).1 ∧ Mem p.2.1 (ordSucc (ordMax q.1 q.2)).1 := by
  have hbound : ∀ x : VOrd.{u}, (Mem x.1 (ordMax p.1 p.2).1 ∨ x = ordMax p.1 p.2) →
      Mem x.1 (ordSucc (ordMax q.1 q.2)).1 := by
    intro x hx
    rcases h with hlt | ⟨heq, _⟩
    · rcases hx with hxm | rfl
      · exact mem_ordSucc_iff.mpr (Or.inl ((ordMax q.1 q.2).2.1 _ _ hlt hxm))
      · exact mem_ordSucc_iff.mpr (Or.inl hlt)
    · rw [heq] at hx
      rcases hx with hxm | rfl
      · exact mem_ordSucc_iff.mpr (Or.inl hxm)
      · exact self_mem_ordSucc _
  exact ⟨hbound p.1 (left_le_ordMax p.1 p.2), hbound p.2 (right_le_ordMax p.1 p.2)⟩

/-- Gödel pairing `VOrd.{u} × VOrd.{u} → VOrd.{u}` via transfinite recursion on `PairLt`. -/
private noncomputable def gpair : VOrd.{u} × VOrd.{u} → VOrd.{u} :=
  pairLt_wf.fix fun q rec =>
    let M := ordSucc (ordMax q.1 q.2)
    let toPair (ij : M.1.Idx × M.1.Idx) : VOrd.{u} × VOrd.{u} :=
      (⟨M.1.elem ij.1, isOrd_mem M.2 (elem_mem M.1 ij.1)⟩,
       ⟨M.1.elem ij.2, isOrd_mem M.2 (elem_mem M.1 ij.2)⟩)
    ordSup fun (p : {ij : M.1.Idx × M.1.Idx // PairLt (toPair ij) q}) =>
      ordSucc (rec (toPair p.1) p.2)

private theorem gpair_lt_of_pairLt {p q : VOrd.{u} × VOrd.{u}} (h : PairLt p q) :
    Mem (gpair p).1 (gpair q).1 := by
  obtain ⟨h1, h2⟩ := pairLt_components_lt h
  obtain ⟨i, hi⟩ := mem_iff_exists_elem.mp h1
  obtain ⟨j, hj⟩ := mem_iff_exists_elem.mp h2
  let M := ordSucc (ordMax q.1 q.2)
  let toPair (ij : M.1.Idx × M.1.Idx) : VOrd.{u} × VOrd.{u} :=
    (⟨M.1.elem ij.1, isOrd_mem M.2 (elem_mem M.1 ij.1)⟩,
     ⟨M.1.elem ij.2, isOrd_mem M.2 (elem_mem M.1 ij.2)⟩)
  have hpeq : toPair (i, j) = p := Prod.ext (Subtype.ext hi.symm) (Subtype.ext hj.symm)
  have hlt : PairLt (toPair (i, j)) q := hpeq.symm ▸ h
  have hstep : gpair q =
      ordSup fun (r : {ij : M.1.Idx × M.1.Idx // PairLt (toPair ij) q}) =>
        ordSucc (gpair (toPair r.1)) :=
    pairLt_wf.fix_eq _ q
  rw [hstep]
  have hmem := subset_ordSup
    (fun (r : {ij : M.1.Idx × M.1.Idx // PairLt (toPair ij) q}) =>
      ordSucc (gpair (toPair r.1)))
    ⟨(i, j), hlt⟩ (self_mem_ordSucc (gpair (toPair (i, j))))
  rwa [hpeq] at hmem

private theorem gpair_inj {p q : VOrd.{u} × VOrd.{u}} (h : gpair p = gpair q) : p = q := by
  rcases pairLt_trichotomy p q with hlt | heq | hgt
  · exfalso
    have hm := gpair_lt_of_pairLt hlt
    rw [h] at hm
    exact not_mem_self _ hm
  · exact heq
  · exfalso
    have hm := gpair_lt_of_pairLt hgt
    rw [h] at hm
    exact not_mem_self _ hm

/-- Every `VSet.{u}` injects into `VOrd.{u}` via `(vrank x, stage-index x)`. -/
private theorem exists_vset_inj_vord :
    ∃ f : VSet.{u} → VOrd.{u}, ∀ x y, f x = f y → x = y := by
  let idxOf (α : VOrd.{u}) : VSet.{u} → VOrd.{u} :=
    Classical.choose (exists_inj_to_vord (vonNeumann (ordSucc α)))
  have hidxOf (α : VOrd.{u}) :
      ∀ x y, Mem x (vonNeumann (ordSucc α)) → Mem y (vonNeumann (ordSucc α)) →
        idxOf α x = idxOf α y → x = y :=
    Classical.choose_spec (exists_inj_to_vord (vonNeumann (ordSucc α)))
  refine ⟨fun x => gpair (vrank x, idxOf (vrank x) x), fun x y hxy => ?_⟩
  have hp := gpair_inj hxy
  have hr : vrank x = vrank y := congrArg Prod.fst hp
  have hi : idxOf (vrank x) x = idxOf (vrank y) y := congrArg Prod.snd hp
  have hmx : Mem x (vonNeumann (ordSucc (vrank x))) := mem_vonNeumann_succ_vrank x
  have hmy : Mem y (vonNeumann (ordSucc (vrank x))) := hr ▸ mem_vonNeumann_succ_vrank y
  rw [← hr] at hi
  exact hidxOf (vrank x) x y hmx hmy hi

/-! ### Universe lifting and Grothendieck universes in `VSet` -/

/-- Embed `VSet.{u}` transitively into `VSet.{u + 1}`. -/
def lift : VSet.{u} → VSet.{u + 1} :=
  Quotient.lift (fun x => mk x.lift) fun _ _ h => Quotient.sound (PSet.Equiv.lift_iff.mp h)

theorem lift_inj {x y : VSet.{u}} (h : lift x = lift y) : x = y := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) h
  exact Quotient.sound (PSet.Equiv.lift_iff.mpr (Quotient.exact hab))

theorem mem_lift_iff {x y : VSet.{u}} : Mem (lift x) (lift y) ↔ Mem x y := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  cases b with
  | mk β B =>
    change (∃ i : ULift.{u + 1} β, PSet.Equiv a.lift (B i.down).lift) ↔
      ∃ i : β, PSet.Equiv a (B i)
    exact ⟨fun ⟨⟨i⟩, hi⟩ => ⟨i, PSet.Equiv.lift_iff.mpr hi⟩,
           fun ⟨i, hi⟩ => ⟨⟨i⟩, PSet.Equiv.lift_iff.mp hi⟩⟩

theorem mem_lift_exists {w : VSet.{u + 1}} {y : VSet.{u}} (h : Mem w (lift y)) :
    ∃ x : VSet.{u}, w = lift x ∧ Mem x y := by
  refine Quotient.inductionOn₂ w y (fun a b hab => ?_) h
  cases b with
  | mk β B =>
    obtain ⟨⟨i⟩, hi⟩ := hab
    exact ⟨mk (B i), Quotient.sound hi, ⟨i, PSet.Equiv.refl _⟩⟩

/-- The set of all lifted `VSet.{u}` sets, living inside `VSet.{u + 1}`. -/
noncomputable def univSet : VSet.{u + 1} :=
  ofFam.{u + 1} VSet.{u} lift

theorem mem_univSet {w : VSet.{u + 1}} :
    Mem w univSet.{u} ↔ ∃ x : VSet.{u}, w = lift x :=
  mem_ofFam

/-- A predicate on `VSet.{u}` is `Type u`-small if covered by a `Type u`-indexed family. -/
private def SmallPred (P : VSet.{u} → Prop) : Prop :=
  ∃ (α : Type u) (f : α → VSet.{u}), ∀ x, P x → ∃ a : α, f a = x

/-- Any non-small predicate on `VSet.{u}` receives an injection from `VOrd.{u}`. -/
private noncomputable def enumUnbounded (P : VSet.{u} → Prop) (hns : ¬ SmallPred P) :
    VOrd.{u} → {x : VSet.{u} // P x} :=
  vord_wf.fix fun α rec =>
    have hex : ∃ x, P x ∧ ∀ (β : VOrd.{u}) (hβ : Mem β.1 α.1), (rec β hβ).1 ≠ x := by
      apply Classical.byContradiction
      intro hno
      apply hns
      refine ⟨α.1.Idx,
        fun i => (rec ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩ (elem_mem α.1 i)).1, ?_⟩
      intro x hx
      have hhit : ¬ ∀ (β : VOrd.{u}) (hβ : Mem β.1 α.1), (rec β hβ).1 ≠ x := fun hall =>
        hno ⟨x, hx, hall⟩
      have hexβ : ∃ (β : VOrd.{u}), ∃ (hβ : Mem β.1 α.1), (rec β hβ).1 = x := by
        apply Classical.byContradiction
        intro hne
        exact hhit fun β hβ heq => hne ⟨β, hβ, heq⟩
      obtain ⟨β, hβ, hrec⟩ := hexβ
      obtain ⟨i, hi⟩ := mem_iff_exists_elem.mp hβ
      refine ⟨i, ?_⟩
      have hβeq : β = ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩ := Subtype.ext hi
      subst hβeq
      exact hrec
    ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

private theorem enumUnbounded_inj (P : VSet.{u} → Prop) (hns : ¬ SmallPred P) :
    ∀ α β : VOrd.{u}, enumUnbounded P hns α = enumUnbounded P hns β → α = β := by
  have hneq : ∀ α β : VOrd.{u}, Mem β.1 α.1 →
      (enumUnbounded P hns β).1 ≠ (enumUnbounded P hns α).1 := by
    intro α β hlt
    have hex : ∃ x, P x ∧ ∀ (γ : VOrd.{u}), Mem γ.1 α.1 → (enumUnbounded P hns γ).1 ≠ x := by
      apply Classical.byContradiction
      intro hno
      apply hns
      refine ⟨α.1.Idx,
        fun i => (enumUnbounded P hns ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩).1, ?_⟩
      intro x hx
      have hhit : ¬ ∀ (γ : VOrd.{u}), Mem γ.1 α.1 → (enumUnbounded P hns γ).1 ≠ x :=
        fun hall => hno ⟨x, hx, hall⟩
      have hexγ : ∃ (γ : VOrd.{u}), Mem γ.1 α.1 ∧ (enumUnbounded P hns γ).1 = x := by
        apply Classical.byContradiction
        intro hne
        exact hhit fun γ hγ heq => hne ⟨γ, hγ, heq⟩
      obtain ⟨γ, hγ, hrec⟩ := hexγ
      obtain ⟨i, hi⟩ := mem_iff_exists_elem.mp hγ
      refine ⟨i, ?_⟩
      have hγeq : γ = ⟨α.1.elem i, isOrd_mem α.2 (elem_mem α.1 i)⟩ := Subtype.ext hi
      subst hγeq
      exact hrec
    have hstep : enumUnbounded P hns α = ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩ :=
      vord_wf.fix_eq _ α
    rw [hstep]
    exact (Classical.choose_spec hex).2 β hlt
  intro α β heq
  rcases isOrd_trichotomy α.2 β.2 with hlt | h | hgt
  · exact absurd (congrArg Subtype.val heq) (hneq β α hlt)
  · exact Subtype.ext h
  · exact absurd (congrArg Subtype.val heq.symm) (hneq α β hgt)

/-- **`VSet.univSet.{u}` is a Grothendieck universe (`Ix.Kernel.IsTGUniverse`) inside `VSet.{u + 1}`.** -/
theorem isTGUniverse_univSet : IsTGUniverse Mem.{u + 1} univSet.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Clause 1: transitivity
    intro y z hy hz
    obtain ⟨y₀, rfl⟩ := mem_univSet.mp hy
    obtain ⟨z₀, rfl, -⟩ := mem_lift_exists hz
    exact mem_univSet.mpr ⟨z₀, rfl⟩
  · -- Clause 2: subsets of members are members
    intro y z hy hsub
    obtain ⟨y₀, rfl⟩ := mem_univSet.mp hy
    refine mem_univSet.mpr ⟨sep y₀ fun w₀ => Mem (lift w₀) z, ext fun w => ?_⟩
    constructor
    · intro hw
      obtain ⟨w₀, rfl, hwy₀⟩ := mem_lift_exists (hsub w hw)
      exact mem_lift_iff.mpr (mem_sep.mpr ⟨hwy₀, hw⟩)
    · intro hw
      obtain ⟨w₀, rfl, hsep⟩ := mem_lift_exists hw
      exact (mem_sep.mp hsep).2
  · -- Clause 3: power sets stay inside
    intro y hy
    obtain ⟨y₀, rfl⟩ := mem_univSet.mp hy
    refine ⟨lift (power y₀), mem_univSet.mpr ⟨power y₀, rfl⟩, fun z hsub => ?_⟩
    have hz : z = lift (sep y₀ fun w₀ => Mem (lift w₀) z) := by
      refine ext fun w => ?_
      constructor
      · intro hw
        obtain ⟨w₀, rfl, hwy₀⟩ := mem_lift_exists (hsub w hw)
        exact mem_lift_iff.mpr (mem_sep.mpr ⟨hwy₀, hw⟩)
      · intro hw
        obtain ⟨w₀, rfl, hsep⟩ := mem_lift_exists hw
        exact (mem_sep.mp hsep).2
    rw [hz, mem_lift_iff, mem_power]
    intro w₀ hw₀
    exact (mem_sep.mp hw₀).1
  · -- Clause 4: Tarski inaccessibility
    intro y hsub
    let P : VSet.{u} → Prop := fun x => Mem (lift x) y
    by_cases hsm : SmallPred P
    · right
      obtain ⟨α, f, hcov⟩ := hsm
      let y₀ : VSet.{u} := ofFam {a : α // P (f a)} fun j => f j.1
      refine mem_univSet.mpr ⟨y₀, ext fun w => ?_⟩
      constructor
      · intro hw
        obtain ⟨w₀, rfl⟩ := mem_univSet.mp (hsub w hw)
        obtain ⟨a, ha⟩ := hcov w₀ hw
        have hpa : P (f a) := ha ▸ hw
        exact mem_lift_iff.mpr (mem_ofFam.mpr ⟨⟨a, hpa⟩, ha.symm⟩)
      · intro hw
        obtain ⟨w₀, rfl, hw₀⟩ := mem_lift_exists hw
        obtain ⟨⟨a, hpa⟩, rfl⟩ := mem_ofFam.mp hw₀
        exact hpa
    · left
      obtain ⟨toOrd, htoOrd⟩ := exists_vset_inj_vord.{u}
      let fSub : {x : VSet.{u} // P x} → VSet.{u} := Subtype.val
      let gSub : VSet.{u} → {x : VSet.{u} // P x} := fun x => enumUnbounded P hsm (toOrd x)
      have hfSub : ∀ a b : {x : VSet.{u} // P x}, fSub a = fSub b → a = b :=
        fun _ _ h => Subtype.ext h
      have hgSub : ∀ a b : VSet.{u}, gSub a = gSub b → a = b :=
        fun _ _ h => htoOrd _ _ (enumUnbounded_inj P hsm _ _ h)
      obtain ⟨bij, hbij_inj, hbij_surj⟩ := csb hfSub hgSub
      classical
      let F : VSet.{u + 1} → VSet.{u + 1} := fun z =>
        if h : ∃ x : VSet.{u}, z = lift x ∧ P x then
          lift (bij ⟨Classical.choose h, (Classical.choose_spec h).2⟩)
        else z
      refine ⟨F, ?_, ?_, ?_⟩
      · intro z hz
        obtain ⟨x, rfl⟩ := mem_univSet.mp (hsub z hz)
        have hex : ∃ x₀ : VSet.{u}, lift x = lift x₀ ∧ P x₀ := ⟨x, rfl, hz⟩
        have hF : F (lift x) = lift (bij ⟨Classical.choose hex, (Classical.choose_spec hex).2⟩) :=
          dif_pos hex
        rw [hF]
        exact mem_univSet.mpr ⟨_, rfl⟩
      · intro z z' hz hz' hFzz'
        obtain ⟨x, rfl⟩ := mem_univSet.mp (hsub z hz)
        obtain ⟨x', rfl⟩ := mem_univSet.mp (hsub z' hz')
        have hex : ∃ x₀ : VSet.{u}, lift x = lift x₀ ∧ P x₀ := ⟨x, rfl, hz⟩
        have hex' : ∃ x₀ : VSet.{u}, lift x' = lift x₀ ∧ P x₀ := ⟨x', rfl, hz'⟩
        have hx0 : Classical.choose hex = x := (lift_inj (Classical.choose_spec hex).1).symm
        have hx0' : Classical.choose hex' = x' := (lift_inj (Classical.choose_spec hex').1).symm
        rw [show F (lift x) = lift (bij ⟨Classical.choose hex, (Classical.choose_spec hex).2⟩) from
              dif_pos hex,
            show F (lift x') = lift (bij ⟨Classical.choose hex', (Classical.choose_spec hex').2⟩) from
              dif_pos hex'] at hFzz'
        have hsubeq := hbij_inj _ _ (lift_inj hFzz')
        have hval := congrArg Subtype.val hsubeq
        simp only at hval
        rw [hx0, hx0'] at hval
        rw [hval]
      · intro w hw
        obtain ⟨w₀, rfl⟩ := mem_univSet.mp hw
        obtain ⟨⟨x, hx⟩, hbx⟩ := hbij_surj w₀
        refine ⟨lift x, hx, ?_⟩
        have hex : ∃ x₀ : VSet.{u}, lift x = lift x₀ ∧ P x₀ := ⟨x, rfl, hx⟩
        have hx0 : Classical.choose hex = x := (lift_inj (Classical.choose_spec hex).1).symm
        rw [show F (lift x) = lift (bij ⟨Classical.choose hex, (Classical.choose_spec hex).2⟩) from
          dif_pos hex]
        have hpair : (⟨Classical.choose hex, (Classical.choose_spec hex).2⟩ : {x // P x}) = ⟨x, hx⟩ :=
          Subtype.ext hx0
        rw [hpair, hbx]

/-- **`VSet.lift` preserves Grothendieck universes**: if `U` is a Grothendieck
universe in `VSet.{u}`, then `lift U` is a Grothendieck universe in `VSet.{u + 1}`. -/
theorem isTGUniverse_lift {U : VSet.{u}} (hU : IsTGUniverse Mem U) :
    IsTGUniverse Mem.{u + 1} (lift U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Clause 1: transitivity
    intro y z hy hz
    obtain ⟨y₀, rfl, hy₀⟩ := mem_lift_exists hy
    obtain ⟨z₀, rfl, hz₀⟩ := mem_lift_exists hz
    exact mem_lift_iff.mpr (hU.1 y₀ z₀ hy₀ hz₀)
  · -- Clause 2: subsets of members are members
    intro y z hy hsub
    obtain ⟨y₀, rfl, hy₀⟩ := mem_lift_exists hy
    have hz : z = lift (sep y₀ fun w₀ => Mem (lift w₀) z) := by
      refine ext fun w => ?_
      constructor
      · intro hw
        obtain ⟨w₀, rfl, hwy₀⟩ := mem_lift_exists (hsub w hw)
        exact mem_lift_iff.mpr (mem_sep.mpr ⟨hwy₀, hw⟩)
      · intro hw
        obtain ⟨w₀, rfl, hsep⟩ := mem_lift_exists hw
        exact (mem_sep.mp hsep).2
    rw [hz, mem_lift_iff]
    exact hU.2.1 y₀ _ hy₀ fun w₀ hw₀ => (mem_sep.mp hw₀).1
  · -- Clause 3: power sets stay inside
    intro y hy
    obtain ⟨y₀, rfl, hy₀⟩ := mem_lift_exists hy
    obtain ⟨p₀, hp₀, hpow⟩ := hU.2.2.1 y₀ hy₀
    refine ⟨lift p₀, mem_lift_iff.mpr hp₀, fun z hsub => ?_⟩
    have hz : z = lift (sep y₀ fun w₀ => Mem (lift w₀) z) := by
      refine ext fun w => ?_
      constructor
      · intro hw
        obtain ⟨w₀, rfl, hwy₀⟩ := mem_lift_exists (hsub w hw)
        exact mem_lift_iff.mpr (mem_sep.mpr ⟨hwy₀, hw⟩)
      · intro hw
        obtain ⟨w₀, rfl, hsep⟩ := mem_lift_exists hw
        exact (mem_sep.mp hsep).2
    rw [hz, mem_lift_iff]
    exact hpow _ fun w₀ hw₀ => (mem_sep.mp hw₀).1
  · -- Clause 4: Tarski inaccessibility
    intro y hsub
    let y₀ : VSet.{u} := sep U fun w₀ => Mem (lift w₀) y
    have hy : y = lift y₀ := by
      refine ext fun w => ?_
      constructor
      · intro hw
        obtain ⟨w₀, rfl, hwU⟩ := mem_lift_exists (hsub w hw)
        exact mem_lift_iff.mpr (mem_sep.mpr ⟨hwU, hw⟩)
      · intro hw
        obtain ⟨w₀, rfl, hsep⟩ := mem_lift_exists hw
        exact (mem_sep.mp hsep).2
    rcases hU.2.2.2 y₀ (fun w₀ hw₀ => (mem_sep.mp hw₀).1) with ⟨f₀, hf_into, hf_inj, hf_surj⟩ | hmem
    · left
      classical
      let F : VSet.{u + 1} → VSet.{u + 1} := fun z =>
        if h : ∃ z₀ : VSet.{u}, z = lift z₀ then lift (f₀ (Classical.choose h)) else z
      have hFlift : ∀ z₀ : VSet.{u}, F (lift z₀) = lift (f₀ z₀) := by
        intro z₀
        have hex : ∃ x : VSet.{u}, lift z₀ = lift x := ⟨z₀, rfl⟩
        have hx : Classical.choose hex = z₀ := (lift_inj (Classical.choose_spec hex)).symm
        change (if h : ∃ x : VSet.{u}, lift z₀ = lift x then lift (f₀ (Classical.choose h)) else lift z₀) =
          lift (f₀ z₀)
        rw [dif_pos hex, hx]
      refine ⟨F, ?_, ?_, ?_⟩
      · intro z hz
        rw [hy] at hz
        obtain ⟨z₀, rfl, hz₀⟩ := mem_lift_exists hz
        rw [hFlift, mem_lift_iff]
        exact hf_into z₀ hz₀
      · intro z z' hz hz' hF
        rw [hy] at hz hz'
        obtain ⟨z₀, rfl, hz₀⟩ := mem_lift_exists hz
        obtain ⟨z₀', rfl, hz₀'⟩ := mem_lift_exists hz'
        rw [hFlift, hFlift] at hF
        rw [hf_inj z₀ z₀' hz₀ hz₀' (lift_inj hF)]
      · intro w hw
        obtain ⟨w₀, rfl, hw₀⟩ := mem_lift_exists hw
        obtain ⟨z₀, hz₀, hfz⟩ := hf_surj w₀ hw₀
        refine ⟨lift z₀, hy ▸ mem_lift_iff.mpr hz₀, ?_⟩
        rw [hFlift, hfz]
    · right
      rw [hy, mem_lift_iff]
      exact hmem

/-! ## Finite-chain `SetTheory` interface and unconditional Lean instances -/

/-- **ZF⁻ plus a finite chain of `n` Grothendieck universes**: the exact
`n`-universe truncation of `Ix.Kernel.SetTheory V`.  Every `SetTheory V`
provides `FiniteSetTheory n V` for all `n`, and for every concrete `n`,
`FiniteSetTheory n VSet.{u + n}` is unconditionally inhabited inside Lean's
universe hierarchy using only `[propext, Classical.choice, Quot.sound]`. -/
structure FiniteSetTheory (n : Nat) (V : Type u) where
  Mem : V → V → Prop
  ext : ∀ {x y : V}, (∀ z, Mem z x ↔ Mem z y) → x = y
  upair : V → V → V
  mem_upair : ∀ {z a b : V}, Mem z (upair a b) ↔ z = a ∨ z = b
  sUnion : V → V
  mem_sUnion : ∀ {z x : V}, Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y
  power : V → V
  mem_power : ∀ {z x : V}, Mem z (power x) ↔ ∀ w, Mem w z → Mem w x
  regularity : ∀ x : V, (∃ y, Mem y x) → ∃ y, Mem y x ∧ ¬ ∃ z, Mem z y ∧ Mem z x
  image : (V → V) → V → V
  mem_image : ∀ {f : V → V} {a z : V}, Mem z (image f a) ↔ ∃ w, Mem w a ∧ z = f w
  univChain : Fin n → V
  univChain_mem : ∀ (i : Nat) (h : i + 1 < n),
    Mem (univChain ⟨i, Nat.lt_of_succ_lt h⟩) (univChain ⟨i + 1, h⟩)
  univChain_tg : ∀ i : Fin n, IsTGUniverse Mem (univChain i)

/-- Every full `Ix.Kernel.SetTheory V` restricts to `FiniteSetTheory n V` for every `n`. -/
def FiniteSetTheory.ofSetTheory {V : Type u} [S : SetTheory V] (n : Nat) :
    FiniteSetTheory n V where
  Mem := S.Mem
  ext := S.ext
  upair := S.upair
  mem_upair := S.mem_upair
  sUnion := S.sUnion
  mem_sUnion := S.mem_sUnion
  power := S.power
  mem_power := S.mem_power
  regularity := S.regularity
  image := S.image
  mem_image := S.mem_image
  univChain i := S.univChain i.val
  univChain_mem i _ := S.univChain_mem i
  univChain_tg i := S.univChain_tg i.val

/-- Assemble a `FiniteSetTheory n VSet.{u}` from any `n`-chain of Grothendieck universes
in `VSet.{u}`. -/
noncomputable def finiteSetTheoryOfChain {n : Nat}
    (U : Fin n → VSet.{u})
    (hmem : ∀ (i : Nat) (h : i + 1 < n), Mem (U ⟨i, Nat.lt_of_succ_lt h⟩) (U ⟨i + 1, h⟩))
    (htg : ∀ i : Fin n, IsTGUniverse Mem (U i)) :
    FiniteSetTheory n VSet.{u} where
  Mem := Mem
  ext := ext
  upair := upair
  mem_upair := mem_upair
  sUnion := sUnion
  mem_sUnion := mem_sUnion
  power := power
  mem_power := mem_power
  regularity := regularity
  image := image
  mem_image := mem_image
  univChain := U
  univChain_mem := hmem
  univChain_tg := htg

/-- **The inductive universe-lifting step**: lift an `n`-chain of Grothendieck
universes in `VSet.{u}` to an `(n + 1)`-chain in `VSet.{u + 1}` by lifting every
previous universe via `VSet.lift` and appending `VSet.univSet.{u}` on top. -/
noncomputable def liftChain {n : Nat}
    (U : Fin n → VSet.{u})
    (hmem : ∀ (i : Nat) (h : i + 1 < n), Mem (U ⟨i, Nat.lt_of_succ_lt h⟩) (U ⟨i + 1, h⟩))
    (htg : ∀ i : Fin n, IsTGUniverse Mem (U i)) :
    { U' : Fin (n + 1) → VSet.{u + 1} //
      (∀ (i : Nat) (h : i + 1 < n + 1), Mem (U' ⟨i, Nat.lt_of_succ_lt h⟩) (U' ⟨i + 1, h⟩)) ∧
      (∀ i : Fin (n + 1), IsTGUniverse Mem (U' i)) } :=
  ⟨fun i => if hi : i.val < n then lift (U ⟨i.val, hi⟩) else univSet.{u},
   ⟨fun i hi => by
      have hi1 : i < n := Nat.lt_of_succ_lt_succ hi
      by_cases hsucc : i + 1 < n
      · simp only [hi1, hsucc, ↓reduceDIte]
        exact mem_lift_iff.mpr (hmem i hsucc)
      · simp only [hi1, hsucc, ↓reduceDIte]
        exact mem_univSet.mpr ⟨U ⟨i, hi1⟩, rfl⟩,
    fun i => by
      by_cases hi : i.val < n
      · simp only [hi, ↓reduceDIte]
        exact isTGUniverse_lift (htg ⟨i.val, hi⟩)
      · simp only [hi, ↓reduceDIte]
        exact isTGUniverse_univSet⟩⟩

/-- Lift a `FiniteSetTheory n VSet.{u}` built on `VSet.Mem` to `FiniteSetTheory (n + 1) VSet.{u + 1}`. -/
noncomputable def finiteSetTheoryStep {n : Nat}
    (U : Fin n → VSet.{u})
    (hmem : ∀ (i : Nat) (h : i + 1 < n), Mem (U ⟨i, Nat.lt_of_succ_lt h⟩) (U ⟨i + 1, h⟩))
    (htg : ∀ i : Fin n, IsTGUniverse Mem (U i)) :
    FiniteSetTheory (n + 1) VSet.{u + 1} :=
  let next := liftChain U hmem htg
  finiteSetTheoryOfChain next.1 next.2.1 next.2.2

/-- Unconditional 0-universe model of ZF⁻ in `VSet.{u}`. -/
noncomputable def finiteSetTheory0 : FiniteSetTheory 0 VSet.{u} :=
  finiteSetTheoryOfChain Fin.elim0 (fun _ h => absurd h (Nat.not_lt_zero _)) (fun i => Fin.elim0 i)

/-- Unconditional 1-universe Grothendieck model in `VSet.{u + 1}`. -/
noncomputable def finiteSetTheory1 : FiniteSetTheory 1 VSet.{u + 1} :=
  finiteSetTheoryStep Fin.elim0 (fun _ h => absurd h (Nat.not_lt_zero _)) (fun i => Fin.elim0 i)

/-- Unconditional 2-universe Grothendieck chain (`U₀ ∈ U₁`) in `VSet.{u + 2}`. -/
noncomputable def finiteSetTheory2 : FiniteSetTheory 2 VSet.{u + 2} :=
  let c1 := liftChain.{u} Fin.elim0 (fun _ h => absurd h (Nat.not_lt_zero _)) (fun i => Fin.elim0 i)
  finiteSetTheoryStep c1.1 c1.2.1 c1.2.2

/-- Unconditional 3-universe Grothendieck chain (`U₀ ∈ U₁ ∈ U₂`) in `VSet.{u + 3}`. -/
noncomputable def finiteSetTheory3 : FiniteSetTheory 3 VSet.{u + 3} :=
  let c1 := liftChain.{u} Fin.elim0 (fun _ h => absurd h (Nat.not_lt_zero _)) (fun i => Fin.elim0 i)
  let c2 := liftChain c1.1 c1.2.1 c1.2.2
  finiteSetTheoryStep c2.1 c2.2.1 c2.2.2

/-- Unconditional 4-universe Grothendieck chain (`U₀ ∈ U₁ ∈ U₂ ∈ U₃`) in `VSet.{u + 4}`. -/
noncomputable def finiteSetTheory4 : FiniteSetTheory 4 VSet.{u + 4} :=
  let c1 := liftChain.{u} Fin.elim0 (fun _ h => absurd h (Nat.not_lt_zero _)) (fun i => Fin.elim0 i)
  let c2 := liftChain c1.1 c1.2.1 c1.2.2
  let c3 := liftChain c2.1 c2.2.1 c2.2.2
  finiteSetTheoryStep c3.1 c3.2.1 c3.2.2

/-! ## Conditional ω-chain `Ix.Kernel.SetTheory` instance on `VSet` -/

/-- **Existence of a strictly increasing ω-chain of Grothendieck universes in `VSet.{u}`**:
the exact set-theoretic hypothesis equivalent to Carneiro's `OmegaInaccessibles`
(cf. `Models/SetTheory/IxSetTheoryModel/Carneiro.lean`), stated directly over
pure-Lean `VSet.{u}` without Mathlib. -/
def OmegaUniverses : Prop :=
  ∃ U : Nat → VSet.{u},
    (∀ n : Nat, Mem (U n) (U (n + 1))) ∧ (∀ n : Nat, IsTGUniverse Mem (U n))

set_option warn.classDefReducibility false in
/-- Assemble a full `Ix.Kernel.SetTheory VSet.{u}` instance from any explicit ω-chain
of Grothendieck universes in `VSet.{u}`. -/
noncomputable def setTheoryOfChain (U : Nat → VSet.{u})
    (hmem : ∀ n : Nat, Mem (U n) (U (n + 1)))
    (htg : ∀ n : Nat, IsTGUniverse Mem (U n)) :
    SetTheory VSet.{u} where
  Mem := Mem
  ext := ext
  upair := upair
  mem_upair := mem_upair
  sUnion := sUnion
  mem_sUnion := mem_sUnion
  power := power
  mem_power := mem_power
  regularity := regularity
  image := image
  mem_image := mem_image
  univChain := U
  univChain_mem := hmem
  univChain_tg := htg

set_option warn.classDefReducibility false in
/-- Concrete `Ix.Kernel.SetTheory VSet.{u}` instance under `VSet.OmegaUniverses.{u}`. -/
noncomputable def setTheoryOfOmegaUniverses (h : OmegaUniverses.{u}) :
    SetTheory VSet.{u} :=
  setTheoryOfChain (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

/-- `VSet.OmegaUniverses.{u}` inhabits `Ix.Kernel.SetTheory` on `VSet.{u}`. -/
theorem omegaUniverses_implies_setTheory :
    OmegaUniverses.{u} → Nonempty (Σ V : Type (u + 1), SetTheory V) :=
  fun h => ⟨⟨VSet.{u}, setTheoryOfOmegaUniverses h⟩⟩

end VSet

end Ix.Kernel
