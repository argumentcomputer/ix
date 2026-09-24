/-
Ported from con-leche (86cd20a65660d757cedc81561a44579099b565d0).
Source attribution and original path: Models/SetTheory/NOTICE.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
Changes: namespaces and imports adapted to Ix; documentation updated.
-/

import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Cardinal
import Ix.Kernel.Model.SetTheory.Core

/-!
# A concrete model of Ix's set-theory interface

A strictly increasing countable sequence of inaccessible cardinals gives
`Ix.Kernel.Model.SetTheory ZFSet.{u}`, with `univChain n := V_ (κ n).ord`.
Mathlib supplies the set operations, including images of arbitrary Lean
functions via `Classical.allZFSetDefinable`. The proof below establishes
Tarski's universe clauses for each inaccessible stage of the von Neumann
hierarchy and assembles the instance.

This separate package is the only part of the construction that imports
Mathlib. `Audit.lean` checks the model-existence theorem's full dependency
graph against Lean's `propext`, `Classical.choice`, and `Quot.sound` axioms.
The inaccessible-cardinal assumption remains a theorem hypothesis.
-/

universe u

open Cardinal Order ZFSet

namespace IxSetTheoryModel

/-- A strictly increasing countable sequence of strongly inaccessible
cardinals. This remains an explicit hypothesis; this package does not assert
the existence of inaccessible cardinals. -/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/-! ### `V_ κ` is a Grothendieck universe in Tarski's form, for `κ` inaccessible -/

variable {κ : Cardinal.{u}}

/-- A subset of `V_ κ.ord` of cardinality `< κ` has rank `< κ.ord`:
regularity of `κ` bounds the least strict upper bound of `< κ` many
ordinals below `κ.ord`. -/
theorem rank_lt_ord_of_card_lt (hκ : κ.IsRegular) {y : ZFSet.{u}}
    (hy : y ⊆ V_ κ.ord) (hc : y.card < κ) : y.rank < κ.ord := by
  let e : y ≃ Shrink.{u} y := equivShrink _
  let f : Shrink.{u} y → Ordinal.{u} := fun z => rank (e.symm z).1
  have hlt : ⨆ z, f z + 1 < κ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hκ.cof_ord]) fun z =>
      mem_vonNeumann.mp (hy (e.symm z).2)
  refine lt_of_le_of_lt ?_ hlt
  rw [rank_le_iff]
  intro z hz
  have := Ordinal.lt_iSup_add_one f (e ⟨z, hz⟩)
  simpa [f, e] using this

/-- Below an inaccessible, the beth function stays below it. -/
theorem preBeth_lt_of_lt_ord (hκ : κ.IsInaccessible) :
    ∀ {a : Ordinal.{u}}, a < κ.ord → preBeth a < κ := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => intro _; rw [preBeth_zero]; exact hκ.pos
  | add_one a ih =>
    intro h
    rw [preBeth_add_one]
    exact hκ.isStrongLimit.isStrongPrelimit (ih ((lt_add_one a).trans h))
  | limit a ha ih =>
    intro h
    rw [preBeth_limit ha.isSuccPrelimit]
    refine Cardinal.lift_iSup_lt_of_lt_cof_ord ?_ fun b => ih b b.2 (b.2.trans h)
    rw [hκ.isRegular.lift.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt]
    exact lt_ord.mp h

/-- `|V_ κ| = κ` for `κ` inaccessible. -/
theorem card_vonNeumann_ord (hκ : κ.IsInaccessible) : card (V_ κ.ord) = κ := by
  rw [card_vonNeumann]
  refine le_antisymm ?_ (le_preBeth_ord κ)
  rw [preBeth_limit (isSuccLimit_ord hκ.aleph0_lt.le).isSuccPrelimit]
  exact ciSup_le' fun b => (preBeth_lt_of_lt_ord hκ b.2).le

/-- A subset of `V_ κ` that is not a member has the cardinality of
`V_ κ`. -/
theorem card_eq_of_not_rank_lt (hκ : κ.IsInaccessible) {y : ZFSet.{u}}
    (hy : y ⊆ V_ κ.ord) (hr : ¬ y.rank < κ.ord) : card y = card (V_ κ.ord) := by
  refine le_antisymm (card_mono hy) ?_
  rw [card_vonNeumann_ord hκ]
  exact not_lt.mp fun h => hr (rank_lt_ord_of_card_lt hκ.isRegular hy h)

/-- Equal cardinality gives Ix's meta-level equinumerosity: a global
function `ZFSet → ZFSet` that restricts to a bijection. -/
theorem equinumerous_of_card_eq {y s : ZFSet.{u}} (h : card y = card s) :
    Ix.Kernel.Model.Equinumerous (· ∈ ·) y s := by
  obtain ⟨e'⟩ := Cardinal.eq.mp h
  let e : y ≃ s := (equivShrink _).trans (e'.trans (equivShrink _).symm)
  classical
  refine ⟨fun z => if hz : z ∈ y then (e ⟨z, hz⟩).1 else z, ?_, ?_, ?_⟩
  · intro z hz
    simp only [hz, ↓reduceDIte]
    exact (e ⟨z, hz⟩).2
  · intro z z' hz hz' hzz'
    simp only [hz, hz', ↓reduceDIte] at hzz'
    have := e.injective (Subtype.ext hzz')
    exact congrArg Subtype.val this
  · intro w hw
    refine ⟨(e.symm ⟨w, hw⟩).1, (e.symm ⟨w, hw⟩).2, ?_⟩
    simp only [(e.symm ⟨w, hw⟩).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]

/-- **`V_ κ` is a Grothendieck universe in Tarski's form** (Ix's
`IsTGUniverse`) for every inaccessible `κ`. -/
theorem isTGUniverse_vonNeumann (hκ : κ.IsInaccessible) :
    Ix.Kernel.Model.IsTGUniverse (· ∈ ·) (V_ κ.ord) := by
  have hlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_lt.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- transitivity
    intro y z (hy : y ∈ V_ κ.ord) (hz : z ∈ y)
    exact isTransitive_vonNeumann _ y hy hz
  · -- subsets of members are members
    intro y z (hy : y ∈ V_ κ.ord) hzy
    exact mem_vonNeumann_of_subset (fun w hw => hzy w hw) hy
  · -- power sets stay inside
    intro y (hy : y ∈ V_ κ.ord)
    refine ⟨powerset y, ?_, fun z hz => mem_powerset.mpr fun w hw => hz w hw⟩
    show powerset y ∈ V_ κ.ord
    rw [mem_vonNeumann, rank_powerset]
    exact hlim.succ_lt (mem_vonNeumann.mp hy)
  · -- Tarski's clause: a subset is a member or equinumerous
    intro y hy
    have hy' : y ⊆ V_ κ.ord := fun w hw => hy w hw
    by_cases hr : y.rank < κ.ord
    · exact Or.inr (mem_vonNeumann.mpr hr)
    · exact Or.inl (equinumerous_of_card_eq (card_eq_of_not_rank_lt hκ hy' hr))

/-! ### The `Ix.Kernel.Model.SetTheory` instance on `ZFSet` -/

set_option warn.classDefReducibility false in
/-- Ix's set theory on Mathlib's `ZFSet.{u}`, from any strictly
increasing sequence of inaccessibles: the ZF⁻ fields are Mathlib's
(`ZFSet.ext`, pairs, `⋃₀`, `powerset`, `mem_wf`, `image` under
`Classical.allZFSetDefinable`), and `univChain n := V_ (κ n).ord`. -/
noncomputable def setTheoryOfChain (κ : ℕ → Cardinal.{u}) (hmono : StrictMono κ)
    (hinacc : ∀ n, (κ n).IsInaccessible) : Ix.Kernel.Model.SetTheory ZFSet.{u} where
  Mem := (· ∈ ·)
  ext h := ZFSet.ext h
  upair a b := {a, b}
  mem_upair := mem_pair
  sUnion := ZFSet.sUnion
  mem_sUnion := mem_sUnion
  power := powerset
  mem_power := mem_powerset
  regularity x h := by
    obtain ⟨y, hy, hmin⟩ := mem_wf.has_min {y | y ∈ x} h
    exact ⟨y, hy, fun ⟨z, hzy, hzx⟩ => hmin z hzx hzy⟩
  image f := @ZFSet.image f (Classical.allZFSetDefinable _)
  mem_image := by
    intro f a z
    rw [@mem_image f (Classical.allZFSetDefinable _)]
    exact exists_congr fun w => and_congr_right fun _ => eq_comm
  univChain n := V_ (κ n).ord
  univChain_mem n := vonNeumann_mem_of_lt (ord_lt_ord.mpr (hmono (Nat.lt_succ_self n)))
  univChain_tg n := isTGUniverse_vonNeumann (hinacc n)

set_option warn.classDefReducibility false in
/-- Ix's set theory on `ZFSet.{u}` under Carneiro's hypothesis. -/
noncomputable def setTheoryOfCarneiro (h : OmegaInaccessibles.{u}) : Ix.Kernel.Model.SetTheory ZFSet.{u} :=
  setTheoryOfChain (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

/-- **Carneiro's hypothesis implies Ix's.**  `ω` strongly inaccessible
cardinals give a model of
Ix's `SetTheory` interface — on Mathlib's `ZFSet.{u}`, with the
universe chain `V_ (κ n).ord`. -/
theorem carneiro_implies_ix :
    OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), Ix.Kernel.Model.SetTheory V) :=
  fun h => ⟨⟨ZFSet.{u}, setTheoryOfCarneiro h⟩⟩


end IxSetTheoryModel
