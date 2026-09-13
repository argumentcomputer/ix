/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.SetModel.Container

/-!
Indexed strictly positive carriers over the explicit set-theory interface.
This supplies a carrier and its induction principle from shape/position data;
the source validator must construct the bounds and target-index proofs.
No field postulates a fixed point, constructor law, or recursor law.
-/

namespace Ix.Theory.Model

open SetTheory

universe u

structure IndexedContainer (V : Type u) where
  indices : V
  shapes : V → V
  positions : V → V
  target : V → V → V

namespace IndexedContainer

variable {V : Type u} [SetTheory V]

structure WF (D : IndexedContainer V) (w : Nat) : Prop where
  shapes_mem : w ≠ 0 → ∀ i, i ∈ˢ D.indices → D.shapes i ∈ˢ (univ w : V)
  positions_mem : w ≠ 0 → ∀ i a, i ∈ˢ D.indices → a ∈ˢ D.shapes i →
    D.positions a ∈ˢ (univ w : V)
  target_mem : ∀ i a p, i ∈ˢ D.indices → a ∈ˢ D.shapes i → p ∈ˢ D.positions a →
    D.target a p ∈ˢ D.indices

noncomputable def node (w : Nat) (a g : V) : V :=
  if w = 0 then pt else spair a g

noncomputable def fibre (D : IndexedContainer V) (w : Nat) (X i : V) : V :=
  sigmaSet w (D.shapes i) fun a => piSet (D.positions a) fun p => app X (D.target a p)

noncomputable def step (D : IndexedContainer V) (w : Nat) : V :=
  graph (fun X => graph (D.fibre w X) D.indices) (famSpace w D.indices)

noncomputable def carrier (D : IndexedContainer V) (w : Nat) : V :=
  lfpFamSet w D.indices (D.step w)

theorem node_mem_fibre {D : IndexedContainer V} {w : Nat} {X i a g : V}
    (ha : a ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app X (D.target a p))) :
    node w a g ∈ˢ D.fibre w X i := by
  by_cases hw : w = 0
  · subst w
    exact pt_mem_sigma ha hg
  · simpa only [node, if_neg hw, fibre] using spair_mem hw ha hg

theorem mem_fibre {D : IndexedContainer V} {w : Nat} {X i x : V} :
    x ∈ˢ D.fibre w X i ↔ ∃ a, a ∈ˢ D.shapes i ∧
      ∃ g, g ∈ˢ piSet (D.positions a) (fun p => app X (D.target a p)) ∧ x = node w a g := by
  constructor
  · intro hx
    obtain ⟨a, g, ha, hg, hz, hp⟩ := mem_sigma_elim hx
    refine ⟨a, ha, g, hg, ?_⟩
    by_cases hw : w = 0
    · simpa only [node, if_pos hw] using hz hw
    · simpa only [node, if_neg hw] using hp hw
  · rintro ⟨a, ha, g, hg, rfl⟩
    exact node_mem_fibre ha hg

theorem app_step {D : IndexedContainer V} {w : Nat} {X : V}
    (hX : X ∈ˢ famSpace w D.indices) :
    app (D.step w) X = graph (D.fibre w X) D.indices := app_graph hX

theorem app_app_step {D : IndexedContainer V} {w : Nat} {X i : V}
    (hX : X ∈ˢ famSpace w D.indices) (hi : i ∈ˢ D.indices) :
    app (app (D.step w) X) i = D.fibre w X i := by
  rw [app_step hX, app_graph hi]

theorem piSet_mono {A : V} {B C : V → V} (h : ∀ a, a ∈ˢ A → B a ⊆ˢ C a) :
    piSet A B ⊆ˢ piSet A C := by
  intro g hg
  obtain ⟨hsub, htotal⟩ := mem_piSet.mp hg
  refine mem_piSet.mpr ⟨?_, htotal⟩
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigmaPairs.mp (hsub q hq)
  exact mem_sigmaPairs.mpr ⟨a, ha, b, h a ha b hb, rfl⟩

theorem step_maps {D : IndexedContainer V} {w : Nat} (hD : D.WF w) :
    MapsFam w D.indices (D.step w) := by
  intro X hX
  rw [app_step hX]
  refine graph_mem_famSpace fun i hi => ?_
  by_cases hw : w = 0
  · subst w
    simpa only [fibre, sigmaSet_zero, univ_zero] using truthVal_mem_univZero
      (∃ a, a ∈ˢ D.shapes i ∧ ∃ g, g ∈ˢ piSet (D.positions a)
        (fun p => app X (D.target a p)))
  · rw [fibre, sigmaSet_pos hw]
    let hU := univ_isTGUniverse (V := V) hw
    refine hU.sigmaPairs_mem (hD.shapes_mem hw i hi) fun a ha => ?_
    exact hU.piSet_mem (hD.positions_mem hw i a hi ha) fun p hp =>
      famSpace_app hX (hD.target_mem i a p hi ha hp)

theorem step_mono {D : IndexedContainer V} {w : Nat} (hD : D.WF w) :
    MonoFam w D.indices (D.step w) := by
  intro X Y hX hY hXY i hi x hx
  rw [app_app_step hX hi] at hx
  rw [app_app_step hY hi]
  obtain ⟨a, ha, g, hg, rfl⟩ := mem_fibre.mp hx
  exact node_mem_fibre ha (piSet_mono
    (fun p hp => hXY _ (hD.target_mem i a p hi ha hp)) g hg)

/-- The closed member needed by the fixed-point theorem is constructed.
At Prop the top truth family suffices; positive sorts use accessible codes. -/
theorem closed_exists {D : IndexedContainer V} {w : Nat} (hD : D.WF w) :
    ∃ L, IsClosedFam w D.indices (D.step w) L := by
  by_cases hw : w = 0
  · subst w
    let L := graph (fun _ => (unitSet : V)) D.indices
    have hL : L ∈ˢ famSpace 0 D.indices :=
      graph_mem_famSpace fun _ _ => unitSet_mem_univ 0
    refine ⟨L, hL, ?_⟩
    intro i hi x hx
    rw [app_app_step hL hi] at hx
    obtain ⟨a, _, g, _, rfl⟩ := mem_fibre.mp hx
    simpa [L, app_graph hi, node] using (pt_mem_unitSet (V := V))
  · apply container_closed_exists hw (fun X => app (D.step w) X)
      D.shapes D.positions D.target spair
      (hD.shapes_mem hw) (hD.positions_mem hw) hD.target_mem
    · intro i a g hi ha hg
      let hU := univ_isTGUniverse (V := V) hw
      simpa only [spair] using hU.kpair_mem (empty_mem_univ w)
        (hU.transitive (hD.shapes_mem hw i hi) ha) hg
    · intro X hX i hi x hx
      rw [app_app_step hX hi] at hx
      obtain ⟨a, ha, g, hg, h⟩ := mem_fibre.mp hx
      exact ⟨a, ha, g, hg, by simpa only [node, if_neg hw] using h⟩

theorem carrier_mem (D : IndexedContainer V) (w : Nat) :
    D.carrier w ∈ˢ famSpace w D.indices := lfpFamSet_mem _ _ _

theorem carrier_fibre_mem (D : IndexedContainer V) (w : Nat) {i : V}
    (hi : i ∈ˢ D.indices) : app (D.carrier w) i ∈ˢ (univ w : V) :=
  famSpace_app (D.carrier_mem w) hi

theorem carrier_eq {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {i : V} (hi : i ∈ˢ D.indices) :
    app (D.carrier w) i = D.fibre w (D.carrier w) i := by
  rw [← app_app_step (D.carrier_mem w) hi]
  exact (app_lfpFamSet_eq (closed_exists hD) (step_mono hD) (step_maps hD) hi).symm

theorem node_mem_carrier {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {i a g : V} (hi : i ∈ˢ D.indices) (ha : a ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p))) :
    node w a g ∈ˢ app (D.carrier w) i := by
  rw [carrier_eq hD hi]
  exact node_mem_fibre ha hg

/-- Structural induction supplies hypotheses at every recursive position,
including all arguments of recursive function fields. -/
theorem induction {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (P : V → V → Prop)
    (hstep : ∀ i, i ∈ˢ D.indices → ∀ a, a ∈ˢ D.shapes i → ∀ g,
      g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)) →
      (∀ p, p ∈ˢ D.positions a → P (D.target a p) (app g p)) → P i (node w a g)) :
    ∀ i, i ∈ˢ D.indices → ∀ x, x ∈ˢ app (D.carrier w) i → P i x := by
  apply lfpFamSet_induction (closed_exists hD) (step_mono hD) P
  intro i hi x hx
  let X := graph (fun i => sep (app (D.carrier w) i) (P i)) D.indices
  have hX : X ∈ˢ famSpace w D.indices :=
    graph_mem_famSpace fun i hi => univ_sep_mem (D.carrier_fibre_mem w hi)
  change x ∈ˢ app (app (D.step w) X) i at hx
  rw [app_app_step hX hi] at hx
  obtain ⟨a, ha, g, hg, rfl⟩ := mem_fibre.mp hx
  have hchild (p : V) (hp : p ∈ˢ D.positions a) :
      app g p ∈ˢ app (D.carrier w) (D.target a p) ∧ P (D.target a p) (app g p) := by
    have h := app_mem_of_mem_piSet hg hp
    rw [show X = graph (fun i => sep (app (D.carrier w) i) (P i)) D.indices from rfl,
      app_graph (hD.target_mem i a p hi ha hp)] at h
    exact mem_sep.mp h
  apply hstep i hi a ha g
  · apply piSet_mono (B := fun p => app X (D.target a p)) _ g hg
    intro p hp y hy
    rw [show X = graph (fun i => sep (app (D.carrier w) i) (P i)) D.indices from rfl,
      app_graph (hD.target_mem i a p hi ha hp)] at hy
    exact (mem_sep.mp hy).1
  · exact fun p hp => (hchild p hp).2

end IndexedContainer
end Ix.Theory.Model
