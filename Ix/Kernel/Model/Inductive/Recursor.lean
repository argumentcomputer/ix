/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Inductive/Recursor.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Inductive.Container

/-!
Recursion over indexed carriers. Large elimination requires recoverable
constructor data: automatic in positive sorts, and derived from singleton
shape fibres at Prop. Accessibility is proved by the carrier's induction
principle. No well-founded recursion or computation law is assumed.
-/

namespace Ix.Kernel.Model.IndexedContainer

open SetTheory

universe u
variable {V : Type u} [SetTheory V]

abbrev Element (D : IndexedContainer V) (w : Nat) :=
  { ix : V × V // ix.1 ∈ˢ D.indices ∧ ix.2 ∈ˢ app (D.carrier w) ix.1 }

/-- At Prop every constructor value is the proof point. Large elimination
therefore needs at most one shape at each index. The source producer checks
this criterion; positive carriers need no singleton restriction. -/
def LargeElim (D : IndexedContainer V) (w : Nat) : Prop :=
  w = 0 → ∀ i, i ∈ˢ D.indices → ∀ a b,
    a ∈ˢ D.shapes i → b ∈ˢ D.shapes i → a = b

theorem largeElim_of_pos (D : IndexedContainer V) {w : Nat} (hw : w ≠ 0) :
    D.LargeElim w := fun h => False.elim (hw h)

theorem node_inj {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) {i a b g h : V}
    (hi : i ∈ˢ D.indices) (ha : a ∈ˢ D.shapes i) (hb : b ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)))
    (hh : h ∈ˢ piSet (D.positions b) (fun p => app (D.carrier w) (D.target b p)))
    (he : node w a g = node w b h) : a = b ∧ g = h := by
  by_cases hw : w = 0
  · subst w
    have hab := hlarge rfl i hi a b ha hb
    subst b
    refine ⟨rfl, eq_of_mem_piSet_app_eq hg hh ?_⟩
    intro p hp
    have hP : app (D.carrier 0) (D.target a p) ∈ˢ (univZero : V) := by
      simpa only [univ_zero] using D.carrier_fibre_mem 0 (hD.target_mem i a p hi ha hp)
    exact (eq_pt_of_mem_univZero hP (app_mem_of_mem_piSet (a := p) hg hp)).trans
      (eq_pt_of_mem_univZero hP (app_mem_of_mem_piSet (a := p) hh hp)).symm
  · apply kpair_inj
    simpa only [node, if_neg hw, spair] using he

def Child (D : IndexedContainer V) (w : Nat) (child parent : D.Element w) : Prop :=
  ∃ a, a ∈ˢ D.shapes parent.val.1 ∧ ∃ g,
    g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)) ∧
    parent.val.2 = node w a g ∧ ∃ p, p ∈ˢ D.positions a ∧
      child.val = (D.target a p, app g p)

theorem child_wellFounded {D : IndexedContainer V} {w : Nat}
    (hD : D.WF w) (hlarge : D.LargeElim w) : WellFounded (D.Child w) := by
  constructor
  rintro ⟨⟨i, x⟩, hi, hx⟩
  apply D.induction hD (fun i x => ∀ h : i ∈ˢ D.indices ∧ x ∈ˢ app (D.carrier w) i,
    Acc (D.Child w) ⟨(i, x), h⟩) ?_ i hi x hx ⟨hi, hx⟩
  intro i hi a ha g hg ih h
  constructor
  intro y hy
  obtain ⟨b, hb, g', hg', he, p, hp, hyp⟩ := hy
  obtain ⟨rfl, rfl⟩ := node_inj hD hlarge hi ha hb hg hg' he
  have hy' : y = ⟨(D.target a p, app g p),
      hD.target_mem i a p hi ha hp, app_mem_of_mem_piSet hg hp⟩ := Subtype.ext hyp
  rw [hy']
  exact ih p hp ⟨hD.target_mem i a p hi ha hp, app_mem_of_mem_piSet hg hp⟩

structure NodeView (D : IndexedContainer V) (w : Nat) (z : D.Element w) where
  shape : V
  branches : V
  shape_mem : shape ∈ˢ D.shapes z.val.1
  branches_mem : branches ∈ˢ piSet (D.positions shape)
    (fun p => app (D.carrier w) (D.target shape p))
  equation : z.val.2 = node w shape branches

noncomputable def view {D : IndexedContainer V} {w : Nat}
    (hD : D.WF w) (z : D.Element w) : D.NodeView w z :=
  let ex := mem_fibre.mp ((carrier_eq hD z.property.1) ▸ z.property.2)
  let a := Classical.choose ex
  let ha := Classical.choose_spec ex
  let g := Classical.choose ha.2
  let hg := Classical.choose_spec ha.2
  ⟨a, g, ha.1, hg.1, hg.2⟩

noncomputable def child {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {i a g : V} (hi : i ∈ˢ D.indices) (ha : a ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)))
    (p : V) (hp : p ∈ˢ D.positions a) : D.Element w :=
  ⟨(D.target a p, app g p), hD.target_mem i a p hi ha hp, app_mem_of_mem_piSet hg hp⟩

theorem child_rel {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {z : D.Element w} (v : D.NodeView w z) {p : V} (hp : p ∈ˢ D.positions v.shape) :
    D.Child w (child hD z.property.1 v.shape_mem v.branches_mem p hp) z :=
  ⟨v.shape, v.shape_mem, v.branches, v.branches_mem, v.equation, p, hp, rfl⟩

noncomputable def childResults {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {i a g : V} (hi : i ∈ˢ D.indices) (ha : a ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)))
    (r : D.Element w → V) : V :=
  open Classical in
  graph (fun p => if hp : p ∈ˢ D.positions a then r (child hD hi ha hg p hp) else empty)
    (D.positions a)

theorem app_childResults {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {i a g : V} (hi : i ∈ˢ D.indices) (ha : a ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)))
    (r : D.Element w → V) {p : V} (hp : p ∈ˢ D.positions a) :
    app (childResults hD hi ha hg r) p = r (child hD hi ha hg p hp) := by
  simp only [childResults, app_graph hp, dif_pos hp]

noncomputable def foldStep {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (algebra : V → V → V → V → V) (z : D.Element w)
    (r : ∀ y, D.Child w y z → V) : V :=
  open Classical in
  let v := view hD z
  algebra z.val.1 v.shape v.branches
    (graph (fun p => if hp : p ∈ˢ D.positions v.shape then
      r (child hD z.property.1 v.shape_mem v.branches_mem p hp) (child_rel hD v hp)
      else empty) (D.positions v.shape))

noncomputable def fold {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) (algebra : V → V → V → V → V) : D.Element w → V :=
  (child_wellFounded hD hlarge).fix (foldStep hD algebra)

theorem fold_eq_view {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) (algebra : V → V → V → V → V) (z : D.Element w) :
    fold hD hlarge algebra z =
      algebra z.val.1 (view hD z).shape (view hD z).branches
        (childResults hD z.property.1 (view hD z).shape_mem (view hD z).branches_mem
          (fold hD hlarge algebra)) := by
  rw [fold, WellFounded.fix_eq]
  rfl

theorem fold_node {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) (algebra : V → V → V → V → V)
    {i a g : V} (hi : i ∈ˢ D.indices) (ha : a ∈ˢ D.shapes i)
    (hg : g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p))) :
    fold hD hlarge algebra ⟨(i, node w a g), hi, node_mem_carrier hD hi ha hg⟩ =
      algebra i a g (childResults hD hi ha hg (fold hD hlarge algebra)) := by
  let z : D.Element w := ⟨(i, node w a g), hi, node_mem_carrier hD hi ha hg⟩
  have inj := node_inj hD hlarge hi ha (view hD z).shape_mem hg
    (view hD z).branches_mem (view hD z).equation
  change fold hD hlarge algebra z = _
  rw [fold_eq_view]
  simp only [← inj.1, ← inj.2]
  rfl

def AlgebraTyping (D : IndexedContainer V) (w : Nat)
    (M : V → V → V) (algebra : V → V → V → V → V) : Prop :=
  ∀ i, i ∈ˢ D.indices → ∀ a, a ∈ˢ D.shapes i → ∀ g,
    g ∈ˢ piSet (D.positions a) (fun p => app (D.carrier w) (D.target a p)) →
    ∀ ih, ih ∈ˢ piSet (D.positions a) (fun p => M (D.target a p) (app g p)) →
      algebra i a g ih ∈ˢ M i (node w a g)

theorem fold_mem {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) {M : V → V → V} {algebra : V → V → V → V → V}
    (ha : D.AlgebraTyping w M algebra) (z : D.Element w) :
    fold hD hlarge algebra z ∈ˢ M z.val.1 z.val.2 := by
  induction z using (child_wellFounded hD hlarge).induction with
  | h z ih =>
    rw [fold_eq_view]
    let v := view hD z
    have hresults : childResults hD z.property.1 v.shape_mem v.branches_mem
        (fold hD hlarge algebra) ∈ˢ
        piSet (D.positions v.shape) (fun p => M (D.target v.shape p) (app v.branches p)) := by
      apply graph_mem_piSet
      intro p hp
      simpa only [dif_pos hp, child] using
        ih (child hD z.property.1 v.shape_mem v.branches_mem p hp) (child_rel hD v hp)
    have hstep := ha z.val.1 z.property.1 v.shape v.shape_mem v.branches v.branches_mem
      _ hresults
    exact (congrArg (fun x => _ ∈ˢ M z.val.1 x) v.equation).mpr hstep

/-- Total form used inside function graphs. Only typed domain elements reach
the recursive branch; the value outside that domain is irrelevant. -/
noncomputable def foldAt {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) (algebra : V → V → V → V → V) (i x : V) : V :=
  open Classical in
  if h : i ∈ˢ D.indices ∧ x ∈ˢ app (D.carrier w) i then
    fold hD hlarge algebra ⟨(i, x), h⟩ else empty

theorem foldAt_eq {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) (algebra : V → V → V → V → V) {i x : V}
    (hi : i ∈ˢ D.indices) (hx : x ∈ˢ app (D.carrier w) i) :
    foldAt hD hlarge algebra i x = fold hD hlarge algebra ⟨(i, x), hi, hx⟩ := by
  simp only [foldAt, dif_pos (And.intro hi hx)]

theorem foldAt_mem {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    (hlarge : D.LargeElim w) {M : V → V → V} {algebra : V → V → V → V → V}
    (ha : D.AlgebraTyping w M algebra) {i x : V}
    (hi : i ∈ˢ D.indices) (hx : x ∈ˢ app (D.carrier w) i) :
    foldAt hD hlarge algebra i x ∈ˢ M i x := by
  rw [foldAt_eq hD hlarge algebra hi hx]
  exact fold_mem hD hlarge ha _

/-- Small elimination does not need constructor injectivity. A Prop-valued
motive follows directly by structural induction, even for many constructors. -/
theorem small_elim {D : IndexedContainer V} {w : Nat} (hD : D.WF w)
    {M : V → V → V} {algebra : V → V → V → V → V}
    (hM : ∀ i, i ∈ˢ D.indices → ∀ x, x ∈ˢ app (D.carrier w) i → M i x ∈ˢ (univZero : V))
    (ha : D.AlgebraTyping w M algebra) :
    ∀ i, i ∈ˢ D.indices → ∀ x, x ∈ˢ app (D.carrier w) i → (pt : V) ∈ˢ M i x := by
  apply D.induction hD (fun i x => (pt : V) ∈ˢ M i x)
  intro i hi a ha' g hg ih
  have hstep := ha i hi a ha' g hg (graph (fun _ => (pt : V)) (D.positions a))
    (graph_mem_piSet ih)
  have he := eq_pt_of_mem_univZero (hM i hi _ (node_mem_carrier hD hi ha' hg)) hstep
  rwa [he] at hstep

end Ix.Kernel.Model.IndexedContainer
