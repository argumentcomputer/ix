module

public import ConLeche.SetTheory.Derive.Pt

@[expose] public section

/-!
# Function graphs, application, and the raw dependent-function set

* `graph F A = {⟨x, F x⟩ : x ∈ A}` — the set-theoretic function graph
  (replacement); never equal to `pt`, since `pt`'s element `ptTag` has
  an empty member and so is not a Kuratowski pair.
* `app f a = ⋃ {y : ⟨a, y⟩ ∈ f}` — untagged application on non-`pt`
  arguments; `app pt a = pt` is the tag that makes proofs degenerate
  (`app_pt` in the `SetTheory` interface).
* `sigmaPairs A B = {⟨x, y⟩ : x ∈ A, y ∈ B x}` — the raw dependent
  pair set (also the `w ≠ 0` sigma).
* `piSet A B ⊆ power (sigmaPairs A B)` — the total single-valued
  graphs: the `v ≠ 0` dependent product.

The level-`0` truncations (`lam 0 = pt`, `pi 0` a truth value) were
layered on top in `Derive/Pi.lean`, deleted at task #221: the model
reads the *annotation-driven* `piR`/`lamR` (`SetModel/Ops.lean`), which
dispatch on the annotation instead of collapsing.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The function graph `{⟨x, F x⟩ : x ∈ A}`. -/
noncomputable def graph (F : V → V) (A : V) : V :=
  image (fun x => kpair x (F x)) A

theorem mem_graph {F : V → V} {A p : V} :
    p ∈ˢ graph F A ↔ ∃ x, x ∈ˢ A ∧ p = kpair x (F x) := mem_image

theorem graph_ne_pt {F : V → V} {A : V} : graph F A ≠ (pt : V) := by
  intro h
  obtain ⟨x, -, hx⟩ :=
    mem_graph.mp (h ▸ ptTag_mem_pt : (ptTag : V) ∈ˢ graph F A)
  exact ptTag_ne_kpair x (F x) hx

theorem graph_congr {F F' : V → V} {A : V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    graph F A = graph F' A :=
  image_congr fun x hx => by rw [h x hx]

open Classical in
/-- Tagged set-theoretic application: the union of the values paired
with `a` in `f` — except at the proof point, which applies to `pt`
again. -/
noncomputable def app (f a : V) : V :=
  if f = pt then pt else sUnion (sep (sUnion (sUnion f)) (fun y => kpair a y ∈ˢ f))

theorem app_pt (a : V) : app (pt : V) a = pt := by
  unfold app; exact if_pos rfl

/-- Application computes on single-valued positions. -/
theorem app_eq_of_unique {f a b : V} (hf : f ≠ pt) (hab : kpair a b ∈ˢ f)
    (huniq : ∀ y, kpair a y ∈ˢ f → y = b) : app f a = b := by
  unfold app
  rw [if_neg hf]
  have : sep (sUnion (sUnion f)) (fun y => kpair a y ∈ˢ f) = sing b := by
    apply ext fun z => ?_
    rw [mem_sep, mem_sing]
    constructor
    · exact fun ⟨_, hz⟩ => huniq z hz
    · rintro rfl
      refine ⟨?_, hab⟩
      exact mem_sUnion.mpr ⟨upair a z, mem_sUnion.mpr ⟨kpair a z, hab, mem_upair_right _ _⟩,
        mem_upair_right a z⟩
  rw [this, sUnion_sing]

/-- Beta on graphs. -/
theorem app_graph {F : V → V} {A a : V} (ha : a ∈ˢ A) :
    app (graph F A) a = F a := by
  refine app_eq_of_unique graph_ne_pt (mem_graph.mpr ⟨a, ha, rfl⟩) ?_
  intro y hy
  obtain ⟨x, -, hx⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hx
  rfl

/-- The raw dependent pair set `{⟨x, y⟩ : x ∈ A, y ∈ B x}`. -/
noncomputable def sigmaPairs (A : V) (B : V → V) : V :=
  sUnion (image (fun x => image (fun y => kpair x y) (B x)) A)

theorem mem_sigmaPairs {A p : V} {B : V → V} :
    p ∈ˢ sigmaPairs A B ↔ ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ B x ∧ p = kpair x y := by
  unfold sigmaPairs
  rw [mem_sUnion]
  constructor
  · rintro ⟨s, hs, hps⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hps
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨image (fun y => kpair x y) (B x), mem_image.mpr ⟨x, hx, rfl⟩,
      mem_image.mpr ⟨y, hy, rfl⟩⟩

theorem sigmaPairs_congr {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : sigmaPairs A B = sigmaPairs A B' := by
  unfold sigmaPairs
  congr 1
  exact image_congr fun x hx => by rw [h x hx]

theorem _root_.ConLeche.IsTGUniverse.sigmaPairs_mem {U A : V} {B : V → V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : sigmaPairs A B ∈ˢ U :=
  hU.famUnion_mem hA fun x hx =>
    hU.image_mem (hB x hx) fun _y hy =>
      hU.kpair_mem hA (hU.transitive hA hx) (hU.transitive (hB x hx) hy)

/-- The set of total single-valued dependent graphs on `A` with fibres
`B`: the `v ≠ 0` dependent product. -/
noncomputable def piSet (A : V) (B : V → V) : V :=
  sep (power (sigmaPairs A B))
    (fun f => ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y)

theorem mem_piSet {A f : V} {B : V → V} :
    f ∈ˢ piSet A B ↔ f ⊆ˢ sigmaPairs A B ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  unfold piSet
  rw [mem_sep, mem_power_iff_subset]

theorem piSet_congr {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piSet A B = piSet A B' := by
  unfold piSet
  rw [sigmaPairs_congr h]

theorem _root_.ConLeche.IsTGUniverse.piSet_mem {U A : V} {B : V → V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : piSet A B ∈ˢ U :=
  hU.mem_of_subset_mem (hU.power_mem (hU.sigmaPairs_mem hA hB)) sep_subset

theorem graph_mem_piSet {A : V} {B F : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : graph F A ∈ˢ piSet A B := by
  rw [mem_piSet]
  constructor
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hp
    exact mem_sigmaPairs.mpr ⟨x, hx, F x, hF x hx, rfl⟩
  · intro x hx
    refine ⟨F x, mem_graph.mpr ⟨x, hx, rfl⟩, ?_⟩
    intro y' hy'
    obtain ⟨x', -, hx'⟩ := mem_graph.mp hy'
    obtain ⟨rfl, rfl⟩ := kpair_inj hx'
    rfl

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) :
    f ≠ pt := by
  rintro rfl
  have := (mem_piSet.mp hf).1 ptTag ptTag_mem_pt
  obtain ⟨x, -, y, -, hy⟩ := mem_sigmaPairs.mp this
  exact ptTag_ne_kpair x y hy

theorem app_mem_of_mem_piSet {A f a : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  obtain ⟨y, hy, huniq⟩ := htot a ha
  rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  obtain ⟨x', -, y', hy', hp⟩ := mem_sigmaPairs.mp (hsub _ hy)
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact hy'

/-- Eta: a member of `piSet A B` is the graph of its own application. -/
theorem eq_graph_app_of_mem_piSet {A f : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) : graph (fun x => app f x) A = f := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  apply ext fun p => ?_
  rw [mem_graph]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, huniq⟩ := htot x hx
    rwa [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  · intro hp
    obtain ⟨x, hx, y, -, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
    obtain ⟨y', hy', huniq⟩ := htot x hx
    refine ⟨x, hx, ?_⟩
    rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy' huniq, huniq y hp]

/-- Members of `piSet A' B` that are graphs over `A` pin the domain:
every `x ∈ A'` lies in `A`. -/
theorem graph_dom_of_mem_piSet {A A' : V} {B F : V → V}
    (hf : graph F A ∈ˢ piSet A' B) : ∀ x, x ∈ˢ A' → x ∈ˢ A := by
  intro x hx
  obtain ⟨y, hy, -⟩ := (mem_piSet.mp hf).2 x hx
  obtain ⟨x', hx', hp⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact hx'

/-! ### Off-domain and junk behavior of `app`

`app` is total: on a non-`pt` value with no pair at the argument —
in particular off a graph's domain, or on the canonical junk value
`empty` itself — it returns `empty`.  These lemmas record that a
graph's off-domain behavior is *canonical*: two graphs over the same
domain that agree on the domain agree everywhere, which is what makes
a **total** equality between interpreted function towers equivalent to
pointwise agreement on fitting inputs (`eq_of_mem_piSet_app_eq`, and
`eq_of_mem_pi_app_eq`, deleted with `Derive/Pi.lean` at task #221). -/

theorem app_eq_empty_of_not_mem {f a : V} (hf : f ≠ pt)
    (h : ∀ y, ¬ kpair a y ∈ˢ f) : app f a = empty := by
  unfold app
  rw [if_neg hf]
  refine eq_empty fun z hz => ?_
  obtain ⟨y, hy, -⟩ := mem_sUnion.mp hz
  exact h y (mem_sep.mp hy).2

/-- `app` off a graph's domain is the canonical junk value. -/
theorem app_graph_of_not_mem {F : V → V} {A a : V} (ha : ¬ a ∈ˢ A) :
    app (graph F A) a = empty := by
  refine app_eq_empty_of_not_mem graph_ne_pt fun y hy => ?_
  obtain ⟨x, hx, hp⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact ha hx

/-- `app` on the canonical junk value returns junk: junk propagates
through applications. -/
theorem app_empty (a : V) : app (empty : V) a = empty :=
  app_eq_empty_of_not_mem (Ne.symm pt_ne_empty)
    (fun _y hy => not_mem_empty _ hy)

/-- A member of `piSet` applied off the domain is junk. -/
theorem app_off_dom_of_mem_piSet {A f a : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) (ha : ¬ a ∈ˢ A) : app f a = empty := by
  rw [← eq_graph_app_of_mem_piSet hf, app_graph_of_not_mem ha]

/-- Function extensionality for members of the raw dependent product:
two total single-valued graphs over the same domain that agree under
application on every domain member are equal (off the domain both
apply to canonical junk, so nothing else distinguishes them). -/
theorem eq_of_mem_piSet_app_eq {A f g : V} {B B' : V → V}
    (hf : f ∈ˢ piSet A B) (hg : g ∈ˢ piSet A B')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← eq_graph_app_of_mem_piSet hf, ← eq_graph_app_of_mem_piSet hg]
  exact graph_congr h

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] app

end ConLeche.SetTheory
