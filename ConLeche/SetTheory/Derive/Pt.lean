module

public import ConLeche.SetTheory.Derive.Universe

@[expose] public section

/-!
# The proof point, truth values, `univ 0`, and `eqv`

* `pt := {ptTag}` with `ptTag := {∅, {{∅}}}` — the tagged proof
  point: the canonical inhabitant of every true proposition.  The tag
  is chosen so that **no data-value encoding produces `pt`** (task
  #109; the battery was `Derive/PtFresh.lean`, deleted at task #221 with
the collapse it served).  Selection principle:
  `pt` must be a singleton whose element (a) has an *empty* member —
  so neither the tag nor `pt` is a Kuratowski pair, pair elements
  being nonempty (the anti-pair tag `Derive/Graphs.lean` exploits, one
  level up from the old `pt = {∅}`); (b) is *not a singleton* — else
  `pt = {{a}} = kpair a a`, a writable pair value; (c) is not `∅` —
  else `pt = {∅} = vnat 1`, a writable numeral (the old collision);
  and (d) has members that **cohabit no writable type** — else `pt` is
  a writable singleton quotient class (`{2}` = the class of
  `Quot.mk (· = 2 ∧ · = 2) 2` killed the `{vnat 2}` candidate).
  `ptTag`'s members `∅` and `{{∅}} = kpair ∅ ∅` live in `Nat` resp.
  pair types only, and no writable type hosts both.
* `unitSet := {pt}` — the true truth value, and the model of `PUnit`.
* `univZero := power unitSet = {∅, {pt}}` — the set of truth values,
  the `U₀ = {∅, {•}}` of Mario Carneiro, *The Type Theory of Lean*,
  master's thesis, Carnegie Mellon University, 2019; stating it as a
  power set makes
  "members of `univ 0` are subsets of `{pt}`" definitional, and
  propositional extensionality one application of `ext`.
* `truthVal p` — the truth value of a meta-level proposition, `{pt}`
  if `p` holds and `∅` otherwise (classical); `eqv x y` is
  `truthVal (x = y)`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The proof-point tag `{∅, {{∅}}}` (see the module docstring for the
selection principle). -/
noncomputable def ptTag : V := upair empty (sing (sing empty))

theorem mem_ptTag {z : V} :
    z ∈ˢ (ptTag : V) ↔ z = empty ∨ z = sing (sing empty) := mem_upair

theorem empty_mem_ptTag : (empty : V) ∈ˢ ptTag :=
  mem_ptTag.mpr (Or.inl rfl)

theorem ptTag_ne_empty : (ptTag : V) ≠ empty :=
  ne_empty_of_mem empty_mem_ptTag

/-- The tag is not a singleton: its two members `∅` and `{{∅}}`
differ.  (Blocks `pt = kpair a a = {{a}}`.) -/
theorem ptTag_ne_sing (a : V) : (ptTag : V) ≠ sing a := by
  intro h
  obtain ⟨h1, h2⟩ := upair_eq_sing h
  exact ne_empty_of_mem (mem_sing.mpr rfl) (h2.trans h1.symm)

/-- The tag is not a Kuratowski pair: `∅` is among its members, while
every member of a pair is nonempty. -/
theorem ptTag_ne_kpair (a b : V) : (ptTag : V) ≠ kpair a b := by
  intro h
  obtain ⟨w, hw⟩ := mem_kpair_nonempty (h ▸ empty_mem_ptTag)
  exact not_mem_empty w hw

/-- The proof point `pt = {ptTag}`. -/
noncomputable def pt : V := sing ptTag

theorem mem_pt {z : V} : z ∈ˢ (pt : V) ↔ z = ptTag := mem_sing

theorem ptTag_mem_pt : (ptTag : V) ∈ˢ pt := mem_pt.mpr rfl

theorem pt_ne_empty : (pt : V) ≠ empty :=
  ne_empty_of_mem ptTag_mem_pt

/-- `pt` is not a Kuratowski pair: `pt` is a singleton, so the pair
would be degenerate (`kpair a a = {{a}}`), forcing the tag to be the
singleton `{a}` — which it is not. -/
theorem pt_ne_kpair (a b : V) : (pt : V) ≠ kpair a b := by
  intro h
  obtain ⟨h1, -⟩ := upair_eq_sing h.symm
  exact ptTag_ne_sing a h1.symm

/-- `pt` is not a member of its own tag (blocks the two-step membership
cycle `pt ∈ ptTag ∈ pt` that `not_mem_self` cannot see). -/
theorem pt_not_mem_ptTag : ¬ (pt : V) ∈ˢ ptTag := by
  intro h
  rcases mem_ptTag.mp h with hpe | hps
  · exact pt_ne_empty hpe
  · have hm := ptTag_mem_pt (V := V)
    rw [hps] at hm
    exact ptTag_ne_sing empty (mem_sing.mp hm)

/-- The canonical singleton `{pt}`: the true truth value. -/
noncomputable def unitSet : V := sing pt

theorem mem_unitSet_iff {z : V} : z ∈ˢ (unitSet : V) ↔ z = pt := mem_sing

theorem pt_mem_unitSet : (pt : V) ∈ˢ unitSet := mem_unitSet_iff.mpr rfl

theorem unitSet_ne_empty : (unitSet : V) ≠ empty :=
  ne_empty_of_mem pt_mem_unitSet

/-- The interpretation of `Sort 0`: the set `{∅, {pt}}` of truth
values, stated as the power set of `{pt}`. -/
noncomputable def univZero : V := power unitSet

theorem mem_univZero {T : V} : T ∈ˢ (univZero : V) ↔ T ⊆ˢ unitSet :=
  mem_power_iff_subset

/-- Members of `univ 0` have at most the proof point as element. -/
theorem eq_pt_of_mem_univZero {T x : V} (hT : T ∈ˢ (univZero : V))
    (hx : x ∈ˢ T) : x = pt :=
  mem_unitSet_iff.mp (mem_univZero.mp hT x hx)

/-- Propositional extensionality: truth values with the same
`pt`-membership are equal. -/
theorem univZero_ext {A B : V} (hA : A ∈ˢ (univZero : V))
    (hB : B ∈ˢ (univZero : V)) (hab : pt ∈ˢ A → pt ∈ˢ B)
    (hba : pt ∈ˢ B → pt ∈ˢ A) : A = B :=
  ext fun z =>
    ⟨fun hz => by
       have h := eq_pt_of_mem_univZero hA hz; subst h; exact hab hz,
     fun hz => by
       have h := eq_pt_of_mem_univZero hB hz; subst h; exact hba hz⟩

open Classical in
/-- The truth value of a meta-level proposition: `{pt}` if it holds,
`∅` otherwise. -/
noncomputable def truthVal (p : Prop) : V := if p then unitSet else empty

theorem mem_truthVal {p : Prop} {z : V} :
    z ∈ˢ (truthVal p : V) ↔ p ∧ z = pt := by
  unfold truthVal
  split
  · next hp => exact ⟨fun hz => ⟨hp, mem_unitSet_iff.mp hz⟩, fun ⟨_, hz⟩ => hz ▸ pt_mem_unitSet⟩
  · next hp =>
    exact ⟨fun hz => absurd hz (not_mem_empty z), fun ⟨h, _⟩ => absurd h hp⟩

theorem pt_mem_truthVal {p : Prop} (hp : p) : (pt : V) ∈ˢ truthVal p :=
  mem_truthVal.mpr ⟨hp, rfl⟩

theorem of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ (truthVal p : V)) : p :=
  (mem_truthVal.mp hz).1

theorem eq_pt_of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ (truthVal p : V)) :
    z = pt :=
  (mem_truthVal.mp hz).2

theorem truthVal_eq_unitSet {p : Prop} (hp : p) : (truthVal p : V) = unitSet := by
  unfold truthVal; exact if_pos hp

theorem truthVal_eq_empty {p : Prop} (hp : ¬ p) : (truthVal p : V) = empty := by
  unfold truthVal; exact if_neg hp

/-- Truth values are `∅` or `{pt}` — never the point `{∅}` itself. -/
theorem truthVal_ne_pt (p : Prop) : (truthVal p : V) ≠ pt := by
  intro h
  by_cases hp : p
  · rw [truthVal_eq_unitSet hp] at h
    have hm := pt_mem_unitSet (V := V)
    rw [h] at hm
    exact not_mem_self (pt : V) hm
  · rw [truthVal_eq_empty hp] at h
    exact pt_ne_empty h.symm

theorem truthVal_congr {p q : Prop} (h : p ↔ q) :
    (truthVal p : V) = truthVal q := by
  rcases Classical.em p with hp | hp
  · rw [truthVal_eq_unitSet hp, truthVal_eq_unitSet (h.mp hp)]
  · rw [truthVal_eq_empty hp, truthVal_eq_empty (fun hq => hp (h.mpr hq))]

theorem truthVal_mem_univZero (p : Prop) :
    (truthVal p : V) ∈ˢ univZero := by
  rcases Classical.em p with hp | hp
  · rw [truthVal_eq_unitSet hp]
    exact mem_univZero.mpr (Subset.refl _)
  · rw [truthVal_eq_empty hp]
    exact mem_univZero.mpr (empty_subset _)

/-- Every member of `univ 0` is the truth value of its own
inhabitedness. -/
theorem mem_univZero_eq_truthVal {T : V} (hT : T ∈ˢ (univZero : V)) :
    T = truthVal (pt ∈ˢ T) := by
  rcases Classical.em ((pt : V) ∈ˢ T) with hp | hp
  · rw [truthVal_eq_unitSet hp]
    exact ext fun z => ⟨fun hz => eq_pt_of_mem_univZero hT hz ▸ pt_mem_unitSet,
      fun hz => mem_unitSet_iff.mp hz ▸ hp⟩
  · rw [truthVal_eq_empty hp]
    exact eq_empty fun z hz => hp (eq_pt_of_mem_univZero hT hz ▸ hz)

/-- The truth value of an equality. -/
noncomputable def eqv (x y : V) : V := truthVal (x = y)

theorem eqv_mem_univZero (x y : V) : eqv x y ∈ˢ (univZero : V) :=
  truthVal_mem_univZero _

theorem eq_of_mem_eqv {a x y : V} (h : a ∈ˢ eqv x y) : x = y :=
  of_mem_truthVal h

theorem pt_mem_eqv_self (x : V) : (pt : V) ∈ˢ eqv x x :=
  pt_mem_truthVal rfl

/-- `pt`, `unitSet`, `univZero` and truth values live in every
(inhabited) Grothendieck universe. -/
theorem _root_.ConLeche.IsTGUniverse.pt_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : (pt : V) ∈ˢ U :=
  hU.sing_mem hy (hU.upair_mem hy (hU.empty_mem hy)
    (hU.sing_mem hy (hU.sing_mem hy (hU.empty_mem hy))))

theorem _root_.ConLeche.IsTGUniverse.unitSet_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : (unitSet : V) ∈ˢ U :=
  hU.sing_mem hy (hU.pt_mem hy)

theorem _root_.ConLeche.IsTGUniverse.univZero_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : (univZero : V) ∈ˢ U :=
  hU.power_mem (hU.unitSet_mem hy)

theorem _root_.ConLeche.IsTGUniverse.truthVal_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) (p : Prop) :
    (truthVal p : V) ∈ˢ U :=
  hU.transitive (hU.univZero_mem hy) (truthVal_mem_univZero p)

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] ptTag pt unitSet eqv

end ConLeche.SetTheory
