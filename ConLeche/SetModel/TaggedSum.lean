module

public import ConLeche.SetModel.TupleTower

@[expose] public section

/-!
# The tagged disjoint union (task #175 sum-types)

The semantic carrier of a directly-installed inductive with **any
number of constructors other than one**: a value is the pair of a
**numeral tag** — the constructor's index, a finite ordinal
`vnat i ∈ ω` — and that constructor's tuple tower
(`ConLeche/SetModel/TupleTower.lean`):

    sumSet w f = sigmaSet w ω (natFibre f)        f i = the i-th tower
    inj i a    = spair (vnat i) a

`natFibre f` is the fibre function over `ω`: `f i` at `vnat i`, junk
(`empty`) off the numerals — never consulted there, since every member
of `ω` is a unique numeral (`mem_omega_iff`/`vnat_inj`).  The same
function is the **case split** the recursor performs: on a member
`inj i a` the recursor reads `i` back through `natFibre` and applies
the `i`-th branch to `a` (`sumRec`).

Both regimes ride one definition: `sigmaSet` reads `w` only through
its zero test, so at `w = 0` the carrier is the truth value "some
constructor's tower is inhabited" (`sumSet_zero_elim`) with every
member the proof point, and above `0` it is the set of tagged pairs
(`sumSet_elim`).  The tag domain `ω` sits in `univ w` for every `w ≥ 1`
(`omega_mem_univ_succ` + cumulativity), which is where the carrier's
formation lands (`sumSet_mem_univ`); at `w = 0` no bound is needed
(`sumSet_zero_mem_univZero`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- The fibre function over the numerals: `f i` at `vnat i`, junk off
the numerals. -/
noncomputable def natFibre (f : Nat → V) (k : V) : V :=
  if h : ∃ i, k = vnat i then f (Classical.choose h) else empty

theorem natFibre_vnat (f : Nat → V) (i : Nat) : natFibre f (vnat i) = f i := by
  unfold natFibre
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact (vnat_inj (Classical.choose_spec (⟨i, rfl⟩ : ∃ i', (vnat i : V) = vnat i'))).symm

/-- Every member of `ω` is a numeral, at which the fibre is the
named set. -/
theorem natFibre_of_mem (f : Nat → V) {k : V} (hk : k ∈ˢ (omega : V)) :
    ∃ i, k = vnat i ∧ natFibre f k = f i := by
  obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
  exact ⟨i, rfl, natFibre_vnat f i⟩

/-- Fibre functions agreeing on the numerals agree on `ω`. -/
theorem natFibre_congr {f g : Nat → V} (h : ∀ i, f i = g i) (k : V) :
    natFibre f k = natFibre g k := by
  unfold natFibre
  split
  · rw [h]
  · rfl

/-- **The tagged sum carrier.** -/
noncomputable def sumSet (w : Nat) (f : Nat → V) : V :=
  sigmaSet w omega (natFibre f)

/-- **The injection** of constructor `i`. -/
noncomputable def inj (i : Nat) (a : V) : V := spair (vnat i) a

/-- The recursor's case split: the branch selected by the tag, applied
to the payload (`natFibre` over the branches). -/
noncomputable def sumRec (r : Nat → V → V) (x : V) : V :=
  natFibre (fun i => r i (ssnd x)) (sfst x)

/-! ## Laws -/

theorem sumSet_congr {w : Nat} {f g : Nat → V} (h : ∀ i, f i = g i) :
    sumSet w f = sumSet w g := by
  unfold sumSet
  exact sigma_congr fun k _ => natFibre_congr h k

/-- **Intro** (graph regime): the injection of a fitting payload is in
the carrier. -/
theorem inj_mem {w : Nat} (hw : w ≠ 0) {f : Nat → V} {i : Nat} {a : V}
    (ha : a ∈ˢ f i) : inj i a ∈ˢ sumSet w f := by
  unfold inj sumSet
  refine spair_mem hw (vnat_mem_omega i) ?_
  rw [natFibre_vnat]
  exact ha

/-- **Intro** (squash regime): the carrier at `w = 0` holds the point
whenever some constructor's tower is inhabited. -/
theorem pt_mem_sumSet_zero {f : Nat → V} {i : Nat} {a : V} (ha : a ∈ˢ f i) :
    (pt : V) ∈ˢ sumSet 0 f := by
  unfold sumSet
  exact pt_mem_sigma (a := vnat i) (b := a) (vnat_mem_omega i)
    (by rw [natFibre_vnat]; exact ha)

/-- **Elim** (graph regime): every carrier member is the injection of
a fitting payload. -/
theorem sumSet_elim {w : Nat} (hw : w ≠ 0) {f : Nat → V} {x : V}
    (hx : x ∈ˢ sumSet w f) : ∃ i a, a ∈ˢ f i ∧ x = inj i a := by
  unfold sumSet at hx
  obtain ⟨k, a, hk, ha, -, hpos⟩ := mem_sigma_elim hx
  obtain ⟨i, rfl, hfib⟩ := natFibre_of_mem f hk
  rw [hfib] at ha
  exact ⟨i, a, ha, hpos hw⟩

/-- **Elim** (squash regime): a `w = 0` carrier member is the point,
and some constructor's tower is inhabited. -/
theorem sumSet_zero_elim {f : Nat → V} {x : V} (hx : x ∈ˢ sumSet 0 f) :
    x = pt ∧ ∃ i a, a ∈ˢ f i := by
  unfold sumSet at hx
  obtain ⟨k, a, hk, ha, hz, -⟩ := mem_sigma_elim hx
  obtain ⟨i, rfl, hfib⟩ := natFibre_of_mem f hk
  rw [hfib] at ha
  exact ⟨hz rfl, i, a, ha⟩

/-- **Tag disjointness and injectivity**: equal injections have equal
tags and payloads. -/
theorem inj_inj {i j : Nat} {a b : V} (h : inj i a = inj j b) : i = j ∧ a = b := by
  unfold inj at h
  have h1 := congrArg sfst h
  have h2 := congrArg ssnd h
  rw [sfst_spair, sfst_spair] at h1
  rw [ssnd_spair, ssnd_spair] at h2
  exact ⟨vnat_inj h1, h2⟩

theorem sfst_inj (i : Nat) (a : V) : sfst (inj i a) = vnat i := sfst_spair _ _
theorem ssnd_inj (i : Nat) (a : V) : ssnd (inj i a) = a := ssnd_spair _ _

/-- **Formation** (graph regime): with every tower in `univ w`, the
carrier is too — the tag domain `ω` sits in every `univ w` above `0`. -/
theorem sumSet_mem_univ {w : Nat} (hw : w ≠ 0) {f : Nat → V}
    (hf : ∀ i, f i ∈ˢ (univ w : V)) : sumSet w f ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hω : (omega : V) ∈ˢ univ (w' + 1) := omega_mem_univ_succ w'
  have h := sigma_mem_univ (u := w' + 1) (v := w' + 1) (B := natFibre f) hω (fun k hk => by
    obtain ⟨i, rfl, hfib⟩ := natFibre_of_mem f hk
    rw [hfib]
    exact hf i)
  rwa [show Nat.max (w' + 1) (w' + 1) = w' + 1 from Nat.max_self _] at h

/-- **Formation** (squash regime), unconditional. -/
theorem sumSet_zero_mem_univZero (f : Nat → V) : sumSet 0 f ∈ˢ (univZero : V) := by
  unfold sumSet
  rw [sigmaSet_zero]
  exact truthVal_mem_univZero _

/-- **Iota** for the case split — unconditional. -/
theorem sumRec_inj (r : Nat → V → V) (i : Nat) (a : V) : sumRec r (inj i a) = r i a := by
  unfold sumRec
  rw [sfst_inj, ssnd_inj, natFibre_vnat]

/-- **Storage hygiene**: the carrier is never the proof point. -/
theorem sumSet_ne_pt {w : Nat} (f : Nat → V) : sumSet w f ≠ (pt : V) := sigmaSet_ne_pt

/-! ## Degeneracy checks -/

/-- Zero constructors: the carrier is empty in the graph regime. -/
example {w : Nat} (hw : w ≠ 0) {x : V} (hx : x ∈ˢ sumSet w (fun _ => (empty : V))) : False := by
  obtain ⟨i, a, ha, -⟩ := sumSet_elim hw hx
  exact not_mem_empty a ha

/-- Two constructors: the two injections are distinct. -/
example (a b : V) : inj 0 a ≠ inj 1 b := fun h => by
  have := (inj_inj h).1
  omega

end ConLeche.SetTheory.Tower
