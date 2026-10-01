module

public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# Quotients

`quotSet u A R` is, for `u ≠ 0`, the set of equivalence classes of the
equivalence closure of "`app (app R a) b` is inhabited" on `A` (classes
by separation, the class set by replacement); for `u = 0` the base
lives in `Prop`, everything collapses to the proof point, and the
quotient is `image (fun _ => pt) A` — the truth value `[A inhabited]`.

`quotLift` lifts `f` to the quotient as the graph of
`q ↦ app f (representative of q)` (representatives by choice) — except
when `f` is the proof point, where the lift is the proof point too.
That tag is what makes the beta law `app (quotLift …) (quotClass … a) =
app f a` hold with *no typing premise on `f`* (matching the interface):
a `pt`-tagged `f` beta-reduces to `pt` on both sides, any other `f`
goes through the representative and the invariance premise, with the
`u = 0` collapse handled by `A ⊆ {pt}` (from `A ∈ univ 0`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The equivalence closure, on `A`, of "`app (app R a) b` is
inhabited". -/
inductive QuotRel (A R : V) : V → V → Prop where
  | base {a b : V} : a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      QuotRel A R a b
  | refl {a : V} : a ∈ˢ A → QuotRel A R a a
  | symm {a b : V} : QuotRel A R a b → QuotRel A R b a
  | trans {a b c : V} : QuotRel A R a b → QuotRel A R b c → QuotRel A R a c

theorem QuotRel.mem {A R a b : V} (h : QuotRel A R a b) : a ∈ˢ A ∧ b ∈ˢ A := by
  induction h with
  | base ha hb _ => exact ⟨ha, hb⟩
  | refl ha => exact ⟨ha, ha⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-- The `QuotRel`-class of `a` in `A`. -/
noncomputable def qclass (A R a : V) : V := sep A (fun b => QuotRel A R a b)

theorem mem_qclass {A R a b : V} :
    b ∈ˢ qclass A R a ↔ b ∈ˢ A ∧ QuotRel A R a b := mem_sep

theorem self_mem_qclass {A R a : V} (ha : a ∈ˢ A) : a ∈ˢ qclass A R a :=
  mem_qclass.mpr ⟨ha, QuotRel.refl ha⟩

theorem qclass_eq_of_rel {A R a b : V} (h : QuotRel A R a b) :
    qclass A R a = qclass A R b :=
  ext fun z => by
    rw [mem_qclass, mem_qclass]
    exact ⟨fun ⟨hz, hr⟩ => ⟨hz, (h.symm).trans hr⟩,
           fun ⟨hz, hr⟩ => ⟨hz, h.trans hr⟩⟩

theorem rel_of_qclass_eq {A R a b : V} (ha : a ∈ˢ A) (_hb : b ∈ˢ A)
    (h : qclass A R a = qclass A R b) : QuotRel A R a b :=
  (mem_qclass.mp (h ▸ self_mem_qclass ha)).2.symm

open Classical in
/-- The quotient (see module docs). -/
noncomputable def quotSet (u : Nat) (A R : V) : V :=
  if u = 0 then image (fun _ => pt) A else image (fun a => qclass A R a) A

open Classical in
/-- The class of `a` in the quotient. -/
noncomputable def quotClass (u : Nat) (A R a : V) : V :=
  if u = 0 then pt else qclass A R a

theorem quotClass_mem {u : Nat} {A R a : V} (ha : a ∈ˢ A) :
    quotClass u A R a ∈ˢ quotSet u A R := by
  unfold quotClass quotSet
  split
  · exact mem_image.mpr ⟨a, ha, rfl⟩
  · exact mem_image.mpr ⟨a, ha, rfl⟩

theorem quotClass_surj {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    ∃ a, a ∈ˢ A ∧ q = quotClass u A R a := by
  unfold quotSet at hq
  unfold quotClass
  split at hq
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (if_pos h).symm⟩
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (if_neg h).symm⟩

/-- A class formed at ONE pair of parameters that lands in the quotient
of ANOTHER: its representative lies in the second parameter's carrier,
and the class is the second quotient's class of that same
representative.  Nothing relates the two parameter pairs — at a positive
level the first class is a `qclass` of the second's, and at level zero
both classes are the point and the second carrier is inhabited because
the quotient is. -/
theorem quotClass_of_mem_quotSet {u : Nat} {Aset R A' R' a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hA' : A' ∈ˢ (univ u : V)) (ha : a ∈ˢ A')
    (hmem : quotClass u A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u A' R' a = quotClass u Aset R a := by
  obtain ⟨b, hb, hcls⟩ := quotClass_surj hmem
  by_cases hu : u = 0
  · subst hu
    refine ⟨?_, by unfold quotClass; rw [if_pos rfl, if_pos rfl]⟩
    rw [univ_zero] at hA' hAset
    rw [eq_pt_of_mem_univZero hA' ha, ← eq_pt_of_mem_univZero hAset hb]
    exact hb
  · unfold quotClass at hcls ⊢
    rw [if_neg hu, if_neg hu] at hcls
    rw [if_neg hu, if_neg hu]
    have hab : a ∈ˢ qclass Aset R b := by rw [← hcls]; exact self_mem_qclass ha
    obtain ⟨haA, hrel⟩ := mem_qclass.mp hab
    exact ⟨haA, hcls.trans (qclass_eq_of_rel hrel)⟩

theorem quotSound {u : Nat} {A R a b w : V} (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hw : w ∈ˢ app (app R a) b) : quotClass u A R a = quotClass u A R b := by
  unfold quotClass
  split
  · rfl
  · exact qclass_eq_of_rel (QuotRel.base ha hb ⟨w, hw⟩)

theorem quotSet_mem_univ {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V)) :
    quotSet u A R ∈ˢ (univ u : V) := by
  unfold quotSet
  split
  · next h =>
    subst h
    rw [univ_zero]
    refine mem_univZero.mpr fun z hz => ?_
    obtain ⟨-, -, rfl⟩ := mem_image.mp hz
    exact pt_mem_unitSet
  · next h =>
    refine (univ_isTGUniverse h).mem_of_subset_mem
      ((univ_isTGUniverse h).power_mem hA) fun z hz => ?_
    obtain ⟨a, -, rfl⟩ := mem_image.mp hz
    exact mem_power.mpr fun w hw => (mem_qclass.mp hw).1

open Classical in
/-- A representative of a quotient class, by choice. -/
noncomputable def qrep (u : Nat) (A R q : V) : V :=
  if h : ∃ a, a ∈ˢ A ∧ q = quotClass u A R a then Classical.choose h else empty

theorem qrep_spec {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    qrep u A R q ∈ˢ A ∧ q = quotClass u A R (qrep u A R q) := by
  unfold qrep
  rw [dif_pos (quotClass_surj hq)]
  exact Classical.choose_spec (quotClass_surj hq)

/-- The invariance premise extends from the base relation to its
equivalence closure. -/
theorem app_eq_of_rel {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (h : QuotRel A R a b) : app f a = app f b := by
  induction h with
  | base ha hb hw => exact hinv _ _ ha hb hw
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equal classes have equal `f`-values: by closure invariance at
`u ≠ 0`, and by the `A ⊆ {pt}` collapse at `u = 0`. -/
theorem app_eq_of_quotClass_eq {u : Nat} {A R f a b : V}
    (hA : A ∈ˢ (univ u : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (hq : quotClass u A R a = quotClass u A R b) : app f a = app f b := by
  unfold quotClass at hq
  split at hq
  · next h =>
    subst h
    rw [univ_zero] at hA
    rw [eq_pt_of_mem_univZero hA ha, eq_pt_of_mem_univZero hA hb]
  · exact app_eq_of_rel hinv (rel_of_qclass_eq ha hb hq)

/-! ## pt-freshness refutation evidence (task #109)

Quotient types are **not** unconditionally pt-fresh, for *any*
constructible proof point: classes are arbitrary nonempty subsets of
the base, so with base `ptTag` itself and a total relation the class
set is exactly `{ptTag} = pt`.  Never resurrect a `quotSet_ne_pt`; the
#109 syntactic freshness guards exclude `Quot`-typed slots instead.
(The base `ptTag` is not the interpretation of any *writable* type —
the obstruction is semantic, in the ∀-A-R quantification of the model
lemmas.  The old `pt = {∅}` was the unique choice immune to this — the
empty set is never a class — which is exactly what the re-choice
trades for data freshness.) -/

theorem quotSet_eq_pt_countermodel :
    ∃ A R : V, quotSet 1 A R = pt := by
  refine ⟨ptTag, graph (fun _ => graph (fun _ => unitSet) ptTag) ptTag, ?_⟩
  have hrel : ∀ a b : V, a ∈ˢ (ptTag : V) → b ∈ˢ (ptTag : V) →
      QuotRel ptTag (graph (fun _ => graph (fun _ => unitSet) ptTag) ptTag)
        a b := by
    intro a b ha hb
    refine QuotRel.base ha hb ⟨pt, ?_⟩
    rw [app_graph ha, app_graph hb]
    exact pt_mem_unitSet
  have hclass : ∀ a : V, a ∈ˢ (ptTag : V) →
      qclass ptTag (graph (fun _ => graph (fun _ => unitSet) ptTag) ptTag) a
        = ptTag := by
    intro a ha
    apply ext fun z => ?_
    rw [mem_qclass]
    exact ⟨fun h => h.1, fun hz => ⟨hz, hrel a z ha hz⟩⟩
  unfold quotSet
  rw [if_neg Nat.one_ne_zero]
  apply ext fun z => ?_
  rw [mem_image, mem_pt]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hclass a ha
  · rintro rfl
    exact ⟨empty, empty_mem_ptTag, (hclass empty empty_mem_ptTag).symm⟩

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] quotSet quotClass

end ConLeche.SetTheory
