module

public import ConLeche.SetTheory.Basic

@[expose] public section

/-!
# The two-regime product and abstraction (task #151, tier B)

`piR`/`lamR` are the **annotation-driven** dependent product and
abstraction: they read a numeral — the codomain sort of the binder,
supplied by the annotation pass — and dispatch on it, rather than
inspecting the semantic value the way the domain-relative collapse
(`pcol`/`piC`/`lamC`, `ConLeche/SetTheory/Derive/Pi.lean` — deleted at
task #221, unread since these operators replaced it) does.

* **`v = 0` — the truth-value (squash) regime.**  `piR 0 A B` is the
  truth value `[∀ x ∈ A, B x inhabited]`, `lamR 0 A F` is the canonical
  proof.  Propositions are subsets of the canonical one-element set
  `unitSet = {pt}`, so proof irrelevance and impredicativity are both
  immediate: *a product landing in `Prop` is small whatever its domain
  is* (`piR_zero_mem_univZero`), with no size or universe side
  condition anywhere.
* **`v ≠ 0` — the graph regime.**  `piR v A B` is `piSet A B`, the set
  of total single-valued function graphs over `A`; `lamR v A F` is the
  literal graph.  **No collapse, no proof point**: a member of a
  positive-regime product is a graph, is never `pt`
  (`not_pt_mem_piR_pos`), determines its own domain
  (`piR_dom_unique`, with *no* `≠ pt` side condition), and applies to
  the canonical junk `∅` off that domain (`app_off_dom_piR_pos`).

The operators are the pre-#100 `SetTheory.pi`/`SetTheory.lam` (see the
git history of `Derive/Pi.lean`), restated in this namespace so that
`ConLeche/SetTheory/*` is untouched; the law battery below is that file's,
plus the *inversion* laws that only the annotation-driven definition can
have (`mem_piR_pos`, `piR_dom_unique`, `not_pt_mem_piR_pos`).

**On `pt`.**  The proof point appears in exactly one place: the `v = 0`
branch of `lamR`, as the canonical inhabitant of a true proposition.
That is forced — `SetTheory`'s `univ 0 = power unitSet` fixes the
canonical one-element set, so the unique element of a true truth value
*is* `pt` — and it is not a collapse: no clause here tests a value, and
the graph regime never produces, contains, or consults it.  So `pt` is
*demoted, not deleted*: deleting it is not achievable — it would mean
re-deriving `univZero` over a different singleton, and renaming the
canonical point changes nothing — and not needed, because nothing here
tests for it.
-/

namespace ConLeche.SetModel

open SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The dependent product at codomain sort `v`: a truth value at `0`,
the set of function graphs above it. -/
noncomputable def piR (v : Nat) (A : V) (B : V → V) : V :=
  if v = 0 then truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) else piSet A B

/-- Abstraction at codomain sort `v`: the canonical proof at `0`, the
literal function graph above it. -/
noncomputable def lamR (v : Nat) (A : V) (F : V → V) : V :=
  if v = 0 then pt else graph F A

/-! ## The two branches -/

theorem piR_zero {A : V} {B : V → V} :
    piR 0 A B = truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) := if_pos rfl

theorem piR_pos {v : Nat} (hv : v ≠ 0) {A : V} {B : V → V} :
    piR v A B = piSet A B := if_neg hv

theorem lamR_zero {A : V} {F : V → V} : lamR 0 A F = (pt : V) := if_pos rfl

theorem lamR_pos {v : Nat} (hv : v ≠ 0) {A : V} {F : V → V} :
    lamR v A F = graph F A := if_neg hv

/-! ## Congruence -/

theorem piR_congr {v : Nat} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piR v A B = piR v A B' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [piR_zero, piR_zero]
    exact truthVal_congr
      ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩
  · rw [piR_pos (Nat.pos_iff_ne_zero.mp hv), piR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact piSet_congr h

theorem lamR_congr {v : Nat} {A : V} {F F' : V → V}
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR v A F = lamR v A F' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, lamR_zero]
  · rw [lamR_pos (Nat.pos_iff_ne_zero.mp hv), lamR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact graph_congr h

/-! ## Zero-agreement

`piR`/`lamR` read their numeral **only through the `v = 0` test**, so
annotations that agree on zero-ness are interchangeable.  This is the
pre-#100 `pi_congr_zero_agree`/`lam_congr_zero_agree` pair, and it is
what lets a λ-tower carry its *result* sort at every binder rather than
the exact `imax` fold: in `(a₁ : A₁) → … → (aₙ : Aₙ) → T` the sort of
each suffix is `imax (…) r` with `r` the sort of `T`, and
`imax x y = 0 ↔ y = 0`.  See `Interp/Value.lean`'s annotation
convention. -/

theorem piR_zero_agree {v v' : Nat} (hz : v = 0 ↔ v' = 0) {A : V}
    {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) : piR v A B = piR v' A B' := by
  by_cases hv : v = 0
  · rw [hv, hz.mp hv]; exact piR_congr h
  · have hv' : v' ≠ 0 := fun h0 => hv (hz.mpr h0)
    rw [piR_pos hv, piR_pos hv']
    exact piSet_congr h

theorem lamR_zero_agree {v v' : Nat} (hz : v = 0 ↔ v' = 0) {A : V}
    {F F' : V → V} (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR v A F = lamR v' A F' := by
  by_cases hv : v = 0
  · rw [hv, hz.mp hv, lamR_zero, lamR_zero]
  · have hv' : v' ≠ 0 := fun h0 => hv (hz.mpr h0)
    rw [lamR_pos hv, lamR_pos hv']
    exact graph_congr h

/-- `imax`'s zero test is its codomain's — the arithmetic behind the
tower convention. -/
theorem imax_eq_zero_iff (x y : Nat) :
    (if y = 0 then 0 else Nat.max x y) = 0 ↔ y = 0 := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [if_neg hy]
    exact ⟨fun h => absurd (Nat.le_zero.mp (h ▸ Nat.le_max_right x y)) hy,
      fun h => absurd h hy⟩

/-! ## Introduction, elimination, beta, eta -/

/-- Introduction: fibre-wise members abstract into the product.  At
`v = 0` the premise itself witnesses every fibre inhabited. -/
theorem lamR_mem {v : Nat} {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lamR v A F ∈ˢ piR v A B := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, piR_zero]
    exact pt_mem_truthVal fun x hx => ⟨F x, hF x hx⟩
  · rw [lamR_pos (Nat.pos_iff_ne_zero.mp hv), piR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact graph_mem_piSet hF

/-- Introduction across zero-agreeing annotations: a tower annotated
with its result sort still inhabits the product annotated with the
exact `imax`. -/
theorem lamR_mem_zero_agree {v v' : Nat} (hz : v = 0 ↔ v' = 0) {A : V}
    {F B : V → V} (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lamR v A F ∈ˢ piR v' A B := by
  rw [lamR_zero_agree hz (fun _ _ => rfl) (F' := F)]
  exact lamR_mem hF

/-- **Proof irrelevance at products**: inhabitants of a `Prop`-valued
product are the canonical proof. -/
theorem eq_pt_of_mem_piR_zero {A f : V} {B : V → V} (hf : f ∈ˢ piR 0 A B) :
    f = pt := by
  rw [piR_zero] at hf; exact eq_pt_of_mem_truthVal hf

/-- **Squash-regime introduction from inhabitation.**  At `v = 0` the
product is a truth value, so membership of the canonical proof needs
only that every fibre is *inhabited* — strictly weaker than
`lamR_mem`'s pointwise `F x ∈ˢ B x`, and the form every tower whose
value carries no regime tag has to use at kind `0`
(`Interp/BasisOk.lean`, the `psigmaMk` finding). -/
theorem pt_mem_piR_zero {A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) : (pt : V) ∈ˢ piR 0 A B := by
  rw [piR_zero]; exact pt_mem_truthVal h

/-- The pointwise form, matching the collapse lane's
`pt_mem_piC_iff.mpr` so the `pt`-valued towers port line for line. -/
theorem pt_mem_piR_zero_of {A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → (pt : V) ∈ˢ B x) : (pt : V) ∈ˢ piR 0 A B :=
  pt_mem_piR_zero fun x hx => ⟨pt, h x hx⟩

/-- Elimination.  The fibre premise is needed only at `v = 0`, where
the fibres must be truth values. -/
theorem app_mem_piR {v : Nat} {A f a : V} {B : V → V}
    (hf : f ∈ˢ piR v A B) (ha : a ∈ˢ A)
    (hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) : app f a ∈ˢ B a := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have hfp : f = pt := eq_pt_of_mem_piR_zero hf
    rw [piR_zero] at hf
    obtain ⟨y, hy⟩ := of_mem_truthVal hf a ha
    rw [hfp, app_pt]
    rwa [eq_pt_of_mem_univZero (hB0 rfl a ha) hy] at hy
  · rw [piR_pos (Nat.pos_iff_ne_zero.mp hv)] at hf
    exact app_mem_of_mem_piSet hf ha

/-- Elimination in the graph regime: no fibre premise at all. -/
theorem app_mem_piR_pos {v : Nat} {A f a : V} {B : V → V} (hv : v ≠ 0)
    (hf : f ∈ˢ piR v A B) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  rw [piR_pos hv] at hf; exact app_mem_of_mem_piSet hf ha

/-- Beta, conditional on domain membership (set-theoretic functions
have set domains). -/
theorem app_lamR {v : Nat} {A a : V} {F B : V → V}
    (ha : a ∈ˢ A) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    app (lamR v A F) a = F a := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, app_pt]
    exact (eq_pt_of_mem_univZero (hB0 rfl a ha) (hF a ha)).symm
  · rw [lamR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact app_graph ha

/-- **Beta in the graph regime**: application of an abstraction on its
domain computes, with no typing premise whatsoever — it is literally
`app_graph`. -/
theorem app_lamR_pos {v : Nat} {A a : V} {F : V → V} (hv : v ≠ 0)
    (ha : a ∈ˢ A) : app (lamR v A F) a = F a := by
  rw [lamR_pos hv]; exact app_graph ha

/-- **Off-domain application in the graph regime** — `app_lamR_pos`'s
complement.  The rigidity a *type former*'s application is inverted
with: off its domain a graph-regime abstraction applies to the
canonical junk `∅`, which has no members, so an inhabited application
forces its argument into the domain.  Added for the caps tier's
pinned-pair η row (task #161). -/
theorem app_lamR_of_not_mem {v : Nat} {A a : V} {F : V → V} (hv : v ≠ 0)
    (ha : ¬ a ∈ˢ A) : app (lamR v A F) a = (empty : V) := by
  rw [lamR_pos hv]; exact app_graph_of_not_mem ha

/-- Graph-regime abstractions are graphs, never the proof point. -/
theorem lamR_ne_pt {v : Nat} {A : V} {F : V → V} (hv : v ≠ 0) :
    lamR v A F ≠ pt := by rw [lamR_pos hv]; exact graph_ne_pt

/-- Eta: a member of a product is the abstraction of its
applications. -/
theorem lamR_eta {v : Nat} {A f : V} {B : V → V} (hf : f ∈ˢ piR v A B) :
    lamR v A (fun x => app f x) = f := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, eq_pt_of_mem_piR_zero hf]
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    rw [piR_pos hv'] at hf
    rw [lamR_pos hv']
    exact eq_graph_app_of_mem_piSet hf

/-- Function extensionality for product members: on-domain agreement is
total agreement.  At `v = 0` both sides are the canonical proof; above
it both are graphs over `A`, whose off-domain applications are the same
canonical junk. -/
theorem eq_of_mem_piR_app_eq {v : Nat} {A f g : V} {B B' : V → V}
    (hf : f ∈ˢ piR v A B) (hg : g ∈ˢ piR v A B')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← lamR_eta hf, ← lamR_eta hg]; exact lamR_congr h

/-! ## The graph regime: inversion and junk-freeness

These are the laws the collapse cannot have.  Under `piC` a product
member is either a graph *or* the proof point (`mem_piC_cases`), so
every consumer dispatches; here the annotation has already decided, and
membership in a positive-regime product is *by definition* graph-hood. -/

/-- **The prized inversion.**  A member of a graph-regime product is a
graph whose domain is exactly the product's domain, whose applications
land pointwise in the fibres, which is never the proof point, and which
applies to the canonical junk `∅` off the domain.  Every clause is by
definition of `piSet`; nothing about `B` is used. -/
theorem mem_piR_pos {v : Nat} {A f : V} {B : V → V} (hv : v ≠ 0)
    (hf : f ∈ˢ piR v A B) :
    graph (fun x => app f x) A = f ∧
    (∀ x, x ∈ˢ A → app f x ∈ˢ B x) ∧
    (∀ a, ¬ a ∈ˢ A → app f a = empty) ∧
    f ≠ pt := by
  rw [piR_pos hv] at hf
  exact ⟨eq_graph_app_of_mem_piSet hf, fun x hx => app_mem_of_mem_piSet hf hx,
    fun a ha => app_off_dom_of_mem_piSet hf ha, ne_pt_of_mem_piSet hf⟩

/-- The proof point never inhabits a graph-regime product — for *any*
domain and *any* fibre family, in particular a universe-valued one.
This is the removal of the collapse's universe-cohabitation wall, where
`pt ∈ˢ piC A (fun _ => univ 0)` holds at an unknown-empty domain. -/
theorem not_pt_mem_piR_pos {v : Nat} {A : V} {B : V → V} (hv : v ≠ 0) :
    ¬ (pt : V) ∈ˢ piR v A B :=
  fun h => (mem_piR_pos hv h).2.2.2 rfl

/-- A graph-regime member applied off the domain is canonical junk —
never a proof point, never anything a consumer must dispatch on. -/
theorem app_off_dom_piR_pos {v : Nat} {A f a : V} {B : V → V} (hv : v ≠ 0)
    (hf : f ∈ˢ piR v A B) (ha : ¬ a ∈ˢ A) : app f a = empty :=
  (mem_piR_pos hv hf).2.2.1 a ha

/-- **Domain uniqueness, unconditional.**  A graph determines its own
domain, so membership in two graph-regime products identifies their
domains — with no `≠ pt` side condition (`piC_dom_unique` needs one,
and supplying it is what the collapse made hard). -/
theorem piR_dom_unique {v v' : Nat} {A A' f : V} {B B' : V → V}
    (hv : v ≠ 0) (hv' : v' ≠ 0)
    (h1 : f ∈ˢ piR v A B) (h2 : f ∈ˢ piR v' A' B') : A = A' := by
  rw [piR_pos hv] at h1
  rw [piR_pos hv'] at h2
  obtain ⟨hsub, htot⟩ := mem_piSet.mp h1
  obtain ⟨hsub', htot'⟩ := mem_piSet.mp h2
  refine ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, -⟩ := htot x hx
    obtain ⟨x2, hx2, y2, -, hp⟩ := mem_sigmaPairs.mp (hsub' _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact hx2
  · obtain ⟨y, hy, -⟩ := htot' x hx
    obtain ⟨x2, hx2, y2, -, hp⟩ := mem_sigmaPairs.mp (hsub _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact hx2

/-! ## The truth-value regime -/

/-- **Impredicativity.**  A product landing in `Prop` is a truth value
— for an arbitrary domain `A` and arbitrary fibres, with no size
condition.  This is the one place a set-theoretic model of Lean has to
say something, and here it is the `v = 0` branch of a numeral test. -/
theorem piR_zero_mem_univZero {A : V} {B : V → V} :
    piR 0 A B ∈ˢ (univZero : V) := by
  rw [piR_zero]; exact truthVal_mem_univZero _

/-- Members of a truth value are all equal: the `v = 0` regime is
subsingleton-valued. -/
theorem subsingleton_of_mem_univZero {T x y : V} (hT : T ∈ˢ (univZero : V))
    (hx : x ∈ˢ T) (hy : y ∈ˢ T) : x = y :=
  (eq_pt_of_mem_univZero hT hx).trans (eq_pt_of_mem_univZero hT hy).symm

/-- Proof irrelevance for the squash regime, in subsingleton form. -/
theorem piR_zero_subsingleton {A x y : V} {B : V → V}
    (hx : x ∈ˢ piR 0 A B) (hy : y ∈ˢ piR 0 A B) : x = y :=
  (eq_pt_of_mem_piR_zero hx).trans (eq_pt_of_mem_piR_zero hy).symm

/-- The empty-domain product is truth — in the graph regime too, where
it is the singleton `{∅}` of the empty graph rather than a collapsed
point.  (Contrast `piC_empty`, where *every* empty-domain product is
`unitSet` and *every* empty-domain abstraction collapses to `pt` — the
countermodel that blocked the #100 flip.) -/
theorem piR_pos_empty {v : Nat} (hv : v ≠ 0) (B : V → V) :
    piR v (empty : V) B = sing (empty : V) := by
  rw [piR_pos hv]
  refine ext fun f => ?_
  rw [mem_sing, mem_piSet]
  constructor
  · rintro ⟨hsub, -⟩
    refine eq_empty fun z hz => ?_
    obtain ⟨x, hx, -⟩ := mem_sigmaPairs.mp (hsub z hz)
    exact not_mem_empty x hx
  · rintro rfl
    exact ⟨fun z hz => absurd hz (not_mem_empty z),
      fun x hx => absurd hx (not_mem_empty x)⟩

/-- Empty-domain abstraction in the graph regime is the empty graph,
**not** the proof point: the annotation, not the (vacuous) value test,
decides.  This is exactly the clause whose collapse analogue
(`lamC_empty`) produced the #100 countermodel. -/
theorem lamR_pos_empty {v : Nat} (hv : v ≠ 0) (F : V → V) :
    lamR v (empty : V) F = (empty : V) := by
  rw [lamR_pos hv]
  refine eq_empty fun z hz => ?_
  obtain ⟨x, hx, -⟩ := mem_graph.mp hz
  exact not_mem_empty x hx

end ConLeche.SetModel
