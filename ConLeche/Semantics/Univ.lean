module

public import ConLeche.Semantics.Kit

@[expose] public section

/-!
# The universe question, in the `pt`-free world (task #151, tier B)

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161: the
module already imported nothing but base, and the graded lane needs it.
Path and module name changed; namespaces, statements and proofs
verbatim.)*


The record's version of the question was: *`pt ∈ univ (u+1)` was forced
— the collapse puts the proof point into `Type`-level function spaces
(`lamC` collapses at every level), so every universe has to contain it,
and a non-transitive universe chain was parked as the escape.*

Under `interp` the question **transforms**, because there is no
collapse and hence no `pt` in the positive regime.  The transformed
question and its answer:

> Do `interp`'s universes contain values that break the graph
> inversion at universe-codomain products — i.e. can something the
> `SetTheory` universe tower happens to contain sneak into
> `⟦(x : A) → Sort k⟧` without being a graph?

**No, and the reason is structural rather than arithmetic.**
`piR v A B` at `v ≠ 0` is `piSet A B`, which is *carved out by
separation*: `f ∈ piSet A B` **iff** `f ⊆ sigmaPairs A B` and `f` is
total and single-valued on `A` (`mem_piR_pos_iff` below).  That is a
property of `f`, quantified over `f`'s own members.  Nothing about `B`,
about universe transitivity, or about what a universe contains can add
a member to it: universe transitivity says members of members of `U`
are in `U`, which enlarges `U`, never `piSet A B`.  So
`interp_mem_pi_pos` holds at universe-valued fibres exactly as it does
anywhere else (`interp_univ_cod_inversion` is the instance, proved by
the general lemma with no extra hypothesis).

**Verdict on the parked contingency.**  The non-transitive-chain
re-choice is **not needed** — indeed there is nothing left for it to
fix.  What forced `pt ∈ univ (u+1)` was that a `Type`-level abstraction
could *be* `pt`; here `lamR_ne_pt` says it never is, and
`not_pt_mem_piR_pos` says the proof point inhabits no graph-regime
product at all.  Both `ConLeche/SetTheory/Core.lean`'s transitivity
clause and the ω-chain stay exactly as they are; this layer imposes no
new demand on them.  This is a **negative finding**: the contingency is
closed, not deferred.

Two further facts fall out and are proved below:

* **The formation law is the `imax` rule, exactly** (`piR_mem_univ`),
  and it is *sharp*: a graph-regime product with inhabited fibres is
  never a truth value (`piR_pos_not_mem_univZero`).  Under the collapse
  only the weaker `piC_mem_univ_max` "may land smaller" is available,
  because a `Type`-level product *can* collapse into `Prop`.
* **The collapse's universe cohabitation is exactly the empty-domain
  case** (`pt_mem_piC_univZero_iff`): `pt ∈ˢ piC A (fun _ => univ 0)`
  holds **iff** `A = ∅` — the proof point is not in `univ 0` at all
  (`pt_not_mem_univZero`).  So the wall the eta-law derivation dodged
  is precisely the unknown-empty domain, and it is gone here: `piR v ∅ B = {∅}`, which does not
  contain `pt`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## Formation along the tower -/

/-- **The `imax` rule, exactly.**  `Prop`-valued products land in
`univ 0` whatever their domain (impredicativity); above `0` they land
at `max u v`.  Contrast `piC_mem_univ`, which states the same bound but
cannot be sharp: a collapsed `Type`-level product may land *lower* than
its annotation, which is what `piC_mem_univ_max` has to paper over. -/
theorem piR_mem_univ {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    piR v A B ∈ˢ (univ (if v = 0 then 0 else Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [if_pos rfl, univ_zero]
    exact piR_zero_mem_univZero
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    have hw : (Nat.max u v : Nat) ≠ 0 :=
      fun h => hv' (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))
    rw [if_neg hv', piR_pos hv']
    exact (univ_isTGUniverse hw).piSet_mem
      (univ_mono (Nat.le_max_left u v) A hA)
      (fun x hx => univ_mono (Nat.le_max_right u v) _ (hB x hx))

open Classical in
/-- Sharpness of the regime split: a graph-regime product whose fibres
are all inhabited is **not** a truth value.  So the annotation is not
merely an upper bound on where the value lands — the two regimes are
genuinely disjoint, and a `Type`-level product never sneaks into
`Prop`. -/
theorem piR_pos_not_mem_univZero {v : Nat} (hv : v ≠ 0) {A : V} {B : V → V}
    (hinh : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) : ¬ piR v A B ∈ˢ (univZero : V) := by
  intro h
  have hchoice : ∃ F : V → V, ∀ x, x ∈ˢ A → F x ∈ˢ B x :=
    ⟨fun x => if hx : x ∈ˢ A then Classical.choose (hinh x hx) else empty,
     fun x hx => by
       show (if h : x ∈ˢ A then Classical.choose (hinh x h) else empty) ∈ˢ B x
       rw [dif_pos hx]
       exact Classical.choose_spec (hinh x hx)⟩
  obtain ⟨F, hF⟩ := hchoice
  have hg : graph F A ∈ˢ piR v A B := by
    rw [piR_pos hv]; exact graph_mem_piSet hF
  exact graph_ne_pt (eq_pt_of_mem_univZero h hg)

/-! ## The inversion is fibre-blind -/

/-- Membership in a graph-regime product **is** graph-hood: separation
from `power (sigmaPairs A B)`, a property of `f`'s own members.  This
is the formal content of "nothing a universe contains can break the
inversion". -/
theorem mem_piR_pos_iff {v : Nat} (hv : v ≠ 0) {A f : V} {B : V → V} :
    f ∈ˢ piR v A B ↔ f ⊆ˢ sigmaPairs A B ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  rw [piR_pos hv]; exact mem_piSet

/-- The universe-codomain instance of the inversion: a member of
`⟦(x : A) → Sort k⟧` is a graph over `⟦A⟧` landing pointwise in
`univ k`.  Proved by the general lemma — *there is no extra
hypothesis*, which is the whole answer to the universe question. -/
theorem interp_univ_cod_inversion (V : Type w) [SetTheory V] {v : Nat}
    (hv : v ≠ 0) {u k : Nat} {ρ : Nat → V} {A : AnnotTerm} {f : V}
    (hf : f ∈ˢ interp V ρ (.pi u v A (.sort k))) :
    graph (fun x => SetTheory.app f x) (interp V ρ A) = f ∧
    (∀ x, x ∈ˢ interp V ρ A → SetTheory.app f x ∈ˢ (univ k : V)) ∧
    (∀ a, ¬ a ∈ˢ interp V ρ A → SetTheory.app f a = empty) ∧
    f ≠ pt :=
  interp_mem_pi_pos V hv hf

/-! ## What the collapse's cohabitation actually was -/

/-- The proof point is **not** a truth value: `pt = {ptTag}` and
`ptTag ≠ pt`, so `pt ⊄ unitSet`. -/
theorem pt_not_mem_univZero : ¬ (pt : V) ∈ˢ univZero := by
  intro h
  have h1 : (ptTag : V) ∈ˢ unitSet := mem_univZero.mp h ptTag ptTag_mem_pt
  have h2 : (ptTag : V) = pt := mem_unitSet_iff.mp h1
  have h3 : (pt : V) ∈ˢ pt := mem_pt.mpr h2.symm
  exact not_mem_self (pt : V) h3

/-- …and in the two-regime world it cannot happen even there: the
empty-domain graph-regime product is `{∅}`, whose only member is the
empty graph. -/
theorem not_pt_mem_piR_empty {v : Nat} (hv : v ≠ 0) (B : V → V) :
    ¬ (pt : V) ∈ˢ piR v (empty : V) B := not_pt_mem_piR_pos hv

/-! ## Placement of the sorts themselves -/

theorem interp_sort_mem (V : Type w) [SetTheory V] (ρ : Nat → V) (n : Nat) :
    interp V ρ (.sort n) ∈ˢ interp V ρ (.sort (n + 1)) := univ_mem_univ n

end ConLeche.Semantics
