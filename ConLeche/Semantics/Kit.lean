module

public import ConLeche.Semantics.Interp
public import ConLeche.Verify.Denote.VClosed

@[expose] public section

/-!
# The `interp` lemma kit (task #151, tier B)

Two halves.

**The substitution stack** — `interp_liftN` and `interp_inst`, the
layer's *entire* substitution metatheory, transposed from
`ConLeche/Term/Semantics/Interp.lean` unchanged in shape.  That they
transpose is the point: `interp` is structural, so removing the
collapse costs nothing here.  (lean4lean needs ~123 syntactic lemmas at
this spot because its metatheory is syntactic; soundness against a
model needs two semantic ones.)

**The regime lemmas** — what the two-regime design is *for*:

* `interp_mem_pi_pos` — the graph-regime inversion.  A member of
  `⟦(x : A) → B⟧` with the codomain sort nonzero **is** a graph, with
  domain exactly `⟦A⟧`, pointwise-fibred, non-`pt`, and canonical `∅`
  off the domain.  By definition, not by dispatch.
* `interp_beta_pos` / `interp_app_graph` — on-domain application
  computes, with no typing premise at all.
* `interp_pi_zero_subsingleton`, `interp_proof_irrel` — the squash
  regime is subsingleton-valued.
* `interp_pi_zero_small` — **impredicativity**: a product landing in
  `Prop` is a truth value, for an arbitrary domain.
* `interp_not_pt_mem_pi_pos`, `interp_app_off_dom` — junk-freeness:
  the proof point never inhabits a graph-regime product, and off-domain
  application is the canonical `∅`, never a point a consumer must
  dispatch on.

On `pt`: the only occurrences in this file are in *conclusions about
the squash regime* (`interp V ρ .prf = pt` and the `v = 0`
subsingleton facts) and in the *negative* junk-freeness statements.  No
lemma here has a `pt` hypothesis, no proof does a case split on whether
a value is `pt`, and the graph regime never mentions it except to deny
it.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## The substitution stack -/

theorem interp_liftN (n : Nat) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V),
      interp V ρ (e.liftN n k) = interp V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [AnnotTerm.liftN_bvar, interp_bvar, shiftE]
    split <;> rfl
  | sort u => intro k ρ; rfl
  | const c us => intro k ρ; rfl
  | app f a ihf iha =>
    intro k ρ; simp only [AnnotTerm.liftN_app, interp_app, ihf, iha]
  | lam v A b ihA ihb =>
    intro k ρ
    simp only [AnnotTerm.liftN_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, cons_shiftE]
  | pi u v A B ihA ihB =>
    intro k ρ
    simp only [AnnotTerm.liftN_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, cons_shiftE]
  | eqE a b iha ihb =>
    intro k ρ; simp only [AnnotTerm.liftN_eqE, interp_eqE, iha, ihb]
  | fst e ihe =>
    intro k ρ; simp only [AnnotTerm.liftN_fst, interp_fst, ihe]
  | snd e ihe =>
    intro k ρ; simp only [AnnotTerm.liftN_snd, interp_snd, ihe]
  | prf => intro k ρ; rfl

theorem interp_lift (e : AnnotTerm) (ρ : Nat → V) :
    interp V ρ e.lift = interp V (fun i => ρ (i + 1)) e := by
  rw [AnnotTerm.lift, interp_liftN, shiftE_zero]

theorem interp_lift_cons (e : AnnotTerm) (x : V) (ρ : Nat → V) :
    interp V (cons x ρ) e.lift = interp V ρ e := by
  rw [interp_lift]; rfl

theorem interp_inst :
    ∀ (e a : AnnotTerm) (k : Nat) (ρ : Nat → V),
      interp V ρ (e.inst a k) =
        interp V (instE k (interp V (shiftE k 0 ρ) a) ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ
    show interp V ρ
        (if i < k then .bvar i
         else if i = k then AnnotTerm.liftN k a else .bvar (i - 1)) =
      instE k (interp V (shiftE k 0 ρ) a) ρ i
    by_cases h : i < k
    · simp only [if_pos h, instE]; rfl
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, instE]
        exact interp_liftN V k a 0 ρ
      · simp only [if_neg h, if_neg h2, instE]; rfl
  | sort u => intro a k ρ; rfl
  | const c us => intro a k ρ; rfl
  | app f b ihf ihb =>
    intro a k ρ; simp only [AnnotTerm.inst_app, interp_app, ihf, ihb]
  | lam v A b ihA ihb =>
    intro a k ρ
    simp only [AnnotTerm.inst_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, shiftE_succ_cons, cons_instE]
  | pi u v A B ihA ihB =>
    intro a k ρ
    simp only [AnnotTerm.inst_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, shiftE_succ_cons, cons_instE]
  | eqE b c ihb ihc =>
    intro a k ρ; simp only [AnnotTerm.inst_eqE, interp_eqE, ihb, ihc]
  | fst e ihe =>
    intro a k ρ; simp only [AnnotTerm.inst_fst, interp_fst, ihe]
  | snd e ihe =>
    intro a k ρ; simp only [AnnotTerm.inst_snd, interp_snd, ihe]
  | prf => intro a k ρ; rfl

/-! ### Interpretation invariance below a bound

`interp_congr_below`/`interp_closed`'s analogue
(`ConLeche/SetR/AnnotOkV.lean`): a closed term's interpretation does not
read the environment.  Stated through the **erasure's** bound rather
than a fresh `AnnotTerm.bvarsBelow`: `erase` maps `bvar i` to `bvar i` and
preserves every former's shape, so `Term.bvarsBelow k e.erase` says
exactly "`e`'s indices are below `k`", and no new predicate is needed.

Needed by the literal clauses of any `Claims2` discharge: the `Nat`/
`String` blocks of `Sound/{Lit,NatOps,NatOpsWf}.lean` touch the
interpretation only through `interp_app`, `interp_bvar`, `interp_sort`,
`interp_pi` and `interp_closed`, and this was the one of the five with
no `interp` analogue. -/

theorem interp_congr_below :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      ConLeche.Term.Term.bvarsBelow k e.erase →
      (∀ i, i < k → ρ i = ρ' i) →
      interp V ρ e = interp V ρ' e := by
  intro e
  induction e with
  | bvar i => intro k ρ ρ' hb hag; exact hag i hb
  | sort u => intros; rfl
  | const c us => intros; rfl
  | prf => intros; rfl
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    simp only [interp_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_lam, ihA k ρ ρ' hb.1 hag]
    refine lamR_congr fun x _ => ihb (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    simp only [interp_pi, ihA k ρ ρ' hb.1 hag]
    refine piR_congr fun x _ => ihB (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_eqE, iha k ρ ρ' hb.1 hag,
      ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    simp only [interp_fst, ihe k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    simp only [interp_snd, ihe k ρ ρ' hb hag]

/-- A closed term interprets the same under every environment. -/
theorem interp_closed {e : AnnotTerm}
    (he : ConLeche.Term.Term.bvarsBelow 0 e.erase) (ρ ρ' : Nat → V) :
    interp V ρ e = interp V ρ' e :=
  interp_congr_below V e 0 ρ ρ' he
    (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- Substitution at the outermost binder — the form every rule uses. -/
theorem interp_inst0 (e a : AnnotTerm) (ρ : Nat → V) :
    interp V ρ (e.inst a) = interp V (cons (interp V ρ a) ρ) e := by
  rw [interp_inst, shiftE_zero_zero, instE_zero]

theorem interp_mkAppN (ρ : Nat → V) :
    ∀ (as : List AnnotTerm) (f : AnnotTerm),
      interp V ρ (AnnotTerm.mkAppN f as) =
        as.foldl (fun r a => SetTheory.app r (interp V ρ a)) (interp V ρ f)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.foldl_cons]
    rw [interp_mkAppN ρ as (.app f a)]
    rfl

/-! ## The graph regime

Everything below is stated at the interpretation, where the annotation
is visible on the term.  Nothing inspects a value. -/

/-- **The graph-regime inversion** — the prized one.  If the codomain
annotation of a product is nonzero, every member of its interpretation
is a genuine function graph: it *is* the graph of its own application
over `⟦A⟧` (so its domain is exactly `⟦A⟧`), its applications land in
the fibres pointwise, it applies to the canonical junk `∅` off the
domain, and it is not the proof point.

All four clauses hold **by definition** of the positive regime — no
case split, no `mem_piC_cases`, and in particular nothing about what
the fibres `⟦B⟧` are: `interp_univ_cod_inversion`
(`Interp/Univ.lean`) is this lemma at universe-valued fibres. -/
theorem interp_mem_pi_pos {v : Nat} (hv : v ≠ 0) {u : Nat} {ρ : Nat → V}
    {A B : AnnotTerm} {f : V} (hf : f ∈ˢ interp V ρ (.pi u v A B)) :
    graph (fun x => SetTheory.app f x) (interp V ρ A) = f ∧
    (∀ x, x ∈ˢ interp V ρ A →
      SetTheory.app f x ∈ˢ interp V (cons x ρ) B) ∧
    (∀ a, ¬ a ∈ˢ interp V ρ A → SetTheory.app f a = empty) ∧
    f ≠ pt :=
  mem_piR_pos hv hf

/-- **Application is graph application.**  On the domain, the value
`app f a` is literally the second component of the pair that `f`, as a
set, contains at `a` — there is no tag, no fallback and no dispatch in
the graph regime. -/
theorem interp_app_graph {v : Nat} (hv : v ≠ 0) {u : Nat} {ρ : Nat → V}
    {A B : AnnotTerm} {f a : V} (hf : f ∈ˢ interp V ρ (.pi u v A B))
    (ha : a ∈ˢ interp V ρ A) :
    kpair a (SetTheory.app f a) ∈ˢ f := by
  have hg := (interp_mem_pi_pos V hv hf).1
  have h1 : kpair a (SetTheory.app f a) ∈ˢ
      graph (fun x => SetTheory.app f x) (interp V ρ A) :=
    mem_graph.mpr ⟨a, ha, rfl⟩
  rwa [hg] at h1

/-- **β in the graph regime**, with *no* typing premise beyond the
argument inhabiting the domain.  Under the collapse this needs the
kernel's annotation gates; here it is `app_graph`. -/
theorem interp_beta_pos {v : Nat} (hv : v ≠ 0) (ρ : Nat → V)
    (A b a : AnnotTerm) (ha : interp V ρ a ∈ˢ interp V ρ A) :
    interp V ρ (.app (.lam v A b) a) = interp V ρ (b.inst a) := by
  rw [interp_app, interp_lam, interp_inst0, app_lamR_pos hv ha]

/-- β in the squash regime: both sides are the canonical proof as soon
as the body's fibres are truth values — the premise a `Prop`-valued
codomain supplies. -/
theorem interp_beta_zero (ρ : Nat → V) (A b a : AnnotTerm) {B : V → V}
    (ha : interp V ρ a ∈ˢ interp V ρ A)
    (hbody : ∀ x, x ∈ˢ interp V ρ A → interp V (cons x ρ) b ∈ˢ B x)
    (hB : ∀ x, x ∈ˢ interp V ρ A → B x ∈ˢ (univZero : V)) :
    interp V ρ (.app (.lam 0 A b) a) = interp V ρ (b.inst a) := by
  rw [interp_app, interp_lam, interp_inst0]
  exact app_lamR ha hbody (fun _ => hB)

/-! ## Junk-freeness: there is no proof point in the graph regime -/

/-- **The proof point never inhabits a graph-regime product.**
Unconditional in the domain and in the fibres — in particular at
universe-valued codomains, where the collapse's
`pt ∈ˢ piC A (fun _ => univ 0)` was the wall that the eta-law
derivation had to dodge. -/
theorem interp_not_pt_mem_pi_pos {v : Nat} (hv : v ≠ 0) {u : Nat}
    {ρ : Nat → V} {A B : AnnotTerm} :
    ¬ (pt : V) ∈ˢ interp V ρ (.pi u v A B) :=
  not_pt_mem_piR_pos hv

/-- Off-domain application of a graph-regime member is the canonical
junk `∅`, never a point: no junk-point is needed, and off-domain
behaviour is *canonical*, so on-domain agreement is total agreement
(`interp_pi_ext`). -/
theorem interp_app_off_dom {v : Nat} (hv : v ≠ 0) {u : Nat} {ρ : Nat → V}
    {A B : AnnotTerm} {f a : V} (hf : f ∈ˢ interp V ρ (.pi u v A B))
    (ha : ¬ a ∈ˢ interp V ρ A) : SetTheory.app f a = empty :=
  app_off_dom_piR_pos hv hf ha

/-- Function extensionality at a product: on-domain agreement is
equality.  (Holds in both regimes — at `v = 0` both sides are the
canonical proof.) -/
theorem interp_pi_ext {v u : Nat} {ρ : Nat → V} {A B B' : AnnotTerm} {f g : V}
    (hf : f ∈ˢ interp V ρ (.pi u v A B))
    (hg : g ∈ˢ interp V ρ (.pi u v A B'))
    (h : ∀ x, x ∈ˢ interp V ρ A →
      SetTheory.app f x = SetTheory.app g x) : f = g :=
  eq_of_mem_piR_app_eq hf hg h

/-! ## The squash regime -/

/-- **Impredicativity.**  A product whose codomain annotation is `0` is
a truth value — whatever its domain is, and with no premise on the
fibres.  This is the whole content of `Prop`'s impredicativity in the
model, and here it is one branch of a numeral test. -/
theorem interp_pi_zero_small {u : Nat} (ρ : Nat → V) (A B : AnnotTerm) :
    interp V ρ (.pi u 0 A B) ∈ˢ (univ 0 : V) := by
  rw [interp_pi, univ_zero]
  exact piR_zero_mem_univZero

/-- Proof irrelevance at a `Prop`-valued product: any two inhabitants
are equal. -/
theorem interp_pi_zero_subsingleton {u : Nat} {ρ : Nat → V} {A B : AnnotTerm}
    {x y : V} (hx : x ∈ˢ interp V ρ (.pi u 0 A B))
    (hy : y ∈ˢ interp V ρ (.pi u 0 A B)) : x = y :=
  piR_zero_subsingleton hx hy

/-- Proof irrelevance, in the form consumers use it: members of a
proposition — anything the interpretation places in `univ 0` — are all
equal, and all equal to the canonical proof `⟦prf⟧`. -/
theorem interp_proof_irrel {ρ : Nat → V} {T : AnnotTerm} {x y : V}
    (hT : interp V ρ T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ interp V ρ T)
    (hy : y ∈ˢ interp V ρ T) : x = y :=
  subsingleton_of_mem_univZero (univ_zero (V := V) ▸ hT) hx hy

end ConLeche.Semantics
