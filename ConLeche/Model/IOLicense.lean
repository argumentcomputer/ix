module

public import ConLeche.SetModel.Ops

public section

/-!
# The io license kit (task #161 stage 2, the io-license batch)

The graph-regime license for the io lane's skipped argument check, and
the squash-regime refutation that fences it — promoted verbatim from
the round-D feasibility study (`agent/inferonly-study` @ `17e943d0`,
probes in `_tmp/inferonly-study/ProbeIO.lean`) to stand beside their
consumer, the io app clause (`Steps/InferIO.lean`).  These four
theorems are the *entire* new mathematics of verified infer-only:

* **The license** (`io_domain_transfer`, `io_app_mem`) — the fact an
  inferOnly-grade app clause skips is `⟦a⟧ ∈ ⟦Aa⟧` for the *computed*
  function type's domain.  `WellDenoted`'s app slot carries
  `⟦f⟧ ∈ piR v A B ∧ ⟦a⟧ ∈ A` for an *existential* domain; the license
  shows the existential fact transfers to ANY computed product whose
  regime numeral is nonzero — `piR_dom_unique` is unconditional there:
  **no** `≠ pt` side condition, **no** domain-nonemptiness premise,
  **no** freshness premise.  The #100 empty-domain countermodel
  `(fun (x : ∀ p : Prop, p) => Prop) Prop` does not touch it: the
  empty graph pins its domain to `∅` and the transfer is vacuous
  truth, while the term itself can never carry the `WellDenoted` app
  slot (its argument is not a member of the empty domain).

* **The fence** (`io_squash_no_transfer`,
  `io_membership_fails_at_squash`) — the license's boundary stated as
  a theorem, the way `gate_zero_kind_unreachable` (`Steps/Gate.lean`)
  fences the β-gate.  At `v' = 0` the premise package does NOT pin the
  domain (both products are truth values inhabited by `pt`) and the
  io-membership conclusion is outright **false** on a closed witness:
  all premises of the premise-form io app claim hold while
  `app ⟦f⟧ ⟦a⟧ ∉ ⟦B'⟧ ⟦a⟧`.  Truth values do not remember domains, so
  **no** proof-irrelevant set model can license official's full
  inferOnly — this is the semantic survivor of the #124
  `InferOnlyRefuted` witness `(fun (x : False) => x) 0`
  (spike `inferonly-metatheory`).  Consequence, binding: a verified
  infer-only mode must KEEP the per-argument check at binders whose
  validated `pw` can be zero, and may skip it exactly at
  `pw = .never` (where `pwBit φ .never = 1 ≠ 0` at every valuation —
  `isNever_iff_forall_pwBit_ne_zero`, `Annot/Bit.lean`).
  `pw = .never` is the whole licensed fragment, forever.

The consumer map (the B4 handoff): `inferBodyIO`'s one gated site
(`Kernel/CoreIO.lean`, the `unless mt.pw.isNever` test wrapping the
argument certificate — the datum alone since the licence ruling of
2026-09-06) is discharged by
`io_app_mem` + `pwBit_ne_zero_of_isNever` in the io app clause's gated
branch; the kept branch (the certificate ran) needs no license.  No
other skip site exists — the io grade narrows the application clause
and nothing else.
-/

namespace ConLeche.Model
open ConLeche.SetModel

open SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The graph-regime license -/

/-- **The io domain transfer.**  If the subject's hereditary app slot
holds (`f` in *some* product with `a` in its domain) and the io-run
derives `f ∈ piR v' A' B'` at a nonzero regime numeral, then `a` lies
in the computed domain `A'` — the fact the skipped per-argument
`infer + defeq` used to supply.  No freshness, no nonemptiness, no
`≠ pt` side condition: the annotation decided the regime, and in the
graph regime membership is graph-hood (`mem_piR_pos`), so domains are
determined (`piR_dom_unique`). -/
theorem io_domain_transfer {v v' : Nat} {A A' f a : V} {B B' : V → V}
    (hv' : v' ≠ 0)
    (hf : f ∈ˢ piR v A B) (ha : a ∈ˢ A)
    (hf' : f ∈ˢ piR v' A' B') : a ∈ˢ A' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · exact absurd (eq_pt_of_mem_piR_zero hf ▸ hf') (not_pt_mem_piR_pos hv')
  · rwa [piR_dom_unique (Nat.pos_iff_ne_zero.mp hv) hv' hf hf'] at ha

/-- The membership conclusion the io app clause owes, recovered at the
graph regime from the hereditary slot alone — `app_mem_piR_pos`
composed with the transfer.  This is the whole soundness content of
skipping the argument check at a `pw = .never` binder. -/
theorem io_app_mem {v v' : Nat} {A A' f a : V} {B B' : V → V}
    (hv' : v' ≠ 0)
    (hf : f ∈ˢ piR v A B) (ha : a ∈ˢ A)
    (hf' : f ∈ˢ piR v' A' B') : app f a ∈ˢ B' a :=
  app_mem_piR_pos hv' hf' (io_domain_transfer hv' hf ha hf')

/-! ## The squash-regime fence (the #124 witness's survivor) -/

/-- **No transfer at the squash regime.**  The full premise package of
a premise-form io app claim is satisfiable with the argument OUTSIDE
the computed domain: `f := pt` inhabits both `piR 0 (truthVal True) B`
(the slot's product, domain inhabited by `a := pt`) and
`piR 0 ∅ B'` (the computed product — vacuously true, so its truth
value contains `pt`), while `a ∉ ∅`.  Truth values do not remember
domains. -/
theorem io_squash_no_transfer :
    ∃ (A A' f a : V) (B B' : V → V),
      f ∈ˢ piR 0 A B ∧ a ∈ˢ A ∧
      (∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) ∧
      f ∈ˢ piR 0 A' B' ∧ ¬ a ∈ˢ A' := by
  refine ⟨truthVal True, empty, pt, pt,
    fun _ => truthVal True, fun _ => empty, ?_, ?_, ?_, ?_, ?_⟩
  · exact pt_mem_piR_zero_of fun _ _ => pt_mem_truthVal trivial
  · exact pt_mem_truthVal trivial
  · exact fun _ _ => truthVal_mem_univZero True
  · exact pt_mem_piR_zero fun x hx => absurd hx (not_mem_empty x)
  · exact not_mem_empty pt

/-- **The io membership conclusion is FALSE at the squash regime**, on
the same witness: every premise of the premise-form io app claim
holds and `app f a ∉ B' a`.  So the argument check cannot be skipped
at a binder whose codomain bit can be `0` — the carve-out is forced,
not chosen. -/
theorem io_membership_fails_at_squash :
    ∃ (A A' f a : V) (B B' : V → V),
      f ∈ˢ piR 0 A B ∧ a ∈ˢ A ∧
      (∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) ∧
      f ∈ˢ piR 0 A' B' ∧
      (∀ x, x ∈ˢ A' → B' x ∈ˢ (univZero : V)) ∧
      ¬ app f a ∈ˢ B' a := by
  refine ⟨truthVal True, empty, pt, pt,
    fun _ => truthVal True, fun _ => empty, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pt_mem_piR_zero_of fun _ _ => pt_mem_truthVal trivial
  · exact pt_mem_truthVal trivial
  · exact fun _ _ => truthVal_mem_univZero True
  · exact pt_mem_piR_zero fun x hx => absurd hx (not_mem_empty x)
  · exact fun x hx => absurd hx (not_mem_empty x)
  · rw [app_pt]
    exact not_mem_empty pt

end ConLeche.Model
