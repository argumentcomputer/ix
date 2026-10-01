module

public import ConLeche.Semantics.Kit
import ConLeche.SetTheory.Derive.Sigma
@[expose] public section

/-!
# `WellDenoted`: kinded hereditary truthfulness over `interp` (task #151 tier C)

The second soundness's invariant — `AnnotOkV`'s clause-for-clause
transpose onto the annotated syntax and the two-regime interpretation,
with the two upgrades the removal campaign stands on — each an interface
change a consumer forced, not a convenience:

* **the application slot carries the product kind** —
  `∃ v A B, ⟦f⟧ ∈ piR v A B ∧ ⟦a⟧ ∈ A ∧ (v = 0 → fibres are truth
  values)` — so at a provably-positive kind the membership *pins* the
  domain (`piR_dom_unique`, no side condition) and the runtime argument
  re-check becomes derivable;
* **the λ clause carries the fibre package at the node's own
  annotation** — `∃ B, (∀ x ∈ ⟦A⟧, ⟦b⟧ ∈ B x) ∧ (v = 0 → fibres are
  truth values)` — the semantic content of `Annotates.lam`'s cached
  codomain sort, and what `graded_beta_pos` consumes.

Being a **semantic** predicate on the annotated term, `WellDenoted`
transports across reduction the way `AnnotOkV` does — the finding-A2
constraint (annotations do not cross `Red`) binds derivation-backed
relations, not this invariant.

The substitution metatheory is the `AnnotOkV` pair, verbatim modulo
`interp → interp` and the two extra clause components (which only
mention `interp` of the clause's own subterms, so they ride the same
rewrites).

## The app clause's kind-`0` amendment (the consumer seal)

The app slot first landed **without** its kind-`0` fibre component,
while the λ clause carried the identically-shaped one.  The asymmetry
was a gap, not a saving: `app_mem_piR` (`SetModel/Ops.lean`) needs
exactly `v = 0 → ∀ x ∈ˢ A, B x ∈ˢ univZero` to conclude
`app ⟦f⟧ ⟦a⟧ ∈ˢ B ⟦a⟧`, the slot's `B` is existentially bound so no
handle on it survives extraction, and the truth-value route does not
substitute: an inhabited `piR 0 A B` gives only that `B ⟦a⟧` is
*inhabited*, never that its inhabitant is `pt` (finding B5's wall, in
the membership formulation).  So at kind `0` the app case could not
close from the invariant at all.

`graded_beta_pos` and `WellDenoted_beta_pos` never saw it because they
require positivity, and `WellDenoted_beta_zero` takes the missing fact as
an explicit `hmem` — which is why the gap survived three consumers.

**Established, not assumed**: `appSlot_of_pi` / `WellDenoted_app_of`
below build the slot — new component included — from the *annotated*
`Π`'s own codomain sort fact, whose supplier is `HasSort.mem_univ`
(`Annot/Kinding.lean`) at the `Π`'s numeral, the same route the λ
clause's component already takes.  The two binder clauses are
symmetric again.

**Consumers of the strengthened clause**, all re-proved at this seal:
`WellDenoted_liftN` / `WellDenoted_inst` (the component mentions only the
∃-bound `v`, `A`, `B`, so it is invariant under the environment change
and rides the existing rewrites); `WellDenoted_beta_pos` and
`WellDenoted_beta_zero` (destructuring only); and, in `Annot/Spine2.lean`,
`SlotChain` — strengthened in step so `AnnotOk2_spine_slots` still
reads the slot off unchanged, with `slotChain_fits` carrying and
dropping the new component (it uses positivity only).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable (V : Type w) [SetTheory V]

/-- Kinded hereditary truthfulness of the binder/application structure
under a variable environment (see the module docstring). -/
def WellDenoted : (Nat → V) → AnnotTerm → Prop
  | ρ, .pi _u _v A B =>
    WellDenoted ρ A ∧
    ∀ x, x ∈ˢ interp V ρ A → WellDenoted (cons x ρ) B
  | ρ, .lam v A b =>
    WellDenoted ρ A ∧
    (∀ x, x ∈ˢ interp V ρ A → WellDenoted (cons x ρ) b) ∧
    ∃ B : V → V,
      (∀ x, x ∈ˢ interp V ρ A → interp V (cons x ρ) b ∈ˢ B x) ∧
      (v = 0 → ∀ x, x ∈ˢ interp V ρ A → B x ∈ˢ (univZero : V))
  | ρ, .app f a =>
    WellDenoted ρ f ∧ WellDenoted ρ a ∧
    ∃ (v : Nat) (A : V) (B : V → V),
      interp V ρ f ∈ˢ piR v A B ∧ interp V ρ a ∈ˢ A ∧
      (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))
  | ρ, .fst e =>
    WellDenoted ρ e ∧
    ∃ u v A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | ρ, .snd e =>
    WellDenoted ρ e ∧
    ∃ u v A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | ρ, .eqE a b => WellDenoted ρ a ∧ WellDenoted ρ b
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | _, .prf => True

/-! ### Clause equations -/

@[simp] theorem WellDenoted_bvar (ρ : Nat → V) (i : Nat) :
    WellDenoted V ρ (.bvar i) = True := by rw [WellDenoted]
@[simp] theorem WellDenoted_sort (ρ : Nat → V) (u : Nat) :
    WellDenoted V ρ (.sort u) = True := by rw [WellDenoted]
@[simp] theorem WellDenoted_const (ρ : Nat → V) (c : ConLeche.Term.BConst)
    (us : List Nat) : WellDenoted V ρ (.const c us) = True := by
  rw [WellDenoted]
@[simp] theorem WellDenoted_prf (ρ : Nat → V) :
    WellDenoted V ρ .prf = True := by rw [WellDenoted]
theorem WellDenoted_pi (ρ : Nat → V) (u v : Nat) (A B : AnnotTerm) :
    WellDenoted V ρ (.pi u v A B) =
      (WellDenoted V ρ A ∧
        ∀ x, x ∈ˢ interp V ρ A → WellDenoted V (cons x ρ) B) := by
  rw [WellDenoted]
theorem WellDenoted_lam (ρ : Nat → V) (v : Nat) (A b : AnnotTerm) :
    WellDenoted V ρ (.lam v A b) =
      (WellDenoted V ρ A ∧
        (∀ x, x ∈ˢ interp V ρ A → WellDenoted V (cons x ρ) b) ∧
        ∃ B : V → V,
          (∀ x, x ∈ˢ interp V ρ A → interp V (cons x ρ) b ∈ˢ B x) ∧
          (v = 0 → ∀ x, x ∈ˢ interp V ρ A →
            B x ∈ˢ (univZero : V))) := by
  rw [WellDenoted]
theorem WellDenoted_app (ρ : Nat → V) (f a : AnnotTerm) :
    WellDenoted V ρ (.app f a) =
      (WellDenoted V ρ f ∧ WellDenoted V ρ a ∧
        ∃ (v : Nat) (A : V) (B : V → V),
          interp V ρ f ∈ˢ piR v A B ∧ interp V ρ a ∈ˢ A ∧
          (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))) := by
  rw [WellDenoted]
theorem WellDenoted_fst (ρ : Nat → V) (e : AnnotTerm) :
    WellDenoted V ρ (.fst e) =
      (WellDenoted V ρ e ∧
        ∃ u v A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
          A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v) := by
  rw [WellDenoted]
theorem WellDenoted_snd (ρ : Nat → V) (e : AnnotTerm) :
    WellDenoted V ρ (.snd e) =
      (WellDenoted V ρ e ∧
        ∃ u v A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
          A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v) := by
  rw [WellDenoted]
theorem WellDenoted_eqE (ρ : Nat → V) (a b : AnnotTerm) :
    WellDenoted V ρ (.eqE a b) = (WellDenoted V ρ a ∧ WellDenoted V ρ b) := by
  rw [WellDenoted]

/-! ### The substitution metatheory (the `AnnotOkV` pair, transposed) -/

/-- Truthfulness through lifting. -/
theorem WellDenoted_liftN (n : Nat) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V),
      WellDenoted V ρ (e.liftN n k) ↔ WellDenoted V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [AnnotTerm.liftN_bvar]
    split <;> simp
  | sort u => intro k ρ; simp
  | const c us => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [AnnotTerm.liftN_app, WellDenoted_app, WellDenoted_app, ihf, iha,
      interp_liftN, interp_liftN]
  | lam v A b ihA ihb =>
    intro k ρ
    rw [AnnotTerm.liftN_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · rw [ihb, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | pi u v A B ihA ihB =>
    intro k ρ
    rw [AnnotTerm.liftN_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    rw [ihB, cons_shiftE]
  | eqE a b iha ihb =>
    intro k ρ
    rw [AnnotTerm.liftN_eqE, WellDenoted_eqE, WellDenoted_eqE, iha, ihb]
  | fst e ihe =>
    intro k ρ
    rw [AnnotTerm.liftN_fst, WellDenoted_fst, WellDenoted_fst, ihe,
      interp_liftN]
  | snd e ihe =>
    intro k ρ
    rw [AnnotTerm.liftN_snd, WellDenoted_snd, WellDenoted_snd, ihe,
      interp_liftN]
  | prf => intro k ρ; simp

/-- Truthfulness through instantiation. -/
theorem WellDenoted_inst :
    ∀ (e a : AnnotTerm) (k : Nat) (ρ : Nat → V),
      WellDenoted V (shiftE k 0 ρ) a →
      (WellDenoted V ρ (e.inst a k) ↔
        WellDenoted V (instE k (interp V (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    show WellDenoted V ρ
        (if i < k then .bvar i
         else if i = k then AnnotTerm.liftN k a else .bvar (i - 1)) ↔ _
    by_cases h : i < k
    · simp [if_pos h]
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, WellDenoted_bvar, iff_true]
        exact (WellDenoted_liftN V k a 0 ρ).mpr ha
      · simp [if_neg h, if_neg h2]
  | sort u => intro a k ρ _; simp [AnnotTerm.inst]
  | const c us => intro a k ρ _; simp [AnnotTerm.inst]
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [AnnotTerm.inst_app, WellDenoted_app, WellDenoted_app, ihf a k ρ ha,
      ihb a k ρ ha, interp_inst, interp_inst]
  | lam v A b ihA ihb =>
    intro a k ρ ha
    rw [AnnotTerm.inst_lam, WellDenoted_lam, WellDenoted_lam, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · have ha' : WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihb a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · have ha' : WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [interp_inst, shiftE_succ_cons, cons_instE]
  | pi u v A B ihA ihB =>
    intro a k ρ ha
    rw [AnnotTerm.inst_pi, WellDenoted_pi, WellDenoted_pi, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    have ha' : WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihB a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
  | eqE x y ihx ihy =>
    intro a k ρ ha
    rw [AnnotTerm.inst_eqE, WellDenoted_eqE, WellDenoted_eqE, ihx a k ρ ha,
      ihy a k ρ ha]
  | fst e ihe =>
    intro a k ρ ha
    rw [AnnotTerm.inst_fst, WellDenoted_fst, WellDenoted_fst, ihe a k ρ ha,
      interp_inst]
  | snd e ihe =>
    intro a k ρ ha
    rw [AnnotTerm.inst_snd, WellDenoted_snd, WellDenoted_snd, ihe a k ρ ha,
      interp_inst]
  | prf => intro a k ρ _; simp [AnnotTerm.inst]

/-- Substitution at the outermost binder — the β/ζ transport form. -/
theorem WellDenoted_inst0 {e a : AnnotTerm} {ρ : Nat → V}
    (ha : WellDenoted V ρ a) :
    WellDenoted V ρ (e.inst a) ↔
      WellDenoted V (cons (interp V ρ a) ρ) e := by
  have h := WellDenoted_inst V e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-! ### The graded β step, complete

`RedS2`'s β case in both conjuncts, at a provably-positive codomain
kind: the interp-equality *and* the truthfulness transport, from the
subject's `WellDenoted` alone — no argument re-check.  This is the
family-2 removal's core theorem; `app_lamR_pos`
(`SetModel/Ops.lean`) is its value-level kernel.  At kind `0` the domain
membership is not recoverable (impredicativity — the #49/#73 residue),
which is why the runtime gate is a kind test, not a deletion. -/
theorem WellDenoted_beta_pos {v : Nat} (hv : v ≠ 0) {A b a : AnnotTerm}
    {ρ : Nat → V}
    (h : WellDenoted V ρ (.app (.lam v A b) a)) :
    interp V ρ (.app (.lam v A b) a) = interp V ρ (b.inst a) ∧
    WellDenoted V ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, v', A', B', hslot, hmem, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, hbody, B, hfib, -⟩ := hlam
  -- the slot's product is in the graph regime: the λ is not `pt`
  have hv' : v' ≠ 0 := by
    intro h0
    subst h0
    have h1 := eq_pt_of_mem_piR_zero hslot
    rw [interp_lam] at h1
    exact lamR_ne_pt hv h1
  -- rigidity pins the slot's domain to the λ's own
  have hown : interp V ρ (.lam v A b)
      ∈ˢ piR v (interp V ρ A) B := by
    rw [interp_lam]
    exact lamR_mem hfib
  have hAA : interp V ρ A = A' := piR_dom_unique hv hv' hown hslot
  have haA : interp V ρ a ∈ˢ interp V ρ A := by
    rw [hAA]
    exact hmem
  refine ⟨?_, ?_⟩
  · rw [interp_app, interp_lam, app_lamR_pos hv haA, interp_inst0]
  · exact (WellDenoted_inst0 V ha).mpr (hbody _ haA)


/-- The graded β step at kind `0` — the residue side: with the
argument membership supplied (the retained `Prop`-codomain runtime
check's fact), the equality holds because both sides are the canonical
proof, and the transport is the hereditary component. -/
theorem WellDenoted_beta_zero {A b a : AnnotTerm} {ρ : Nat → V}
    (h : WellDenoted V ρ (.app (.lam 0 A b) a))
    (hmem : interp V ρ a ∈ˢ interp V ρ A) :
    interp V ρ (.app (.lam 0 A b) a) = interp V ρ (b.inst a) ∧
    WellDenoted V ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, hbody, B, hfib, hz⟩ := hlam
  refine ⟨?_, (WellDenoted_inst0 V ha).mpr (hbody _ hmem)⟩
  rw [interp_app, interp_lam, lamR_zero, app_pt, interp_inst0]
  exact (eq_pt_of_mem_univZero (hz rfl _ hmem) (hfib _ hmem)).symm

/-! ## The app slot's establishment

The clause's kind-`0` fibre component (added at the consumer seal —
see the module docstring) is not a wish: it is exactly what an
*annotated* `Π` hands over at the application site.  Stated at the
value level, so the supplier is a theorem before the clause that
consumes it is relied on. -/

/-- **The app slot, established from the function type's own
annotation.**  Given the function in an annotated `Π`'s
interpretation, the argument in its domain, and the `Π`'s *codomain
sort fact at kind `0`*, the slot follows — new component included.

The codomain premise's supplier is `HasSort.mem_univ`
(`ConLeche/SetR/Annot/Kinding.lean`) at the `Π`'s own numeral `v`,
which is the same route `Annotates.lam`'s cached `HasSortC` takes for
the λ clause's identically-shaped component.  So the two binder
clauses are symmetric, which is what the amendment restores. -/
theorem appSlot_of_pi {u v : Nat} {ρ : Nat → V} {f a Aa Ba : AnnotTerm}
    (hf : interp V ρ f ∈ˢ interp V ρ (.pi u v Aa Ba))
    (ha : interp V ρ a ∈ˢ interp V ρ Aa)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    ∃ (v' : Nat) (A : V) (B : V → V),
      interp V ρ f ∈ˢ piR v' A B ∧ interp V ρ a ∈ˢ A ∧
      (v' = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) := by
  rw [interp_pi] at hf
  exact ⟨v, interp V ρ Aa, fun x => interp V (cons x ρ) Ba,
    hf, ha, hcod⟩

/-- The full app-clause establishment: the hereditary halves plus the
slot.  This is the shape `Claims2`'s `app` case will discharge. -/
theorem WellDenoted_app_of {u v : Nat} {ρ : Nat → V} {f a Aa Ba : AnnotTerm}
    (hokf : WellDenoted V ρ f) (hoka : WellDenoted V ρ a)
    (hf : interp V ρ f ∈ˢ interp V ρ (.pi u v Aa Ba))
    (ha : interp V ρ a ∈ˢ interp V ρ Aa)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    WellDenoted V ρ (.app f a) := by
  rw [WellDenoted_app]
  exact ⟨hokf, hoka, appSlot_of_pi V hf ha hcod⟩

end ConLeche.Semantics
