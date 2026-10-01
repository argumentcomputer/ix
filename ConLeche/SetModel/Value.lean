module

public import ConLeche.SetModel.Ops
public import ConLeche.Term.Const
public import ConLeche.SetTheory.Derive.Sigma
public import ConLeche.SetTheory.Derive.Quot
public import ConLeche.SetTheory.Derive.Choice
public import ConLeche.SetTheory.Derive.LfpFam

@[expose] public section

/-!
# The built-in constants, two-regime (task #151, tier B — B2)

`ConLeche/Term/Semantics/Value.lean`'s `bval` restated over `piR`/`lamR`.
The old towers are `lamC`-built, so they inherit the domain-relative
collapse; these are annotation-built, and the law surface changes with
them in the way the tier-B design priced.

## The annotation convention

Every λ in a constant's tower carries the tower's **result sort** `r`
— the sort of the type of the innermost body.  That is not the exact
sort of each binder's codomain (which is an `imax` fold ending in `r`),
but it agrees with it on the only thing `piR`/`lamR` read: for
`(a₁ : A₁) → … → (aₙ : Aₙ) → T` with `T : Sort r`, each suffix has sort
`imax (…) r`, and `imax x y = 0 ↔ y = 0` (`imax_eq_zero_iff`).
`lamR_mem_zero_agree` is the bridge for any consumer that wants the
exact annotation.

*Domains* carry their exact sorts, because those are what the
consumers' membership hypotheses are stated with: the motive spaces are
`piR (r+1) …` (a space of `Sort r`-valued functions is `Sort (r+1)`-…
valued), the relation space is `piR (max u 1) …` (`A → Prop` is a
*type*: its codomain `Prop = Sort 0` lives in `Sort 1`), and the
invariance/double-negation spaces are `piR 0 …` throughout.

## The law surface, as priced

The collapse's `app_lamC` fires on domain membership alone, so under
`bval` every constant's application law needs only its arguments'
typings.  Here each law **splits by regime**:

* `r ≠ 0` — the graph regime — is the clean case: `app_lamR_pos`, no
  premise beyond domain membership, strictly *fewer* hypotheses than
  the collapse version needed;
* `r = 0` — the tower *is* the canonical proof, so the law holds only
  because both sides are, which is the pre-#100
  `v = 0 → the fibres are truth values` premise resurfacing.  Each law
  below discharges it from its own motive/fibre hypothesis rather than
  taking it as an extra argument, so **no statement grew a premise**:
  `natRecV_app` needs `hM` (which `natRecV_app` also had),
  `punitRecV_app` needs `hM`, and so on.

Two values genuinely **change**, both because the empty-domain collapse
is gone:

* `Empty.rec` was `pt` (its inner λ has an empty domain, and *every*
  empty-domain `lamC` collapses).  It is now `lamR v … (lamR v ∅ …)` —
  a graph at `v ≠ 0`, `pt` at `v = 0`.
* `SetTheory.quotLift` is `lamC`-built, so tier B carries its own
  `quotLiftR` (the same abstraction at an annotation).  It is the only
  `SetTheory` operator this file has to replace; `natrec`, `schoice`,
  `quotSet`, `quotClass`, `qrep`, `sigmaSet`, `sfst`/`ssnd` are all
  collapse-free already, and `sigmaSet`/`quotSet`/`quotClass` are in
  fact *already* annotation-driven — the recorded precedent.
-/

namespace ConLeche.SetModel

open SetTheory
open ConLeche.Term (BConst lv)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat.succ` -/

/-- `Nat.succ : Nat → Nat`; result sort `1`. -/
noncomputable def natSuccV : V := lamR 1 omega natsucc

theorem natSuccV_app {n : V} (hn : n ∈ˢ (omega : V)) :
    app (natSuccV V) n = natsucc n := app_lamR_pos Nat.one_ne_zero hn

theorem natSuccV_mem : natSuccV V ∈ˢ piR 1 (omega : V) fun _ => omega :=
  lamR_mem fun _ hx => natsucc_mem hx

/-! ## `Nat.rec` -/

/-- `Nat → Sort u`, the motive space. -/
noncomputable def natMotiveSpace (u : Nat) : V := piR (u + 1) omega fun _ => univ u

/-- `(n : Nat) → M n → M (n+1)`, the minor-premise space. -/
noncomputable def natStepSpace (u : Nat) (M : V) : V :=
  piR u omega fun n => piR u (app M n) fun _ => app M (natsucc n)

/-- `Nat.rec.{u}`; result sort `u`. -/
noncomputable def natRecV (u : Nat) : V :=
  lamR u (natMotiveSpace V u) fun M =>
    lamR u (app M natzero) fun z =>
      lamR u (natStepSpace V u M) fun s =>
        lamR u omega fun n => natrec z s n

theorem natMotive_apply {u : Nat} {M n : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hn : n ∈ˢ (omega : V)) : app M n ∈ˢ (univ u : V) :=
  app_mem_piR_pos (Nat.succ_ne_zero u) hM hn

/-- The step premise, unpacked.  At `u = 0` this is where the
fibre-universe facts are consumed — twice, once per `piR`. -/
theorem natStep_apply {u : Nat} {M s : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hs : s ∈ˢ natStepSpace V u M) :
    ∀ k, k ∈ˢ (omega : V) → ∀ ih, ih ∈ˢ app M k →
      app (app s k) ih ∈ˢ app M (natsucc k) := by
  intro k hk ih hih
  have h1 : app s k ∈ˢ piR u (app M k) fun _ => app M (natsucc k) := by
    refine app_mem_piR hs hk fun hu n _hn => ?_
    subst hu
    exact piR_zero_mem_univZero
  refine app_mem_piR h1 hih fun hu _ _ => ?_
  subst hu
  have h2 := natMotive_apply V hM (natsucc_mem hk)
  rwa [univ_zero] at h2

theorem natRecV_mem_fibre {u : Nat} {M z s n : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hz : z ∈ˢ app M natzero) (hs : s ∈ˢ natStepSpace V u M)
    (hn : n ∈ˢ (omega : V)) : natrec z s n ∈ˢ app M n :=
  natrec_mem hz (natStep_apply V hM hs) hn

/-- ι for `Nat.rec`.  At `u ≠ 0` the four βs are `app_lamR_pos` — no
premise but domain membership.  At `u = 0` both sides are the canonical
proof, which is exactly the resurfaced pre-#100 premise, discharged
here from `hM`. -/
theorem natRecV_app {u : Nat} {M z s n : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hz : z ∈ˢ app M natzero) (hs : s ∈ˢ natStepSpace V u M)
    (hn : n ∈ˢ (omega : V)) :
    app (app (app (app (natRecV V u) M) z) s) n = natrec z s n := by
  by_cases hu : u = 0
  · subst hu
    rw [natRecV, lamR_zero, app_pt, app_pt, app_pt, app_pt]
    exact (mem_univ_zero (natMotive_apply V hM hn)
      (natRecV_mem_fibre V hM hz hs hn)).symm
  · rw [natRecV, app_lamR_pos hu hM, app_lamR_pos hu hz, app_lamR_pos hu hs,
      app_lamR_pos hu hn]

/-! ## `PUnit.rec` -/

/-- `PUnit.{u} → Sort v`. -/
noncomputable def punitMotiveSpace (v : Nat) : V :=
  piR (v + 1) unitSet fun _ => univ v

/-- `PUnit.rec.{u,v}`; result sort `v`. -/
noncomputable def punitRecV (v : Nat) : V :=
  lamR v (punitMotiveSpace V v) fun M =>
    lamR v (app M pt) fun m =>
      lamR v unitSet fun _ => m

theorem punitRecV_app {v : Nat} {M m t : V} (hM : M ∈ˢ punitMotiveSpace V v)
    (hm : m ∈ˢ app M pt) (ht : t ∈ˢ (unitSet : V)) :
    app (app (app (punitRecV V v) M) m) t = m := by
  by_cases hv : v = 0
  · subst hv
    have hMpt : app M pt ∈ˢ (univ 0 : V) :=
      app_mem_piR_pos (Nat.succ_ne_zero 0) hM (pt_mem_unitSet (V := V))
    rw [punitRecV, lamR_zero, app_pt, app_pt, app_pt]
    exact (mem_univ_zero hMpt hm).symm
  · rw [punitRecV, app_lamR_pos hv hM, app_lamR_pos hv hm, app_lamR_pos hv ht]

/-! ## `PSigma'` -/

/-- `A → Sort v`, the fibre space. -/
noncomputable def psigmaFibreSpace (v : Nat) (A : V) : V :=
  piR (v + 1) A fun _ => univ v

theorem psigmaFibre_apply {v : Nat} {A B a : V} (hB : B ∈ˢ psigmaFibreSpace V v A)
    (ha : a ∈ˢ A) : app B a ∈ˢ (univ v : V) :=
  app_mem_piR_pos (Nat.succ_ne_zero v) hB ha

/-- `PSigma'.{u,v}`; result sort `max u v + 1` — a type former, so
always in the graph regime. -/
noncomputable def psigmaV (u v : Nat) : V :=
  lamR (Nat.max u v + 1) (univ u) fun A =>
    lamR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun B =>
      sigmaSet (Nat.max u v) A fun x => app B x

theorem psigmaV_app {u v : Nat} {A B : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) :
    app (app (psigmaV V u v) A) B = sigmaSet (Nat.max u v) A fun x => app B x := by
  rw [psigmaV, app_lamR_pos (Nat.succ_ne_zero _) hA,
    app_lamR_pos (Nat.succ_ne_zero _) hB]

/-- **The pinned pair type's rigidity** (`mem_psigmaV_app`'s mirror at
`interp`): an inhabited `PSigma'` application forces both arguments
into their places and exhibits the inhabitant in the sigma set.  Off
either domain the application is canonical junk, which has no members
(`app_lamR_of_not_mem`).  Added for the caps tier's pinned-pair η row
(task #161). -/
theorem mem_psigmaV2_app {u v : Nat} {A B x : V}
    (hx : x ∈ˢ app (app (psigmaV V u v) A) B) :
    A ∈ˢ (univ u : V) ∧ B ∈ˢ psigmaFibreSpace V v A ∧
      x ∈ˢ sigmaSet (Nat.max u v) A fun y => app B y := by
  by_cases hA : A ∈ˢ (univ u : V)
  · rw [psigmaV, app_lamR_pos (Nat.succ_ne_zero _) hA] at hx
    by_cases hB : B ∈ˢ psigmaFibreSpace V v A
    · rw [app_lamR_pos (Nat.succ_ne_zero _) hB] at hx
      exact ⟨hA, hB, hx⟩
    · rw [app_lamR_of_not_mem (Nat.succ_ne_zero _) hB] at hx
      exact absurd hx (not_mem_empty x)
  · rw [psigmaV, app_lamR_of_not_mem (Nat.succ_ne_zero _) hA,
      app_empty] at hx
    exact absurd hx (not_mem_empty x)

/-- `PSigma'.mk.{u,v}`; result sort `max u v`.  The old value's
explicit `if max u v = 0 then pt` tag is **gone from the definition**:
the annotation already squashes the whole tower at `0`, so the body is
unconditionally the Kuratowski pair. -/
noncomputable def psigmaMkV (u v : Nat) : V :=
  lamR (Nat.max u v) (univ u) fun A =>
    lamR (Nat.max u v) (psigmaFibreSpace V v A) fun B =>
      lamR (Nat.max u v) A fun a =>
        lamR (Nat.max u v) (app B a) fun b => spair a b

theorem psigmaMkV_app {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    app (app (app (app (psigmaMkV V u v) A) B) a) b =
      if Nat.max u v = 0 then pt else spair a b := by
  by_cases hw : Nat.max u v = 0
  · rw [psigmaMkV, hw, lamR_zero, app_pt, app_pt, app_pt, app_pt, if_pos rfl]
  · rw [psigmaMkV, app_lamR_pos hw hA, app_lamR_pos hw hB, app_lamR_pos hw ha,
      app_lamR_pos hw hb, if_neg hw]

/-- At a `Prop`-level pair the joint level is `0`, hence both component
levels are. -/
theorem psigma_zero_levels {u v : Nat} (h : Nat.max u v = 0) : u = 0 ∧ v = 0 :=
  ⟨Nat.le_zero.mp (h ▸ Nat.le_max_left u v),
   Nat.le_zero.mp (h ▸ Nat.le_max_right u v)⟩

/-! ### The projections -/

theorem sfst_mem2 {u v : Nat} {A B p : V} (hA : A ∈ˢ (univ u : V))
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A fun x => app B x) : sfst p ∈ˢ A := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · rw [h0 hw, sfst_pt]
    exact (mem_univ_zero ((psigma_zero_levels hw).1 ▸ hA) ha) ▸ ha
  · rw [hne hw, sfst_spair]; exact ha

theorem ssnd_mem2 {u v : Nat} {A B p : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A)
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A fun x => app B x) :
    ssnd p ∈ˢ app B (sfst p) := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · obtain ⟨hu, hv⟩ := psigma_zero_levels hw
    have hapt : a = pt := mem_univ_zero (hu ▸ hA) ha
    have hBa : app B a ∈ˢ (univ 0 : V) := hv ▸ psigmaFibre_apply V hB ha
    have hbpt : b = pt := mem_univ_zero hBa hb
    rw [h0 hw, ssnd_pt, sfst_pt, show app B pt = app B a by rw [hapt]]
    exact hbpt ▸ hb
  · rw [hne hw, ssnd_spair, sfst_spair]; exact hb

theorem sfst_mk2 {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    sfst (app (app (app (app (psigmaMkV V u v) A) B) a) b) = a := by
  rw [psigmaMkV_app V hA hB ha hb]
  split
  · next h =>
    rw [sfst_pt]
    exact (mem_univ_zero ((psigma_zero_levels h).1 ▸ hA) ha).symm
  · next _ => exact sfst_spair a b

theorem ssnd_mk2 {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    ssnd (app (app (app (app (psigmaMkV V u v) A) B) a) b) = b := by
  rw [psigmaMkV_app V hA hB ha hb]
  split
  · next h =>
    rw [ssnd_pt]
    obtain ⟨_, hv⟩ := psigma_zero_levels h
    have hBa : app B a ∈ˢ (univ 0 : V) := hv ▸ psigmaFibre_apply V hB ha
    exact (mem_univ_zero hBa hb).symm
  · next _ => exact ssnd_spair a b

/-- Structure η for the basis pair. -/
theorem psigmaEta_law {u v : Nat} {A B p : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A)
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A fun x => app B x) :
    app (app (app (app (psigmaMkV V u v) A) B) (sfst p)) (ssnd p) = p := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · obtain ⟨hu, hv⟩ := psigma_zero_levels hw
    have hapt : a = pt := mem_univ_zero (hu ▸ hA) ha
    have hBa : app B a ∈ˢ (univ 0 : V) := hv ▸ psigmaFibre_apply V hB ha
    have hbpt : b = pt := mem_univ_zero hBa hb
    have hpa : (pt : V) ∈ˢ A := hapt ▸ ha
    have hpb : (pt : V) ∈ˢ app B pt := by
      have h1 : (pt : V) ∈ˢ app B a := hbpt ▸ hb
      rwa [hapt] at h1
    rw [h0 hw, sfst_pt, ssnd_pt, psigmaMkV_app V hA hB hpa hpb, if_pos hw]
  · rw [hne hw, sfst_spair, ssnd_spair, psigmaMkV_app V hA hB ha hb, if_neg hw]

/-! ## `Quot` -/

theorem maxOne_ne_zero (u : Nat) : Nat.max u 1 ≠ 0 := by
  intro h
  have h1 : (1 : Nat) ≤ Nat.max u 1 := Nat.le_max_right u 1
  rw [h] at h1
  exact absurd (Nat.le_zero.mp h1) Nat.one_ne_zero

/-- `A → A → Prop`.  Note the annotations: `Prop = Sort 0` lives in
`Sort 1`, so `A → Prop` has codomain sort `1` and is itself a *type*
of sort `max u 1` — both products are in the graph regime, which is
why a relation is a genuine graph and never the proof point. -/
noncomputable def relSpace (u : Nat) (A : V) : V :=
  piR (Nat.max u 1) A fun _ => piR 1 A fun _ => univ 0

/-- `Quot.{u}`; result sort `u + 1` (a type former). -/
noncomputable def quotV (u : Nat) : V :=
  lamR (u + 1) (univ u) fun A =>
    lamR (u + 1) (relSpace V u A) fun R => quotSet u A R

theorem quotV_app {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V u A) :
    app (app (quotV V u) A) R = quotSet u A R := by
  rw [quotV, app_lamR_pos (Nat.succ_ne_zero u) hA,
    app_lamR_pos (Nat.succ_ne_zero u) hR]

/-- `Quot.mk.{u}`; result sort `u`. -/
noncomputable def quotMkV (u : Nat) : V :=
  lamR u (univ u) fun A =>
    lamR u (relSpace V u A) fun R =>
      lamR u A fun a => quotClass u A R a

theorem quotMkV_app {u : Nat} {A R a : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V u A) (ha : a ∈ˢ A) :
    app (app (app (quotMkV V u) A) R) a = quotClass u A R a := by
  by_cases hu : u = 0
  · subst hu
    have hcp : quotClass 0 A R a = pt :=
      mem_univ_zero (quotSet_mem_univ hA) (quotClass_mem ha)
    rw [quotMkV, lamR_zero, app_pt, app_pt, app_pt, hcp]
  · rw [quotMkV, app_lamR_pos hu hA, app_lamR_pos hu hR, app_lamR_pos hu ha]

/-- The lift of `f` to the quotient, at an annotation:
`SetTheory.quotLift` with `lamC` replaced by `lamR v`.  This is the one
`SetTheory` operator tier B has to carry its own copy of. -/
noncomputable def quotLiftR (u v : Nat) (A R f : V) : V :=
  lamR v (quotSet u A R) fun q => app f (qrep u A R q)

theorem quotLiftR_app {u v : Nat} (hv : v ≠ 0) {A R f q : V}
    (hq : q ∈ˢ quotSet u A R) :
    app (quotLiftR V u v A R f) q = app f (qrep u A R q) := by
  rw [quotLiftR]; exact app_lamR_pos hv hq

theorem quotLiftR_mem {u v : Nat} {A R f B : V}
    (hf : f ∈ˢ piR v A fun _ => B) (hB0 : v = 0 → B ∈ˢ (univZero : V)) :
    quotLiftR V u v A R f ∈ˢ piR v (quotSet u A R) fun _ => B :=
  lamR_mem fun _q hq => app_mem_piR hf (qrep_spec hq).1 fun hv _ _ => hB0 hv

/-! ## `Quot.lift` -/

/-- `∀ a b, r a b → f a = f b`: `Prop`-valued throughout, so every
annotation is `0`. -/
noncomputable def quotInvSpace (A R f : V) : V :=
  piR 0 A fun a => piR 0 A fun b =>
    piR 0 (app (app R a) b) fun _ => eqv (app f a) (app f b)

/-- The invariance premise, read off a proof's membership.  Three
`app_mem_piR` steps, each discharging its `v = 0` fibre premise from
`piR_zero_mem_univZero` / `eqv_mem_univZero` — the pre-#100 shape,
recovered. -/
theorem quotInv_of_mem {A R f h : V} (hh : h ∈ˢ quotInvSpace V A R f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      app f a = app f b := by
  intro a b ha hb hw
  obtain ⟨wv, hwv⟩ := hw
  rw [quotInvSpace] at hh
  have h1 : app h a ∈ˢ
      piR 0 A fun b => piR 0 (app (app R a) b) fun _ => eqv (app f a) (app f b) :=
    app_mem_piR hh ha fun _ _ _ => piR_zero_mem_univZero
  have h2 : app (app h a) b ∈ˢ
      piR 0 (app (app R a) b) fun _ => eqv (app f a) (app f b) :=
    app_mem_piR h1 hb fun _ _ _ => piR_zero_mem_univZero
  have h3 : app (app (app h a) b) wv ∈ˢ eqv (app f a) (app f b) :=
    app_mem_piR h2 hwv fun _ _ _ => eqv_mem_univZero _ _
  exact mem_eqv h3

/-- `Quot.lift.{u,v}`; result sort `v`. -/
noncomputable def quotLiftV (u v : Nat) : V :=
  lamR v (univ u) fun A =>
    lamR v (relSpace V u A) fun R =>
      lamR v (univ v) fun B =>
        lamR v (piR v A fun _ => B) fun f =>
          lamR v (quotInvSpace V A R f) fun _ => quotLiftR V u v A R f

theorem quotLiftV_app {u v : Nat} (hv : v ≠ 0) {A R B f h : V}
    (hA : A ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u A)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piR v A fun _ => B)
    (hh : h ∈ˢ quotInvSpace V A R f) :
    app (app (app (app (app (quotLiftV V u v) A) R) B) f) h =
      quotLiftR V u v A R f := by
  rw [quotLiftV, app_lamR_pos hv hA, app_lamR_pos hv hR, app_lamR_pos hv hB,
    app_lamR_pos hv hf, app_lamR_pos hv hh]

/-- **ι for `Quot.lift` at a `Prop`-valued target** — the case
`quotLiftV_app`'s `v ≠ 0` side condition excludes, and it needs no
premises at all.

The ENDGAME D and E seals both flagged `quotLiftR_app`/`quotLiftV_app`
as "the only two firing laws with a `v ≠ 0` side condition", with the
`natRecV_app` precedent recorded as not transferring.  It does not
have to: at `v = 0` **both sides are `pt`**, because `lamR 0` is `pt`
by `lamR_zero` and `quotLiftR` is itself a `lamR v`.  There is no
squash-regime reasoning to do, no motive membership to consume, and no
premise to discharge — the two collapses meet on the nose.

Recorded here rather than in a seal because the ledger's rule is that
a claim about a wall is re-checked, not inherited: this is the check,
and it costs two lines. -/
theorem quotLiftV_app_zero {u : Nat} (A R B f h : V) :
    app (app (app (app (app (quotLiftV V u 0) A) R) B) f) h =
      quotLiftR V u 0 A R f := by
  rw [quotLiftV, lamR_zero, app_pt, app_pt, app_pt, app_pt, app_pt,
    quotLiftR, lamR_zero]

/-- The two branches, packaged: `Quot.lift` fires at **every**
numeral. -/
theorem quotLiftV_app_any {u v : Nat} {A R B f h : V}
    (hA : A ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V u A)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piR v A fun _ => B)
    (hh : h ∈ˢ quotInvSpace V A R f) :
    app (app (app (app (app (quotLiftV V u v) A) R) B) f) h =
      quotLiftR V u v A R f := by
  by_cases hv : v = 0
  · subst hv; exact quotLiftV_app_zero V A R B f h
  · exact quotLiftV_app V hv hA hR hB hf hh

/-! ## `Classical.choice` -/

/-- `¬¬A`, i.e. `(A → False) → False`: `Prop`-valued, annotations `0`. -/
noncomputable def dnegSpace (A : V) : V :=
  piR 0 (piR 0 A fun _ => empty) fun _ => empty

theorem piR_zero_empty (B : V → V) : piR 0 (empty : V) B = unitSet := by
  rw [piR_zero, truthVal_eq_unitSet (fun x hx => absurd hx (not_mem_empty x))]

/-- A `¬¬A` inhabitant witnesses that `A` is inhabited. -/
theorem exists_mem_of_dneg {A h : V} (hh : h ∈ˢ dnegSpace V A) :
    ∃ x, x ∈ˢ A := by
  rcases Classical.em (∃ x, x ∈ˢ A) with hex | hne
  · exact hex
  · exfalso
    have hA : A = empty := eq_empty fun z hz => hne ⟨z, hz⟩
    subst hA
    have hpt : (pt : V) ∈ˢ piR 0 (empty : V) fun _ => (empty : V) := by
      rw [piR_zero_empty]; exact pt_mem_unitSet
    have hemp : (empty : V) ∈ˢ (univZero : V) := by
      have h0 := empty_mem_univ (V := V) 0
      rwa [univ_zero] at h0
    rw [dnegSpace] at hh
    exact not_mem_empty _ (app_mem_piR hh hpt fun _ _ _ => hemp)

/-- `Classical.choice.{u}`; result sort `u`. -/
noncomputable def choiceV (u : Nat) : V :=
  lamR u (univ u) fun A => lamR u (dnegSpace V A) fun _ => schoice A

theorem choiceV_app {u : Nat} {A h : V} (hA : A ∈ˢ (univ u : V))
    (hh : h ∈ˢ dnegSpace V A) : app (app (choiceV V u) A) h = schoice A := by
  by_cases hu : u = 0
  · subst hu
    obtain ⟨x, hx⟩ := exists_mem_of_dneg V hh
    rw [choiceV, lamR_zero, app_pt, app_pt]
    exact (mem_univ_zero hA (schoice_mem hx)).symm
  · rw [choiceV, app_lamR_pos hu hA, app_lamR_pos hu hh]

/-! ## `Empty.rec`

**The value changes.**  Under the collapse this constant is the proof
point at every level, because its inner λ has the empty domain and
`lamC_empty` collapses at every level.  Two-regime it is a graph
whenever the motive is `Type`-valued — one of the two concrete places
the #100 countermodel's cause shows up in the basis. -/

/-- `Empty.{u} → Sort v`. -/
noncomputable def emptyMotiveSpace (v : Nat) : V :=
  piR (v + 1) empty fun _ => univ v

/-- `Empty.rec.{u,v}`; result sort `v`.  The inner λ has an empty
domain, so its value is the empty graph at `v ≠ 0` (and the canonical
proof at `v = 0`) — **not** unconditionally `pt`. -/
noncomputable def emptyRecV (v : Nat) : V :=
  lamR v (emptyMotiveSpace V v) fun _ => lamR v empty fun _ => empty

theorem emptyRecV_ne_pt {v : Nat} (hv : v ≠ 0) : emptyRecV V v ≠ pt :=
  lamR_ne_pt hv

/-- …and it is still the canonical proof in the squash regime. -/
theorem emptyRecV_zero : emptyRecV V 0 = pt := lamR_zero

/-! ## `lfpFam` (task #188, indexed)

The least pre-fixed point of a functor on FAMILIES over an index set `I`
(`lfpFamSet`, `ConLeche/SetTheory/Derive/LfpFam.lean`).  The family space
`I → Sort w` is `piR (w + 1) I (fun _ => univ w)` — bit `w + 1`, the
codomain's sort, so a graph at every regime; the functor space is the
arrow over it at the sort `max u (w + 1)` of `I → Sort w`.  Total: the
value is a member of the family space for EVERY functor. -/

/-- `I → Sort w`, the family space. -/
noncomputable def lfpFamSpace (w : Nat) (I : V) : V := piR (w + 1) I fun _ => univ w

/-- `(I → Sort w) → (I → Sort w)`, the functor space. -/
noncomputable def lfpFamFunSpace (u w : Nat) (I : V) : V :=
  piR (Nat.max u (w + 1)) (lfpFamSpace V w I) fun _ => lfpFamSpace V w I

/-- `lfpFam.{u,w}`; result sort `max (u + 1) (w + 1)`. -/
noncomputable def lfpFamV (u w : Nat) : V :=
  lamR (Nat.max u (w + 1)) (univ u) fun I =>
    lamR (Nat.max u (w + 1)) (lfpFamFunSpace V u w I) fun F => lfpFamSet w I F

theorem max_succ_ne_zero (u w : Nat) : Nat.max u (w + 1) ≠ 0 := by
  show max u (w + 1) ≠ 0
  rw [Nat.max_def]
  split <;> omega

theorem lfpFamSet_mem_space (w : Nat) (I F : V) : lfpFamSet w I F ∈ˢ lfpFamSpace V w I := by
  unfold lfpFamSpace
  rw [piR_pos (Nat.succ_ne_zero w)]
  exact lfpFamSet_mem w I F

theorem lfpFamV_app {u w : Nat} {I F : V} (hI : I ∈ˢ (univ u : V))
    (hF : F ∈ˢ lfpFamFunSpace V u w I) :
    app (app (lfpFamV V u w) I) F = lfpFamSet w I F := by
  rw [lfpFamV, app_lamR_pos (max_succ_ne_zero u w) hI, app_lamR_pos (max_succ_ne_zero u w) hF]

theorem lfpFamV_mem (u w : Nat) :
    lfpFamV V u w ∈ˢ piR (Nat.max u (w + 1)) (univ u : V) fun I =>
      piR (Nat.max u (w + 1)) (lfpFamFunSpace V u w I) fun _ => lfpFamSpace V w I :=
  lamR_mem fun I _ => lamR_mem fun F _ => lfpFamSet_mem_space V w I F

/-! ## The value assignment -/

/-- The two-regime value of each built-in constant at a concrete level
instantiation — `ConLeche.Term.bval`'s transpose.  `quotInd`, `quotSound`
and `propext` are the canonical proof because their result sorts *are*
`0`; `punitUnit` is because `unitSet = {pt}` at every level.  The one
value that differs from `bval` beyond the operator change is
`emptyRec`. -/
noncomputable def bval : BConst → List Nat → V
  | .nat, _ => omega
  | .natZero, _ => natzero
  | .natSucc, _ => natSuccV V
  | .natRec, us => natRecV V (lv us 0)
  | .punit, _ => unitSet
  | .punitUnit, _ => pt
  | .punitRec, us => punitRecV V (lv us 1)
  | .psigma, us => psigmaV V (lv us 0) (lv us 1)
  | .psigmaMk, us => psigmaMkV V (lv us 0) (lv us 1)
  | .empty, _ => empty
  | .emptyRec, us => emptyRecV V (lv us 1)
  | .quot, us => quotV V (lv us 0)
  | .quotMk, us => quotMkV V (lv us 0)
  | .quotLift, us => quotLiftV V (lv us 0) (lv us 1)
  | .quotInd, _ => pt
  | .quotSound, _ => pt
  | .propext, _ => pt
  | .choice, us => choiceV V (lv us 0)
  | .lfpFam, us => lfpFamV V (lv us 0) (lv us 1)

end ConLeche.SetModel
