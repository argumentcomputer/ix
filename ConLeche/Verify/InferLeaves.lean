module

public import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Leaves
import ConLeche.Verify.Subst
import ConLeche.Verify.Abstract

public section

/-!
# Leaf-closure and loose-bvar preservation for `whnf` and `inferTypeCore`

Reduction and inference only ever *copy* material from the input (delta
unfoldings are closed), so their outputs' free-variable leaves are a
subset of the input's — which transports every leaf-closure condition
(`FvarsOk`, `LeavesBounded`, `LeafCond`) for free.  Loose-bvar bounds
are threaded via `LeavesBounded` (the `fvar` rule jumps into the
annotation).
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr in
/-- `instPisAt` residual leaves come from the telescope or the
arguments (task #175 wiring W2c: the tower-entry residual's leaves). -/
theorem instPisAt_fvarLeaves :
    ∀ (args : List Expr) (ty : Expr) {doms : List Expr} {res : Expr},
      Expr.instPisAt args ty = some (doms, res) →
      ∀ l, l ∈ res.fvarLeaves →
        l ∈ ty.fvarLeaves ∨ ∃ a ∈ args, l ∈ a.fvarLeaves
  | [], ty, doms, res, h, l, hl => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl hl
  | a :: as, ty, doms, res, h, l, hl => by
    cases ty with
    | forallE dom body mb =>
      simp only [Expr.instPisAt] at h
      revert h
      cases hrec : Expr.instPisAt as (body.instantiate1 a) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨ds, rest⟩ := p
        intro h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases instPisAt_fvarLeaves as _ hrec l hl with hty | ⟨a', ha', hla⟩
        · rcases fvarLeaves_instantiate1 body 0 hty with hb | hb
          · refine Or.inl ?_
            simp only [Expr.fvarLeaves, List.mem_append]
            exact Or.inr hb
          · exact Or.inr ⟨a, List.mem_cons_self, hb⟩
        · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hla⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
    | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h

open Expr in
/-- Peeling a `∀`-telescope along scoped arguments preserves
well-scopedness. -/

theorem piResidual_WScoped {d : Nat} :
    ∀ {as : List Expr} {t res : Expr}, piResidual t as = some res →
      WScoped d t → (∀ x ∈ as, WScoped d x) → WScoped d res
  | [], t, res, h, hw, _ => by
    simp only [piResidual, Option.some.injEq] at h
    exact h ▸ hw
  | a :: as, t, res, h, hw, has => by
    match t, h with
    | .forallE ty body mb, h =>
      have hw' : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hw
      have h' : piResidual (body.instantiate1 a) as = some res := h
      exact piResidual_WScoped h'
        (WScoped.instantiate1_gen (has a (List.mem_cons_self ..)) 0 hw'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))

open Expr in
/-- Peeling only introduces the telescope's and the arguments'
leaves. -/
theorem piResidual_fvarLeaves :
    ∀ {as : List Expr} {t res : Expr}, piResidual t as = some res →
      ∀ l ∈ res.fvarLeaves,
        l ∈ t.fvarLeaves ∨ ∃ x ∈ as, l ∈ x.fvarLeaves
  | [], t, res, h, l, hl => by
    simp only [piResidual, Option.some.injEq] at h
    exact Or.inl (h ▸ hl)
  | a :: as, t, res, h, l, hl => by
    match t, h with
    | .forallE ty body mb, h =>
      have h' : piResidual (body.instantiate1 a) as = some res := h
      rcases piResidual_fvarLeaves h' l hl with hb | ⟨x, hx, hlx⟩
      · rcases fvarLeaves_instantiate1 body 0 hb with hb | hb
        · exact Or.inl (by simp [Expr.fvarLeaves, hb])
        · exact Or.inr ⟨a, List.mem_cons_self .., hb⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hlx⟩

open Expr in
/-- Peeling a bounded telescope along bounded arguments stays
bounded. -/
theorem piResidual_looseBVars :
    ∀ {as : List Expr} {t res : Expr}, piResidual t as = some res →
      t.looseBVarsBounded 0 = true →
      (∀ x ∈ as, x.looseBVarsBounded 0 = true) →
      res.looseBVarsBounded 0 = true
  | [], t, res, h, hb, _ => by
    simp only [piResidual, Option.some.injEq] at h
    exact h ▸ hb
  | a :: as, t, res, h, hb, has => by
    match t, h with
    | .forallE ty body mb, h =>
      have hb' : ty.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        simpa only [Expr.looseBVarsBounded, Bool.and_eq_true] using hb
      have h' : piResidual (body.instantiate1 a) as = some res := h
      exact piResidual_looseBVars h'
        (looseBVarsBounded_instantiate1_gen
          (has a (List.mem_cons_self ..)) hb'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))


open Expr

/-- Every leaf annotation is bvar-closed. -/
@[expose] def Expr.LeavesBounded (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, Expr.looseBVarsBounded 0 l.2 = true

/-- The per-index leaf condition backing `fvarConsistent`. -/
@[expose] def Expr.LeafCond (d : Nat) (ty : Expr) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, l.1 = d → l.2 = ty

theorem Expr.fvarConsistent_of_leafCond {d : Nat} {ty : Expr} :
    ∀ (e : Expr), Expr.LeafCond d ty e → fvarConsistent d ty e := by
  intro e
  induction e with
  | fvar idx ty' ih =>
    intro hc
    simp only [fvarConsistent]
    intro hd
    exact hc (idx, ty') (by simp [fvarLeaves]) hd
  | app f a ihf iha =>
    intro hc
    exact ⟨ihf (fun l hl => hc l (by simp [fvarLeaves, hl])),
      iha (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | lam ty' body m ihty ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | forallE ty' body m ihty ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | letE ty' val body ihty ihval ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihval (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | proj s i e ih =>
    intro hc
    exact ih (fun l hl => hc l (by simp [fvarLeaves, hl]))
  | _ => intro _; simp [fvarConsistent]

/-- Abstraction removes exactly the index-`d` leaves (for scoped terms). -/
theorem Expr.fvarLeaves_abstract1_ne {D : Nat} :
    ∀ (e : Expr) (k : Nat), WScoped (D + 1) e →
      ∀ l ∈ (e.abstract1 D k).fvarLeaves, l ∈ e.fvarLeaves ∧ l.1 ≠ D := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · next hne =>
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨by simp [fvarLeaves], hne⟩
      · obtain ⟨hlt, -⟩ := WScoped_leaves ty hw.2 l hl
        exact ⟨by simp [fvarLeaves, hl], by omega⟩
  | app f a ihf iha =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihf k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := iha k hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | lam ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | forallE ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | letE ty val body ihty ihval ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihval k hw.2.1 l hl
      exact ⟨Or.inl (Or.inr h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | proj s i e ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih k hw l hl
  | bvar i => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | sort u => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | const n us => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | lit ll => intro k _ l hl; simp [abstract1, fvarLeaves] at hl

theorem Expr.LeavesBounded.of_not_hasFvar {e : Expr} (h : e.hasFvar = false) :
    Expr.LeavesBounded e := by
  intro l hl
  rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  cases hl

theorem fvarLeaves_getAppFn :
    ∀ {e : Expr}, ∀ l ∈ e.getAppFn.fvarLeaves, l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro l hl
    simp only [fvarLeaves, List.mem_append]
    exact Or.inl (ihf l hl)
  | _ => intro l hl; exact hl

theorem fvarLeaves_getAppArgs :
    ∀ {e x : Expr}, x ∈ e.getAppArgs → ∀ l ∈ x.fvarLeaves, l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro x hx l hl
    simp only [getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [fvarLeaves, List.mem_append]
    rcases hx with hx | rfl
    · exact Or.inl (ihf hx l hl)
    · exact Or.inr hl
  | _ => intro x hx; simp [getAppArgs] at hx

theorem looseBVarsBounded_mkAppN {k : Nat} : ∀ {xs : List Expr} {f : Expr},
    f.looseBVarsBounded k = true → (∀ x ∈ xs, x.looseBVarsBounded k = true) →
    (Expr.mkAppN f xs).looseBVarsBounded k = true := by
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hxs
    simp only [Expr.mkAppN]
    refine ih ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hf, hxs x List.mem_cons_self⟩

theorem fvarLeaves_mkAppN : ∀ {xs : List Expr} {f : Expr}
    {l : Nat × Expr},
    l ∈ (Expr.mkAppN f xs).fvarLeaves →
    l ∈ f.fvarLeaves ∨ ∃ x, x ∈ xs ∧ l ∈ x.fvarLeaves := by
  intro xs
  induction xs with
  | nil => intro f l hl; exact Or.inl hl
  | cons x xs ih =>
    intro f l hl
    simp only [Expr.mkAppN] at hl
    rcases ih hl with hl' | ⟨y, hy, hly⟩
    · simp only [fvarLeaves, List.mem_append] at hl'
      rcases hl' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_self, h⟩
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hly⟩

/-! ## Preservation through `whnf` -/

/-- The constructor form of a literal has no leaves. -/
theorem natLitToConstructor_fvarLeaves (n : Nat) :
    (natLitToConstructor n).fvarLeaves = [] := by
  cases n <;> simp [natLitToConstructor, Expr.fvarLeaves]

/-- The constructor form of a literal has no loose bvars. -/
theorem natLitToConstructor_looseBVars (n : Nat) {k : Nat} :
    (natLitToConstructor n).looseBVarsBounded k = true := by
  cases n <;> simp [natLitToConstructor, Expr.looseBVarsBounded]

/-- The literal-major conversion only shrinks the leaf closure. -/
theorem litToCtorIfNat_fvarLeaves {env : Env} {e : Expr} :
    ∀ l ∈ (litToCtorIfNat env e).fvarLeaves, l ∈ e.fvarLeaves := by
  intro l hl
  match e, hl with
  | .lit (.natVal n), hl =>
    rw [litToCtorIfNat] at hl
    split at hl
    · rw [natLitToConstructor_fvarLeaves] at hl
      cases hl
    · exact hl
  | .lit (.strVal _), hl => exact hl
  | .bvar _, hl | .fvar _ _, hl | .sort _, hl | .const _ _, hl
  | .app _ _, hl | .lam _ _ _, hl | .forallE _ _ _, hl
  | .letE _ _ _, hl | .proj _ _ _, hl => exact hl

/-- The literal-major conversion preserves the bvar bound. -/
theorem litToCtorIfNat_looseBVars {env : Env} {e : Expr} {k : Nat}
    (hb : e.looseBVarsBounded k = true) :
    (litToCtorIfNat env e).looseBVarsBounded k = true := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · exact natLitToConstructor_looseBVars n
    · exact hb
  | .lit (.strVal _) => exact hb
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ =>
    exact hb

/-- Unfolding a definition at the head only shrinks the leaf
closure. -/
theorem unfoldDefinition_fvarLeaves {env : Env} (henv : EnvWF env)
    {e e₂ : Expr} (h : unfoldDefinition env e = some e₂) :
    ∀ l ∈ e₂.fvarLeaves, l ∈ e.fvarLeaves := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    intro l hl
    obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
    obtain ⟨hvc, -, -, -⟩ := hval cv value hint rfl
    rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar
        (by rw [hasFvar_instantiateLevelParams]; exact hvc)] at hl'
      cases hl'
    · exact fvarLeaves_getAppArgs hx l hlx
  · intro h; exact nomatch h

/-- Unfolding a definition at the head preserves the bvar bound. -/
theorem unfoldDefinition_looseBVars {env : Env} (henv : EnvWF env)
    {e e₂ : Expr} (h : unfoldDefinition env e = some e₂)
    (hb : e.looseBVarsBounded 0 = true) :
    e₂.looseBVarsBounded 0 = true := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
    obtain ⟨-, -, -, hvb⟩ := hval cv value hint rfl
    refine looseBVarsBounded_mkAppN ?_ ?_
    · rw [looseBVarsBounded_instantiateLevelParams]
      exact hvb
    · intro x hx
      exact looseBVarsBounded_getAppArgs hb x hx
  · intro h; exact nomatch h

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop only shrink the leaf
closure. -/
theorem whnfPres_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {d : Nat} {e e' : Expr}, whnfCore mode env fuel d e = .ok e' →
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode env fuel d e = .ok e' →
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves)
  | 0 => ⟨(fun {_ _ _} h => nomatch h), (fun {_ _ _} h => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_fvarLeaves henv fuel
    constructor
    · -- whnfCore
      intro d e e' h
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | fvar idx ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | forallE ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | lam ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | lit l0 =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE tt vv bb =>
        -- task #241: the ζ arm is a positive `.internal` error
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | app f a =>
        intro l hl
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        simp only [fvarLeaves, List.mem_append]
        rcases hcase with ⟨ty, body, mm, rfl, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · have hl' := ihCore hbeta l hl
          rcases fvarLeaves_instantiate1 body 0 hl' with hb | hb
          · exact Or.inl (ihCore hwf l (by simp [fvarLeaves, hb]))
          · exact Or.inr hb
        · -- iota step
          obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj,
            cvj, cnP, cnF, r, hfn, hfc, hlen, -, hprep,
            hmfn, hfj,
            hrule,
            hml, -, hlev, hpeq, hcerts, hmcerts, -, rfl⟩ :=
            iotaRec_inv hio
          -- the major's leaves are the argument's, through the chain in
          -- either order
          have hsubM : ∀ l ∈ major.fvarLeaves,
              l ∈ ((Expr.app f' a).getAppArgs.getD mI (.bvar 0)).fvarLeaves :=
            prepareMajorFueled_ind hprep
              (fun x => ∀ l ∈ x.fvarLeaves,
                l ∈ ((Expr.app f' a).getAppArgs.getD mI (.bvar 0)).fvarLeaves)
              (fun hw' hP l' hl' => hP l' (ihLoop hw' l' hl'))
              (fun hl hP l' hl' => by
                rcases litMajorToCtorFueled_inv hl with rfl | ⟨s, -, -, hred⟩
                · exact hP l' (litToCtorIfNat_fvarLeaves l' hl')
                · have h0 := ihLoop hred l' hl'
                  rw [strLitToConstructor_fvarLeaves] at h0
                  cases h0)
              (fun hs hP l' hl' => by
                rcases majorToCtor_inv hs with rfl | ⟨-, -, hall, -⟩
                · exact hP l' hl'
                · have := List.all_eq_true.mp hall l' hl'
                  exact hP l' (by simpa using this))
              (fun l' hl' => hl')
          have hl2 := ihCore hwe'' l hl
          rcases fvarLeaves_mkAppN hl2 with hrl | ⟨x, hx, hlx⟩
          · obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
            obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl r
              (List.mem_of_find?_eq_some hrule)
            rw [fvarLeaves_eq_nil_of_not_hasFvar
              (by rw [hasFvar_instantiateLevelParams]; exact hrf)] at hrl
            cases hrl
          · rcases List.mem_append.mp hx with hx | hx
            · have hll := fvarLeaves_getAppArgs (List.mem_of_mem_take hx)
                l hlx
              simp only [fvarLeaves, List.mem_append] at hll
              rcases hll with hll | hll
              · exact Or.inl (ihCore hwf l hll)
              · exact Or.inr hll
            · have hxa := fvarLeaves_getAppArgs (List.mem_of_mem_drop hx)
                l hlx
              have hmj := hsubM l hxa
              have hll := fvarLeaves_getAppArgs
                (getD_mem (l := (Expr.app f' a).getAppArgs) (by omega)) l hmj
              simp only [fvarLeaves, List.mem_append] at hll
              rcases hll with hll | hll
              · exact Or.inl (ihCore hwf l hll)
              · exact Or.inr hll
        · simp only [fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact Or.inl (ihCore hwf l hl)
          · exact Or.inr hl
      | proj sn i pe =>
        intro l hl
        obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
        have hsub₃ : ∀ l ∈ e₃.fvarLeaves, l ∈ e₂.fvarLeaves := by
          rcases projLitToCtorFueled_inv hlit with rfl | ⟨s, -, -, hred⟩
          · exact fun l hl => hl
          · intro l hl
            have := ihLoop hred l hl
            rw [strLitToConstructor_fvarLeaves] at this
            cases this
        simp only [fvarLeaves]
        rcases hcase with rfl |
          ⟨us, entry, hfn, hf, hi, hlen, hus, -, hred, -⟩
        · simp only [fvarLeaves] at hl
          exact ihLoop he l (hsub₃ l hl)
        · have hl2 := ihCore hred l hl
          exact ihLoop he l (hsub₃ l
            (fvarLeaves_getAppArgs (getD_mem (by omega)) l hl2))
    · -- whnf loop: induction on the loop's own step budget (task #106)
      have hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr},
          whnfLoop (pureFns mode env fuel) env d n e = .ok e' →
          ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves := by
        intro n
        induction n with
        | zero => intro _ _ _ h _ _; exact nomatch h
        | succ n ihN =>
          intro d e e' h l hl
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
          · rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
            · have := ihN hcont l hl
              simp [Expr.fvarLeaves] at this
          · exact ihCore hwc l
              (unfoldDefinition_fvarLeaves henv hu l (ihN hcont l hl))
          · exact ihCore hwc l hl
      intro d e e' h l hl
      exact hloop whnfLoopFuel h l hl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop preserve the bvar
bound. -/
theorem whnfPres_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {d : Nat} {e e' : Expr}, whnfCore mode env fuel d e = .ok e' →
        e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode env fuel d e = .ok e' →
        e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true)
  | 0 => ⟨(fun {_ _ _} h _ => nomatch h), (fun {_ _ _} h _ => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_looseBVars henv fuel
    constructor
    · -- whnfCore
      intro d e e' h hb
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | fvar idx ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | forallE ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | lam ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | lit l0 =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE tt vv bb =>
        -- task #241: the ζ arm is a positive `.internal` error
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | app f a =>
        simp only [looseBVarsBounded, Bool.and_eq_true] at hb
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        have hbf' := ihCore hwf hb.1
        rcases hcase with ⟨ty, body, mm, rfl, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · simp only [looseBVarsBounded, Bool.and_eq_true] at hbf'
          exact ihCore hbeta
            (looseBVarsBounded_instantiate1_gen hb.2 hbf'.2)
        · -- iota step
          obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj,
            cvj, cnP, cnF, r, hfn, hfc, hlen, -, hprep,
            hmfn, hfj,
            hrule,
            hml, -, hlev, hpeq, hcerts, hmcerts, -, rfl⟩ :=
            iotaRec_inv hio
          have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
            simp only [looseBVarsBounded, Bool.and_eq_true]
            exact ⟨hbf', hb.2⟩
          -- the major's bound variables, through the chain in either order
          have hbmaj : major.looseBVarsBounded 0 = true :=
            prepareMajorFueled_ind hprep (fun x => x.looseBVarsBounded 0 = true)
              (fun hw' hb' => ihLoop hw' hb')
              (fun hl hb' => by
                rcases litMajorToCtorFueled_inv hl with rfl | ⟨s, -, -, hred⟩
                · exact litToCtorIfNat_looseBVars hb'
                · exact ihLoop hred (strLitToConstructor_looseBVars s 0))
              (fun hs hb' => by
                rcases majorToCtor_inv hs with rfl | ⟨-, hbM, -, -⟩
                · exact hb'
                · exact hbM)
              (looseBVarsBounded_getAppArgs hbapp _ (getD_mem (by omega)))
          refine ihCore hwe'' ?_
          refine looseBVarsBounded_mkAppN ?_ ?_
          · obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
            obtain ⟨-, -, -, hrb, -⟩ := hrules cv mI rP rules rfl r
              (List.mem_of_find?_eq_some hrule)
            rw [looseBVarsBounded_instantiateLevelParams]
            exact hrb
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact looseBVarsBounded_getAppArgs hbapp _
                (List.mem_of_mem_take hx)
            · exact looseBVarsBounded_getAppArgs hbmaj _
                (List.mem_of_mem_drop hx)
        · simp only [looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hbf', hb.2⟩
      | proj sn i pe =>
        simp only [looseBVarsBounded] at hb
        obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
        have hbe₂ := ihLoop he hb
        have hbe₃ : e₃.looseBVarsBounded 0 = true := by
          rcases projLitToCtorFueled_inv hlit with rfl | ⟨s, -, -, hred⟩
          · exact hbe₂
          · exact ihLoop hred (strLitToConstructor_looseBVars s 0)
        rcases hcase with rfl |
          ⟨us, entry, hfn, hf, hi, hlen, hus, -, hred, -⟩
        · simpa [looseBVarsBounded] using hbe₃
        · exact ihCore hred
            (looseBVarsBounded_getAppArgs hbe₃ _ (getD_mem (by omega)))
    · -- whnf loop: induction on the loop's own step budget (task #106)
      have hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr},
          whnfLoop (pureFns mode env fuel) env d n e = .ok e' →
          e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true := by
        intro n
        induction n with
        | zero => intro _ _ _ h _; exact nomatch h
        | succ n ihN =>
          intro d e e' h hb
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          have hbe₁ := ihCore hwc hb
          rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
          · rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
              exact ihN hcont (by simp [looseBVarsBounded])
          · exact ihN hcont (unfoldDefinition_looseBVars henv hu hbe₁)
          · exact hbe₁
      intro d e e' h hb
      exact hloop whnfLoopFuel h hb

/-- Head normalization only shrinks the leaf closure. -/
theorem whnfCore_fvarLeaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnfCore mode env fuel d e = .ok e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  (whnfPres_fvarLeaves henv fuel).1 h

/-- The reduction loop only shrinks the leaf closure. -/
theorem whnf_fvarLeaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf mode env fuel d e = .ok e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  (whnfPres_fvarLeaves henv fuel).2 h

/-- Head normalization preserves the bvar bound. -/
theorem whnfCore_looseBVars {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnfCore mode env fuel d e = .ok e')
    (hb : e.looseBVarsBounded 0 = true) : e'.looseBVarsBounded 0 = true :=
  (whnfPres_looseBVars henv fuel).1 h hb

/-- The reduction loop preserves the bvar bound. -/
theorem whnf_looseBVars {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf mode env fuel d e = .ok e')
    (hb : e.looseBVarsBounded 0 = true) : e'.looseBVarsBounded 0 = true :=
  (whnfPres_looseBVars henv fuel).2 h hb

/-! ## Preservation through `inferTypeCore` -/

theorem inferTypeCore_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore mode env fuel d e = .ok t → WScoped d e → WScoped d t
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [WScoped]
    | fvar idx ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, pure,
        Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        simp only [WScoped] at hw
        exact hw.2.mono (by omega)
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          revert h
          split
          · intro h
            simp only [Except.ok.injEq] at h
            subst h
            obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
            exact WScoped.of_not_hasFvar
              (by rw [hasFvar_instantiateLevelParams]; exact htc)
          · intro h; exact nomatch h
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [WScoped]
      case natCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [WScoped]
    | forallE ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ :=
        inferTypeCore_forall_inv h
      simp [WScoped]
    | lam ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCore_WScoped henv fuel hbt hwo
      simp only [WScoped]
      exact ⟨hw.1, WScoped.abstract1 0 hwbt⟩
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      have hwtf := inferTypeCore_WScoped henv fuel htf hw.1
      have hwPi := whnf_WScoped henv fuel hwh hwtf
      simp only [WScoped] at hwPi
      exact WScoped.instantiate1_gen hw.2 0 hwPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCore_proj_inv h
      simp only [WScoped] at hw
      have hwte := inferTypeCore_WScoped henv fuel hte hw
      have hwPi := whnf_WScoped henv fuel hwt hwte
      -- task #175 S1: the body at the spine and the subject — the
      -- stored body is fvar-free and the spine and subject are scoped
      exact projEntry_typeAt_WScoped henv hfp us hlen
        (fun a ha => hwPi.getAppArgs a ha) hw
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCore_letE_inv h).elim

theorem inferTypeCore_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore mode env fuel d e = .ok t → WScoped d e →
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, pure, Except.pure, Except.ok.injEq] at h
      subst h; intro l hl; simp [fvarLeaves] at hl
    | fvar idx ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, pure,
        Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        intro l hl
        simp [fvarLeaves, hl]
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          revert h
          split
          · intro h
            simp only [Except.ok.injEq] at h
            subst h
            obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
            intro l hl
            rw [fvarLeaves_eq_nil_of_not_hasFvar
              (by rw [hasFvar_instantiateLevelParams]; exact htc)] at hl
            cases hl
          · intro h; exact nomatch h
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; intro l hl; simp [fvarLeaves] at hl
      case natCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; intro l hl; simp [fvarLeaves] at hl
    | forallE ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ :=
        inferTypeCore_forall_inv h
      intro l hl
      simp [fvarLeaves] at hl
    | lam ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCore_WScoped henv fuel hbt hwo
      intro l hl
      simp only [fvarLeaves, List.mem_append] at hl ⊢
      rcases hl with hl | hl
      · exact Or.inl hl
      · obtain ⟨hlbt, hlne⟩ := fvarLeaves_abstract1_ne bt 0 hwbt l hl
        have hlo := inferTypeCore_fvarLeaves henv fuel hbt hwo l hlbt
        rcases fvarLeaves_instantiate1 body 0 hlo with hb | hb
        · exact Or.inr hb
        · simp only [fvarLeaves, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd rfl hlne
          · exact Or.inl hb
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves, List.mem_append]
      rcases fvarLeaves_instantiate1 body' 0 hl with hb | hb
      · refine Or.inl (inferTypeCore_fvarLeaves henv fuel htf hw.1 l ?_)
        refine whnf_fvarLeaves henv fuel hwh l ?_
        simp [fvarLeaves, hb]
      · exact Or.inr hb
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCore_proj_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves]
      have hsub : ∀ l', l' ∈ te.fvarLeaves → l' ∈ pe.fvarLeaves :=
        fun l' hl' =>
        inferTypeCore_fvarLeaves henv fuel hte hw l'
          (whnf_fvarLeaves henv fuel hwt l' hl')
      -- task #175 S1: the body's leaves come from the spine or the
      -- subject (the stored body is fvar-free)
      rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe] at hl
      rcases fvarLeaves_instSpine _ hl with hty | ⟨a, ha, hla⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar
          (projEntry_body_hasFvar henv hfp us)] at hty
        exact nomatch hty
      · rcases List.mem_append.mp ha with ha | ha
        · exact hsub l (fvarLeaves_getAppArgs ha l hla)
        · rcases List.mem_singleton.mp ha with rfl
          exact hla
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCore_letE_inv h).elim

theorem inferTypeCore_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore mode env fuel d e = .ok t → WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      t.looseBVarsBounded 0 = true
  | 0, d, e, t, h, _, _, _ => nomatch h
  | fuel + 1, d, e, t, h, hw, hb, hLb => by
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [looseBVarsBounded]
    | fvar idx ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, pure,
        Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        exact hLb (idx, ty) (by simp [fvarLeaves])
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          revert h
          split
          · intro h
            simp only [Except.ok.injEq] at h
            subst h
            obtain ⟨-, -, -, htb, -⟩ := henv _ (find?_mem hf)
            rw [looseBVarsBounded_instantiateLevelParams]
            exact htb
          · intro h; exact nomatch h
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [looseBVarsBounded]
      case natCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [looseBVarsBounded]
    | forallE ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ :=
        inferTypeCore_forall_inv h
      simp [looseBVarsBounded]
    | lam ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
        hw.1.instantiate1 0 hw.2
      have hbo : (body.instantiate1 (.fvar d ty)).looseBVarsBounded 0
          = true := looseBVarsBounded_instantiate1 body 0 hb.2
      have hLbo : Expr.LeavesBounded (body.instantiate1 (.fvar d ty)) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
        · exact hLb l (by simp [fvarLeaves, hb'])
        · simp only [fvarLeaves, List.mem_cons] at hb'
          rcases hb' with rfl | hb'
          · exact hb.1
          · exact hLb l (by simp [fvarLeaves, hb'])
      have hbbt := inferTypeCore_looseBVars henv fuel hbt hwo hbo hLbo
      simp only [looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 bt 0 hbbt⟩
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hLbf : Expr.LeavesBounded f := fun l hl =>
        hLb l (by simp [fvarLeaves, hl])
      have hbtf := inferTypeCore_looseBVars henv fuel htf hw.1 hb.1 hLbf
      have hbPi := whnf_looseBVars henv fuel hwh hbtf
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      exact looseBVarsBounded_instantiate1_gen hb.2 hbPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCore_proj_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded] at hb
      have hLbe : Expr.LeavesBounded pe := fun l hl => hLb l (by
        simp only [fvarLeaves]; exact hl)
      have hbte := inferTypeCore_looseBVars henv fuel hte hw hb hLbe
      have hbPi := whnf_looseBVars henv fuel hwt hbte
      -- task #175 S1: the body at bvar-closed arguments is bvar-closed
      exact projEntry_typeAt_looseBVars henv hfp us hlen
        (fun a ha => looseBVarsBounded_getAppArgs hbPi _ ha) hb
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCore_letE_inv h).elim

end ConLeche
