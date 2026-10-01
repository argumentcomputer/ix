module

public import ConLeche.Verify.Denote

public section

/-!
# Denotation across level-preserving environment correspondences

Relocated verbatim from `ConLeche/TTVerify/EnvSwap.lean` (task #148, T5):
the denotation reads the environment only through the stored level
parameters and the two literal guards, so it is invariant across any
correspondence preserving those — the workhorse of the recursor-group
swap in both verification lanes.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- The stored level parameters only read the constant's
level-parameter slot. -/
theorem levelParamsAt_ext {env₁ env₂ : Env} {n : Name}
    (h : (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams)) :
    levelParamsAt env₁ n = levelParamsAt env₂ n := by
  unfold levelParamsAt
  cases h1 : env₁.find? n <;> cases h2 : env₂.find? n <;>
    rw [h1, h2] at h <;> simp at h ⊢ <;> exact h

/-- **Denotation reads the environment only through the stored level
parameters and the two literal guards.**  Transpose of
`interp_env_ext`; the swap's workhorse.  An equation, so a law's
denote *hypotheses* and *conclusions* both move across it for free —
which is what makes the fired-form fields transportable at all. -/
theorem denote_env_ext {cval : TConstVal} {env₁ env₂ : Env}
    {φ : Name → Nat}
    (henvLev : ∀ n,
      (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported env₁ = natLitSupported env₂)
    (hstr : strLitSupported env₁ = strLitSupported env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = env₂.findProj? sn i) :
    ∀ (d : Nat) (e : Expr),
      denote cval env₁ φ d e = denote cval env₂ φ d e := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env₁) (φ := φ) with
  | case1 d u => simp only [denote_sort]
  | case2 d idx ty => simp only [denote_fvar]
  | case3 d n us ci h1 h2 =>
    have h := henvLev n
    rw [h1] at h
    cases h2' : env₂.find? n with
    | none => rw [h2'] at h; exact nomatch h
    | some ci₂ =>
      rw [h2'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [denote_const, h1, h2', ← h, if_pos h2]
  | case4 d n us ci h1 h2 =>
    have h := henvLev n
    rw [h1] at h
    cases h2' : env₂.find? n with
    | none => rw [h2'] at h; exact nomatch h
    | some ci₂ =>
      rw [h2'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [denote_const, h1, h2', ← h, if_neg h2]
  | case5 d n us h1 =>
    have h := henvLev n
    rw [h1] at h
    cases h2' : env₂.find? n with
    | none => simp only [denote_const, h1, h2']
    | some ci₂ => rw [h2'] at h; exact nomatch h
  | case6 d ty body mb h1 ihty =>
    simp only [denote_forallE, ← ihty, h1]
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_forallE, ← ihty, ← ihbody, h1, h2]
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_forallE, ← ihty, ← ihbody, h1, h2]
  | case9 d ty body mb h1 ihty => simp only [denote_lam, ← ihty, h1]
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_lam, ← ihty, ← ihbody, h1, h2]
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_lam, ← ihty, ← ihbody, h1, h2]
  | case12 d f a vf va h1 h2 ihf iha =>
    simp only [denote_app, ← ihf, ← iha]
  | case13 d f a hbad ihf iha => simp only [denote_app, ← ihf, ← iha]
  | case14 d ty val body =>
    simp only [denote_letE]
  | case15 d sn i e h1 ihe => simp only [denote_proj, ← ihe, hproj sn i]
  | case16 d sn i e B h1 entry h2 ihe =>
    simp only [denote_proj, ← ihe, hproj sn i]
  | case17 d sn i e B h1 h2 ihe =>
    simp only [denote_proj, ← ihe, hproj sn i]
  | case18 d n _ | case19 d n _ =>
    simp only [denote_natLit, hnat]
  | case20 d s _ | case21 d s _ =>
    simp only [denote_strLit, hstr]
    by_cases hg2 : strLitSupported env₂ = true
    · rw [if_pos hg2, if_pos hg2, strLitT, strLitT,
        levelParamsAt_ext (henvLev listNilName),
        levelParamsAt_ext (henvLev listConsName)]
    · simp [hg2]
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    match x with
    | .bvar i => simp only [denote_bvar]
    | .sort u => exact (k1 u rfl).elim
    | .fvar a c => exact (k2 a c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE b c dd => exact (k4 b c dd rfl).elim
    | .lam b c dd => exact (k5 b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE b c dd => exact (k7 b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-! ## The swap relation -/


end ConLeche.Verify
