module

public import ConLeche.Model.Annot.BitInstall
public import ConLeche.Semantics.ConstsBound

public section

/-!
# `denoteMeta` across an environment extension (task #161, P3.2)

The mirror of `Denote2EnvExtend` (`Interp/Keys2.lean`) and its
discharge `denote2_envExtend` (`Interp/Denote2Extend.lean`) — and the
place where the P3 pivot pays out most visibly.

**`SortAgree` is deleted.**  `denote2_envExtend` takes three premises:
`FindPreserved` (the `.const` clause and the string spine's
`levelParamsAt`), `LitGuardsAgree` (the two literal guards), and
`SortAgree` — "`sortOfE` and `lamSortE` agree at `env₀` and `env`",
itself a composition of `EnvExtendStable`, `EnvExtendReflect` and
`InferOutputBound` (`sortAgree_of`), i.e. three *open* checker
metatheorems.  It is used at exactly three rewrites, all inside the
`∀` and `λ` clauses (`hS.1 hc.1`, `hS.1 hcb`, `hS.2 hcb`).

`denoteMeta`'s binder numeral is `pwBit φ mb.pw`: a function of the
term's own validated meta and the valuation `φ`, mentioning no
environment at all.  So those three rewrites have no mirror and no
residue — the binder clauses close on the two induction hypotheses
alone, exactly like `.app`.  The two kept premises are the ones the
*reading itself* needs: `denoteMeta` consults `env` only through
`find?` and the two support guards.

That is the whole Θ-residue for this key, gone by construction rather
than by discharge.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **`denoteMeta` is stable under environment extension**, stated.
`Denote2EnvExtend` with the fuel and mode indices deleted.

An **equation**, not an implication, for the reason the original is
one: an install must not be able to assume silently that an
annotation exists on one side and not the other. -/
@[expose] def DenotePEnvExtend (env₀ env : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
    denoteMeta acval env₀ φ d e = denoteMeta acval env φ d e

/-- **`DenotePEnvExtend`, discharged** — from `FindPreserved` and
`LitGuardsAgree` alone.  See the module docstring for the dropped
`SortAgree`. -/
theorem denoteMeta_envExtend {env₀ env : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsAgree env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₀.findProj? sn i = none → env.findProj? sn i = none) :
    DenotePEnvExtend env₀ env acval φ := by
  -- a preserved lookup carries its entry across unchanged
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₀) with
  | case1 d u => intro _; rw [denoteMeta, denoteMeta]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    intro _
    rw [denoteMeta, hf, denoteMeta, hF hf]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteMeta, hf, denoteMeta, hF hf]
  | case5 d n us hf =>
    intro hc
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d ty body m ihty ihbody =>
    intro hc
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denoteMeta, denoteMeta, ihty hc.1, ihbody hcb]
  | case7 d ty body m ihty ihbody =>
    intro hc
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denoteMeta, denoteMeta, ihty hc.1, ihbody hcb]
  | case8 d f a ihf iha =>
    intro hc
    rw [constsBound_app] at hc
    rw [denoteMeta, denoteMeta, ihf hc.1, iha hc.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hc
    rw [constsBound_proj] at hc
    rw [denoteMeta, denoteMeta, ihe hc]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some ea =>
      show (match env₀.findProj? sn i with
          | some entry => some (projAV (i + entry.off) ea)
          | none => AnnotTerm.projPair? i ea)
        = (match env.findProj? sn i with
          | some entry => some (projAV (i + entry.off) ea)
          | none => AnnotTerm.projPair? i ea)
      cases hfp0 : env₀.findProj? sn i with
      | some entry => rw [hmono sn i entry hfp0]
      | none => rw [hproj sn i hfp0]
  | case11 d n hsup =>
    intro _
    rw [denoteMeta, if_pos hsup, denoteMeta, if_pos (hG.1 ▸ hsup)]
  | case12 d n hsup =>
    intro _
    rw [denoteMeta, if_neg hsup, denoteMeta,
      if_neg (fun h => hsup (hG.1.trans h))]
  | case13 d s hsup =>
    intro _
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteMeta, if_pos hsup, denoteMeta, if_pos (hG.2 ▸ hsup),
      levelParamsAt_congr hF hnil, levelParamsAt_congr hF hcons]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, if_neg hsup, denoteMeta,
      if_neg (fun h => hsup (hG.2.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The monotone crossing (task #161, the literal tier's opening)

`LitGuardsAgree` — the guard *equality* — is refutable at a
support-completing install (a pinned-type `def` named `String.ofList`
flips `strLitSupported` upward, and nothing forbids the name).  The
fold therefore rides the **monotone** crossing below: literal guards
only ever gain under a fresh cons (`natLitSupported_cons`/
`strLitSupported_cons`), and a *successful* prefix reading transfers
forward — which is the only direction the harvests use for their
subjects, whose acceptance guaranteed prefix-supported literals. -/

/-- The literal guards are monotone across the extension. -/
@[expose] def LitGuardsMono (env₀ env : Env) : Prop :=
  (natLitSupported env₀ = true → natLitSupported env = true) ∧
  (strLitSupported env₀ = true → strLitSupported env = true)

/-- Free at every fresh cons, of any kind. -/
theorem litGuardsMono_cons {env : Env} {c₀ : ConLeche.ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    LitGuardsMono env ⟨c₀ :: env.consts⟩ :=
  ⟨natLitSupported_cons hfresh, strLitSupported_cons hfresh⟩

/-- **The monotone crossing**: a successful prefix reading is
reproduced verbatim at the extension. -/
theorem denoteMeta_envExtend_mono {env₀ env : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₀.findProj? sn i = none → env.findProj? sn i = none) :
    ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
      ∀ {ea : AnnotTerm}, denoteMeta acval env₀ φ d e = some ea →
        denoteMeta acval env φ d e = some ea := by
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₀) with
  | case1 d u => intro _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case2 d idx ty => intro _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ ea h
    rw [denoteMeta, hf] at h
    rw [denoteMeta, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro hc ea h
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d ty body m ihty ihbody =>
    intro hc ea h
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    rw [denoteMeta, ihty hc.1 hta, ihbody hcb hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro hc ea h
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    rw [denoteMeta, ihty hc.1 hta, ihbody hcb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc ea h
    rw [constsBound_app] at hc
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    rw [denoteMeta, ihf hc.1 hfa, iha hc.2 haa]
    rfl
  | case9 d ty val body =>
    intro _ ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hc ea h
    rw [constsBound_proj] at hc
    obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
    rcases hcase with ⟨entry, hfp0, rfl⟩ | ⟨hnt0, hdec⟩
    · -- a table entry at the prefix persists unchanged
      rw [denoteMeta, ihe hc hea', hmono sn i entry hfp0]
      rfl
    · -- the table-free path: the extension adds no entry either
      rw [denoteMeta, ihe hc hea', hproj sn i hnt0]
      exact hdec
  | case11 d n hsup =>
    intro _ ea h
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Model
