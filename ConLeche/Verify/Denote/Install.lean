module

import ConLeche.Verify.Denote
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.EnvGuards
import ConLeche.Verify.EnvPreds
public import ConLeche.Verify.Denote.Pinned
public import ConLeche.Verify.Denote.Levels

public section

/-!
# Denotations survive environment extension — the install transport core

Relocated verbatim from `ConLeche/TTVerify/Extend.lean` (task #148, T5;
the same move T3 made for `ConLeche/Verify/Denote/Levels.lean`): the
environment-extension transport machinery for `denote` is `V`-free and
lane-independent — both the TT lane (`EnvTT`'s field transports) and
the [set] lane (`EnvS`'s, task #148 T5) consume it — so it lives where
both can import it.  Statements unchanged; the namespace stays
`ConLeche.Verify` so no call site moves.

Contents: `EnvExtends` + `denote_mono` (denotations survive a larger
environment), `denote_cval_congr` (and a changed valuation),
`LitAgree`, the literal-guard congruence/monotonicity family,
`denote_env_shrink` / `denote_install` (the backwards direction), the
`Installs` bundle, the two `V`-free field transports
(`BasisPinnedTT.cons`, `ProjOkT.cons`), and `cvalAt` (the valuation an
ordinary value-carrying install chooses).  The TT-specific transports
(`has_type_cons`, `RecRulesTT.cons`, …) remain in
`ConLeche/TTVerify/Extend.lean`.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- `env₂` extends `env₁`: every constant stored in `env₁` is stored in
`env₂`, unchanged.  (The checker's installs are cons-extensions with a
freshness check, so this always holds of them; stating it as a relation
keeps the lemma independent of *how* the extension arose, exactly as
`EnvModel`'s transports are.) -/
def EnvExtends (env₁ env₂ : Env) : Prop :=
  ∀ n ci, env₁.find? n = some ci → env₂.find? n = some ci

theorem EnvExtends.refl (env : Env) : EnvExtends env env := fun _ _ h => h

theorem EnvExtends.trans {e₁ e₂ e₃ : Env} (h₁ : EnvExtends e₁ e₂)
    (h₂ : EnvExtends e₂ e₃) : EnvExtends e₁ e₃ :=
  fun n ci h => h₂ n ci (h₁ n ci h)

/-- A cons-extension over a fresh name extends. -/
theorem EnvExtends.cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    EnvExtends env ⟨c₀ :: env.consts⟩ := by
  intro n ci h
  rw [Env.find?_cons]
  split
  · next hn =>
    rw [← hn, hfresh] at h
    exact nomatch h
  · exact h

/-- `findProj?` transports up an extension (a table is stored under a
name; `hext` carries the lookup). -/
theorem EnvExtends.findProj?_mono {env₁ env₂ : Env}
    (hext : EnvExtends env₁ env₂) {sn : Name} {i : Nat}
    {entry : ProjEntry} (h : env₁.findProj? sn i = some entry) :
    env₂.findProj? sn i = some entry := by
  obtain ⟨tbl, h0, hi, rfl⟩ := Env.findProj?_some h
  exact Env.findProj?_of_table (hext _ _ h0) hi

/-- A fresh cons that is not a projection table cannot create a table
lookup where none existed. -/
theorem findProj?_cons_of_base_none {env : Env} {c₀ : ConstantInfo}
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl) :
    ∀ (sn : Name) (i : Nat),
      env.findProj? sn i = none →
      Env.findProj? ⟨c₀ :: env.consts⟩ sn i = none := by
  intro sn i h0
  by_cases hn : c₀.name = projTableName sn
  · have hf : (⟨c₀ :: env.consts⟩ : Env).find? (projTableName sn) = some c₀ := by
      rw [Env.find?_cons, if_pos hn]
    unfold Env.findProj?
    rw [hf]
    cases c₀ <;> first | rfl | exact absurd rfl (hntc _)
  · rw [Env.findProj?_cons_ne hn]; exact h0

/-- **Denotations survive extension.**

The literal guards and the stored level-parameter lists are hypotheses
rather than consequences, and the reason is worth stating so that the
next person does not take them for a gap.  They *are* consequences of
`hext`: a guard that held in `env₁` forced its slots to be stored
there, `hext` carries those lookups over unchanged, and the guard reads
nothing else — that derivation is `natLitSupported_inv` +
`natLitSupported_congr` (and the `strLit` pair) of
`ConLeche/Verify/EnvGuards.lean`.  They are passed in rather than
derived here so that the install sites, which have the freshness facts
in hand, discharge them the cheap way. -/
theorem denote_mono {cval : TConstVal} {env₁ env₂ : Env} {φ : Name → Nat}
    (hext : EnvExtends env₁ env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = none → env₂.findProj? sn i = none)
    (hnat : natLitSupported env₁ = true → natLitSupported env₂ = true)
    (hstr : strLitSupported env₁ = true → strLitSupported env₂ = true)
    (hlpNil : strLitSupported env₁ = true →
      levelParamsAt env₂ listNilName = levelParamsAt env₁ listNilName)
    (hlpCons : strLitSupported env₁ = true →
      levelParamsAt env₂ listConsName = levelParamsAt env₁ listConsName) :
    ∀ (d : Nat) (e : Expr) {v : Term},
      denote cval env₁ φ d e = some v → denote cval env₂ φ d e = some v := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env₁) (φ := φ) with
  | case1 d u => intro v h; rw [denote_sort] at h ⊢; exact h
  | case2 d idx ty => intro v h; rw [denote_fvar] at h ⊢; exact h
  | case3 d n us ci h1 h2 =>
    intro v h
    simp only [denote_const, h1, if_pos h2] at h
    simp only [denote_const, hext n ci h1, if_pos h2]
    exact h
  | case4 d n us ci h1 h2 =>
    intro v h
    simp only [denote_const, h1, if_neg h2] at h
    exact nomatch h
  | case5 d n us h1 =>
    intro v h
    rw [denote_const, h1] at h
    exact nomatch h
  | case6 d ty body mb h1 ihty =>
    intro v h
    rw [denote_forallE, h1] at h
    exact nomatch h
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    intro v h
    rw [denote_forallE, h1, h2] at h
    exact nomatch h
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    intro v h
    rw [denote_forallE, h1, h2] at h
    rw [denote_forallE, ihty h1, ihbody h2]
    exact h
  | case9 d ty body mb h1 ihty =>
    intro v h
    rw [denote_lam, h1] at h
    exact nomatch h
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    intro v h
    rw [denote_lam, h1, h2] at h
    exact nomatch h
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    intro v h
    rw [denote_lam, h1, h2] at h
    rw [denote_lam, ihty h1, ihbody h2]
    exact h
  | case12 d f a vf va h1 h2 ihf iha =>
    intro v h
    rw [denote_app, h1, h2] at h
    rw [denote_app, ihf h2, iha h1]
    exact h
  | case13 d f a hbad ihf iha =>
    intro v h
    rw [denote_app] at h
    split at h
    · next vf va h1 h2 => exact (hbad vf va h1 h2).elim
    · exact nomatch h
  | case14 d ty val body =>
    intro v h
    rw [denote_letE] at h
    exact nomatch h
  | case15 d sn i e h1 ihe =>
    intro v h
    rw [denote_proj, h1] at h
    exact nomatch h
  | case16 d sn i e B h1 entry h2 ihe =>
    intro v h
    rw [denote_proj, h1, h2] at h
    rw [denote_proj, ihe h1, hext.findProj?_mono h2]
    exact h
  | case17 d sn i e B h1 h2 ihe =>
    intro v h
    rw [denote_proj, h1, h2] at h
    rw [denote_proj, ihe h1, hproj sn i h2]
    exact h
  | case18 d n hg =>
    intro v h
    rw [denote_natLit, if_pos hg] at h
    rw [denote_natLit, if_pos (hnat hg)]
    exact h
  | case19 d n hg =>
    intro v h
    rw [denote_natLit, if_neg hg] at h
    exact nomatch h
  | case20 d s hg =>
    intro v h
    rw [denote_strLit, if_pos hg] at h
    rw [denote_strLit, if_pos (hstr hg), strLitT, hlpNil hg, hlpCons hg]
    exact h
  | case21 d s hg =>
    intro v h
    rw [denote_strLit, if_neg hg] at h
    exact nomatch h
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro v h
    match x with
    | .bvar i => rw [denote_bvar] at h; exact nomatch h
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


/-! ## Changing the valuation at a fresh name

**Read this together with `denote_mono` above: they are two halves of
one fact**, and a reader meeting either alone would not see it —

> *Installing a fresh constant disturbs no existing denotation.*

`denote_mono` moves a denotation to a **larger environment**;
`denote_cval_congr` moves it to a **changed valuation**.  An install
does both at once, so every case of `CheckDeclTT` uses both, and
neither alone says anything reassuring.

The companion to `denote_mono`, and the other half of what every
install case needs.  `denote_mono` moves a denotation to a **larger
environment**; this moves it to a **changed valuation** — which is what
happens when a declaration installs, since the new constant's value has
to be added to `cval`.

Together they say the obvious thing precisely: *installing a fresh
constant disturbs no existing denotation.*  The freshness is what makes
the hypothesis dischargeable — an old term's constants all resolve in
the old environment, and the new name is not among them.

The literal-support agreements are named **one by one** — the seven
names `natLitT` and `strLitT` actually read — rather than as a blanket
"the valuations agree".  A blanket hypothesis would make the lemma
*trivially true and useless*.

**The failure mode, and how it relates to the ease-of-proof signal of
DESIGN.md's "House practices".**  A statement can typecheck, prove,
and be worth nothing because a hypothesis subsumes its conclusion — and
unlike a *wrong* statement it leaves no trace, since everything
downstream still compiles.  The practice says a proof going through without
adaptation is evidence the statement has the right shape.  Both are
true, and they are **ordered, not in tension**:

> **First check the hypotheses are weaker than the conclusion; then
> take ease of proof as evidence.**  Ease is confirmation of a
> statement already established to be non-vacuous, never a substitute
> for establishing it.

So a suspiciously easy proof is not a reason to distrust the ease — it
is a reason to go and read the hypotheses.  **The tell to look for is a
hypothesis quantified more broadly than the conclusion needs**: here,
"the valuations agree *everywhere*" where exactly seven names are read.
Listing the seven is the fix.

They are hypotheses for the same reason they are in `denote_mono`:
deriving them from the guards needs `natLitSupported_inv`
(`ConLeche/Verify/EnvGuards.lean`), while the install sites discharge
them from freshness directly. -/

/-- Denotation reads the valuation only at names the environment
resolves, so valuations agreeing there give equal denotations. -/
theorem denote_cval_congr {cval₁ cval₂ : TConstVal} {env : Env}
    {φ : Name → Nat}
    (hag : ∀ n ci, env.find? n = some ci → cval₁ n = cval₂ n)
    (hnat : natLitSupported env = true →
      cval₁ natZeroName = cval₂ natZeroName)
    (hsucc : natLitSupported env = true →
      cval₁ natSuccName = cval₂ natSuccName)
    (hsol : strLitSupported env = true →
      cval₁ stringOfListName = cval₂ stringOfListName)
    (hnil : strLitSupported env = true →
      cval₁ listNilName = cval₂ listNilName)
    (hcons : strLitSupported env = true →
      cval₁ listConsName = cval₂ listConsName)
    (hchar : strLitSupported env = true → cval₁ charName = cval₂ charName)
    (hofn : strLitSupported env = true →
      cval₁ charOfNatName = cval₂ charOfNatName) :
    ∀ (d : Nat) (e : Expr),
      denote cval₁ env φ d e = denote cval₂ env φ d e := by
  intro d e
  induction d, e using denote.induct (cval := cval₁) (env := env) (φ := φ) with
  | case1 d u => simp only [denote_sort]
  | case2 d idx ty => simp only [denote_fvar]
  | case3 d n us ci h1 h2 =>
    simp only [denote_const, h1, if_pos h2, hag n ci h1]
  | case4 d n us ci h1 h2 => simp only [denote_const, h1, if_neg h2]
  | case5 d n us h1 => simp only [denote_const, h1]
  | case6 d ty body mb h1 ihty =>
    simp only [denote_forallE, h1, ← ihty]
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_forallE, h1, h2, ← ihty, ← ihbody]
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_forallE, h1, h2, ← ihty, ← ihbody]
  | case9 d ty body mb h1 ihty => simp only [denote_lam, h1, ← ihty]
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_lam, h1, h2, ← ihty, ← ihbody]
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_lam, h1, h2, ← ihty, ← ihbody]
  | case12 d f a vf va h1 h2 ihf iha =>
    simp only [denote_app, h1, h2, ← ihf, ← iha]
  | case13 d f a hbad ihf iha => simp only [denote_app, ← ihf, ← iha]
  | case14 d ty val body =>
    simp only [denote_letE]
  | case15 d sn i e h1 ihe => simp only [denote_proj, h1, ← ihe]
  | case16 d sn i e B h1 entry h2 ihe =>
    simp only [denote_proj, h1, ← ihe]
  | case17 d sn i e B h1 h2 ihe =>
    simp only [denote_proj, h1, ← ihe]
  | case18 d n _ | case19 d n _ =>
    simp only [denote_natLit]
    by_cases hg2 : natLitSupported env = true
    · rw [if_pos hg2, if_pos hg2, hnat hg2, hsucc hg2]
    · simp [hg2]
  | case20 d s _ | case21 d s _ =>
    simp only [denote_strLit]
    by_cases hg2 : strLitSupported env = true
    · have hgN : natLitSupported env = true := by
        simp only [strLitSupported, Bool.and_eq_true] at hg2
        exact hg2.1.1.1.1.1.1.1
      rw [if_pos hg2, if_pos hg2, strLitT, strLitT, hnat hgN, hsucc hgN,
        hsol hg2, hnil hg2, hcons hg2, hchar hg2, hofn hg2]
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


/-! ## The install transport

What every case of `CheckDeclTT` does to the *old* constants: they must
still denote, and still be derivably of their types, in the extended
environment under the extended valuation.  Both transport lemmas above
fire here, which is the point of naming them a pair.

The valuation hypothesis is stated as "agrees away from the new name"
rather than "agrees where the environment resolves", because that form
is **discharged by freshness alone** — `List.find?_eq_none` turns
`hfresh` into name-distinctness for every stored constant, with no
appeal to well-formedness. -/

/-- The literal-support agreements, bundled.  Every install transport
needs the same seven, so they travel together rather than as seven
arguments each time.

Kept as a *structure of equations* rather than folded into the
"agrees away from the new name" hypothesis, because a basis install
changes exactly these valuations — see `has_type_cons`. -/
structure LitAgree (env : Env) (cval cval' : TConstVal) : Prop where
  nat : natLitSupported env = true →
    cval natZeroName = cval' natZeroName
  succ : natLitSupported env = true →
    cval natSuccName = cval' natSuccName
  sol : strLitSupported env = true →
    cval stringOfListName = cval' stringOfListName
  nil : strLitSupported env = true → cval listNilName = cval' listNilName
  cons : strLitSupported env = true →
    cval listConsName = cval' listConsName
  char : strLitSupported env = true → cval charName = cval' charName
  ofn : strLitSupported env = true →
    cval charOfNatName = cval' charOfNatName

/-- **An ordinary install gets all seven from freshness alone** — no
name disequalities.  §8.5 once more: the unconditional form was
over-strong and *unprovable* at a `def` named `List.nil`, which
nothing in `checkConstantVal` forbids (the string-support names are
pinned, not reserved).  The conditional form is what the consumer
actually needs: `denote`'s literal clauses fire only under the guard,
and under the guard every one of the seven is **stored**, hence not the
fresh name. -/
theorem LitAgree.of_fresh {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n) :
    LitAgree env cval cval' := by
  have step : ∀ n : Name, (env.find? n).isSome = true →
      cval n = cval' n := fun n hn =>
    hag n (fun hh => by rw [hh, hfresh] at hn; exact nomatch hn)
  refine ⟨fun hg => step _ ?_, fun hg => step _ ?_, fun hg => step _ ?_,
    fun hg => step _ ?_, fun hg => step _ ?_, fun hg => step _ ?_,
    fun hg => step _ ?_⟩
  · simp only [natLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? natZeroName <;> simp [natZeroOk]
  · simp only [natLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? natSuccName <;> simp [natSuccOk]
  · simp only [strLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? stringOfListName <;> simp [stringOfListTyOk]
  · simp only [strLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? listNilName <;> simp [listNilTyOk]
  · simp only [strLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? listConsName <;> simp [listConsTyOk]
  · simp only [strLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? charName <;> simp [charTyOk]
  · simp only [strLitSupported, Bool.and_eq_true] at hg
    revert hg; cases env.find? charOfNatName <;> simp [charOfNatTyOk]


/-! ## The literal guards under a fresh install

Both guards read the environment only at fixed names, so an install
under a *different* name leaves them alone.  Proving the congruence
directly avoids needing `natLitSupported_inv` at all: **the inversion is
only needed to derive the guard from its consequences; the congruence
needs just the lookups**, which is a cheaper thing to want. -/

/-- The `Nat`-literal guard reads three slots. -/
theorem natLitSupported_cons_of_ne {env : Env} {c₀ : ConstantInfo}
    (h1 : c₀.name ≠ natName) (h2 : c₀.name ≠ natZeroName)
    (h3 : c₀.name ≠ natSuccName) :
    natLitSupported ⟨c₀ :: env.consts⟩ = natLitSupported env := by
  unfold natLitSupported
  rw [Env.find?_cons, Env.find?_cons, Env.find?_cons,
    if_neg h1, if_neg h2, if_neg h3]

/-- The `String`-literal guard reads the `Nat` slots and seven more. -/
theorem strLitSupported_cons_of_ne {env : Env} {c₀ : ConstantInfo}
    (h1 : c₀.name ≠ natName) (h2 : c₀.name ≠ natZeroName)
    (h3 : c₀.name ≠ natSuccName) (h4 : c₀.name ≠ stringName)
    (h5 : c₀.name ≠ stringOfListName) (h6 : c₀.name ≠ listName)
    (h7 : c₀.name ≠ listNilName) (h8 : c₀.name ≠ listConsName)
    (h9 : c₀.name ≠ charName) (h10 : c₀.name ≠ charOfNatName) :
    strLitSupported ⟨c₀ :: env.consts⟩ = strLitSupported env := by
  unfold strLitSupported
  rw [natLitSupported_cons_of_ne h1 h2 h3]
  rw [Env.find?_cons, Env.find?_cons, Env.find?_cons, Env.find?_cons,
    Env.find?_cons, Env.find?_cons, Env.find?_cons,
    if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
    if_neg h10]

/-- The stored level parameters of a name other than the new one. -/
theorem levelParamsAt_cons_of_ne {env : Env} {c₀ : ConstantInfo} {n : Name}
    (h : c₀.name ≠ n) :
    levelParamsAt ⟨c₀ :: env.consts⟩ n = levelParamsAt env n := by
  unfold levelParamsAt
  rw [Env.find?_cons, if_neg h]


/-! ## Denotations run *backwards* across a fresh install

`denote_mono` moves a denotation from the smaller environment to the
larger one.  The environment invariant needs the other direction as
well, and it needs it for a reason that only shows up when a *field* is
transported rather than a term: a
law that takes a denotation as a **hypothesis** is stated about the
larger environment after the install, so discharging it from the
smaller environment's law means running that hypothesis down, not up.

The converse is false in general — the larger environment denotes
strictly more — so it is guarded by `Expr.constsResolve`, which holds of
every *stored* expression by `EnvWF`, and it is consumed through a
telescope-level shrink at the law's own premise.

**It needs no guard or level-parameter hypotheses**, unlike
`denote_mono`: for a literal node `constsResolve` already asserts that
every slot the guard reads is stored in the *small* environment, and
freshness then says the new constant is none of them. -/

/-- A stored name is not the freshly installed one. -/
theorem ne_of_isSome_fresh {env : Env} {c₀ : ConstantInfo} {n : Name}
    (hfresh : env.find? c₀.name = none) (h : (env.find? n).isSome = true) :
    c₀.name ≠ n := by
  intro he
  rw [← he, hfresh] at h
  exact nomatch h

/-- Denotation is unchanged by a fresh install on expressions whose
constants already resolve.  Transpose of `interp_mono`. -/
theorem denote_env_shrink {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    (hntc : ∀ e', c₀ ≠ .projInfo e') :
    ∀ (d : Nat) (e : Expr), e.constsResolve env = true →
      denote cval ⟨c₀ :: env.consts⟩ φ d e = denote cval env φ d e := by
  have hbranch : ∀ (sn : Name) (i : Nat) (ve : Term),
      (match Env.findProj? ⟨c₀ :: env.consts⟩ sn i with
        | some entry => some (projNV (i + entry.off) ve)
        | none => Term.projPair? i ve)
      = (match env.findProj? sn i with
        | some entry => some (projNV (i + entry.off) ve)
        | none => Term.projPair? i ve) := by
    intro sn i ve
    by_cases hn : c₀.name = projTableName sn
    · have h0 : env.findProj? sn i = none :=
        Env.findProj?_none_of_fresh (by rw [← hn]; exact hfresh) i
      rw [h0, findProj?_cons_of_base_none hntc sn i h0]
    · rw [Env.findProj?_cons_ne hn]
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env) (φ := φ) with
  | case1 d u => intro _; rw [denote_sort, denote_sort]
  | case2 d idx ty => intro _; rw [denote_fvar, denote_fvar]
  | case3 d n us ci h1 h2 =>
    intro _
    simp only [denote_const, h1, if_pos h2,
      Env.find?_cons_of_isSome hfresh (by rw [h1]; rfl)]
  | case4 d n us ci h1 h2 =>
    intro _
    simp only [denote_const, h1, if_neg h2,
      Env.find?_cons_of_isSome hfresh (by rw [h1]; rfl)]
  | case5 d n us h1 =>
    intro hres
    rw [Expr.constsResolve, h1] at hres
    exact nomatch hres
  | case6 d ty body mb h1 ihty =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_forallE, denote_forallE, ihty hres.1, h1]
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_forallE, denote_forallE, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_forallE, denote_forallE, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case9 d ty body mb h1 ihty =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_lam, denote_lam, ihty hres.1, h1]
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_lam, denote_lam, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_lam, denote_lam, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case12 d f a vf va h1 h2 ihf iha =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_app, denote_app, ihf hres.1, iha hres.2]
  | case13 d f a hbad ihf iha =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_app, denote_app, ihf hres.1, iha hres.2]
  | case14 d ty val body =>
    intro _
    rw [denote_letE, denote_letE]
  | case15 d sn i e h1 ihe =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_proj, denote_proj, ihe hres.2]
    cases denote cval env φ d e with
    | none => rfl
    | some ve => exact hbranch sn i ve
  | case16 d sn i e B h1 entry h2 ihe =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_proj, denote_proj, ihe hres.2]
    cases denote cval env φ d e with
    | none => rfl
    | some ve => exact hbranch sn i ve
  | case17 d sn i e B h1 h2 ihe =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_proj, denote_proj, ihe hres.2]
    cases denote cval env φ d e with
    | none => rfl
    | some ve => exact hbranch sn i ve
  | case18 d n hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_natLit, denote_natLit,
      natLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh hres.1.1)
        (ne_of_isSome_fresh hfresh hres.1.2)
        (ne_of_isSome_fresh hfresh hres.2)]
  | case19 d n hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_natLit, denote_natLit,
      natLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh hres.1.1)
        (ne_of_isSome_fresh hfresh hres.1.2)
        (ne_of_isSome_fresh hfresh hres.2)]
  | case20 d s hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hres
    rw [denote_strLit, denote_strLit,
      strLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh k1)
        (ne_of_isSome_fresh hfresh k2) (ne_of_isSome_fresh hfresh k3)
        (ne_of_isSome_fresh hfresh k4) (ne_of_isSome_fresh hfresh k5)
        (ne_of_isSome_fresh hfresh k6) (ne_of_isSome_fresh hfresh k7)
        (ne_of_isSome_fresh hfresh k8) (ne_of_isSome_fresh hfresh k9)
        (ne_of_isSome_fresh hfresh k10),
      strLitT, strLitT,
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k7),
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k8)]
  | case21 d s hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hres
    rw [denote_strLit, denote_strLit,
      strLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh k1)
        (ne_of_isSome_fresh hfresh k2) (ne_of_isSome_fresh hfresh k3)
        (ne_of_isSome_fresh hfresh k4) (ne_of_isSome_fresh hfresh k5)
        (ne_of_isSome_fresh hfresh k6) (ne_of_isSome_fresh hfresh k7)
        (ne_of_isSome_fresh hfresh k8) (ne_of_isSome_fresh hfresh k9)
        (ne_of_isSome_fresh hfresh k10),
      strLitT, strLitT,
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k7),
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k8)]
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro _
    match x with
    | .bvar i => rw [denote_bvar, denote_bvar]
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

/-- Denotations of *old* terms survive an install: same value, larger
environment, changed valuation.  The shared core of every field's
transport — `has_type_cons` above is this plus a valuation rewrite, and
`defn_eq_cons` below is the same again. -/
theorem denote_install {cval cval' : TConstVal} {env : Env} {φ : Name → Nat}
    {c₀ : ConstantInfo} {d : Nat} {e : Expr} {v : Term}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ e', c₀ ≠ .projInfo e')
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hlit : LitAgree env cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
        = levelParamsAt env listNilName)
    (hlpCons : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
        = levelParamsAt env listConsName)
    (h : denote cval env φ d e = some v) :
    denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v := by
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hfind
    refine hag n ?_
    intro hh
    rw [hh, hfresh] at hfind
    exact nomatch hfind
  rw [denote_cval_congr hagE hlit.nat hlit.succ hlit.sol hlit.nil
    hlit.cons hlit.char hlit.ofn d _] at h
  exact denote_mono (EnvExtends.cons hfresh)
    (findProj?_cons_of_base_none hntc) hguardN hguardS hlpNil
    hlpCons d _ h


/-! ## The guards are monotone, not merely congruent

`natLitSupported_cons_of_ne` and its siblings above need the new
constant's name to differ from each slot's.  At an install those
distinctness facts have to come from somewhere, and there is a cheaper
source than freshness plus a case analysis: **the guard itself**.  A
guard that holds has already found every slot it reads, so each slot is
`isSome` in the *small* environment, and freshness then supplies the
distinctness for free.

The resulting monotonicity lemmas take a single hypothesis and
discharge the `hguardN`/`hguardS` obligations of `denote_mono`,
`denote_install` and `has_type_cons` at every ordinary install. -/

/-- The `Nat`-literal guard is monotone under a fresh install. -/
theorem natLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : natLitSupported env = true) :
    natLitSupported ⟨c₀ :: env.consts⟩ = true := by
  simp only [natLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have i1 : (env.find? natName).isSome = true := by
    revert h1; cases env.find? natName <;> simp [natIndOk]
  have i2 : (env.find? natZeroName).isSome = true := by
    revert h2; cases env.find? natZeroName <;> simp [natZeroOk]
  have i3 : (env.find? natSuccName).isSome = true := by
    revert h3; cases env.find? natSuccName <;> simp [natSuccOk]
  rw [Env.find?_cons_of_isSome hfresh i1, Env.find?_cons_of_isSome hfresh i2,
    Env.find?_cons_of_isSome hfresh i3]
  exact ⟨⟨h1, h2⟩, h3⟩

/-- The `String`-literal guard is monotone under a fresh install. -/
theorem strLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : strLitSupported env = true) :
    strLitSupported ⟨c₀ :: env.consts⟩ = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have i1 : (env.find? stringName).isSome = true := by
    revert h1; cases env.find? stringName <;> simp [stringTyOk]
  have i2 : (env.find? stringOfListName).isSome = true := by
    revert h2; cases env.find? stringOfListName <;> simp [stringOfListTyOk]
  have i3 : (env.find? listName).isSome = true := by
    revert h3; cases env.find? listName <;> simp [listTyOk]
  have i4 : (env.find? listNilName).isSome = true := by
    revert h4; cases env.find? listNilName <;> simp [listNilTyOk]
  have i5 : (env.find? listConsName).isSome = true := by
    revert h5; cases env.find? listConsName <;> simp [listConsTyOk]
  have i6 : (env.find? charName).isSome = true := by
    revert h6; cases env.find? charName <;> simp [charTyOk]
  have i7 : (env.find? charOfNatName).isSome = true := by
    revert h7; cases env.find? charOfNatName <;> simp [charOfNatTyOk]
  rw [Env.find?_cons_of_isSome hfresh i1, Env.find?_cons_of_isSome hfresh i2,
    Env.find?_cons_of_isSome hfresh i3, Env.find?_cons_of_isSome hfresh i4,
    Env.find?_cons_of_isSome hfresh i5, Env.find?_cons_of_isSome hfresh i6,
    Env.find?_cons_of_isSome hfresh i7]
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupported_cons hfresh h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- The `Nat`-operation guard is monotone under a fresh install. -/
theorem natOpGuard_cons {env : Env} {c₀ : ConstantInfo} {c : Name}
    (hfresh : env.find? c₀.name = none) (h : natOpGuard env c = true) :
    natOpGuard ⟨c₀ :: env.consts⟩ c = true := by
  simp only [natOpGuard, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h0, hdeps⟩, hbool⟩ := h
  refine ⟨⟨natLitSupported_cons hfresh h0, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at hdeps ⊢
    intro n hn
    have hn' := hdeps n hn
    have i : (env.find? n).isSome = true := by
      revert hn'; cases env.find? n <;> simp
    rw [Env.find?_cons_of_isSome hfresh i]
    exact hn'
  · split at hbool
    · next hc =>
      rw [if_pos hc]
      simp only [Bool.and_eq_true] at hbool ⊢
      obtain ⟨hT, hF⟩ := hbool
      have iT : (env.find? boolTrueName).isSome = true := by
        revert hT; cases env.find? boolTrueName <;> simp
      have iF : (env.find? boolFalseName).isSome = true := by
        revert hF; cases env.find? boolFalseName <;> simp
      rw [Env.find?_cons_of_isSome hfresh iT,
        Env.find?_cons_of_isSome hfresh iF]
      exact ⟨hT, hF⟩
    · next hc => rw [if_neg hc]


/-! ## The install context

Every field transport wants the same five facts, and passing them one
at a time was becoming the bulk of each statement.  `Installs` bundles
them.  It describes an **ordinary** install: the new constant is fresh,
the valuation changes only at it, and the literal-support constants and
their level parameters are untouched.  A *basis* install is precisely
the case that violates the last three, and is handled separately —
which is the honest division, because a basis install is the one thing
that can change what a literal denotes. -/

/-- The context of an ordinary install: `c₀` is fresh, the valuation
moves only at `c₀.name`, and nothing a literal reads changes. -/
structure Installs (env : Env) (cval cval' : TConstVal)
    (c₀ : ConstantInfo) : Prop where
  /-- The installed name is not already stored. -/
  fresh : env.find? c₀.name = none
  /-- The installed constant is not a projection table (task #175
  wiring W3; the table installs get their own transports). -/
  ntc : ∀ e', c₀ ≠ .projInfo e'
  /-- The valuation changes only at the installed name. -/
  ag : ∀ n, n ≠ c₀.name → cval n = cval' n
  /-- Literal support is valued the same on both sides. -/
  lit : LitAgree env cval cval'
  /-- `List.nil`'s stored level parameters do not move — needed only
  where a string literal can denote, i.e. under the guard. -/
  lpNil : strLitSupported env = true →
    levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
      = levelParamsAt env listNilName
  /-- `List.cons`'s stored level parameters do not move. -/
  lpCons : strLitSupported env = true →
    levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
      = levelParamsAt env listConsName

/-- **An ordinary install needs nothing but freshness.**  Both the
literal agreements and the two level-parameter clauses are conditional
on the guard holding *before* the install, and under the guard every
constant they mention is stored — hence distinct from the fresh name.

So `Installs` costs a caller exactly one hypothesis (the valuation
changes only at the new name), which is what an install lemma should
cost.  Before §8.5's second pass it cost seven name disequalities and
two level-parameter equations, and two of the disequalities were not
even *true* in general: nothing in `checkConstantVal` forbids a `def`
named `List.nil` (the string-support names are pinned, not reserved). -/
theorem Installs.of_fresh {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    (hntc : ∀ e', c₀ ≠ .projInfo e')
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n) :
    Installs env cval cval' c₀ := by
  have step : ∀ n : Name, (env.find? n).isSome = true →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := fun n hn =>
    Env.find?_cons_of_isSome hfresh hn
  refine ⟨hfresh, hntc, hag, LitAgree.of_fresh hfresh hag, fun hg => ?_,
    fun hg => ?_⟩
  · have hs : (env.find? listNilName).isSome = true := by
      simp only [strLitSupported, Bool.and_eq_true] at hg
      revert hg; cases env.find? listNilName <;> simp [listNilTyOk]
    rw [levelParamsAt, levelParamsAt, step _ hs]
  · have hs : (env.find? listConsName).isSome = true := by
      simp only [strLitSupported, Bool.and_eq_true] at hg
      revert hg; cases env.find? listConsName <;> simp [listConsTyOk]
    rw [levelParamsAt, levelParamsAt, step _ hs]

/-- A denotation survives an ordinary install.  The guard hypotheses of
`denote_install` are discharged by monotonicity, so this form takes
none. -/
theorem Installs.denoteUp {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    {φ : Name → Nat} {d : Nat} {e : Expr} {v : Term}
    (h : denote cval env φ d e = some v) :
    denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v :=
  denote_install hi.fresh hi.ntc hi.ag hi.lit
    (natLitSupported_cons hi.fresh)
    (strLitSupported_cons hi.fresh) hi.lpNil hi.lpCons h

/-- A stored name is valued the same after an ordinary install. -/
theorem Installs.agree {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀) {n : Name}
    (h : (env.find? n).isSome = true) : cval n = cval' n :=
  hi.ag n (Ne.symm (ne_of_isSome_fresh hi.fresh h))

/-- A denotation of a *stored* expression runs back down to the smaller
environment.  The two moves compose in one order only: shrink first
(the expression resolves there), then change the valuation (the two
agree on everything stored there, but not at the new constant). -/
theorem Installs.denoteDown {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    {φ : Name → Nat} {d : Nat} {e : Expr} {v : Term}
    (hres : e.constsResolve env = true)
    (h : denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v) :
    denote cval env φ d e = some v := by
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hf
    refine hi.ag n ?_
    intro hh
    rw [hh, hi.fresh] at hf
    exact nomatch hf
  rw [denote_env_shrink hi.fresh hi.ntc d e hres] at h
  rwa [denote_cval_congr hagE hi.lit.nat hi.lit.succ hi.lit.sol hi.lit.nil
    hi.lit.cons hi.lit.char hi.lit.ofn d e]

/-- Lookups of stored names are unchanged by an ordinary install. -/
theorem Installs.find {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀) {n : Name}
    (h : (env.find? n).isSome = true) :
    Env.find? ⟨c₀ :: env.consts⟩ n = env.find? n :=
  Env.find?_cons_of_isSome hi.fresh h


/-! ## The remaining field transports

One `.cons` per `EnvTT` field, each in the same shape: the head case is
a hypothesis (the install must establish its own constant's law), and
everything else transports.  The `Installs` context supplies the three
moves they share — a denotation goes up, a stored name's valuation is
unchanged, a stored name's lookup is unchanged. -/

/-- The pinned basis valuations survive an install at another name. -/
theorem BasisPinnedTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : BasisPinnedTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : reservedBasisNames.contains c₀.name = true →
      c₀ = pinnedInfo c₀.name ∧
      ∀ (ψ : Name → Nat) (t : Term),
        pinnedStructT c₀.name ψ = some t → cval' c₀.name ψ = t) :
    BasisPinnedTT ⟨c₀ :: env.consts⟩ cval' := by
  intro n ci hf hres
  by_cases hn : c₀.name = n
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    obtain rfl : ci = c₀ := (Option.some.inj hf).symm
    exact ⟨(hhead hres).1, fun t ψ hp => (hhead hres).2 ψ t hp⟩
  · rw [Env.find?_cons, if_neg hn] at hf
    refine ⟨(h n ci hf hres).1, fun t ψ hp => ?_⟩
    rw [← hi.ag n (fun hh => hn hh.symm)]
    exact (h n ci hf hres).2 t ψ hp

/-- The projection-table discipline survives an install.  A head that
is a table supplies its own head data (task #175 wiring W5); the
stored tables' head data survives by freshness. -/
theorem ProjOkT.cons {env : Env} {c₀ : ConstantInfo} (h : ProjOkT env)
    (hfresh : env.find? c₀.name = none)
    (hheadTower : ∀ tbl, c₀ = .projInfo tbl →
      ∀ i, i < tbl.numFields → TowerHead ⟨c₀ :: env.consts⟩ (tbl.entry i)) :
    ProjOkT ⟨c₀ :: env.consts⟩ := by
  have hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env.find? n = some ci → (⟨c₀ :: env.consts⟩ : Env).find? n = some ci := by
    intro n ci _ hf
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]; exact hf
  intro n tbl hf i hi
  by_cases hn : c₀.name = n
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hheadTower tbl (Option.some.inj hf) i hi
  · rw [Env.find?_cons, if_neg hn] at hf
    exact TowerHead.mono hkeep (h n tbl hf i hi)

/-- Every name a clause set reads is valued the same after an install
at a different name. -/
theorem divModNames_agree {env : Env} {cval cval' : TConstVal} {c : Name}
    (hag : ∀ n, (env.find? n).isSome = true → cval n = cval' n)
    (hg : natOpGuard env c = true) :
    (∀ n ∈ natOpDeps c, cval n = cval' n) ∧
      cval natZeroName = cval' natZeroName ∧
      cval natSuccName = cval' natSuccName ∧
      (natDivModNames.contains c = true →
        cval boolTrueName = cval' boolTrueName ∧
        cval boolFalseName = cval' boolFalseName) := by
  simp only [natOpGuard, Bool.and_eq_true] at hg
  obtain ⟨⟨h0, hdeps⟩, hbool⟩ := hg
  simp only [natLitSupported, Bool.and_eq_true] at h0
  obtain ⟨⟨-, h2⟩, h3⟩ := h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [List.all_eq_true] at hdeps
    have hn' := hdeps n (by simpa using hn)
    exact hag n (by revert hn'; cases env.find? n <;> simp)
  · exact hag _ (by revert h2; cases env.find? natZeroName <;> simp [natZeroOk])
  · exact hag _ (by revert h3; cases env.find? natSuccName <;> simp [natSuccOk])
  · intro hc
    rw [show (decide (c = natBeqName) || decide (c = natBleName) ||
        natDivModNames.contains c) = true from by
          simp only [hc, Bool.or_true]] at hbool
    simp only [if_true] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨hT, hF⟩ := hbool
    exact ⟨hag _ (by revert hT; cases env.find? boolTrueName <;> simp),
      hag _ (by revert hF; cases env.find? boolFalseName <;> simp)⟩


/-- Extend a valuation at one name by an explicitly chosen term. -/
@[expose] def cvalWith (cval : TConstVal) (n : Name) (V : (Name → Nat) → Term) :
    TConstVal := fun c ψ => if c = n then V ψ else cval c ψ

theorem cvalWith_ne {cval : TConstVal} {n : Name}
    {V : (Name → Nat) → Term} {c : Name} (h : c ≠ n) :
    cvalWith cval n V c = cval c := by
  funext ψ; simp [cvalWith, h]

theorem cvalWith_self {cval : TConstVal} {n : Name}
    {V : (Name → Nat) → Term} : cvalWith cval n V n = V := by
  funext ψ; simp [cvalWith]

/-! ## The valuation an install chooses

At a fresh name, by the value's denotation; everywhere else unchanged.
(Relocated from `ConLeche/TTVerify/DeclValue.lean`; `EnvTT.defn_eq` — and
`EnvS.defn_eq`, its [set] twin — is what fixes this: there is no other
function that could satisfy it.) -/

/-- Extend a valuation at one name by a closed expression's
denotation. -/
def cvalAt (cval : TConstVal) (env : Env) (n : Name) (value : Expr) :
    TConstVal := fun c ψ =>
  if c = n then (denoteClosed cval env ψ value).getD (cval c ψ)
  else cval c ψ

theorem cvalAt_ne {cval : TConstVal} {env : Env} {n : Name} {value : Expr}
    {c : Name} (h : c ≠ n) : cvalAt cval env n value c = cval c := by
  funext ψ; simp [cvalAt, h]

theorem cvalAt_self {cval : TConstVal} {env : Env} {n : Name}
    {value : Expr} {ψ : Name → Nat} {v : Term}
    (h : denoteClosed cval env ψ value = some v) :
    cvalAt cval env n value n ψ = v := by
  simp [cvalAt, h]

end ConLeche.Verify
