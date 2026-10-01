module

public import ConLeche.Model.Annot.BitClosed
public import ConLeche.Semantics.Install
import ConLeche.Verify.EnvGuards

public section

/-!
# `denoteMeta` at an install (task #161, P3.2)

The install-tier surface: the leaf-valuation congruence and its fresh
corollary (`Interp/Install.lean`), the same-run agreement
(`Interp/Step2Cons.lean`), and the spine head swap
(`Interp/Steps/Levels.lean`).

All four are VERIFIED-grade mirrors — the sort steps in the originals
are valuation- and spine-independent and simply vanish:

* `denoteMeta_acval_congr` walks the same fifteen clauses; the binder
  cases were `rw [denoteAnnot, denoteAnnot, ihty, ihbody]` and stay exactly
  that, because `pwBit φ m.pw` mentions no valuation;
* `denoteMeta_mkAppN_swap` loses the fuel-move (`F ≤ F'` and its
  `denote2_fuelMono` step) — with no fuel there is nothing to move,
  so the swap is stated at one reading and the argument rides along
  on `rfl`;
* `denoteMeta_agree_same` loses its content with the fuel it quantified
  over.  `denote2_agree_same` says two successes *at different fuels*
  agree; `denoteMeta` has one reading per subject, so the mirror is
  `Option.some.inj`.  It is kept, at its mirror name, because the
  consumers of the original (`hback` in `declStep2_of_value`) call it
  by name at exactly this instance.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

variable {env : Env} {φ : Name → Nat}

/-! ## `denoteMeta` reads only what the environment stores -/

/-- **The congruence.**  `denoteMeta` consults its valuation only at
names the environment stores — every `.const` leaf behind its own
`find?`, the two literal spines behind their support guards.  So two
valuations agreeing on the stored names denote every term alike.

Stated as an equation rather than an implication: the two runs are
`none` together as well, which is what a *fresh* install needs. -/
theorem denoteMeta_acval_congr
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    (hag : ∀ n, (env.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr),
      denoteMeta acval₁ env φ d e = denoteMeta acval₂ env φ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u => rw [denoteMeta, denoteMeta]
  | case2 d idx ty => rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    rw [denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen, hag n (by rw [hf]; rfl)]
  | case4 d n us ci hf hlen =>
    rw [denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => rw [denoteMeta, denoteMeta, hf]
  | case6 d ty body m ihty ihbody =>
    rw [denoteMeta, denoteMeta, ihty, ihbody]
  | case7 d ty body m ihty ihbody =>
    rw [denoteMeta, denoteMeta, ihty, ihbody]
  | case8 d f a ihf iha => rw [denoteMeta, denoteMeta, ihf, iha]
  | case9 d ty val body =>
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe => rw [denoteMeta, denoteMeta, ihe]
  | case11 d n hsup =>
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hS, -⟩ :=
      natLitSupported_inv hsup
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup,
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hS]; rfl)]
  | case12 d n hsup =>
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
      hfS, hfO, hfL, hfN, hfC, hfH, hfF, -⟩ :=
      strLitSupported_inv hsup
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hSu, -⟩ :=
      natLitSupported_inv hnat
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup,
      hag stringOfListName (by rw [hfO]; rfl),
      hag listNilName (by rw [hfN]; rfl),
      hag listConsName (by rw [hfC]; rfl),
      hag charName (by rw [hfH]; rfl),
      hag charOfNatName (by rw [hfF]; rfl),
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hSu]; rfl)]
  | case14 d s hsup =>
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
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

/-- **The install corollary**: choosing the new declaration's
annotated leaf moves no denotation in the environment it was checked
in. -/
theorem denoteMeta_acvalWith_fresh
    {acval : Name → (Name → Nat) → AnnotTerm} {n : Name}
    {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? n = none)
    (d : Nat) (e : Expr) :
    denoteMeta (acvalWith acval n A) env φ d e
      = denoteMeta acval env φ d e := by
  refine denoteMeta_acval_congr (fun c hc => ?_) d e
  refine acvalWith_ne (fun h => ?_)
  rw [h, hfresh] at hc
  exact nomatch hc

/-! ## One reading per subject -/

/-- **`denote2_agree_same`'s mirror.**  The original reconciles two
successes at *different fuels* through `denote2_fuelMono`; `denoteMeta`
takes no fuel, so the two runs are the same run and the reconciliation
is `Option.some.inj`.  Kept at the mirror name because the consumers
of the original invoke it at exactly this instance. -/
theorem denoteMeta_agree_same {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {value : Expr} {ra ra' : AnnotTerm}
    (h : denoteMeta acval env ψ 0 value = some ra)
    (h' : denoteMeta acval env ψ 0 value = some ra') : ra = ra' :=
  Option.some.inj (h.symm.trans h')

/-! ## The spine -/

/-- **Head swap under a spine.**  If the head's annotation survives a
move to another head — for whatever reason: the same term, an
unfolding, a different term with the same validated annotation — then
so does the whole application's, unchanged.  `denote2_mkAppN_swap`
without the fuel move. -/
theorem denoteMeta_mkAppN_swap {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} :
    ∀ (as : List Expr) {f g : Expr} {ea : AnnotTerm},
      (∀ fa : AnnotTerm, denoteMeta acval env φ d f = some fa →
        denoteMeta acval env φ d g = some fa) →
      denoteMeta acval env φ d (Expr.mkAppN f as) = some ea →
      denoteMeta acval env φ d (Expr.mkAppN g as) = some ea := by
  intro as
  induction as with
  | nil => intro f g ea hswap h; exact hswap ea h
  | cons a as ih =>
    intro f g ea hswap h
    refine ih (f := .app f a) (g := .app g a) ?_ h
    intro fa hfa
    rw [denoteMeta] at hfa
    rcases hf : denoteMeta acval env φ d f with _ | fx
    · rw [hf] at hfa; exact nomatch hfa
    rw [hf] at hfa
    rcases ha : denoteMeta acval env φ d a with _ | ax
    · rw [ha] at hfa; exact nomatch hfa
    rw [ha] at hfa
    obtain rfl : fa = .app fx ax := (Option.some.inj hfa).symm
    rw [denoteMeta, hswap fx hf, ha]
    rfl

end ConLeche.Model
