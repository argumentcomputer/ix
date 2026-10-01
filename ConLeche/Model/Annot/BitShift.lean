module

public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Verify.Shift

public section

/-!
# `denoteMeta`'s depth shift (task #161, P3.2)

`denote2_shiftFrom`/`denote2_weaken_top` (`Interp/Steps/Dispatch.lean`)
mirrored for the validated-annotation reading.

**The dropped premise.**  `denote2_shiftFrom` takes `ConLeche.EnvWF env`
and uses it in exactly two places — `sortOfE_shiftFrom` in the `∀`
clause, `lamSortE_shiftFrom` in the `λ` clause, the two rewrites that
move a *checker run* across the shift.  `denoteMeta` runs no checker: its
binder numeral is `pwBit φ mb.pw`, a function of the term's own meta,
and `Expr.shiftFrom` carries metas through unchanged — so the numeral
is literally the same expression on both sides and the clause closes
by the recursion alone.  `EnvWF` therefore has no occurrence left and
is dropped.

`hacl` is kept: it is the *leaf* obligation (stored annotations are
lift-invariant), which the constant and literal clauses need and which
has nothing to do with sorts.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- The `Nat`-literal spine is lift-invariant when its two heads are.
A private local copy of `Dispatch.lean`'s helper of the same name,
which is `private` there and so not in scope here. -/
private theorem natLitAV_liftN {za sa : AnnotTerm} {k : Nat}
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ n : Nat, (natLitAV za sa n).liftN 1 k = natLitAV za sa n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    show (AnnotTerm.app sa (natLitAV za sa n)).liftN 1 k = _
    rw [AnnotTerm.liftN_app, hs, ih]
    rfl

/-- Ditto the character-list spine (private local copy, as above). -/
private theorem charListAV_liftN {nilA consA ofNatA za sa : AnnotTerm}
    {k : Nat} (hn : nilA.liftN 1 k = nilA)
    (hc : consA.liftN 1 k = consA) (ho : ofNatA.liftN 1 k = ofNatA)
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ cs : List Char,
      (charListAV nilA consA ofNatA za sa cs).liftN 1 k
        = charListAV nilA consA ofNatA za sa cs := by
  intro cs
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    show (AnnotTerm.app (.app consA (.app ofNatA _)) _).liftN 1 k = _
    rw [AnnotTerm.liftN_app, AnnotTerm.liftN_app, AnnotTerm.liftN_app, hc, ho,
      natLitAV_liftN hz hs, ih]
    rfl

/-- **`denoteMeta`'s depth shift.**  `denote2_shiftFrom` with the two
sort-run rewrites deleted — see the module docstring for why `EnvWF`
goes with them.

Generalized over the cut `p` for the same reason both ancestors are:
the binder clause compares `denoteMeta (d+2) (body.instantiate1 (.fvar
(d+1) …))` with `denoteMeta (d+1) (body.instantiate1 (.fvar d …))`, two
genuinely different expressions related by `Expr.shiftFrom d`. -/
theorem denoteMeta_shiftFrom
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {p : Nat} :
    ∀ (e : Expr) (d : Nat), p ≤ d → Expr.WScoped d e →
      denoteMeta acval env φ (d + 1) (e.shiftFrom p) =
        (denoteMeta acval env φ d e).map (AnnotTerm.liftN 1 · (d - p))
  | .bvar i, d, _, _ => by
    have h1 : denoteMeta acval env φ (d + 1) (.bvar i) = none := by
      rw [denoteMeta.eq_def]
    have h2 : denoteMeta acval env φ d (.bvar i) = none := by
      rw [denoteMeta.eq_def]
    simp [ConLeche.Expr.shiftFrom, h1, h2]
  | .sort u, d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denoteMeta, Option.map_some]
    rfl
  | .const n us, d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some, hacl]
      · rfl
  | .fvar idx ty, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hlt : idx < d := hw.1
    simp only [ConLeche.Expr.shiftFrom]
    split
    · next hge =>
      rw [denoteMeta, denoteMeta, Option.map_some, AnnotTerm.liftN_bvar,
        if_pos (show d - 1 - idx < d - p by omega),
        show d + 1 - 1 - (idx + 1) = d - 1 - idx from by omega]
    · next hge =>
      rw [denoteMeta, denoteMeta, Option.map_some, AnnotTerm.liftN_bvar,
        if_neg (show ¬ d - 1 - idx < d - p by omega),
        show d + 1 - 1 - idx = d - 1 - idx + 1 from by omega]
  | .app fe a, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    rw [denoteMeta_shiftFrom hacl fe d hpd hw.1,
      denoteMeta_shiftFrom hacl a d hpd hw.2]
    cases denoteMeta acval env φ d fe <;>
      cases denoteMeta acval env φ d a <;> rfl
  | .forallE ty body mb, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d ty)) :=
      ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    rw [← ConLeche.Expr.shiftFrom_instantiate1 hpd body 0,
      denoteMeta_shiftFrom hacl ty d hpd hw.1,
      denoteMeta_shiftFrom hacl (body.instantiate1 (.fvar d ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denoteMeta acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denoteMeta acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some ba => rfl
  | .lam ty body mb, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d ty)) :=
      ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    rw [← ConLeche.Expr.shiftFrom_instantiate1 hpd body 0,
      denoteMeta_shiftFrom hacl ty d hpd hw.1,
      denoteMeta_shiftFrom hacl (body.instantiate1 (.fvar d ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denoteMeta acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denoteMeta acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some ba => rfl
  | .letE ty val body, d, hpd, hw => by
    -- task #241: `denoteMeta` is `none` at a `letE`, on both sides
    simp only [ConLeche.Expr.shiftFrom, denoteMeta, Option.map_none]
  | .proj sn i e, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    rw [denoteMeta_shiftFrom hacl e d hpd hw]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      cases env.findProj? sn i with
      | none =>
        dsimp only
        rcases i with _ | _ | i <;> rfl
      | some entry =>
        show some (projAV (i + entry.off) (AnnotTerm.liftN 1 ea (d - p)))
          = Option.map (fun x => AnnotTerm.liftN 1 x (d - p))
            (some (projAV (i + entry.off) ea))
        simp only [Option.map_some, projAV_liftN]
  | .lit (.natVal k), d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    split
    · simp only [Option.map_some]
      rw [natLitAV_liftN (hacl _ _ _) (hacl _ _ _)]
    · rfl
  | .lit (.strVal s), d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denoteMeta]
    split
    · simp only [Option.map_some]
      refine congrArg some ?_
      symm
      rw [AnnotTerm.liftN_app, hacl,
        charListAV_liftN (by rw [AnnotTerm.liftN_app, hacl, hacl])
          (by rw [AnnotTerm.liftN_app, hacl, hacl]) (hacl _ _ _)
          (hacl _ _ _) (hacl _ _ _)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [ConLeche.Expr.sizeB]; omega)
  | (rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]
     simp [ConLeche.Expr.sizeB]; omega)
  | (simp [ConLeche.Expr.sizeB])

/-- **One level of weakening.**  `denote2_weaken_top`'s mirror: a
`d`-scoped term denoted at `d + 1` is its depth-`d` annotation,
lifted.  `EnvWF` goes with the shift it is derived from. -/
theorem denoteMeta_weaken_top
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) :
    denoteMeta acval env φ (d + 1) e
      = (denoteMeta acval env φ d e).map (AnnotTerm.liftN 1 · 0) := by
  have h := denoteMeta_shiftFrom (env := env) (φ := φ) hacl (p := d) e d
    (Nat.le_refl d) hw
  rw [ConLeche.Expr.shiftFrom_eq_self hw.fvarsBelow, Nat.sub_self] at h
  exact h

end ConLeche.Model
