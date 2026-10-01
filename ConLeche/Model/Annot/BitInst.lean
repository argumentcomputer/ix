module

public import ConLeche.Model.Annot.BitShift
import ConLeche.Semantics.DenoteClosed
public import ConLeche.Verify.Denote.Inst

public section

/-!
# `denoteMeta` commutes with instantiation (task #161, P3 batch 2)

`denote_substFvarAt`/`denote_beta` (`Verify/Denote/Inst.lean`)
mirrored for the validated-annotation reading — the substitution
crossing the β/ζ clauses of the P-tier step proof run through, exactly
as the v1 walk is what `CheckStepTT`'s application clause runs
through.

## What the mirror costs, and what it does not

**It does not cost `EnvWF`.**  Same reason as `denoteMeta_shiftFrom`
(`BitShift.lean`): `denoteAnnot`'s binder clauses move a *checker run*
across the substitution, `denoteMeta`'s binder numeral is `pwBit φ mb.pw`
— a function of the term's own meta — and `Expr.substFvarAt` carries
binder metas through **unchanged**.  Read its definition
(`Verify/Subst.lean`): the `.lam`/`.forallE` clauses are
`.lam (substFvarAt p a ty) (substFvarAt p a body) m`, the meta `m`
copied verbatim.  So the numeral is literally the same expression on
both sides of every binder clause and each closes by the recursion
alone.

**It costs two leaf premises, not one.**  The brief proposed the
single `inst`-invariance premise `hainst`; the walk needs a second.

* `hainst : ∀ n ψ y k, (acval n ψ).inst y k = acval n ψ` is what the
  `.const` and `.lit` clauses read — the exact analogue of v1's
  `Term.inst_eq_self_of_closed (hcl _ _)`, and of batch 1's `hacl`
  one operation over.
* `hacl : ∀ n ψ k, (acval n ψ).liftN 1 k = acval n ψ` — batch 1's
  premise, unchanged — is what the **`fvar`-at-`p` clause** reads,
  through `denoteMeta_lift` below.  That clause is v1's
  `denote_lift hcl hwa.fvarsBelow D hpD` step; v1 hides the split
  because `Term.Closed` implies both invariances at once, while the
  `AnnotTerm` side states each as its own equation and neither implies
  the other (`inst`-invariance at every cut is the stronger of the
  two, but extracting the lift from it is a fresh induction, not a
  rewrite).

Both are discharged from one closedness fact at every real supplier:
`AnnotTerm.liftN_eq_self` and `AnnotTerm.inst_eq_self`
(`Interp/DenoteClosed.lean`) take the same
`Term.bvarsBelow k (acval n ψ).erase` hypothesis, and `hacl` is
already an `EnvModelU` field (`acval_closed`).

## Where the arithmetic lands

Verbatim v1's, and for v1's reason: at depth `D + 1` the variable
`fvar p` denotes `.bvar (D - p)`, so the substitution happens at cut
`k = D - p`, and `AnnotTerm.inst e a k` already substitutes `liftN k a`
— which makes `inst`'s built-in lift *be* the depth shift.
-/

-- The lift identities extend `ConLeche.Semantics.AnnotTerm` itself (dot
-- notation and the unqualified `liftN_*` names resolve there), so this
-- block stays in the semantic tier's namespace.
namespace ConLeche.Semantics.AnnotTerm
open ConLeche.SetModel

/-! ### Two lift identities the depth-lift needs

`Term` had these (`Verify/Denote/SubstAlgebra.lean`, deleted unread
at task #221); `AnnotTerm` did
not, because nothing before this file iterated a lift. -/

/-- A zero lift is the identity. -/
theorem liftN_zero : ∀ (e : AnnotTerm) (k : Nat), liftN 0 e k = e := by
  intro e
  induction e with
  | bvar i => intro k; simp only [liftN_bvar]; split <;> rfl
  | sort u => intro _; rfl
  | const c us => intro _; rfl
  | prf => intro _; rfl
  | app f a ihf iha => intro k; rw [liftN_app, ihf, iha]
  | lam u A b ihA ihb => intro k; rw [liftN_lam, ihA, ihb]
  | pi u v A B ihA ihB => intro k; rw [liftN_pi, ihA, ihB]
  | eqE a b iha ihb => intro k; rw [liftN_eqE, iha, ihb]
  | fst e ihe => intro k; rw [liftN_fst, ihe]
  | snd e ihe => intro k; rw [liftN_snd, ihe]

/-- Two lifts at the same cut compose. -/
theorem liftN_liftN : ∀ (e : AnnotTerm) (n m k : Nat),
    liftN n (liftN m e k) k = liftN (n + m) e k := by
  intro e
  induction e with
  | bvar i =>
    intro n m k
    simp only [liftN_bvar]
    by_cases h : i < k
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg (show ¬ i + m < k from by omega)]
      congr 1
      omega
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro n m k; rw [liftN_app, liftN_app, ihf, iha]; rfl
  | lam u A b ihA ihb =>
    intro n m k; rw [liftN_lam, liftN_lam, ihA, ihb]; rfl
  | pi u v A B ihA ihB =>
    intro n m k; rw [liftN_pi, liftN_pi, ihA, ihB]; rfl
  | eqE a b iha ihb =>
    intro n m k; rw [liftN_eqE, liftN_eqE, iha, ihb]; rfl
  | fst e ihe =>
    intro n m k; rw [liftN_fst, liftN_fst, ihe]; rfl
  | snd e ihe =>
    intro n m k; rw [liftN_snd, liftN_snd, ihe]; rfl

end ConLeche.Semantics.AnnotTerm

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel


open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- The `Nat`-literal spine is `inst`-invariant when its two heads
are.  `BitShift.lean`'s `natLitAV_liftN` one operation over. -/
private theorem natLitAV_inst {za sa y : AnnotTerm} {k : Nat}
    (hz : za.inst y k = za) (hs : sa.inst y k = sa) :
    ∀ n : Nat, (natLitAV za sa n).inst y k = natLitAV za sa n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    show (AnnotTerm.app sa (natLitAV za sa n)).inst y k = _
    rw [AnnotTerm.inst_app, hs, ih]
    rfl

/-- Ditto the character-list spine. -/
private theorem charListAV_inst {nilA consA ofNatA za sa y : AnnotTerm}
    {k : Nat} (hn : nilA.inst y k = nilA)
    (hc : consA.inst y k = consA) (ho : ofNatA.inst y k = ofNatA)
    (hz : za.inst y k = za) (hs : sa.inst y k = sa) :
    ∀ cs : List Char,
      (charListAV nilA consA ofNatA za sa cs).inst y k
        = charListAV nilA consA ofNatA za sa cs := by
  intro cs
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    show (AnnotTerm.app (.app consA (.app ofNatA _)) _).inst y k = _
    rw [AnnotTerm.inst_app, AnnotTerm.inst_app, AnnotTerm.inst_app, hc, ho,
      natLitAV_inst hz hs, ih]
    rfl

/-- **Depth lifting for `denoteMeta`** — `denote_lift`'s mirror, iterated
out of `denoteMeta_weaken_top`.  The scoping premise is `WScoped` rather
than v1's `fvarsBelow` because that is what `denoteMeta_shiftFrom` takes
(the annotations have to be scoped too, hereditarily). -/
theorem denoteMeta_lift
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {p : Nat} {e : Expr} (hw : Expr.WScoped p e) :
    ∀ D : Nat, p ≤ D →
      denoteMeta acval env φ D e
        = (denoteMeta acval env φ p e).map (AnnotTerm.liftN (D - p) · 0) := by
  intro D
  induction D with
  | zero =>
    intro hpD
    have hp : p = 0 := by omega
    subst hp
    simp only [Nat.sub_self]
    cases denoteMeta acval env φ 0 e with
    | none => rfl
    | some v => simp only [Option.map_some, AnnotTerm.liftN_zero]
  | succ D ih =>
    intro hpD
    by_cases hpD' : p = D + 1
    · subst hpD'
      simp only [Nat.sub_self]
      cases denoteMeta acval env φ (D + 1) e with
      | none => rfl
      | some v => simp only [Option.map_some, AnnotTerm.liftN_zero]
    · have hpD2 : p ≤ D := by omega
      rw [denoteMeta_weaken_top hacl (hw.mono hpD2), ih hpD2]
      cases denoteMeta acval env φ p e with
      | none => rfl
      | some v =>
        simp only [Option.map_some, AnnotTerm.liftN_liftN]
        congr 2
        omega

/-- **The substitution lemma, validated-annotation reading.**
Substituting the expression `a` for `fvar p` corresponds to
instantiating the annotation at de Bruijn cut `D - p`.  Mirror of
`denote_substFvarAt`; see the module docstring for the two leaf
premises and for why `EnvWF` is absent. -/
theorem denoteMeta_substFvarAt
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {p : Nat} {a : Expr} {x : AnnotTerm}
    (hwa : Expr.WScoped p a) (hba : a.looseBVarsBounded 0 = true)
    (ha : denoteMeta acval env φ p a = some x) :
    ∀ (e : Expr) (D : Nat), p ≤ D → Expr.fvarsBelow (D + 1) e →
      denoteMeta acval env φ D (Expr.substFvarAt p a e) =
        (denoteMeta acval env φ (D + 1) e).map (AnnotTerm.inst · x (D - p))
  | .bvar i, D, hpD, hfb => by
    have h1 : denoteMeta acval env φ D (.bvar i) = none := by
      rw [denoteMeta.eq_def]
    have h2 : denoteMeta acval env φ (D + 1) (.bvar i) = none := by
      rw [denoteMeta.eq_def]
    simp [ConLeche.Expr.substFvarAt, h1, h2]
  | .sort u, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta, Option.map_some]
    rfl
  | .const n us, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some, hainst]
      · rfl
  | .fvar idx ty, D, hpD, hfb => by
    have hlt : idx < D + 1 := hfb
    by_cases h1 : idx = p
    · subst h1
      rw [show ConLeche.Expr.substFvarAt idx a (Expr.fvar idx ty) = a from by
            simp [ConLeche.Expr.substFvarAt],
        denoteMeta_lift hacl hwa D hpD, ha, denoteMeta]
      simp only [Option.map_some, AnnotTerm.inst_bvar,
        show D + 1 - 1 - idx = D - idx from by omega]
      simp
    · by_cases h2 : idx > p
      · rw [show ConLeche.Expr.substFvarAt p a (Expr.fvar idx ty)
              = .fvar (idx - 1) (ConLeche.Expr.substFvarAt p a ty) from by
              simp [ConLeche.Expr.substFvarAt, h1, h2],
          denoteMeta, denoteMeta]
        simp only [Option.map_some, AnnotTerm.inst_bvar,
          if_pos (show D + 1 - 1 - idx < D - p from by omega)]
        congr 2
        omega
      · rw [show ConLeche.Expr.substFvarAt p a (Expr.fvar idx ty)
              = .fvar idx ty from by
              simp [ConLeche.Expr.substFvarAt, h1, h2],
          denoteMeta, denoteMeta]
        simp only [Option.map_some, AnnotTerm.inst_bvar,
          if_neg (show ¬ D + 1 - 1 - idx < D - p from by omega),
          if_neg (show ¬ D + 1 - 1 - idx = D - p from by omega)]
        congr 2
        omega
  | .app fe b, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    rw [denoteMeta_substFvarAt hacl hainst hwa hba ha fe D hpD hfb.1,
      denoteMeta_substFvarAt hacl hainst hwa hba ha b D hpD hfb.2]
    cases denoteMeta acval env φ (D + 1) fe <;>
      cases denoteMeta acval env φ (D + 1) b <;> rfl
  | .forallE ty body mb, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    rw [denoteMeta_substFvarAt hacl hainst hwa hba ha ty D hpD hfb.1,
      ← ConLeche.Expr.substFvarAt_instantiate1 hpD hba body 0,
      denoteMeta_substFvarAt hacl hainst hwa hba ha
        (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
        (ConLeche.Expr.fvarsBelow_instantiate1 0 hfb.2),
      show D + 1 - p = D - p + 1 from by omega]
    cases denoteMeta acval env φ (D + 1) ty with
    | none => rfl
    | some ta =>
      cases denoteMeta acval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some ba => rfl
  | .lam ty body mb, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    rw [denoteMeta_substFvarAt hacl hainst hwa hba ha ty D hpD hfb.1,
      ← ConLeche.Expr.substFvarAt_instantiate1 hpD hba body 0,
      denoteMeta_substFvarAt hacl hainst hwa hba ha
        (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
        (ConLeche.Expr.fvarsBelow_instantiate1 0 hfb.2),
      show D + 1 - p = D - p + 1 from by omega]
    cases denoteMeta acval env φ (D + 1) ty with
    | none => rfl
    | some ta =>
      cases denoteMeta acval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some ba => rfl
  | .letE ty val body, D, hpD, hfb => by
    -- task #241: `denoteMeta` is `none` at a `letE`, on both sides
    simp only [ConLeche.Expr.substFvarAt, denoteMeta, Option.map_none]
  | .proj sn i e, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    rw [denoteMeta_substFvarAt hacl hainst hwa hba ha e D hpD hfb]
    cases denoteMeta acval env φ (D + 1) e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      split
      · exact congrArg some (projAV_inst _ ea x (D - p)).symm
      · rcases i with _ | _ | i <;> rfl
  | .lit (.natVal k), D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    split
    · simp only [Option.map_some]
      rw [natLitAV_inst (hainst _ _ _ _) (hainst _ _ _ _)]
    · rfl
  | .lit (.strVal s), D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denoteMeta]
    split
    · simp only [Option.map_some]
      refine congrArg some ?_
      symm
      rw [AnnotTerm.inst_app, hainst,
        charListAV_inst (by rw [AnnotTerm.inst_app, hainst, hainst])
          (by rw [AnnotTerm.inst_app, hainst, hainst]) (hainst _ _ _ _)
          (hainst _ _ _ _) (hainst _ _ _ _)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [ConLeche.Expr.sizeB]; omega)
  | (rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]
     simp [ConLeche.Expr.sizeB]; omega)
  | (simp [ConLeche.Expr.sizeB])

/-- **Beta, validated-annotation side** — the form the reduction
clauses consume: opening a binder body with the argument directly is
opening it with a fresh variable and then instantiating.  Mirror of
`denote_beta`. -/
theorem denoteMeta_beta
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} {ty body a : Expr} {x : AnnotTerm}
    (hfb : Expr.fvarsBelow d body) (hwa : Expr.WScoped d a)
    (hba : a.looseBVarsBounded 0 = true)
    (ha : denoteMeta acval env φ d a = some x) (k : Nat) :
    denoteMeta acval env φ d (body.instantiate1 a k) =
      (denoteMeta acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty) k)).map (AnnotTerm.inst · x 0) := by
  have h := denoteMeta_substFvarAt (p := d) hacl hainst hwa hba ha
    (body.instantiate1 (.fvar d ty) k) d (Nat.le_refl d)
    (ConLeche.Expr.fvarsBelow_instantiate1 k hfb)
  rw [ConLeche.Expr.substFvarAt_instantiate1_self body k hfb,
    Nat.sub_self] at h
  exact h


end ConLeche.Model
