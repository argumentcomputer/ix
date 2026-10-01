module

public import ConLeche.Verify.Denote.Shift
public import ConLeche.Verify.Subst

public section

/-!
# Denotation commutes with instantiation

The bottleneck every interesting step of the checker's application
rule runs through: `infer` on `.app f a` returns the *expression*
`B.instantiate1 a`, while an application's type is the *term*
`(⟦B⟧).inst ⟦a⟧`, and those have to agree.

## Why the arithmetic lines up

Substituting a free variable at level `p` becomes a de Bruijn
substitution here, with no auxiliary shifting, which is not obvious in
advance:

* at depth `D + 1` the variable `fvar p` denotes `.bvar (D - p)`, so the
  substitution happens at cut `k = D - p`;
* an outer `fvar j` (`j < p`) denotes `.bvar (p-1-j)` at depth `p` and
  `.bvar (D-1-j)` at depth `D`, and `D-1-j = (p-1-j) + (D-p)` — the
  deeper denotation is the shallower one lifted by exactly `D - p`;
* `Term.inst e a k` already substitutes `liftN k a`.

So `k = D - p` makes `Term.inst`'s built-in lift *be* the depth shift,
and the substituted variable's case is discharged by `denote_lift`
(`ConLeche/Verify/Denote/Shift.lean`) with nothing left over.

## Where it is nicer for a second reason

Every binder case below is structural, because `denote` is
(`ConLeche/Verify/Denote.lean`, "Why `denote` is structural").  Had a
`let` denoted to its zeta reduct, this proof — like the shift lemma
before it — would need lifting to commute with instantiation, and then
with itself.  It needs neither.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- `projNV` commutes with instantiation (no binders; task #175
wiring W3). -/
theorem inst_projNV :
    ∀ (i : Nat) (v x : Term) (k : Nat),
      (projNV i v).inst x k = projNV i (v.inst x k)
  | 0, _, _, _ => rfl
  | i + 1, v, x, k => inst_projNV i (.snd v) x k

/-- **The substitution lemma.**  Substituting the expression `a` for
`fvar p` corresponds to instantiating the denotation at de Bruijn cut
`D - p`. -/
theorem denote_substFvarAt (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {p : Nat} {a : Expr} {x : Term}
    (hwa : Expr.WScoped p a) (hba : a.looseBVarsBounded 0 = true)
    (ha : denote cval env φ p a = some x) :
    ∀ (e : Expr) (D : Nat), p ≤ D → Expr.fvarsBelow (D + 1) e →
      denote cval env φ D (Expr.substFvarAt p a e) =
        (denote cval env φ (D + 1) e).map (Term.inst · x (D - p))
  | .bvar i, D, hpD, hfb => by simp [Expr.substFvarAt]
  | .sort u, D, hpD, hfb => by simp [Expr.substFvarAt]
  | .const n us, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_const]
    split
    · next ci hf =>
      split
      · next hlen =>
        simp only [Option.map_some]
        rw [Term.inst_eq_self_of_closed (hcl _ _)]
      · rfl
    · rfl
  | .fvar idx ty, D, hpD, hfb => by
    have hlt : idx < D + 1 := hfb
    by_cases h1 : idx = p
    · -- the substituted variable: `denote_lift` is exactly the fact
      subst h1
      rw [show Expr.substFvarAt idx a (Expr.fvar idx ty) = a from by
            simp [Expr.substFvarAt],
        denote_lift (env := env) (φ := φ) hcl hwa.fvarsBelow D hpD, ha]
      simp only [denote_fvar, Option.map_some, Term.inst_bvar,
        show D + 1 - 1 - idx = D - idx from by omega]
      simp
    · by_cases h2 : idx > p
      · simp only [Expr.substFvarAt, if_neg h1, if_pos h2, denote_fvar,
          Option.map_some, Term.inst_bvar,
          if_pos (show D + 1 - 1 - idx < D - p from by omega)]
        congr 2
        omega
      · simp only [Expr.substFvarAt, if_neg h1, if_neg h2, denote_fvar,
          Option.map_some, Term.inst_bvar,
          if_neg (show ¬ D + 1 - 1 - idx < D - p from by omega),
          if_neg (show ¬ D + 1 - 1 - idx = D - p from by omega)]
        congr 2
        omega
  | .app f b, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_app]
    rw [denote_substFvarAt hcl hwa hba ha f D hpD hfb.1,
      denote_substFvarAt hcl hwa hba ha b D hpD hfb.2]
    cases denote cval env φ (D + 1) f <;>
      cases denote cval env φ (D + 1) b <;> rfl
  | .forallE ty body m, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_forallE]
    rw [denote_substFvarAt hcl hwa hba ha ty D hpD hfb.1]
    cases hty : denote cval env φ (D + 1) ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.substFvarAt_instantiate1 hpD hba body 0,
        denote_substFvarAt hcl hwa hba ha
          (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
          (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show D + 1 - p = D - p + 1 from by omega]
      cases denote cval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, Term.inst_pi]
  | .lam ty body m, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_lam]
    rw [denote_substFvarAt hcl hwa hba ha ty D hpD hfb.1]
    cases hty : denote cval env φ (D + 1) ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.substFvarAt_instantiate1 hpD hba body 0,
        denote_substFvarAt hcl hwa hba ha
          (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
          (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show D + 1 - p = D - p + 1 from by omega]
      cases denote cval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, Term.inst_lam]
  | .letE ty val body, D, hpD, hfb => by
    -- task #241: `denote` is `none` at a `letE`, on both sides
    simp only [Expr.substFvarAt, denote_letE, Option.map_none]
  | .proj s i e, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_proj]
    rw [denote_substFvarAt hcl hwa hba ha e D hpD hfb]
    cases denote cval env φ (D + 1) e with
    | none => rfl
    | some ve =>
      simp only [Option.map_some]
      cases env.findProj? s i with
      | none =>
        dsimp only
        rcases i with _ | _ | i
        · simp only [Term.projPair?, Option.map_some, Term.inst_fst]
        · simp only [Term.projPair?, Option.map_some, Term.inst_snd]
        · rfl
      | some entry =>
        simp only [Option.map_some, inst_projNV]
  | .lit (.natVal k), D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_natLit]
    split
    · simp only [Option.map_some]
      rw [Term.inst_eq_self_of_closed
        (natLitT_closed (hcl _ _) (hcl _ _) k)]
    · rfl
  | .lit (.strVal s), D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_strLit]
    split
    · simp only [Option.map_some]
      rw [Term.inst_eq_self_of_closed (strLitT_closed hcl s)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- **Beta, denotation side** — the form the reduction clauses consume:
opening a binder body with the argument directly is opening it with a
fresh variable and then instantiating.  Transpose of `interp_beta`. -/
theorem denote_beta (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {d : Nat} {ty body a : Expr} {x : Term}
    (hfb : Expr.fvarsBelow d body) (hwa : Expr.WScoped d a)
    (hba : a.looseBVarsBounded 0 = true)
    (ha : denote cval env φ d a = some x) (k : Nat) :
    denote cval env φ d (body.instantiate1 a k) =
      (denote cval env φ (d + 1)
        (body.instantiate1 (.fvar d ty) k)).map (Term.inst · x 0) := by
  have h := denote_substFvarAt (p := d) hcl hwa hba ha
    (body.instantiate1 (.fvar d ty) k) d (Nat.le_refl d)
    (Expr.fvarsBelow_instantiate1 k hfb)
  rw [Expr.substFvarAt_instantiate1_self body k hfb, Nat.sub_self] at h
  exact h

/-! ## Name insensitivity

The standard-axiom pins compare stored types to pinned ones **up to
binder names** (they are no longer part of an `Expr`), so
every inhabitation key needs the denotation to ignore exactly what the
pin ignores.  It does — `denote` reads a binder's name only to build the
`fvar` it opens with, and an `fvar` denotes to its de Bruijn index.

**The pin's tolerance and the denotation's blindness are the same set
of syntax**, which is why a `matchesPin` hit is usable at all. -/

/-- Erasure-equal expressions denote equally. -/
theorem denote_erasedEq {cval : TConstVal} {env : Env} {φ : Name → Nat} :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
      ∀ d : Nat, denote cval env φ d e₁ = denote cval env φ d e₂
  | .bvar i, e₂, he, d => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i ty, e₂, he, d => by
    match e₂, he with
    | .fvar j ty', he =>
      obtain rfl : i = j := he
      simp [denote_fvar]
  | .sort u, e₂, he, d => by
    match e₂, he with
    | .sort u', he => obtain rfl : u = u' := he; rfl
  | .const n us, e₂, he, d => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := he
      rfl
  | .app f a, e₂, he, d => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ : Expr.ErasedEq f g ∧ Expr.ErasedEq a b := he
      simp only [denote_app, denote_erasedEq h1 d, denote_erasedEq h2 d]
  | .forallE ty body m, e₂, he, d => by
    match e₂, he with
    | .forallE ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denote_forallE, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .lam ty body m, e₂, he, d => by
    match e₂, he with
    | .lam ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denote_lam, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .letE ty vl body, e₂, he, d => by
    match e₂, he with
    | .letE ty' vl' body', he => simp only [denote_letE]
  | .lit l, e₂, he, d => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj sn i pe, e₂, he, d => by
    match e₂, he with
    | .proj sn' i' pe', he =>
      obtain ⟨rfl, rfl, h⟩ :
          sn = sn' ∧ i = i' ∧ Expr.ErasedEq pe pe' := he
      simp only [denote_proj, denote_erasedEq h d]
termination_by e₁ => e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-! ### `pw` transparency (task #161 P5)

`ConstantVal.matchesPin` now compares stored types to pinned ones up to
the binder *prop-ness datum* as well as up to binder names
(`Expr.erasePw`, `ConLeche/Kernel/StdAxioms.lean`).  The paragraph
above's rule — *a pin comparison must never forgive something the
interpretation reads* — is what has to be re-established, and it is:
`denote`'s ∀/λ clauses bind `m` and never mention it again, exactly as
they bind `n` and use it only to build the `fvar` they open with.  So
the forgiveness is again matched by blindness, and `denote_matchesPin`
keeps its statement verbatim.

The two lemmas below are the mechanical half of that.  `erasePw` is a
structural rewrite that also rewrites the *type carried on an `fvar`
leaf* — which `denote` does not read either (`denote_fvar`) — so it
commutes with `instantiate1` and the binder clauses' opened bodies line
up on the nose. -/

/-- `erasePw` commutes with opening a binder. -/
theorem Expr.erasePw_instantiate1 :
    ∀ (e v : Expr) (k : Nat),
      (e.instantiate1 v k).erasePw = e.erasePw.instantiate1 v.erasePw k := by
  intro e
  induction e <;> intro v k <;>
    simp_all [Expr.instantiate1, Expr.erasePw]
  case bvar i =>
    split
    · rfl
    · split <;> rfl

/-- **`pw` transparency**: erasing the binder prop-ness data does not
change a denotation.  `denote` reads a binder's metadata never, and its
name only to build the `fvar` it opens with. -/
theorem denote_erasePw {cval : TConstVal} {env : Env} {φ : Name → Nat} :
    ∀ (e : Expr) (d : Nat),
      denote cval env φ d e.erasePw = denote cval env φ d e
  | .bvar _, _ => rfl
  | .fvar i ty, d => by simp [Expr.erasePw, denote_fvar]
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, d => by
    simp only [Expr.erasePw, denote_app, denote_erasePw f d, denote_erasePw a d]
  | .forallE ty body m, d => by
    have hb : (body.erasePw).instantiate1 (Expr.fvar d ty.erasePw)
        = (body.instantiate1 (.fvar d ty)).erasePw := by
      rw [Expr.erasePw_instantiate1]; rfl
    simp only [Expr.erasePw, denote_forallE, denote_erasePw ty d, hb,
      denote_erasePw (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .lam ty body m, d => by
    have hb : (body.erasePw).instantiate1 (Expr.fvar d ty.erasePw)
        = (body.instantiate1 (.fvar d ty)).erasePw := by
      rw [Expr.erasePw_instantiate1]; rfl
    simp only [Expr.erasePw, denote_lam, denote_erasePw ty d, hb,
      denote_erasePw (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .letE ty vl body, d => by
    simp only [Expr.erasePw, denote_letE]
  | .lit _, _ => rfl
  | .proj sn i pe, d => by
    simp only [Expr.erasePw, denote_proj, denote_erasePw pe d]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- **The pin comparison's tolerance, as a denotation equality.**  Two
types that agree after both erasures — exactly what
`ConstantVal.matchesPin` checks of them — denote equally.  This is the
form the pinned-family shape facts (`Verify/StdAxiomPin.lean`) hand to
their consumers. -/
theorem denote_pinEq {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {a b : Expr} (h : a.erasePw = b.erasePw)
    (d : Nat) : denote cval env φ d a = denote cval env φ d b := by
  rw [← denote_erasePw a d, ← denote_erasePw b d]
  exact denote_erasedEq (h ▸ Expr.ErasedEq.rfl _) d

/-- A `matchesPin` hit lets a stored type be denoted on the pin. -/
theorem denote_matchesPin {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {cv pin : ConstantVal} (h : ConstantVal.matchesPin cv pin = true)
    (d : Nat) :
    denote cval env φ d cv.type = denote cval env φ d pin.type := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, beq_iff_eq] at h
  rw [← denote_erasePw cv.type d, ← denote_erasePw pin.type d]
  exact denote_erasedEq (h.2 ▸ Expr.ErasedEq.rfl _) d

end ConLeche.Verify
