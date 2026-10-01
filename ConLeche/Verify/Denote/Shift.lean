module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.Denote.VClosed
public import ConLeche.Verify.Shift
import ConLeche.Verify.Abstract

public section

/-!
# Depth shifting

Reading the same expression at two depths, and what it costs that
`denote` carries no free-variable valuation.

## A lift, not an equation

A free variable at level `i` read at depth `d` denotes `.bvar (d-1-i)`
(`ConLeche/Verify/Denote.lean`), which is depth-*relative*.  So the two
readings are not equal; they are related by a lift:

```
WScoped p e → p ≤ D →
  denote cval env φ D e = (denote cval env φ p e).map (·.liftN (D - p))
```

This is the second half of the same trade as
`ConLeche/Verify/Denote/VClosed.lean`'s: `denote` saves a valuation
parameter on every clause, and pays for it here and in `cval_closed`.

## The generalization: a shift, not a lift

An induction on `D` alone, stepping down by one, does not close,
because its binder clause compares

```
denote (D+2) (body.instantiate1 (.fvar (D+1) ty))
denote (D+1) (body.instantiate1 (.fvar  D    ty))
```

— two **genuinely different expressions**, related by
`Expr.shiftFrom D` (`ConLeche/Verify/Shift.lean`).  So `denote.induct` on
a single expression cannot see them, and the statement has to be
generalized over the *cut*: `denote_shiftFrom` below relates `e` and
`e.shiftFrom p` with the lift cut `d - p`, which the binder clause
increments to `(d - p) + 1` exactly as `Term.liftN` increments its
own cut.  That is why the generalization closes.

The fact that makes the cut behave: **the freshly opened variable
denotes `.bvar 0` at every level.**  `fvar d` at depth `d + 1` and
`fvar (d+1)` at depth `d + 2` both come out `.bvar 0`, so only the
*outer* variables move, and they move by exactly one.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- Lifts at cut `0` compose by addition. -/
theorem liftN_liftN : ∀ (v : Term) (m n k : Nat),
    Term.liftN n (Term.liftN m v k) k = Term.liftN (m + n) v k := by
  intro v
  induction v with
  | bvar i =>
    intro m n k
    simp only [Term.liftN_bvar]
    by_cases h : i < k
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg (show ¬ i + m < k by omega)]
      congr 1; omega
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha => intro m n k; simp only [Term.liftN_app, ihf, iha]
  | lam A b ihA ihb => intro m n k; simp only [Term.liftN_lam, ihA, ihb]
  | pi A B ihA ihB => intro m n k; simp only [Term.liftN_pi, ihA, ihB]
  | eqE a b iha ihb =>
    intro m n k; simp only [Term.liftN_eqE, iha, ihb]
  | fst e ihe => intro m n k; simp only [Term.liftN_fst, ihe]
  | snd e ihe => intro m n k; simp only [Term.liftN_snd, ihe]

/-- Lifting by zero is the identity. -/
theorem liftN_zero : ∀ (v : Term) (k : Nat), Term.liftN 0 v k = v := by
  intro v
  induction v with
  | bvar i => intro k; simp only [Term.liftN_bvar]; split <;> rfl
  | sort u => intro _; rfl
  | const c us => intro _; rfl
  | prf => intro _; rfl
  | app f a ihf iha => intro k; simp only [Term.liftN_app, ihf, iha]
  | lam A b ihA ihb => intro k; simp only [Term.liftN_lam, ihA, ihb]
  | pi A B ihA ihB => intro k; simp only [Term.liftN_pi, ihA, ihB]
  | eqE a b iha ihb => intro k; simp only [Term.liftN_eqE, iha, ihb]
  | fst e ihe => intro k; simp only [Term.liftN_fst, ihe]
  | snd e ihe => intro k; simp only [Term.liftN_snd, ihe]

/-- A `Nat` literal's term is closed when the two constructor
valuations are. -/
theorem natLitT_closed {zv sv : Term} (hz : Term.Closed zv)
    (hs : Term.Closed sv) : ∀ n, Term.Closed (natLitT zv sv n)
  | 0 => hz
  | n + 1 => ⟨hs, natLitT_closed hz hs n⟩

/-- A character list's term is closed when its constituents are. -/
theorem charListT_closed {nilV consV ofNatV zv sv : Term}
    (hn : Term.Closed nilV) (hc : Term.Closed consV)
    (ho : Term.Closed ofNatV) (hz : Term.Closed zv)
    (hs : Term.Closed sv) :
    ∀ cs : List Char, Term.Closed (charListT nilV consV ofNatV zv sv cs)
  | [] => hn
  | c :: cs =>
    ⟨⟨hc, ⟨ho, natLitT_closed hz hs c.toNat⟩⟩,
      charListT_closed hn hc ho hz hs cs⟩

/-- A `String` literal's term is closed when the valuation is. -/
theorem strLitT_closed (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    (s : String) : Term.Closed (strLitT cval env φ s) := by
  refine ⟨hcl _ _, charListT_closed ?_ ?_ (hcl _ _) (hcl _ _) (hcl _ _)
    s.toList⟩
  · exact ⟨hcl _ _, hcl _ _⟩
  · exact ⟨hcl _ _, hcl _ _⟩

/-- `projNV` commutes with lifting (it introduces no binders; task
#175 wiring W3). -/
theorem liftN_projNV (n : Nat) :
    ∀ (i : Nat) (v : Term) (k : Nat),
      (projNV i v).liftN n k = projNV i (v.liftN n k)
  | 0, _, _ => rfl
  | i + 1, v, k => liftN_projNV n i (.snd v) k

/-- `projNV` preserves bvar bounds (hereditary proj clauses). -/
theorem projNV_bvarsBelow {d : Nat} :
    ∀ (i : Nat) {v : Term}, Term.bvarsBelow d v →
      Term.bvarsBelow d (projNV i v)
  | 0, _, h => h
  | i + 1, v, h => projNV_bvarsBelow i (v := .snd v) h

/-- **Depth shifting.**  Denoting `e.shiftFrom p` one level deeper is
denoting `e` and lifting at cut `d - p`.

The `cval` closedness hypothesis is what lets the `.const` and literal
clauses go through: a constant's term must not move when the context
around it grows (`ConLeche/Verify/Denote/VClosed.lean`). -/
theorem denote_shiftFrom (hcl : ∀ n ψ, Term.Closed (cval n ψ)) {p : Nat} :
    ∀ (e : Expr) (d : Nat), p ≤ d → Expr.fvarsBelow d e →
      denote cval env φ (d + 1) (e.shiftFrom p) =
        (denote cval env φ d e).map (Term.liftN 1 · (d - p))
  | .bvar i, d, hpd, hfb => by simp [Expr.shiftFrom]
  | .sort u, d, hpd, hfb => by simp [Expr.shiftFrom]
  | .const n us, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_const]
    split
    · next ci hf =>
      split
      · next hlen =>
        simp only [Option.map_some]
        rw [Term.liftN_eq_self_of_closed (hcl _ _)]
      · rfl
    · rfl
  | .fvar idx ty, d, hpd, hfb => by
    have hlt : idx < d := hfb
    simp only [Expr.shiftFrom]
    split
    · next hge =>
      -- at or above the shift point: the index does not move, because
      -- `d + 1 - 1 - (idx + 1) = d - 1 - idx`
      rw [denote_fvar, denote_fvar, Option.map_some, Term.liftN_bvar,
        if_pos (show d - 1 - idx < d - p by omega),
        show d + 1 - 1 - (idx + 1) = d - 1 - idx from by omega]
    · next hge =>
      -- below the shift point: the index moves up by one
      rw [denote_fvar, denote_fvar, Option.map_some, Term.liftN_bvar,
        if_neg (show ¬ d - 1 - idx < d - p by omega),
        show d + 1 - 1 - idx = d - 1 - idx + 1 from by omega]
  | .app f a, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_app]
    rw [denote_shiftFrom hcl f d hpd hfb.1, denote_shiftFrom hcl a d hpd hfb.2]
    cases denote cval env φ d f <;> cases denote cval env φ d a <;> rfl
  | .forallE ty body m, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_forallE]
    rw [denote_shiftFrom hcl ty d hpd hfb.1]
    cases hty : denote cval env φ d ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.shiftFrom_instantiate1 hpd body 0,
        denote_shiftFrom hcl (body.instantiate1 (.fvar d ty)) (d + 1)
          (by omega) (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show d + 1 - p = d - p + 1 from by omega]
      cases denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, Term.liftN_pi]
  | .lam ty body m, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_lam]
    rw [denote_shiftFrom hcl ty d hpd hfb.1]
    cases hty : denote cval env φ d ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.shiftFrom_instantiate1 hpd body 0,
        denote_shiftFrom hcl (body.instantiate1 (.fvar d ty)) (d + 1)
          (by omega) (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show d + 1 - p = d - p + 1 from by omega]
      cases denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, Term.liftN_lam]
  | .letE ty val body, d, hpd, hfb => by
    -- task #241: `denote` is `none` at a `letE`, on both sides
    simp only [Expr.shiftFrom, denote_letE, Option.map_none]
  | .proj s i e, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_proj]
    rw [denote_shiftFrom hcl e d hpd hfb]
    cases denote cval env φ d e with
    | none => rfl
    | some ve =>
      simp only [Option.map_some]
      cases env.findProj? s i with
      | none =>
        dsimp only
        rcases i with _ | _ | i
        · simp only [Term.projPair?, Option.map_some, Term.liftN_fst]
        · simp only [Term.projPair?, Option.map_some, Term.liftN_snd]
        · rfl
      | some entry =>
        simp only [Option.map_some, liftN_projNV]
  | .lit (.natVal k), d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_natLit]
    split
    · simp only [Option.map_some]
      rw [Term.liftN_eq_self_of_closed
        (natLitT_closed (hcl _ _) (hcl _ _) k)]
    · rfl
  | .lit (.strVal s), d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_strLit]
    split
    · simp only [Option.map_some]
      rw [Term.liftN_eq_self_of_closed (strLitT_closed hcl s)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- One level of weakening: denoting a `d`-scoped term at `d + 1` lifts
it by one.  The transpose of `interp_weaken_top`, and the step
`denote_lift`'s induction takes. -/
theorem denote_weaken_top (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {d : Nat} {e : Expr} (hfb : Expr.fvarsBelow d e) :
    denote cval env φ (d + 1) e =
      (denote cval env φ d e).map (Term.liftN 1 · 0) := by
  have h := denote_shiftFrom (env := env) (φ := φ) hcl e d (Nat.le_refl d) hfb
  rw [Expr.shiftFrom_eq_self hfb, Nat.sub_self] at h
  exact h

/-- **Depth lifting** — the transpose of `interp_lift`.  Where the model
gets a literal equation (its valuation absorbs the depth), the bridge
gets a lift; see the module docstring for why that deviation is forced
rather than chosen. -/
theorem denote_lift (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {p : Nat} {e : Expr} (hfb : Expr.fvarsBelow p e) :
    ∀ D : Nat, p ≤ D →
      denote cval env φ D e =
        (denote cval env φ p e).map (Term.liftN (D - p) · 0) := by
  intro D
  induction D with
  | zero =>
    intro hpD
    have hp : p = 0 := by omega
    subst hp
    simp only [Nat.sub_self]
    cases denote cval env φ 0 e with
    | none => rfl
    | some v => simp only [Option.map_some, liftN_zero]
  | succ D ih =>
    intro hpD
    by_cases hpD' : p = D + 1
    · subst hpD'
      simp only [Nat.sub_self]
      cases denote cval env φ (D + 1) e with
      | none => rfl
      | some v => simp only [Option.map_some, liftN_zero]
    · have hpD2 : p ≤ D := by omega
      rw [denote_weaken_top hcl (Expr.fvarsBelow_mono hpD2 hfb), ih hpD2]
      cases denote cval env φ p e with
      | none => rfl
      | some v =>
        simp only [Option.map_some, liftN_liftN]
        congr 2
        omega

/-! ## Scoping transfers to the denotation

The one place the `Expr`/`Term` separation of §12.6 is crossed
*deliberately*: a term scoped below depth `d` denotes to a `Term`
whose bound variables are below `d`.  That is not a leak — it is the
direction that *does* hold, because `denote` maps an `fvar` at index
`idx < d` to `.bvar (d - 1 - idx) < d` and opens each binder one level
deeper.  The converse (typing telling you about syntax) is what does
not hold.

Consumed at the `.const` clause of `inferBody`, where the stored type
is a closed `Expr` and its denotation has to be a closed `Term` for
the environment invariant's typing to survive `denote_lift`. -/

theorem denote_bvarsBelow (hcl : ∀ n ψ, Term.Closed (cval n ψ)) :
    ∀ (d : Nat) (e : Expr), Expr.WScoped d e →
      e.looseBVarsBounded 0 = true →
      ∀ {v : Term}, denote cval env φ d e = some v →
        Term.bvarsBelow d v := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env) (φ := φ) with
  | case1 d u =>
    intro _ _ v h
    rw [denote_sort] at h
    obtain rfl : v = .sort (u.eval φ) := (Option.some.inj h).symm
    trivial
  | case2 d idx ty =>
    intro hws _ v h
    rw [denote_fvar] at h
    obtain rfl : v = .bvar (d - 1 - idx) := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_refl d)
  | case3 d n us ci h1 h2 =>
    intro _ _ v h
    simp only [denote_const, h1, if_pos h2] at h
    obtain rfl : v = cval n (Level.substFn φ ci.toConstantVal.levelParams us) :=
      (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d) (hcl _ _)
  | case4 d n us ci h1 h2 =>
    intro _ _ v h; simp only [denote_const, h1, if_neg h2] at h; exact nomatch h
  | case5 d n us h1 =>
    intro _ _ v h; rw [denote_const, h1] at h; exact nomatch h
  | case6 d ty body mb h1 ihty =>
    intro _ _ v h; rw [denote_forallE, h1] at h; exact nomatch h
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    intro _ _ v h; rw [denote_forallE, h1, h2] at h; exact nomatch h
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hws hb v h
    rw [denote_forallE, h1, h2] at h
    obtain rfl : v = .pi B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty hws.1 hb.1 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case9 d ty body mb h1 ihty =>
    intro _ _ v h; rw [denote_lam, h1] at h; exact nomatch h
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    intro _ _ v h; rw [denote_lam, h1, h2] at h; exact nomatch h
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hws hb v h
    rw [denote_lam, h1, h2] at h
    obtain rfl : v = .lam B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty hws.1 hb.1 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case12 d f a vf va h1 h2 ihf iha =>
    intro hws hb v h
    rw [denote_app, h1, h2] at h
    obtain rfl : v = .app vf va := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf hws.1 hb.1 h2, iha hws.2 hb.2 h1⟩
  | case13 d f a hbad ihf iha =>
    intro _ _ v h
    rw [denote_app] at h
    split at h
    · next vf va k1 k2 => exact (hbad vf va k1 k2).elim
    · exact nomatch h
  | case14 d ty val body =>
    intro _ _ v h; rw [denote_letE] at h; exact nomatch h
  | case15 d sn i e h1 ihe =>
    intro _ _ v h; rw [denote_proj, h1] at h; exact nomatch h
  | case16 d sn i e B h1 entry h2 ihe =>
    intro hws hb v h
    rw [denote_proj, h1, h2] at h
    simp only [Option.some.injEq] at h
    simp only [Expr.WScoped] at hws
    obtain rfl : v = projNV (i + entry.off) B := h.symm
    exact projNV_bvarsBelow _ (ihe hws hb h1)
  | case17 d sn i e B h1 h2 ihe =>
    intro hws hb v h
    rw [denote_proj, h1, h2] at h
    simp only [Expr.WScoped] at hws
    have hB : Term.bvarsBelow d B := ihe hws hb h1
    rcases i with _ | _ | i
    · simp only [Term.projPair?, Option.some.injEq] at h
      exact h ▸ hB
    · simp only [Term.projPair?, Option.some.injEq] at h
      exact h ▸ hB
    · exact nomatch h
  | case18 d n hg =>
    intro _ _ v h
    rw [denote_natLit, if_pos hg] at h
    obtain rfl := (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d)
      (natLitT_closed (hcl _ _) (hcl _ _) n)
  | case19 d n hg =>
    intro _ _ v h; rw [denote_natLit, if_neg hg] at h; exact nomatch h
  | case20 d t hg =>
    intro _ _ v h
    rw [denote_strLit, if_pos hg] at h
    obtain rfl := (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d) (strLitT_closed hcl t)
  | case21 d t hg =>
    intro _ _ v h; rw [denote_strLit, if_neg hg] at h; exact nomatch h
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro _ _ v h
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

/-- A closed expression denotes to a closed term. -/
theorem denote_closed (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} {v : Term} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denoteClosed cval env φ e = some v) : Term.Closed v :=
  denote_bvarsBelow hcl 0 e (Expr.WScoped.of_not_hasFvar hnf) hb h

/-- **A closed expression denotes the same at every depth.**  The
binder depth only enters `denote` through `fvar` leaves and there are
none, so the whole `denote_weaken_top` chain collapses.  Consumed
wherever a *stored declaration's* type has to be denoted in an open
context — the environment states its typing at depth `0`. -/
theorem denote_depth_closed (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) :
    ∀ d : Nat, denote cval env φ d e = denoteClosed cval env φ e := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [denote_weaken_top hcl (Expr.WScoped.of_not_hasFvar (d := d)
      hnf).fvarsBelow, ih]
    cases hv : denoteClosed cval env φ e with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      rw [Term.liftN_eq_self_of_closed (denote_closed hcl hnf hb hv)]

end ConLeche.Verify
