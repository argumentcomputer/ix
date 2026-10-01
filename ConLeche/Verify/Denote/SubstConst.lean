module

public import ConLeche.Verify.Denote.Install
public import ConLeche.Verify.Denote.VClosed
import ConLeche.Verify.Denote.Shift

public section

/-!
# Substituting the operation for its own constant

`certifyNatEqs` certifies the structural-`Nat` recurrences in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value (`Expr.substConst0`); the div/mod
certificates make the same move with `substConstAll`.  Verifying an
install therefore has to move facts across that substitution — from
"`⟦substConst0 c v e⟧` in `env` under `cval`" to "`⟦e⟧` in `c₀ :: env`
under `cvalAt cval env c v`".  The two sides denote to the *same*
term, because `cvalAt` sends `c` to `v`'s denotation, which is what
`substConst0` writes in its place.

Relocated from `ConLeche/TTVerify/SubstConst.lean` (task #148, T5), with
the one generalization its own docstring predicted: the `EnvTT`
argument becomes a bare valuation plus its closedness — the only two
fields the proof read — so both verification lanes can consume it.

**`substConst0` is shallow** — it recurses through `.app` and stops —
so the lemma is restricted to the fragment the equations live in
(`sort`, `const`, `fvar`, `app`); `natOpEquations`' sides are spines
over constants and two free variables, with no binder anywhere.
-/

namespace ConLeche.Verify

open ConLeche.Term

private theorem substFn_nil0 (φ : Name → Nat) :
    Level.substFn φ [] [] = φ := funext fun _ => rfl

/-- The fragment `Expr.substConst0` is faithful on: application spines
over constants, sorts and free variables. -/
@[expose] def shallowE : Expr → Bool
  | .sort _ => true
  | .const _ _ => true
  | .fvar _ _ => true
  | .app f a => shallowE f && shallowE a
  | _ => false

/-- **The substitution lemma for the install's own constant.**  On the
shallow fragment, denoting in the *extended* environment under the
extended valuation is denoting the *substituted* expression in the old
one. -/
theorem denote_substConst0 {env : Env} {cval : TConstVal}
    (hcl : ∀ n ψ, Term.Closed (cval n ψ)) {c₀ : ConstantInfo}
    {c : Name} {v : Expr} {V : Term} (φ : Name → Nat)
    (hname : c₀.name = c) (hfresh : env.find? c = none)
    (hlp : c₀.toConstantVal.levelParams = [])
    (hv : denoteClosed cval env φ v = some V)
    (hvf : v.hasFvar = false) (hvb : v.looseBVarsBounded 0 = true) :
    ∀ (d : Nat) (e : Expr), shallowE e = true →
      denote (cvalAt cval env c v) ⟨c₀ :: env.consts⟩ φ d e
        = denote cval env φ d (Expr.substConst0 c v e) := by
  intro d e
  induction e with
  | sort u =>
    intro _
    show denote (cvalAt cval env c v) ⟨c₀ :: env.consts⟩ φ d (.sort u)
      = denote cval env φ d (.sort u)
    rw [denote_sort, denote_sort]
  | fvar idx ty =>
    intro _
    show denote (cvalAt cval env c v) ⟨c₀ :: env.consts⟩ φ d
        (.fvar idx ty) = denote cval env φ d (.fvar idx ty)
    rw [denote_fvar, denote_fvar]
  | const n us =>
    intro _
    by_cases hn : n = c
    · subst hn
      by_cases hus : us = []
      · subst hus
        rw [show Expr.substConst0 n v (.const n []) = v from by
          rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
        rw [denote_const, Env.find?_cons, if_pos hname]
        dsimp only
        rw [if_pos (by rw [hlp]; rfl), hlp, substFn_nil0, cvalAt_self hv,
          denote_depth_closed hcl hvf hvb d]
        exact hv.symm
      · show denote (cvalAt cval env n v) ⟨c₀ :: env.consts⟩ φ d
            (.const n us) = denote cval env φ d
            (Expr.substConst0 n v (.const n us))
        rw [show Expr.substConst0 n v (.const n us) = .const n us from by
          rw [Expr.substConst0, if_neg (fun h => hus h.2)]]
        rw [denote_const, denote_const, Env.find?_cons, if_pos hname,
          hfresh]
        dsimp only
        rw [if_neg (by rw [hlp]; simpa using hus)]
    · rw [show Expr.substConst0 c v (.const n us) = .const n us from by
        rw [Expr.substConst0, if_neg (fun h => hn h.1)]]
      rw [denote_const, denote_const,
        Env.find?_cons, if_neg (fun hh => hn (by rw [← hname]; exact hh.symm))]
      cases hf : env.find? n with
      | none => rfl
      | some ci =>
        dsimp only
        rw [cvalAt_ne hn]
  | app f a ihf iha =>
    intro hfr
    simp only [shallowE, Bool.and_eq_true] at hfr
    rw [show Expr.substConst0 c v (.app f a)
      = .app (Expr.substConst0 c v f) (Expr.substConst0 c v a) from rfl]
    rw [denote_app, denote_app, ihf hfr.1, iha hfr.2]
  | bvar _ => intro hfr; simp [shallowE] at hfr
  | lam _ _ _ => intro hfr; simp [shallowE] at hfr
  | forallE _ _ _ => intro hfr; simp [shallowE] at hfr
  | letE _ _ _ => intro hfr; simp [shallowE] at hfr
  | proj _ _ _ => intro hfr; simp [shallowE] at hfr
  | lit _ => intro hfr; simp [shallowE] at hfr

end ConLeche.Verify
