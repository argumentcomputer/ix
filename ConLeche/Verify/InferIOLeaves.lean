module

public import ConLeche.Verify.InferLeaves
public import ConLeche.Verify.InferIOLemmas

public section

/-!
# Leaf-closure and loose-bvar preservation for the io lane

`ConLeche/Verify/InferLeaves.lean`'s three `inferTypeCore` preservation
inductions, at the io lane (task #161 stage 2, the io-license batch).
The reduction legs are the full lane's (`whnf_*` — the io knot is a
leaf lane), and the io app inversion's certificate **disjunct is
discarded** in all three proofs, exactly as the full proofs discard
the certificate conjunct: preservation never consumed the argument's
run, so the gate costs these lemmas nothing.  That is the structural
reason the io lane's scoping metatheory is the full lane's, clause
for clause.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

theorem inferTypeCoreIO_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCoreIO mode env fuel d e = .ok t → WScoped d e →
      WScoped d t
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [WScoped]
    | fvar idx ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure] at h
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
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure] at h
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
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, Bind.bind, Except.bind,
          pure, Except.pure] at h
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
        dsimp only [inferBodyIO, Bind.bind, Except.bind,
          pure, Except.pure] at h
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
        inferTypeCoreIO_forall_inv h
      simp [WScoped]
    | lam ty body m =>
      obtain ⟨bt, hbt, -, -, rfl⟩ :=
        inferTypeCoreIO_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCoreIO_WScoped henv fuel hbt hwo
      simp only [WScoped]
      exact ⟨hw.1, WScoped.abstract1 0 hwbt⟩
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCoreIO_app_inv h
      simp only [WScoped] at hw
      have hwtf := inferTypeCoreIO_WScoped henv fuel htf hw.1
      have hwPi := whnf_WScoped henv fuel hwh hwtf
      simp only [WScoped] at hwPi
      exact WScoped.instantiate1_gen hw.2 0 hwPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [WScoped] at hw
      have hwte := inferTypeCoreIO_WScoped henv fuel hte hw
      have hwPi := whnf_WScoped henv fuel hwt hwte
      exact projEntry_typeAt_WScoped henv hfp us hlen
        (fun a ha => hwPi.getAppArgs a ha) hw
    | bvar i =>
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCoreIO_letE_inv h).elim

theorem inferTypeCoreIO_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCoreIO mode env fuel d e = .ok t → WScoped d e →
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h; intro l hl; simp [fvarLeaves] at hl
    | fvar idx ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure] at h
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
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure] at h
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
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, Bind.bind, Except.bind,
          pure, Except.pure] at h
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
        dsimp only [inferBodyIO, Bind.bind, Except.bind,
          pure, Except.pure] at h
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
        inferTypeCoreIO_forall_inv h
      intro l hl
      simp [fvarLeaves] at hl
    | lam ty body m =>
      obtain ⟨bt, hbt, -, -, rfl⟩ :=
        inferTypeCoreIO_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCoreIO_WScoped henv fuel hbt hwo
      intro l hl
      simp only [fvarLeaves, List.mem_append] at hl ⊢
      rcases hl with hl | hl
      · exact Or.inl hl
      · obtain ⟨hlbt, hlne⟩ := fvarLeaves_abstract1_ne bt 0 hwbt l hl
        have hlo := inferTypeCoreIO_fvarLeaves henv fuel hbt hwo l hlbt
        rcases fvarLeaves_instantiate1 body 0 hlo with hb | hb
        · exact Or.inr hb
        · simp only [fvarLeaves, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd rfl hlne
          · exact Or.inl hb
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCoreIO_app_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves, List.mem_append]
      rcases fvarLeaves_instantiate1 body' 0 hl with hb | hb
      · refine Or.inl (inferTypeCoreIO_fvarLeaves henv fuel htf hw.1 l ?_)
        refine whnf_fvarLeaves henv fuel hwh l ?_
        simp [fvarLeaves, hb]
      · exact Or.inr hb
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves]
      have hsub : ∀ l', l' ∈ te.fvarLeaves → l' ∈ pe.fvarLeaves :=
        fun l' hl' =>
        inferTypeCoreIO_fvarLeaves henv fuel hte hw l'
          (whnf_fvarLeaves henv fuel hwt l' hl')
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
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCoreIO_letE_inv h).elim

theorem inferTypeCoreIO_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCoreIO mode env fuel d e = .ok t → WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      t.looseBVarsBounded 0 = true
  | 0, d, e, t, h, _, _, _ => nomatch h
  | fuel + 1, d, e, t, h, hw, hb, hLb => by
    cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [looseBVarsBounded]
    | fvar idx ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        exact hLb (idx, ty) (by simp [fvarLeaves])
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind,
        pure, Except.pure] at h
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
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, Bind.bind, Except.bind,
          pure, Except.pure] at h
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
        dsimp only [inferBodyIO, Bind.bind, Except.bind,
          pure, Except.pure] at h
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
        inferTypeCoreIO_forall_inv h
      simp [looseBVarsBounded]
    | lam ty body m =>
      obtain ⟨bt, hbt, -, -, rfl⟩ :=
        inferTypeCoreIO_lam_inv h
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
      have hbbt := inferTypeCoreIO_looseBVars henv fuel hbt hwo hbo hLbo
      simp only [looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 bt 0 hbbt⟩
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCoreIO_app_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hLbf : Expr.LeavesBounded f := fun l hl =>
        hLb l (by simp [fvarLeaves, hl])
      have hbtf := inferTypeCoreIO_looseBVars henv fuel htf hw.1 hb.1 hLbf
      have hbPi := whnf_looseBVars henv fuel hwh hbtf
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      exact looseBVarsBounded_instantiate1_gen hb.2 hbPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded] at hb
      have hLbe : Expr.LeavesBounded pe := fun l hl => hLb l (by
        simp only [fvarLeaves]; exact hl)
      have hbte := inferTypeCoreIO_looseBVars henv fuel hte hw hb hLbe
      have hbPi := whnf_looseBVars henv fuel hwt hbte
      exact projEntry_typeAt_looseBVars henv hfp us hlen
        (fun a ha => looseBVarsBounded_getAppArgs hbPi _ ha) hb
    | bvar i =>
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCoreIO_letE_inv h).elim



/-! ## The slot shims (task #172 B4)

The knot's io slot (`inferTypeIO`) inherits each scoping preservation
from whichever lane the mode selects — `inferTypeIO_off`/`_on` plus
the full- and io-lane inductions above.  Stated once here so every
walk that meets a converted call site consumes one name. -/

theorem inferTypeIO_WScoped {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) (hw : WScoped d e) :
    WScoped d t := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h
             exact inferTypeCore_WScoped henv fuel h hw
  | true => rw [inferTypeIO_on hg] at h
            exact inferTypeCoreIO_WScoped henv fuel h hw

theorem inferTypeIO_fvarLeaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) (hw : WScoped d e) :
    ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h
             exact inferTypeCore_fvarLeaves henv fuel h hw
  | true => rw [inferTypeIO_on hg] at h
            exact inferTypeCoreIO_fvarLeaves henv fuel h hw

theorem inferTypeIO_looseBVars {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) (hw : WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded e) :
    t.looseBVarsBounded 0 = true := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h
             exact inferTypeCore_looseBVars henv fuel h hw hb hLb
  | true => rw [inferTypeIO_on hg] at h
            exact inferTypeCoreIO_looseBVars henv fuel h hw hb hLb

end ConLeche
