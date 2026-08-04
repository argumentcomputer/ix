import Ix.Tc.Verify.Whnf.Beta.SimultaneousSubstitution

/-!
# Walker-tight lambda instantiation

The original `TrKExprS.instN` uses an ambient-context-size bound because its
hit case weakens the substituted argument through that context.  Production's
walker contract instead records the exact loose-binder bound of the argument.
This slice replays the same structural proof using `TrKExprS.weakBV_lbr`, so
the theorem consumes precisely the final bound carried by `WalkerRequest`.
-/

namespace Ix.Tc

open Lean4Lean

private theorem instNatLit_bx (v : Nat) (e₀ : VExpr) (k : Nat) :
    (Lean4Lean.VExpr.natLit v).inst e₀ k = Lean4Lean.VExpr.natLit v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    show Lean4Lean.VExpr.app _ _ = _
    rw [show ((Lean4Lean.VExpr.natLit v).inst e₀ k) =
        Lean4Lean.VExpr.natLit v from ih]
    rfl

private theorem instListCharLit_bx (s : List Char) (e₀ : VExpr) (k : Nat) :
    (Lean4Lean.VExpr.listCharLit s).inst e₀ k =
      Lean4Lean.VExpr.listCharLit s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    show Lean4Lean.VExpr.app (Lean4Lean.VExpr.app _ (Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.natLit c.toNat).inst e₀ k)))
      ((Lean4Lean.VExpr.listCharLit s).inst e₀ k) = _
    rw [instNatLit_bx, ih]
    rfl

private theorem instTrLiteral_bx (l : Lean.Literal) (e₀ : VExpr) (k : Nat) :
    (Lean4Lean.VExpr.trLiteral l).inst e₀ k =
      Lean4Lean.VExpr.trLiteral l := by
  cases l with
  | natVal v => exact instNatLit_bx v e₀ k
  | strVal s =>
    show Lean4Lean.VExpr.app _
      ((Lean4Lean.VExpr.listCharLit _).inst e₀ k) = _
    rw [instListCharLit_bx]
    rfl

/-- `substSpec` tracks Theory instantiation under the exact loose-binder
bound carried by a substitution walker request. -/
theorem TrKExprS.instN_lbr {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : Nat → List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (htp : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
      {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' →
      trProj uvars Γ s i e e' →
      trProj uvars Γ' s i (e.liftN n k) (e'.liftN n k))
    (htpI : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
      {Γ₁ Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
      env.HasType uvars Γ₀ e₀ A₀ →
      Lean4Lean.Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
      trProj uvars Γ₁ s i e e' →
      trProj uvars Γ s i (e.inst e₀ k) (e'.inst e₀ k))
    {Δ₀ : KVLCtx} {arg : KExpr .anon} {e₀' A₀ : VExpr}
    (harg : KExpr.Constructed arg)
    (h₀ : TrKExprS env uvars nameOf trProj Δ₀ arg e₀')
    (t₀ : env.HasType uvars Δ₀.toCtx e₀' A₀)
    {Δ₁ : KVLCtx} {body : KExpr .anon} {body' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ₁ body body') :
    ∀ {Δ : KVLCtx} {dk k : Nat} {depth : UInt64},
      KVLCtx.KInstN Δ₀ e₀' A₀ dk k Δ₁ Δ →
      depth.toNat = dk →
      arg.lbr.toNat + arg.size + depth.toNat + body.size < UInt64.size →
      TrKExprS env uvars nameOf trProj Δ
        (KExpr.substSpec body arg depth) (body'.inst e₀' k) := by
  induction H with
  | @var Δ₁' i nm md e A h =>
    intro Δ dk k depth W hdepth hbig
    rw [KExpr.substSpec]
    by_cases heq : (i == depth) = true
    · have hik : i.toNat = dk := by rw [eq_of_beq heq]; exact hdepth
      rw [if_pos heq]
      rw [show e.inst e₀' k = e₀'.liftN k from
        W.find?_hit (by rw [← hik]; exact h)]
      exact TrKExprS.weakBV_lbr henv htp harg h₀ W.toKBVLift hdepth rfl
        (by rw [show (0 : UInt64).toNat = 0 from rfl]; omega) (by omega)
    · by_cases hgt : i > depth
      · have hik : dk < i.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp hgt
          omega
        rw [if_neg heq, if_pos hgt, KExpr.mkVar_shape]
        refine .var (A := A.inst e₀' k) ?_
        have h1i : (1 : UInt64) ≤ i :=
          UInt64.le_iff_toNat_le.mpr (by
            rw [show (1 : UInt64).toNat = 1 from rfl]
            omega)
        rw [UInt64.toNat_sub_of_le i 1 h1i,
          show (1 : UInt64).toNat = 1 from rfl]
        exact W.find?_gt hik h
      · have hik : i.toNat < dk := by
          have hne : i.toNat ≠ depth.toNat := fun hh =>
            heq (beq_iff_eq.mpr (UInt64.toNat_inj.mp hh))
          have hnlt : ¬(depth.toNat < i.toNat) := fun hh =>
            hgt (UInt64.lt_iff_toNat_lt.mpr hh)
          omega
        rw [if_neg heq, if_neg hgt]
        exact .var (A := A.inst e₀' k) (W.find?_lt hik h)
  | @fvar Δ₁' fv nm md e A h =>
    intro Δ dk k depth W hdepth hbig
    exact .fvar (A := A.inst e₀' k) (W.find?_fvar h)
  | @sort Δ₁' u md h =>
    intro Δ dk k depth W hdepth hbig
    exact .sort h
  | @const Δ₁' id us md c ci h1 h2 h3 h4 =>
    intro Δ dk k depth W hdepth hbig
    exact .const h1 h2 h3 h4
  | @app Δ₁' f a md f' a' A B h1 h2 htf hta ihf iha =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : arg.lbr.toNat + arg.size + depth.toNat +
        (f.size + a.size + 1) < UInt64.size := hbig
    rw [KExpr.substSpec, KExpr.mkApp_shape]
    exact .app (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx t₀)
      (ihf W hdepth (by omega)) (iha W hdepth (by omega))
  | @lam Δ₁' nm bi ty body md ty' body' h1 htty htbody ihty ihbody =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : arg.lbr.toNat + arg.size + depth.toNat +
        (ty.size + body.size + 1) < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hdepth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.substSpec, KExpr.mkLam_shape]
    exact .lam (h1.instN henv W.toCtx t₀)
      (ihty W hdepth (by omega))
      (ihbody (W.succ (d := .vlam ty')) hc1 (by rw [hc1]; omega))
  | @all Δ₁' nm bi ty body md ty' body' h1 h2 htty htbody ihty ihbody =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : arg.lbr.toNat + arg.size + depth.toNat +
        (ty.size + body.size + 1) < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hdepth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.substSpec, KExpr.mkAll_shape]
    exact .all (h1.instN henv W.toCtx t₀)
      (h2.instN henv W.toCtx.succ t₀)
      (ihty W hdepth (by omega))
      (ihbody (W.succ (d := .vlam ty')) hc1 (by rw [hc1]; omega))
  | @letE Δ₁' nm ty val body nd md ty' val' body' h1 htty htval htbody
      ihty ihval ihbody =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : arg.lbr.toNat + arg.size + depth.toNat +
        (ty.size + val.size + body.size + 1) < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = dk + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, hdepth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    rw [KExpr.substSpec, KExpr.mkLet_shape]
    exact .letE (h1.instN henv W.toCtx t₀)
      (ihty W hdepth (by omega))
      (ihval W hdepth (by omega))
      (ihbody (W.succ (d := .vlet ty' val')) hc1 (by rw [hc1]; omega))
  | @prj Δ₁' sid field val md sName e' e'' h1 htval htrp ihval =>
    intro Δ dk k depth W hdepth hbig
    have hbig' : arg.lbr.toNat + arg.size + depth.toNat +
        (val.size + 1) < UInt64.size := hbig
    rw [KExpr.substSpec, KExpr.mkPrj_shape]
    exact .prj h1 (ihval W hdepth (by omega)) (htpI t₀ W.toCtx htrp)
  | @nat Δ₁' v blob md h =>
    intro Δ dk k depth W hdepth hbig
    rw [show (Lean4Lean.VExpr.natLit v).inst e₀' k =
        Lean4Lean.VExpr.natLit v from instNatLit_bx v e₀' k]
    exact .nat h
  | @str Δ₁' s blob md h =>
    intro Δ dk k depth W hdepth hbig
    rw [show (Lean4Lean.VExpr.trLiteral (.strVal s)).inst e₀' k =
        Lean4Lean.VExpr.trLiteral (.strVal s) from
      instTrLiteral_bx (.strVal s) e₀' k]
    exact .str h

end Ix.Tc
