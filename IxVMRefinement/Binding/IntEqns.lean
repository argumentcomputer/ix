import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.Binding.OpInstall
import IxVMRefinement.Binding.EqnsKit

/-! # Certified `Int` primitive equations (`PrimEqnEnv`)

Derives `Core.PrimEqnEnv env` from `BaseKit env` and `Shapes (· < 77) env`, turning the
validated equations of `Decidable`, `ite`, `Nat.decEq`, and the `Int` family (groups `46..76`)
into closed kernel `Red` derivations on canonical `intLitExpr` and `Nat` literal terms at every
depth. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Rules (Red DefEq Infer PiRed Grade)

/-! ## Multi-variable substitution congruence and generic equation eliminators -/

section EqnElim

variable {env : Ix.Kernel.Env .anon}

private abbrev Γ₀ : Nat → KExpr := fun _ => .sort .zero
private abbrev ΓNat1 : Nat → KExpr := fvarUpdate Γ₀ 0 BaseKit.natT
private abbrev ΓNat2 : Nat → KExpr := fvarUpdate ΓNat1 1 BaseKit.natT

private theorem lbb_abstract1_ge (d : Nat) :
    ∀ (e : KExpr) {k m : Nat}, k < m → (e.abstract1 d k).looseBVarsBounded m = e.looseBVarsBounded m
  | .bvar _, _, _, _ => rfl
  | .fvar _ _, k, m, hkm => by
    simp only [Ix.Kernel.Expr.abstract1]
    split <;> simp [Ix.Kernel.Expr.looseBVarsBounded, hkm]
  | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, k, m, hkm => by
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      lbb_abstract1_ge d f hkm, lbb_abstract1_ge d a hkm]
  | .lam ty b _, k, m, hkm | .forallE ty b _, k, m, hkm => by
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      lbb_abstract1_ge d ty hkm, lbb_abstract1_ge d b (Nat.succ_lt_succ hkm)]
  | .letE ty v b _, k, m, hkm => by
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      lbb_abstract1_ge d ty hkm, lbb_abstract1_ge d v hkm,
      lbb_abstract1_ge d b (Nat.succ_lt_succ hkm)]
  | .proj _ _ e, k, m, hkm => by
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      lbb_abstract1_ge d e hkm]

private theorem lbb_abstract1_succ (d : Nat) (e : KExpr) (m : Nat) :
    (e.abstract1 d).looseBVarsBounded (m + 1) = e.looseBVarsBounded (m + 1) :=
  lbb_abstract1_ge d e (Nat.zero_lt_succ m)

private theorem lbb_of_lbb0 {e : KExpr} (h : e.looseBVarsBounded 0 = true) (k : Nat) :
    e.looseBVarsBounded k = true :=
  looseBVarsBounded_mono e (Nat.zero_le k) h

private theorem inst1_of_lbb0 {e : KExpr} (h : e.looseBVarsBounded 0 = true) (v : KExpr) (k : Nat) :
    e.instantiate1 v k = e :=
  instantiate1_eq_self e (lbb_of_lbb0 h k)

private theorem fvarSubst_comm {d₁ d₂ : Nat} {v₁ v₂ : KExpr} (hne : d₁ ≠ d₂)
    (hv₁ : v₁.hasFvar = false) (hv₂ : v₂.hasFvar = false) :
    ∀ {e : KExpr}, fvarSubst d₂ v₂ (fvarSubst d₁ v₁ e) = fvarSubst d₁ v₁ (fvarSubst d₂ v₂ e)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar idx ty => by
    by_cases h1 : idx = d₁
    · subst h1
      simp [fvarSubst, hne, fvarSubst_of_not_hasFvar hv₁]
    · by_cases h2 : idx = d₂
      · subst h2
        simp [fvarSubst, h1, fvarSubst_of_not_hasFvar hv₂]
      · simp [fvarSubst, h1, h2]
  | .app f a => by simp [fvarSubst, fvarSubst_comm hne hv₁ hv₂]
  | .lam t b _ => by simp [fvarSubst, fvarSubst_comm hne hv₁ hv₂]
  | .forallE t b _ => by simp [fvarSubst, fvarSubst_comm hne hv₁ hv₂]
  | .letE t v b _ => by simp [fvarSubst, fvarSubst_comm hne hv₁ hv₂]
  | .proj _ _ e => by simp [fvarSubst, fvarSubst_comm (e := e) hne hv₁ hv₂]

private theorem fvarSubst2_defEq {d i j : Nat} {v₁ v₂ w₁ w₂ : KExpr} (hne : i ≠ j)
    (hv : DefEq env d v₁ v₂) (hw : DefEq env d w₁ w₂)
    (hv1 : v₁.hasFvar = false) (hv2 : v₂.hasFvar = false) :
    ∀ {e : KExpr}, isSimpleExpr e = true →
      DefEq env d (fvarSubst j w₁ (fvarSubst i v₁ e)) (fvarSubst j w₂ (fvarSubst i v₂ e))
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => .refl
  | .fvar idx _, _ => by
    by_cases h1 : idx = i
    · subst h1
      simp only [fvarSubst, ↓reduceIte, fvarSubst_of_not_hasFvar hv1, fvarSubst_of_not_hasFvar hv2]
      exact hv
    · by_cases h2 : idx = j
      · subst h2
        simp only [fvarSubst, h1, ↓reduceIte]
        exact hw
      · simp [fvarSubst, h1, h2]
        exact .refl
  | .app f a, h => by
    simp only [isSimpleExpr, Bool.and_eq_true] at h
    exact .app (fvarSubst2_defEq hne hv hw hv1 hv2 h.1) (fvarSubst2_defEq hne hv hw hv1 hv2 h.2)

private theorem fvarSubst5_defEq {d : Nat}
    {a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 : KExpr}
    (h0 : DefEq env d a0 b0) (h1 : DefEq env d a1 b1) (h2 : DefEq env d a2 b2)
    (h3 : DefEq env d a3 b3) (h4 : DefEq env d a4 b4)
    (ha0 : a0.hasFvar = false) (hb0 : b0.hasFvar = false)
    (ha1 : a1.hasFvar = false) (hb1 : b1.hasFvar = false)
    (ha2 : a2.hasFvar = false) (hb2 : b2.hasFvar = false)
    (ha3 : a3.hasFvar = false) (hb3 : b3.hasFvar = false) :
    ∀ {e : KExpr}, isSimpleExpr e = true →
      DefEq env d
        (fvarSubst 4 a4 (fvarSubst 3 a3 (fvarSubst 2 a2 (fvarSubst 1 a1 (fvarSubst 0 a0 e)))))
        (fvarSubst 4 b4 (fvarSubst 3 b3 (fvarSubst 2 b2 (fvarSubst 1 b1 (fvarSubst 0 b0 e)))))
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => .refl
  | .fvar idx _, _ => by
    match idx with
    | 0 => simp [fvarSubst, fvarSubst_of_not_hasFvar ha0, fvarSubst_of_not_hasFvar hb0]; exact h0
    | 1 => simp [fvarSubst, fvarSubst_of_not_hasFvar ha1, fvarSubst_of_not_hasFvar hb1]; exact h1
    | 2 => simp [fvarSubst, fvarSubst_of_not_hasFvar ha2, fvarSubst_of_not_hasFvar hb2]; exact h2
    | 3 => simp [fvarSubst, fvarSubst_of_not_hasFvar ha3, fvarSubst_of_not_hasFvar hb3]; exact h3
    | 4 => simp [fvarSubst]; exact h4
    | _ + 5 => simp [fvarSubst]; exact .refl
  | .app f a, h => by
    simp only [isSimpleExpr, Bool.and_eq_true] at h
    exact .app
      (fvarSubst5_defEq h0 h1 h2 h3 h4 ha0 hb0 ha1 hb1 ha2 hb2 ha3 hb3 h.1)
      (fvarSubst5_defEq h0 h1 h2 h3 h4 ha0 hb0 ha1 hb1 ha2 hb2 ha3 hb3 h.2)

/-- Eliminate a 0-variable, 0-hypothesis, 0-level equation `e`. -/
theorem applyEqn0 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    (hvars : e.vars = []) (hhyps : e.hyps = []) (hlev : e.level = .succ .zero)
    {Cw : KExpr} (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hlhs : ClosedAt env e.lhs Cw) (hrhs : ClosedAt env e.rhs Cw)
    (hCcl : TermClosed e.carrier := by exact ⟨rfl, rfl⟩) :
    DefEq env 0 e.lhs e.rhs := by
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simpa [eqnsSideExact, hvars] using hde
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    have hEqC : ClosedType env
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) hlhs.witness) hrhs.witness) .zero :=
      closedType_eq bk.eqStored hC hlhs.wInfer hlhs.wClosed hrhs.wInfer hrhs.wClosed
    have hStmt : eqnsStmtExact e =
        .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs := by
      simp [eqnsStmtExact, hvars, hhyps, hlev]
    have hStmtCl : TermClosed (eqnsStmtExact e) := by
      rw [hStmt]; exact (((TermClosed.const _ _).app hCcl).app hlhs.closed).app hrhs.closed
    have hStmtPi : PiRed env 0
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) hlhs.witness) hrhs.witness)
        (eqnsStmtExact e) := by
      rw [hStmt]
      exact .app (.app (.app (.ofRed .refl) (.ofRed hCred)) (.ofRed hlhs.wRed)) (.ofRed hrhs.wRed)
    have hp := ClosedAt.ofThm0_de bk.storeClosed hf hlen hde hStmtCl hStmtPi hEqC
    exact defEq_of_eqProof_de bk.storeClosed bk.eqStored hp
      (.app (.app (.app .refl .refl) hlhs.defEq_witness) hrhs.defEq_witness) hlhs hrhs hC

/-- Eliminate a 1-variable, 0-hypothesis, 0-level equation `e` at closed argument `a`. -/
theorem applyEqn1 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    {T₀ T₀w Cw lhsW rhsW a lhsA rhsA : KExpr} {u₀ : KLevel}
    (hvars : e.vars = [T₀]) (hhyps : e.hyps = []) (hlev : e.level = .succ .zero)
    (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hCcl : e.carrier.hasFvar = false) (hCbl : e.carrier.looseBVarsBounded 0 = true)
    (hDom : OpenType env 0 Γ₀ T₀ T₀w u₀)
    (hLhsBl : e.lhs.looseBVarsBounded 0 = true) (hRhsBl : e.rhs.looseBVarsBounded 0 = true)
    (hLhsS : isSimpleExpr e.lhs = true) (hRhsS : isSimpleExpr e.rhs = true)
    (hLhsO : OpenAt env 1 (fvarUpdate Γ₀ 0 T₀w) (fvarSubst 0 (.fvar 0 T₀w) e.lhs) lhsW Cw)
    (hRhsO : OpenAt env 1 (fvarUpdate Γ₀ 0 T₀w) (fvarSubst 0 (.fvar 0 T₀w) e.rhs) rhsW Cw)
    (ha : ClosedAt env a T₀w)
    (heL : fvarSubst 0 a e.lhs = lhsA) (heR : fvarSubst 0 a e.rhs = rhsA)
    (hLhsInst : DefEq env 0 (fvarSubst 0 ha.witness lhsW) lhsA)
    (hRhsInst : DefEq env 0 (fvarSubst 0 ha.witness rhsW) rhsA)
    (hLhsCl : ClosedAt env lhsA Cw) (hRhsCl : ClosedAt env rhsA Cw)
    (hLhsNL : lhsW.lamPw = none := by rfl) (hRhsNL : rhsW.lamPw = none := by rfl) :
    DefEq env 0 lhsA rhsA := by
  have hsc := bk.storeClosed
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp only [eqnsSideExact, hvars, hlev, List.zipIdx, List.foldr, bmeta,
      Ix.Kernel.Level.zeronessOf] at hde
    have hCO := OpenType.ofClosed hsc (d := 1) (Γ := fvarUpdate Γ₀ 0 T₀w) hC
    have hLamL := OpenAt.lam_abs_inner (pw := .never) hLhsBl hDom hLhsO hCO.wInfer hCO.wRed rfl hLhsNL
    have hLamR := OpenAt.lam_abs_inner (pw := .never) hRhsBl hDom hRhsO hCO.wInfer hCO.wRed rfl hRhsNL
    have haO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ha hDom.wOk.hasFvar_false
    have hAppL := hLamL.app_abs haO .refl hC.closed.2
    have hAppR := hLamR.app_abs haO .refl hC.closed.2
    have hRedL : Red env 0 (.app (.lam T₀w (lhsW.abstract1 0) { pw := .never }) ha.witness)
        (fvarSubst 0 ha.witness lhsW) := by
      have h := Red.beta (env := env) (d := 0) (ty := T₀w) (body := lhsW.abstract1 0)
        (mb := { pw := .never }) ha.wInfer.toIO .refl
      rwa [abstract1_instantiate1_eq_fvarSubst hLhsO.wClosed] at h
    have hRedR : Red env 0 (.app (.lam T₀w (rhsW.abstract1 0) { pw := .never }) ha.witness)
        (fvarSubst 0 ha.witness rhsW) := by
      have h := Red.beta (env := env) (d := 0) (ty := T₀w) (body := rhsW.abstract1 0)
        (mb := { pw := .never }) ha.wInfer.toIO .refl
      rwa [abstract1_instantiate1_eq_fvarSubst hRhsO.wClosed] at h
    exact OpenAt.defEq_chain hAppL hAppR (.app hde .refl) hRedL hLhsInst hRedR hRhsInst
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    let eqRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs
    have hEqBl : eqRaw.looseBVarsBounded 0 = true := by
      simp [eqRaw, Ix.Kernel.Expr.looseBVarsBounded, hCbl, hLhsBl, hRhsBl]
    have hCO := OpenType.liftClosed hsc (d := 1) (Γ := fvarUpdate Γ₀ 0 T₀w) hC (.ofRed hCred) ⟨hCcl, hCbl⟩
    have hEqO : OpenType env 1 (fvarUpdate Γ₀ 0 T₀w) (fvarSubst 0 (.fvar 0 T₀w) eqRaw)
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW) .zero := by
      simp [eqRaw, fvarSubst, fvarSubst_of_not_hasFvar hCcl]
      exact OpenType.eq bk.eqStored hCO hLhsO .refl hRhsO .refl
    have hStmtO := OpenType.forallE_abs (pw := .ifAllZero []) hEqBl hDom hEqO rfl
    have hStmtEq : eqnsStmtExact e = .forallE T₀ (eqRaw.abstract1 0) { pw := .ifAllZero [] } := by
      simp [eqnsStmtExact, eqRaw, hvars, hhyps, hlev]
    rw [← hStmtEq] at hStmtO
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hEqO.wClosed
    simp [fvarSubst, fvarSubst_of_not_hasFvar hC.closed.1] at hp1
    exact defEq_of_eqProof_de hsc bk.eqStored hp1
      (.app (.app (.app .refl .refl) hLhsInst) hRhsInst) hLhsCl hRhsCl hC

/-- Eliminate a 2-variable (non-dependent domains), 0-hypothesis, 0-level equation `e` at closed
arguments `a, b`. -/
theorem applyEqn2 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    {T₀ T₀w T₁ T₁w Cw lhsW rhsW a b lhsAB rhsAB : KExpr} {u₀ u₁ : KLevel}
    (hvars : e.vars = [T₀, T₁]) (hhyps : e.hyps = []) (hlev : e.level = .succ .zero)
    (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hCcl : e.carrier.hasFvar = false) (hCbl : e.carrier.looseBVarsBounded 0 = true)
    (hDom0 : OpenType env 0 Γ₀ T₀ T₀w u₀)
    (hDom1 : OpenType env 0 Γ₀ T₁ T₁w u₁)
    (hT1cl : T₁.hasFvar = false) (hT1bl : T₁.looseBVarsBounded 0 = true)
    (hLhsBl : e.lhs.looseBVarsBounded 0 = true) (hRhsBl : e.rhs.looseBVarsBounded 0 = true)
    (hLhsS : isSimpleExpr e.lhs = true) (hRhsS : isSimpleExpr e.rhs = true)
    (hLhsO : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w)
      (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) e.lhs)) lhsW Cw)
    (hRhsO : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w)
      (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) e.rhs)) rhsW Cw)
    (ha : ClosedAt env a T₀w) (hb : ClosedAt env b T₁w)
    (heL : fvarSubst 1 b (fvarSubst 0 a e.lhs) = lhsAB)
    (heR : fvarSubst 1 b (fvarSubst 0 a e.rhs) = rhsAB)
    (hLhsInst : DefEq env 0 (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness lhsW)) lhsAB)
    (hRhsInst : DefEq env 0 (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness rhsW)) rhsAB)
    (hLhsCl : ClosedAt env lhsAB Cw) (hRhsCl : ClosedAt env rhsAB Cw)
    (hLhsNL : lhsW.lamPw = none := by rfl) (hRhsNL : rhsW.lamPw = none := by rfl) :
    DefEq env 0 lhsAB rhsAB := by
  have hsc := bk.storeClosed
  have hT0wCl : T₀w.hasFvar = false := hDom0.wOk.hasFvar_false
  have hT1wCl : T₁w.hasFvar = false := hDom1.wOk.hasFvar_false
  let Γ1 := fvarUpdate Γ₀ 0 T₀w
  let Γ2 := fvarUpdate Γ1 1 T₁w
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (wscopedB_of_hasFvar_false T₀w hT0wCl)
  have hDom1_1 : OpenType env 1 Γ1 T₁ T₁w u₁ :=
    OpenType.liftClosed hsc (d := 1) (Γ := Γ1) hDom1.toClosedType hDom1.wPiRed ⟨hT1cl, hT1bl⟩
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp only [eqnsSideExact, hvars, hlev, List.zipIdx, List.foldr, bmeta,
      Ix.Kernel.Level.zeronessOf] at hde
    have hCO := OpenType.ofClosed hsc (d := 2) (Γ := Γ2) hC
    have hLamL1 := OpenAt.lam_abs_inner (pw := .never) (fvarSubst_looseBVarsBounded rfl hLhsBl)
      hDom1_1 hLhsO hCO.wInfer hCO.wRed rfl hLhsNL hCtx1
    have hLamR1 := OpenAt.lam_abs_inner (pw := .never) (fvarSubst_looseBVarsBounded rfl hRhsBl)
      hDom1_1 hRhsO hCO.wInfer hCO.wRed rfl hRhsNL hCtx1
    have hL1bl : (Ix.Kernel.Expr.lam T₁ (e.lhs.abstract1 1) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hLhsBl]
    have hR1bl : (Ix.Kernel.Expr.lam T₁ (e.rhs.abstract1 1) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hRhsBl]
    have hLamL0 := OpenAt.lam_abs_outer hL1bl hDom0
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
            ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]; exact hLamL1)
    have hLamR0 := OpenAt.lam_abs_outer hR1bl hDom0
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
            ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]; exact hLamR1)
    have haO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ha hT0wCl
    have hbO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hb hT1wCl
    have hTy1Bl : (Ix.Kernel.Expr.forallE T₁w (Cw.abstract1 1) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hDom1.wClosed, looseBVarsBounded_abstract1' hC.closed.2]
    have hAppL1 := hLamL0.app_abs haO .refl hTy1Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
      fvarSubst_of_not_hasFvar hC.closed.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hbO .refl hC.closed.2
    have hAppR1 := hLamR0.app_abs haO .refl hTy1Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
      fvarSubst_of_not_hasFvar hC.closed.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hbO .refl hC.closed.2
    have hRedL1 : Red env 0
        (.app (.lam T₀w ((Ix.Kernel.Expr.lam T₁w (lhsW.abstract1 1) { pw := .never }).abstract1 0) { pw := .never }) ha.witness)
        (.lam T₁w ((fvarSubst 0 ha.witness lhsW).abstract1 1) { pw := .never }) := by
      have h := Red.beta (env := env) (d := 0) (ty := T₀w)
        (body := (Ix.Kernel.Expr.lam T₁w (lhsW.abstract1 1) { pw := .never }).abstract1 0)
        (mb := { pw := .never }) ha.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom1.wClosed, looseBVarsBounded_abstract1' hLhsO.wClosed])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl,
        ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] using h
    have hRedL2 : Red env 0
        (.app (.lam T₁w ((fvarSubst 0 ha.witness lhsW).abstract1 1) { pw := .never }) hb.witness)
        (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness lhsW)) := by
      have h := Red.beta (env := env) (d := 0) (ty := T₁w)
        (body := (fvarSubst 0 ha.witness lhsW).abstract1 1)
        (mb := { pw := .never }) hb.wInfer.toIO .refl
      rwa [abstract1_instantiate1_eq_fvarSubst (fvarSubst_looseBVarsBounded ha.wClosed.2 hLhsO.wClosed)] at h
    have hRedR1 : Red env 0
        (.app (.lam T₀w ((Ix.Kernel.Expr.lam T₁w (rhsW.abstract1 1) { pw := .never }).abstract1 0) { pw := .never }) ha.witness)
        (.lam T₁w ((fvarSubst 0 ha.witness rhsW).abstract1 1) { pw := .never }) := by
      have h := Red.beta (env := env) (d := 0) (ty := T₀w)
        (body := (Ix.Kernel.Expr.lam T₁w (rhsW.abstract1 1) { pw := .never }).abstract1 0)
        (mb := { pw := .never }) ha.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom1.wClosed, looseBVarsBounded_abstract1' hRhsO.wClosed])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl,
        ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] using h
    have hRedR2 : Red env 0
        (.app (.lam T₁w ((fvarSubst 0 ha.witness rhsW).abstract1 1) { pw := .never }) hb.witness)
        (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness rhsW)) := by
      have h := Red.beta (env := env) (d := 0) (ty := T₁w)
        (body := (fvarSubst 0 ha.witness rhsW).abstract1 1)
        (mb := { pw := .never }) hb.wInfer.toIO .refl
      rwa [abstract1_instantiate1_eq_fvarSubst (fvarSubst_looseBVarsBounded ha.wClosed.2 hRhsO.wClosed)] at h
    exact OpenAt.defEq_chain hAppL2 hAppR2 (.app (.app hde .refl) .refl)
      (.trans (.appFn hRedL1) hRedL2) hLhsInst (.trans (.appFn hRedR1) hRedR2) hRhsInst
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    let eqRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs
    have hEqBl : eqRaw.looseBVarsBounded 0 = true := by
      simp [eqRaw, Ix.Kernel.Expr.looseBVarsBounded, hCbl, hLhsBl, hRhsBl]
    have hCO := OpenType.liftClosed hsc (d := 2) (Γ := Γ2) hC (.ofRed hCred) ⟨hCcl, hCbl⟩
    have hEqO : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) eqRaw))
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW) .zero := by
      simp [eqRaw, fvarSubst, fvarSubst_of_not_hasFvar hCcl]
      exact OpenType.eq bk.eqStored hCO hLhsO .refl hRhsO .refl
    have hBody1O : OpenType env 1 Γ1
        (fvarSubst 0 (.fvar 0 T₀w) (.forallE T₁ (eqRaw.abstract1 1) { pw := .ifAllZero [] }))
        (.forallE T₁w ((Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW).abstract1 1)
          { pw := .ifAllZero [] })
        (.imax u₁ .zero) := by
      simp [fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
        ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]
      exact OpenType.forallE_abs (fvarSubst_looseBVarsBounded rfl hEqBl) hDom1_1 hEqO rfl hCtx1
    have hB1bl : (Ix.Kernel.Expr.forallE T₁ (eqRaw.abstract1 1) { pw := .ifAllZero [] }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hEqBl]
    have hStmtO := OpenType.forallE_abs (pw := .ifAllZero []) hB1bl hDom0 hBody1O rfl
    have hStmtEq : eqnsStmtExact e =
        .forallE T₀ ((Ix.Kernel.Expr.forallE T₁ (eqRaw.abstract1 1) { pw := .ifAllZero [] }).abstract1 0) { pw := .ifAllZero [] } := by
      simp [eqnsStmtExact, eqRaw, hvars, hhyps, hlev]
    rw [← hStmtEq] at hStmtO
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hBody1O.wClosed
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] at hp1
    have hp2 := hp1.app_abs hb .refl (fvarSubst_looseBVarsBounded ha.wClosed.2 hEqO.wClosed)
    simp [fvarSubst, fvarSubst_of_not_hasFvar hC.closed.1] at hp2
    exact defEq_of_eqProof_de hsc bk.eqStored hp2
      (.app (.app (.app .refl .refl) hLhsInst) hRhsInst) hLhsCl hRhsCl hC

/-- Eliminate a 2-variable, 1-`Bool`-equality-hypothesis, 0-level conditional equation `e` at
closed arguments `a, b` when the guard reduces to `gR` (`true` or `false`). -/
theorem applyEqn2Hyp1 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    {T₀ T₀w T₁ T₁w Cw gL gLw gR lhsW rhsW a b lhsAB rhsAB : KExpr} {u₀ u₁ : KLevel}
    (hvars : e.vars = [T₀, T₁])
    (hhyps : e.hyps = [.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gL) gR])
    (hlev : e.level = .succ .zero)
    (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hCcl : e.carrier.hasFvar = false) (hCbl : e.carrier.looseBVarsBounded 0 = true)
    (hDom0 : OpenType env 0 Γ₀ T₀ T₀w u₀)
    (hDom1 : OpenType env 0 Γ₀ T₁ T₁w u₁)
    (hT1cl : T₁.hasFvar = false) (hT1bl : T₁.looseBVarsBounded 0 = true)
    (hgLbl : gL.looseBVarsBounded 0 = true) (hgRcl : ClosedAt env gR BaseKit.boolT)
    (hLhsBl : e.lhs.looseBVarsBounded 0 = true) (hRhsBl : e.rhs.looseBVarsBounded 0 = true)
    (hgLO : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w)
      (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) gL)) gLw BaseKit.boolT)
    (hLhsO : OpenAt env 3
      (fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w) 2
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
      (fvarSubst 2 (.fvar 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
        (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) e.lhs)))
      lhsW Cw)
    (hRhsO : OpenAt env 3
      (fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w) 2
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
      (fvarSubst 2 (.fvar 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
        (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) e.rhs)))
      rhsW Cw)
    (hLhsNo2 : ∀ v, fvarSubst 2 v lhsW = lhsW)
    (hRhsNo2 : ∀ v, fvarSubst 2 v rhsW = rhsW)
    (ha : ClosedAt env a T₀w) (hb : ClosedAt env b T₁w)
    (hGuard : DefEq env 0 (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness gLw)) hgRcl.witness)
    (hLhsInst : DefEq env 0 (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness lhsW)) lhsAB)
    (hRhsInst : DefEq env 0 (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness rhsW)) rhsAB)
    (hLhsCl : ClosedAt env lhsAB Cw) (hRhsCl : ClosedAt env rhsAB Cw) :
    DefEq env 0 lhsAB rhsAB := by
  have hsc := bk.storeClosed
  have hT0wCl : T₀w.hasFvar = false := hDom0.wOk.hasFvar_false
  have hT1wCl : T₁w.hasFvar = false := hDom1.wOk.hasFvar_false
  rcases hv with ⟨hemp, _⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp [hhyps] at hemp
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    let Γ1 := fvarUpdate Γ₀ 0 T₀w
    let Γ2 := fvarUpdate Γ1 1 T₁w
    have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (wscopedB_of_hasFvar_false T₀w hT0wCl)
    have hCtx2 : CtxWs 2 Γ2 := hCtx1.update (wscopedB_of_hasFvar_false T₁w hT1wCl)
    let hypRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gL) gR
    let hypW : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness
    let Γ3 := fvarUpdate Γ2 2 hypW
    let eqRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs
    let eqW : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW
    have hEqBl : eqRaw.looseBVarsBounded 0 = true := by
      simp [eqRaw, Ix.Kernel.Expr.looseBVarsBounded, hCbl, hLhsBl, hRhsBl]
    have hHypBl : hypRaw.looseBVarsBounded 0 = true := by
      simp [hypRaw, Ix.Kernel.Expr.looseBVarsBounded, hgLbl, hgRcl.closed.2]
    have hBool2 := OpenType.ofClosed hsc (d := 2) (Γ := Γ2) bk.boolType
    have hgRO2 : OpenAt env 2 Γ2 gR hgRcl.witness BaseKit.boolT :=
      OpenAt.ofClosed hsc hgRcl rfl
    have hHypO : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) hypRaw)) hypW .zero := by
      simp [hypRaw, fvarSubst, fvarSubst_of_not_hasFvar hgRcl.closed.1]
      exact OpenType.eq bk.eqStored hBool2 hgLO .refl hgRO2 .refl
    have hCO3 := OpenType.liftClosed hsc (d := 3) (Γ := Γ3) hC (.ofRed hCred) ⟨hCcl, hCbl⟩
    have hEqO : OpenType env 3 Γ3
        (fvarSubst 2 (.fvar 2 hypW) (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) eqRaw)))
        eqW .zero := by
      simp [eqRaw, fvarSubst, fvarSubst_of_not_hasFvar hCcl]
      exact OpenType.eq bk.eqStored hCO3 hLhsO .refl hRhsO .refl
    let hBody2Raw : KExpr := .forallE hypRaw (eqRaw.abstract1 2) { pw := .ifAllZero [] }
    have hBody2Bl : hBody2Raw.looseBVarsBounded 0 = true := by
      simp [hBody2Raw, Ix.Kernel.Expr.looseBVarsBounded, hHypBl, looseBVarsBounded_abstract1' hEqBl]
    have hBody2O : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) hBody2Raw))
        (.forallE hypW (eqW.abstract1 2) { pw := .ifAllZero [] }) (.imax .zero .zero) := by
      simp [hBody2Raw, fvarSubst,
        ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 2),
        ← fvarSubst_abstract1_comm_fvar (by decide : (1 : Nat) ≠ 2)]
      exact OpenType.forallE_abs
        (fvarSubst_looseBVarsBounded rfl (fvarSubst_looseBVarsBounded rfl hEqBl))
        hHypO hEqO rfl hCtx2
    have hDom1_1 : OpenType env 1 Γ1 T₁ T₁w u₁ :=
      OpenType.liftClosed hsc (d := 1) (Γ := Γ1) hDom1.toClosedType hDom1.wPiRed ⟨hT1cl, hT1bl⟩
    let hBody1Raw : KExpr := .forallE T₁ (hBody2Raw.abstract1 1) { pw := .ifAllZero [] }
    have hBody1Bl : hBody1Raw.looseBVarsBounded 0 = true := by
      simp [hBody1Raw, Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hBody2Bl]
    have hBody1O : OpenType env 1 Γ1
        (fvarSubst 0 (.fvar 0 T₀w) hBody1Raw)
        (.forallE T₁w ((Ix.Kernel.Expr.forallE hypW (eqW.abstract1 2) { pw := .ifAllZero [] }).abstract1 1) { pw := .ifAllZero [] })
        (.imax u₁ (.imax .zero .zero)) := by
      simp [hBody1Raw, fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
        ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]
      exact OpenType.forallE_abs (fvarSubst_looseBVarsBounded rfl hBody2Bl) hDom1_1 hBody2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs (pw := .ifAllZero []) hBody1Bl hDom0 hBody1O rfl
    have hStmtEq : eqnsStmtExact e = .forallE T₀ (hBody1Raw.abstract1 0) { pw := .ifAllZero [] } := by
      simp [eqnsStmtExact, hBody1Raw, hBody2Raw, hypRaw, eqRaw, hvars, hhyps, hlev]
    rw [← hStmtEq] at hStmtO
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hBody1O.wClosed
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] at hp1
    have hp2 := hp1.app_abs hb .refl (fvarSubst_looseBVarsBounded ha.wClosed.2 hBody2O.wClosed)
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1] at hp2
    have hrefl := closedAt_eqRefl bk.eqReflStored bk.boolType hgRcl
    have hHypMatch : DefEq env 0
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) hgRcl.witness) hgRcl.witness)
        (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness hypW)) := by
      simp [hypW, fvarSubst, fvarSubst_of_not_hasFvar hgRcl.wClosed.1]
      exact .app (.app (.app .refl .refl) hGuard.symm) .refl
    have hp3 := hp2.app_abs hrefl hHypMatch
      (fvarSubst_looseBVarsBounded hb.wClosed.2 (fvarSubst_looseBVarsBounded ha.wClosed.2 hEqO.wClosed))
    simp [eqW, fvarSubst, fvarSubst_of_not_hasFvar hC.closed.1] at hp3
    rw [fvarSubst_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1 hrefl.wClosed.1,
        fvarSubst_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1 hrefl.wClosed.1,
        hLhsNo2,
        fvarSubst_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1 hrefl.wClosed.1,
        fvarSubst_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1 hrefl.wClosed.1,
        hRhsNo2] at hp3
    exact defEq_of_eqProof_de hsc bk.eqStored hp3
      (.app (.app (.app .refl .refl) hLhsInst) hRhsInst) hLhsCl hRhsCl hC

end EqnElim

/-! ## Role witness bundle (`IntKit`) -/

/-- Exact closed witnesses for all roles involved in `Decidable`, `ite`, `Nat.decEq`, and `Int`.
The seven type/proposition-forming witnesses are explicit parameters so all dependent types
stay transparent without `Prop`-to-`Type` elimination. -/
structure IntKit (env : Ix.Kernel.Env .anon)
    (wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd : KExpr) where
  bk : BaseKit env
  shapes : Shapes (· < 77) env
  decAt : ClosedAt env (.const (.role .decidable) [])
    (.forallE (.sort .zero) (.sort (.succ .zero)) { pw := .never })
  decW : decAt.witness = wDec
  notAt : ClosedAt env (.const (.role .notProp) [])
    (.forallE (.sort .zero) (.sort .zero) { pw := .never })
  notW : notAt.witness = wNot
  isTrueAt : ClosedAt env (.const (.role .decidableIsTrue) [])
    (.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort .zero))
        ((Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).abstract1 1) { pw := .never }).abstract1 0)
      { pw := .never })
  isFalseAt : ClosedAt env (.const (.role .decidableIsFalse) [])
    (.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.app wNot (.fvar 0 (.sort .zero)))
        ((Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).abstract1 1) { pw := .never }).abstract1 0)
      { pw := .never })
  decideAt : ClosedAt env (.const (.role .decidableDecide) [])
    (.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
        (BaseKit.boolT.abstract1 1) { pw := .never }).abstract1 0)
      { pw := .never })
  decideW : decideAt.witness = wDecide
  ofDecideTrueAt : ClosedAt env (.const (.role .ofDecideEqTrue) [])
    (.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
        ((Ix.Kernel.Expr.forallE
          (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
            (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar 1 (.app wDec (.fvar 0 (.sort .zero))))))
            BaseKit.trueE)
          ((Ix.Kernel.Expr.fvar 0 (.sort .zero)).abstract1 2) { pw := .ifAllZero [] }).abstract1 1)
        { pw := .ifAllZero [] }).abstract1 0)
      { pw := .ifAllZero [] })
  ofDecideFalseAt : ClosedAt env (.const (.role .ofDecideEqFalse) [])
    (.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
        ((Ix.Kernel.Expr.forallE
          (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
            (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar 1 (.app wDec (.fvar 0 (.sort .zero))))))
            BaseKit.falseE)
          ((Ix.Kernel.Expr.app wNot (.fvar 0 (.sort .zero))).abstract1 2) { pw := .ifAllZero [] }).abstract1 1)
        { pw := .ifAllZero [] }).abstract1 0)
      { pw := .ifAllZero [] })
  intAt : ClosedAt env (.const (.role .int) []) (.sort (.succ .zero))
  intW : intAt.witness = wInt
  intOfNatAt : ClosedAt env (.const (.role .intOfNat) []) (.forallE BaseKit.natT wInt { pw := .never })
  intOfNatW : intOfNatAt.witness = wIntOfNat
  intNegSuccAt : ClosedAt env (.const (.role .intNegSucc) []) (.forallE BaseKit.natT wInt { pw := .never })
  intLeAt : ClosedAt env (.const (.role .intLe) [])
    (.forallE wInt (.forallE wInt (.sort .zero) { pw := .never }) { pw := .never })
  intLeW : intLeAt.witness = wIntLe
  iteAt : ClosedAt env (.const (.role .ifThenElse) [.succ .zero])
    (.forallE (.sort (.succ .zero))
      ((Ix.Kernel.Expr.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 1 (.sort .zero)))
          ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort (.succ .zero)))
            ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort (.succ .zero)))
              ((Ix.Kernel.Expr.fvar 0 (.sort (.succ .zero))).abstract1 4) { pw := .never }).abstract1 3)
            { pw := .never }).abstract1 2)
          { pw := .never }).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  natDecEqAt : ClosedAt env (.const (.role .natDecEq) [])
    (.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE BaseKit.natT
        ((Ix.Kernel.Expr.app wDec (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
          (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  intNegOfNatAt : ClosedAt env (.const (.role .intNegOfNat) []) (.forallE BaseKit.natT wInt { pw := .never })
  intSubNatNatAt : ClosedAt env (.const (.role .intSubNatNat) [])
    (.forallE BaseKit.natT (.forallE BaseKit.natT wInt { pw := .never }) { pw := .never })
  intNegAt : ClosedAt env (.const (.role .intNeg) []) (.forallE wInt wInt { pw := .never })
  intNatAbsAt : ClosedAt env (.const (.role .intNatAbs) []) (.forallE wInt BaseKit.natT { pw := .never })
  intAddAt : ClosedAt env (.const (.role .intAdd) [])
    (.forallE wInt (.forallE wInt wInt { pw := .never }) { pw := .never })
  intAddW : intAddAt.witness = wIntAdd
  intSubAt : ClosedAt env (.const (.role .intSub) [])
    (.forallE wInt (.forallE wInt wInt { pw := .never }) { pw := .never })
  intMulAt : ClosedAt env (.const (.role .intMul) [])
    (.forallE wInt (.forallE wInt wInt { pw := .never }) { pw := .never })
  intEdivAt : ClosedAt env (.const (.role .intEdiv) [])
    (.forallE wInt (.forallE wInt wInt { pw := .never }) { pw := .never })
  intEmodAt : ClosedAt env (.const (.role .intEmod) [])
    (.forallE wInt (.forallE wInt wInt { pw := .never }) { pw := .never })
  intPowAt : ClosedAt env (.const (.role .intPow) [])
    (.forallE wInt (.forallE BaseKit.natT wInt { pw := .never }) { pw := .never })
  intDecLeAt : ClosedAt env (.const (.role .intDecLe) [])
    (.forallE wInt
      ((Ix.Kernel.Expr.forallE wInt
        ((Ix.Kernel.Expr.app wDec (.app (.app wIntLe (.fvar 0 wInt)) (.fvar 1 wInt))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  intDecLtAt : ClosedAt env (.const (.role .intDecLt) [])
    (.forallE wInt
      ((Ix.Kernel.Expr.forallE wInt
        ((Ix.Kernel.Expr.app wDec
          (.app (.app wIntLe
            (.app (.app wIntAdd (.fvar 0 wInt))
              (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
            (.fvar 1 wInt))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  intBmodAt : ClosedAt env (.const (.role .intBmod) [])
    (.forallE wInt (.forallE BaseKit.natT wInt { pw := .never }) { pw := .never })
  intBdivAt : ClosedAt env (.const (.role .intBdiv) [])
    (.forallE wInt (.forallE BaseKit.natT wInt { pw := .never }) { pw := .never })
  isTrueTy_nf : (Ix.Kernel.Expr.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort .zero))
        ((Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).abstract1 1) { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  isFalseTy_nf : (Ix.Kernel.Expr.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.app wNot (.fvar 0 (.sort .zero)))
        ((Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).abstract1 1) { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  decideTy_nf : (Ix.Kernel.Expr.forallE (.sort .zero)
      ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
        (BaseKit.boolT.abstract1 1) { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  iteTy_nf : (Ix.Kernel.Expr.forallE (.sort (.succ .zero))
      ((Ix.Kernel.Expr.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 1 (.sort .zero)))
          ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort (.succ .zero)))
            ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort (.succ .zero)))
              ((Ix.Kernel.Expr.fvar 0 (.sort (.succ .zero))).abstract1 4) { pw := .never }).abstract1 3)
            { pw := .never }).abstract1 2)
          { pw := .never }).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  natDecEqTy_nf : (Ix.Kernel.Expr.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE BaseKit.natT
        ((Ix.Kernel.Expr.app wDec (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
          (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  intDecLeTy_nf : (Ix.Kernel.Expr.forallE wInt
      ((Ix.Kernel.Expr.forallE wInt
        ((Ix.Kernel.Expr.app wDec (.app (.app wIntLe (.fvar 0 wInt)) (.fvar 1 wInt))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  intDecLtTy_nf : (Ix.Kernel.Expr.forallE wInt
      ((Ix.Kernel.Expr.forallE wInt
        ((Ix.Kernel.Expr.app wDec
          (.app (.app wIntLe
            (.app (.app wIntAdd (.fvar 0 wInt))
              (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
            (.fvar 1 wInt))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false

/-! ### Constructing `IntKit` from `BaseKit` and `Shapes (· < 77)` -/

section BuildIntKit

variable {env : Ix.Kernel.Env .anon}

private theorem eqnsShape_of (hs : Shapes (· < 77) env) (r : Role)
    (h46 : 46 ≤ Ix.SpecDigest.groupOf r) : EqnsRoleShape env r :=
  hs.eqns r h46 (RoleVal.groupOf_lt_77 r)

private theorem roleExact_eqns (hs : Shapes (· < 77) env) (r : Role)
    (h46 : 46 ≤ Ix.SpecDigest.groupOf r) (h5 : RoleVal.roleSpecKindNat r = 5) :
    RoleExactTy env r :=
  ((eqnsShape_of hs r h46).1 h5).1

private theorem roleExact_anchor_of (hs : Shapes (· < 77) env) (r ar : Role)
    (h46 : 46 ≤ Ix.SpecDigest.groupOf r) (h5 : RoleVal.roleSpecKindNat r = 5)
    (har : ar ∈ eqnsAnchorsOf r) : RoleExactTy env ar :=
  ((eqnsShape_of hs r h46).1 h5).2.1 ar har

private theorem roleExact_walked (hs : Shapes (· < 77) env) (r : Role)
    (h46 : 46 ≤ Ix.SpecDigest.groupOf r) (h1 : RoleVal.roleSpecKindNat r = 1)
    (hw : RoleVal.anchorWalked r = true) : RoleExactTy env r :=
  (eqnsShape_of hs r h46).2 h1 hw

private theorem eqnValid_of (hs : Shapes (· < 77) env) (r : Role)
    (h46 : 46 ≤ Ix.SpecDigest.groupOf r) (h5 : RoleVal.roleSpecKindNat r = 5)
    {k : Nat} {e : Ix.Kernel.Equation .anon} (hget : (eqnsOfRole r)[k]? = some e) :
    EqnValid env r e :=
  ((eqnsShape_of hs r h46).1 h5).2.2 e (List.mem_of_getElem? hget)

/-- Build `IntKit` from `BaseKit env` and `Shapes (· < 77) env`. -/
theorem intKit_exists (bk : BaseKit env) (hs : Shapes (· < 77) env) :
    ∃ wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd,
      Nonempty (IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) := by
  have hsc := bk.storeClosed
  have hwf := bk.wf
  -- 1. `Decidable` and `Not`
  have hDecTy : ClosedType env (.forallE (.sort .zero) (.sort (.succ .zero)) { pw := .never })
      (.imax (.succ .zero) (.succ (.succ .zero))) :=
    ClosedType.forall_nondep hsc (ClosedType.sort env .zero) (ClosedType.sort env (.succ .zero))
  have decAt : ClosedAt env (.const (.role .decidable) [])
      (.forallE (.sort .zero) (.sort (.succ .zero)) { pw := .never }) :=
    ClosedAt.ofRole0 hsc
      (roleExact_anchor_of hs .decidableDecide .decidable (by decide) (by decide) (by decide))
      (by decide) rfl hDecTy
  let wDec := decAt.witness
  have hwDecCl : TermClosed wDec := decAt.wClosed
  have hNotTy : ClosedType env (.forallE (.sort .zero) (.sort .zero) { pw := .never })
      (.imax (.succ .zero) (.succ .zero)) :=
    ClosedType.forall_nondep hsc (ClosedType.sort env .zero) (ClosedType.sort env .zero)
  have notAt : ClosedAt env (.const (.role .notProp) [])
      (.forallE (.sort .zero) (.sort .zero) { pw := .never }) :=
    ClosedAt.ofRole0 hsc
      (roleExact_anchor_of hs .decidableDecide .notProp (by decide) (by decide) (by decide))
      (by decide) rfl hNotTy
  let wNot := notAt.witness
  -- 2. `Decidable.isTrue`, `Decidable.isFalse`, `Decidable.decide`
  have isTrueO : OpenType env 0 Γ₀
      (.forallE (.sort .zero)
        (.forallE (.bvar 0) (.app (.const (.role .decidable) []) (.bvar 1)) { pw := .never })
        { pw := .never })
      (.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort .zero))
          ((Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).abstract1 1) { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax .zero (.succ .zero))) := by
    refine OpenType.forallE (OpenType.sort .zero) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofOpenAt (OpenAt.fvar (d := 1) (idx := 0) (by omega))) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    exact OpenType.ofOpenAt
      ((OpenAt.ofClosed hsc decAt rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (by omega)) .refl rfl)
  have isTrueAt := ClosedAt.ofRole0_open hsc
    (roleExact_anchor_of hs .decidableDecide .decidableIsTrue (by decide) (by decide) (by decide))
    (by decide) rfl isTrueO
  have isFalseO : OpenType env 0 Γ₀
      (.forallE (.sort .zero)
        (.forallE (.app (.const (.role .notProp) []) (.bvar 0))
          (.app (.const (.role .decidable) []) (.bvar 1)) { pw := .never })
        { pw := .never })
      (.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.app wNot (.fvar 0 (.sort .zero)))
          ((Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).abstract1 1) { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax .zero (.succ .zero))) := by
    refine OpenType.forallE (OpenType.sort .zero) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hDom1 : OpenType env 1 (fvarUpdate Γ₀ 0 (.sort .zero))
        (.app (.const (.role .notProp) []) (.fvar 0 (.sort .zero)))
        (.app wNot (.fvar 0 (.sort .zero))) .zero :=
      OpenType.ofOpenAt
        ((OpenAt.ofClosed hsc notAt rfl).app_nondep (OpenAt.fvar (d := 1) (idx := 0) (by omega)) .refl rfl)
    refine OpenType.forallE hDom1 ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    exact OpenType.ofOpenAt
      ((OpenAt.ofClosed hsc decAt rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (by omega)) .refl rfl)
  have isFalseAt := ClosedAt.ofRole0_open hsc
    (roleExact_anchor_of hs .decidableDecide .decidableIsFalse (by decide) (by decide) (by decide))
    (by decide) rfl isFalseO
  have decideO : OpenType env 0 Γ₀
      (.forallE (.sort .zero)
        (.forallE (.app (.const (.role .decidable) []) (.bvar 0)) BaseKit.boolT { pw := .never })
        { pw := .never })
      (.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
          (BaseKit.boolT.abstract1 1) { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (OpenType.sort .zero) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hDom1 : OpenType env 1 (fvarUpdate Γ₀ 0 (.sort .zero))
        (.app (.const (.role .decidable) []) (.fvar 0 (.sort .zero)))
        (.app wDec (.fvar 0 (.sort .zero))) (.succ .zero) :=
      OpenType.ofOpenAt
        ((OpenAt.ofClosed hsc decAt rfl).app_nondep (OpenAt.fvar (d := 1) (idx := 0) (by omega)) .refl rfl)
    refine OpenType.forallE hDom1 ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    exact OpenType.ofClosed hsc bk.boolType
  have decideAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .decidableDecide (by decide) (by decide))
    (by decide) rfl decideO
  let wDecide := decideAt.witness
  -- 3. `of_decide_eq_true` and `of_decide_eq_false`
  have ofDecTrueO : OpenType env 0 Γ₀
      (.forallE (.sort .zero)
        (.forallE (.app (.const (.role .decidable) []) (.bvar 0))
          (.forallE
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
              (.app (.app (.const (.role .decidableDecide) []) (.bvar 1)) (.bvar 0)))
              BaseKit.trueE)
            (.bvar 2) { pw := .ifAllZero [] })
          { pw := .ifAllZero [] })
        { pw := .ifAllZero [] })
      (.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
          ((Ix.Kernel.Expr.forallE
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
              (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar 1 (.app wDec (.fvar 0 (.sort .zero))))))
              BaseKit.trueE)
            ((Ix.Kernel.Expr.fvar 0 (.sort .zero)).abstract1 2) { pw := .ifAllZero [] }).abstract1 1)
          { pw := .ifAllZero [] }).abstract1 0)
        { pw := .ifAllZero [] })
      (.imax (.succ .zero) (.imax (.succ .zero) (.imax .zero .zero))) := by
    refine OpenType.forallE (OpenType.sort .zero) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hDom1 : OpenType env 1 (fvarUpdate Γ₀ 0 (.sort .zero))
        (.app (.const (.role .decidable) []) (.fvar 0 (.sort .zero)))
        (.app wDec (.fvar 0 (.sort .zero))) (.succ .zero) :=
      OpenType.ofOpenAt
        ((OpenAt.ofClosed hsc decAt rfl).app_nondep (OpenAt.fvar (d := 1) (idx := 0) (by omega)) .refl rfl)
    refine OpenType.forallE hDom1 ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 (.sort .zero)) 1 (.app wDec (.fvar 0 (.sort .zero)))
    have hDec2 : OpenAt env 2 Γ2
        (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero)))
          (.fvar 1 (.app wDec (.fvar 0 (.sort .zero)))))
        (.app (.app wDecide (.fvar 0 (.sort .zero)))
          (.fvar 1 (.app wDec (.fvar 0 (.sort .zero)))))
        BaseKit.boolT := by
      have h1 := (OpenAt.ofClosed hsc decideAt decideO.wOk.hasFvar_false).app_abs
        (OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)) .refl
        (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, hwDecCl.2])
      simp [fvarSubst, fvarSubst_of_not_hasFvar hwDecCl.1] at h1
      have h2 := h1.app_abs (OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)) .refl rfl
      simpa [Γ2, fvarUpdate, fvarSubst] using h2
    have hDom2 := OpenType.eq bk.eqStored (OpenType.ofClosed hsc bk.boolType) hDec2 .refl
      (OpenAt.ofClosed hsc bk.boolTrueAt rfl) .refl
    refine OpenType.forallE hDom2 ?_ rfl
    exact OpenType.ofOpenAt (OpenAt.fvar (d := 3) (idx := 0) (by omega))
  have ofDecideTrueAt := ClosedAt.ofRole0_open hsc
    (roleExact_walked hs .ofDecideEqTrue (by decide) (by decide) (by decide))
    (by decide) rfl ofDecTrueO
  have ofDecFalseO : OpenType env 0 Γ₀
      (.forallE (.sort .zero)
        (.forallE (.app (.const (.role .decidable) []) (.bvar 0))
          (.forallE
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
              (.app (.app (.const (.role .decidableDecide) []) (.bvar 1)) (.bvar 0)))
              BaseKit.falseE)
            (.app (.const (.role .notProp) []) (.bvar 2)) { pw := .ifAllZero [] })
          { pw := .ifAllZero [] })
        { pw := .ifAllZero [] })
      (.forallE (.sort .zero)
        ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 0 (.sort .zero)))
          ((Ix.Kernel.Expr.forallE
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
              (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar 1 (.app wDec (.fvar 0 (.sort .zero))))))
              BaseKit.falseE)
            ((Ix.Kernel.Expr.app wNot (.fvar 0 (.sort .zero))).abstract1 2) { pw := .ifAllZero [] }).abstract1 1)
          { pw := .ifAllZero [] }).abstract1 0)
        { pw := .ifAllZero [] })
      (.imax (.succ .zero) (.imax (.succ .zero) (.imax .zero .zero))) := by
    refine OpenType.forallE (OpenType.sort .zero) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hDom1 : OpenType env 1 (fvarUpdate Γ₀ 0 (.sort .zero))
        (.app (.const (.role .decidable) []) (.fvar 0 (.sort .zero)))
        (.app wDec (.fvar 0 (.sort .zero))) (.succ .zero) :=
      OpenType.ofOpenAt
        ((OpenAt.ofClosed hsc decAt rfl).app_nondep (OpenAt.fvar (d := 1) (idx := 0) (by omega)) .refl rfl)
    refine OpenType.forallE hDom1 ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 (.sort .zero)) 1 (.app wDec (.fvar 0 (.sort .zero)))
    have hDec2 : OpenAt env 2 Γ2
        (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero)))
          (.fvar 1 (.app wDec (.fvar 0 (.sort .zero)))))
        (.app (.app wDecide (.fvar 0 (.sort .zero)))
          (.fvar 1 (.app wDec (.fvar 0 (.sort .zero)))))
        BaseKit.boolT := by
      have h1 := (OpenAt.ofClosed hsc decideAt decideO.wOk.hasFvar_false).app_abs
        (OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)) .refl
        (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, hwDecCl.2])
      simp [fvarSubst, fvarSubst_of_not_hasFvar hwDecCl.1] at h1
      have h2 := h1.app_abs (OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)) .refl rfl
      simpa [Γ2, fvarUpdate, fvarSubst] using h2
    have hDom2 := OpenType.eq bk.eqStored (OpenType.ofClosed hsc bk.boolType) hDec2 .refl
      (OpenAt.ofClosed hsc bk.boolFalseAt rfl) .refl
    refine OpenType.forallE hDom2 ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    exact OpenType.ofOpenAt
      ((OpenAt.ofClosed hsc notAt rfl).app_nondep (OpenAt.fvar (d := 3) (idx := 0) (by omega)) .refl rfl)
  have ofDecideFalseAt := ClosedAt.ofRole0_open hsc
    (roleExact_walked hs .ofDecideEqFalse (by decide) (by decide) (by decide))
    (by decide) rfl ofDecFalseO
  -- 4. `Int`, `Int.ofNat`, `Int.negSucc`, `Int.le`
  have intAt : ClosedAt env (.const (.role .int) []) (.sort (.succ .zero)) :=
    ClosedAt.ofRole0 hsc
      (roleExact_anchor_of hs .intNegOfNat .int (by decide) (by decide) (by decide))
      (by decide) rfl (ClosedType.sort env (.succ .zero))
  let wInt := intAt.witness
  have hwIntCl : TermClosed wInt := intAt.wClosed
  have hIntTy : ClosedType env wInt (.succ .zero) := ClosedType.ofClosedAt intAt
  have hIntPi0 : PiRed env 0 wInt (.const (.role .int) []) := .ofRed intAt.wRed
  have hIntPi1 : PiRed env 1 wInt (.const (.role .int) []) := by
    have h := PiRed.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := 1) hIntPi0
    rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar intAt.wClosed.1,
        Ix.Kernel.Expr.renFV_of_not_hasFvar rfl] at h
    exact h
  have hIntPi2 : PiRed env 2 wInt (.const (.role .int) []) := by
    have h := PiRed.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := 2) hIntPi0
    rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar intAt.wClosed.1,
        Ix.Kernel.Expr.renFV_of_not_hasFvar rfl] at h
    exact h
  have hNatIntTy := ClosedType.forall_nondep hsc bk.natType hIntTy
  have hNatIntPi : PiRed env 0
      (.forallE BaseKit.natT wInt { pw := .never })
      (.forallE BaseKit.natT (.const (.role .int) []) { pw := .never }) :=
    .forallE (by simp [Ix.Kernel.Expr.wscopedB]) (.ofRed .refl)
      (by simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2] using hIntPi1)
  have intOfNatAt := ClosedAt.ofRole0_de hsc
    (roleExact_anchor_of hs .intNegOfNat .intOfNat (by decide) (by decide) (by decide))
    (by decide) rfl ⟨rfl, rfl⟩ hNatIntPi hNatIntTy
  let wIntOfNat := intOfNatAt.witness
  have intNegSuccAt := ClosedAt.ofRole0_de hsc
    (roleExact_anchor_of hs .intNegOfNat .intNegSucc (by decide) (by decide) (by decide))
    (by decide) rfl ⟨rfl, rfl⟩ hNatIntPi hNatIntTy
  have hIntLeTy := ClosedType.forall_nondep hsc hIntTy
    (ClosedType.forall_nondep hsc hIntTy (ClosedType.sort env .zero))
  have hIntLePi : PiRed env 0
      (.forallE wInt (.forallE wInt (.sort .zero) { pw := .never }) { pw := .never })
      (.forallE (.const (.role .int) [])
        (.forallE (.const (.role .int) []) (.sort .zero) { pw := .never }) { pw := .never }) := by
    refine .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi0 ?_
    simp only [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2]
    exact .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi1 (.ofRed .refl)
  have intLeAt := ClosedAt.ofRole0_de hsc
    (roleExact_anchor_of hs .intDecLe .intLe (by decide) (by decide) (by decide))
    (by decide) rfl ⟨rfl, rfl⟩ hIntLePi hIntLeTy
  let wIntLe := intLeAt.witness
  -- 5. `ite.{1}`
  have iteO : OpenType env 0 Γ₀
      ((Ix.Kernel.Expr.forallE (.sort (.param 0))
        (.forallE (.sort .zero)
          (.forallE (.app (.const (.role .decidable) []) (.bvar 0))
            (.forallE (.bvar 2) (.forallE (.bvar 3) (.bvar 4) { pw := .ifAllZero [0] })
              { pw := .ifAllZero [0] })
            { pw := .ifAllZero [0] })
          { pw := .ifAllZero [0] })
        { pw := .ifAllZero [0] }).instantiateLevelParams [0] [.succ .zero])
      (.forallE (.sort (.succ .zero))
        ((Ix.Kernel.Expr.forallE (.sort .zero)
          ((Ix.Kernel.Expr.forallE (.app wDec (.fvar 1 (.sort .zero)))
            ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort (.succ .zero)))
              ((Ix.Kernel.Expr.forallE (.fvar 0 (.sort (.succ .zero)))
                ((Ix.Kernel.Expr.fvar 0 (.sort (.succ .zero))).abstract1 4) { pw := .never }).abstract1 3)
              { pw := .never }).abstract1 2)
            { pw := .never }).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ (.succ .zero)) (.imax (.succ .zero)
        (.imax (.succ .zero) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))))) := by
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go, Ix.Kernel.Level.substPW, ↓reduceIte, List.map]
    refine OpenType.forallE (OpenType.sort (.succ .zero)) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.sort .zero) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hDom2 : OpenType env 2 (fvarUpdate (fvarUpdate Γ₀ 0 (.sort (.succ .zero))) 1 (.sort .zero))
        (.app (.const (.role .decidable) []) (.fvar 1 (.sort .zero)))
        (.app wDec (.fvar 1 (.sort .zero))) (.succ .zero) :=
      OpenType.ofOpenAt
        ((OpenAt.ofClosed hsc decAt rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 1) (by omega)) .refl rfl)
    refine OpenType.forallE hDom2 ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofOpenAt (OpenAt.fvar (d := 3) (idx := 0) (by omega))) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofOpenAt (OpenAt.fvar (d := 4) (idx := 0) (by omega))) ?_ rfl
    exact OpenType.ofOpenAt (OpenAt.fvar (d := 5) (idx := 0) (by omega))
  have iteAt := ClosedAt.ofRole1_open hsc hwf
    (roleExact_eqns hs .ifThenElse (by decide) (by decide))
    (by decide) rfl (by decide) ⟨by decide, by decide⟩ iteO
  -- 6. `Nat.decEq`
  have natDecEqO : OpenType env 0 Γ₀
      (.forallE BaseKit.natT
        (.forallE BaseKit.natT
          (.app (.const (.role .decidable) [])
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT) (.bvar 1)) (.bvar 0)))
          { pw := .never })
        { pw := .never })
      (.forallE BaseKit.natT
        ((Ix.Kernel.Expr.forallE BaseKit.natT
          ((Ix.Kernel.Expr.app wDec (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
            (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT))).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (OpenType.ofClosed hsc bk.natType) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofClosed hsc bk.natType) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hEq2 := OpenAt.eq bk.eqStored (OpenType.ofClosed hsc bk.natType)
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl
      (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc decAt rfl).app_nondep hEq2 .refl rfl)
  have natDecEqAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .natDecEq (by decide) (by decide))
    (by decide) rfl natDecEqO
  -- 7. Non-dependent `Int` operations
  have hNNITy := ClosedType.forall_nondep hsc bk.natType hNatIntTy
  have hNNIPi : PiRed env 0
      (.forallE BaseKit.natT (.forallE BaseKit.natT wInt { pw := .never }) { pw := .never })
      (.forallE BaseKit.natT (.forallE BaseKit.natT (.const (.role .int) []) { pw := .never }) { pw := .never }) := by
    refine .forallE (by simp [Ix.Kernel.Expr.wscopedB]) (.ofRed .refl) ?_
    simp only [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt (lbb_of_lbb0 hwIntCl.2 1)]
    exact .forallE (by simp [Ix.Kernel.Expr.wscopedB]) (.ofRed .refl)
      (by simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2] using hIntPi2)
  have hUnTy := ClosedType.forall_nondep hsc hIntTy hIntTy
  have hUnPi : PiRed env 0
      (.forallE wInt wInt { pw := .never })
      (.forallE (.const (.role .int) []) (.const (.role .int) []) { pw := .never }) :=
    .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi0
      (by simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2] using hIntPi1)
  have hAbsTy := ClosedType.forall_nondep hsc hIntTy bk.natType
  have hAbsPi : PiRed env 0
      (.forallE wInt BaseKit.natT { pw := .never })
      (.forallE (.const (.role .int) []) BaseKit.natT { pw := .never }) :=
    .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi0 (.ofRed .refl)
  have hBinTy := ClosedType.forall_nondep hsc hIntTy hUnTy
  have hBinPi : PiRed env 0
      (.forallE wInt (.forallE wInt wInt { pw := .never }) { pw := .never })
      (.forallE (.const (.role .int) [])
        (.forallE (.const (.role .int) []) (.const (.role .int) []) { pw := .never }) { pw := .never }) := by
    refine .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi0 ?_
    simp only [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2,
      instantiate1_eq_self wInt (lbb_of_lbb0 hwIntCl.2 1)]
    exact .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi1
      (by simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2] using hIntPi2)
  have hIntNatIntTy := ClosedType.forall_nondep hsc hIntTy hNatIntTy
  have hIntNatIntPi : PiRed env 0
      (.forallE wInt (.forallE BaseKit.natT wInt { pw := .never }) { pw := .never })
      (.forallE (.const (.role .int) [])
        (.forallE BaseKit.natT (.const (.role .int) []) { pw := .never }) { pw := .never }) := by
    refine .forallE (by simp [Ix.Kernel.Expr.wscopedB]) hIntPi0 ?_
    simp only [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt (lbb_of_lbb0 hwIntCl.2 1)]
    exact .forallE (by simp [Ix.Kernel.Expr.wscopedB]) (.ofRed .refl)
      (by simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wInt hwIntCl.2] using hIntPi2)
  have intNegOfNatAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intNegOfNat (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hNatIntPi hNatIntTy
  have intSubNatNatAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intSubNatNat (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hNNIPi hNNITy
  have intNegAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intNeg (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hUnPi hUnTy
  have intNatAbsAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intNatAbs (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hAbsPi hAbsTy
  have intAddAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intAdd (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hBinPi hBinTy
  let wIntAdd := intAddAt.witness
  have intSubAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intSub (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hBinPi hBinTy
  have intMulAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intMul (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hBinPi hBinTy
  have intEdivAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intEdiv (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hBinPi hBinTy
  have intEmodAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intEmod (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hBinPi hBinTy
  have intPowAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intPow (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hIntNatIntPi hIntNatIntTy
  have intBmodAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intBmod (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hIntNatIntPi hIntNatIntTy
  have intBdivAt := ClosedAt.ofRole0_de hsc
    (roleExact_eqns hs .intBdiv (by decide) (by decide)) (by decide) rfl ⟨rfl, rfl⟩ hIntNatIntPi hIntNatIntTy
  -- 8. `Int.decLe` and `Int.decLt`
  have intDecLeO : OpenType env 0 Γ₀
      (.forallE (.const (.role .int) [])
        (.forallE (.const (.role .int) [])
          (.app (.const (.role .decidable) [])
            (.app (.app (.const (.role .intLe) []) (.bvar 1)) (.bvar 0)))
          { pw := .never })
        { pw := .never })
      (.forallE wInt
        ((Ix.Kernel.Expr.forallE wInt
          ((Ix.Kernel.Expr.app wDec (.app (.app wIntLe (.fvar 0 wInt)) (.fvar 1 wInt))).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (OpenType.ofClosedAt hsc intAt) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofClosedAt hsc intAt) ?_ rfl
      (by simp [Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false wInt hwIntCl.1])
    simp only [Ix.Kernel.Expr.instantiate1]
    let ΓI2 := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 wInt
    have hLe2 := ((OpenAt.ofClosed hsc intLeAt
      (by simp [Ix.Kernel.Expr.hasFvar, hwIntCl.1])).app_nondep
        (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓI2) (by omega)) .refl
        (by simp [Ix.Kernel.Expr.looseBVarsBounded, hwIntCl.2])).app_nondep
        (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓI2) (by omega)) .refl rfl
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc decAt rfl).app_nondep hLe2 .refl rfl)
  have intDecLeAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .intDecLe (by decide) (by decide)) (by decide) rfl intDecLeO
  have intDecLtO : OpenType env 0 Γ₀
      (.forallE (.const (.role .int) [])
        (.forallE (.const (.role .int) [])
          (.app (.const (.role .decidable) [])
            (.app (.app (.const (.role .intLe) [])
              (.app (.app (.const (.role .intAdd) []) (.bvar 1))
                (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))))
              (.bvar 0)))
          { pw := .never })
        { pw := .never })
      (.forallE wInt
        ((Ix.Kernel.Expr.forallE wInt
          ((Ix.Kernel.Expr.app wDec
            (.app (.app wIntLe
              (.app (.app wIntAdd (.fvar 0 wInt))
                (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
              (.fvar 1 wInt))).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (OpenType.ofClosedAt hsc intAt) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofClosedAt hsc intAt) ?_ rfl
      (by simp [Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false wInt hwIntCl.1])
    simp only [Ix.Kernel.Expr.instantiate1]
    let ΓI2 := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 wInt
    have hOne2 : OpenAt env 2 ΓI2
        (.app BaseKit.natSuccE BaseKit.natZeroE) (.app BaseKit.natSuccE BaseKit.natZeroE) BaseKit.natT :=
      OpenAt.ofClosed hsc (bk.natSuccApp bk.natZeroAt) rfl
    have hOfOne2 := (OpenAt.ofClosed hsc intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, hwIntCl.1])).app_nondep hOne2 .refl hwIntCl.2
    have hAdd2 := ((OpenAt.ofClosed hsc intAddAt
      (by simp [Ix.Kernel.Expr.hasFvar, hwIntCl.1])).app_nondep
        (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓI2) (by omega)) .refl
        (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_of_lbb0 hwIntCl.2])).app_nondep
        hOfOne2 .refl hwIntCl.2
    have hLe2 := ((OpenAt.ofClosed hsc intLeAt
      (by simp [Ix.Kernel.Expr.hasFvar, hwIntCl.1])).app_nondep
        hAdd2 .refl
        (by simp [Ix.Kernel.Expr.looseBVarsBounded, hwIntCl.2])).app_nondep
        (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓI2) (by omega)) .refl rfl
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc decAt rfl).app_nondep hLe2 .refl rfl)
  have intDecLtAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .intDecLt (by decide) (by decide)) (by decide) rfl intDecLtO
  exact ⟨wDec, wNot, wDecide, wInt, wIntLe, wIntOfNat, wIntAdd, ⟨{
    bk, shapes := hs, decAt, decW := rfl, notAt, notW := rfl,
    isTrueAt, isFalseAt, decideAt, decideW := rfl,
    ofDecideTrueAt, ofDecideFalseAt, intAt, intW := rfl,
    intOfNatAt, intOfNatW := rfl, intNegSuccAt, intLeAt, intLeW := rfl,
    iteAt, natDecEqAt, intNegOfNatAt, intSubNatNatAt, intNegAt, intNatAbsAt,
    intAddAt, intAddW := rfl, intSubAt, intMulAt, intEdivAt, intEmodAt,
    intPowAt, intDecLeAt, intDecLtAt, intBmodAt, intBdivAt,
    isTrueTy_nf := isTrueO.wOk.hasFvar_false,
    isFalseTy_nf := isFalseO.wOk.hasFvar_false,
    decideTy_nf := decideO.wOk.hasFvar_false,
    iteTy_nf := iteO.wOk.hasFvar_false,
    natDecEqTy_nf := natDecEqO.wOk.hasFvar_false,
    intDecLeTy_nf := intDecLeO.wOk.hasFvar_false,
    intDecLtTy_nf := intDecLtO.wOk.hasFvar_false
  }⟩⟩

end BuildIntKit

/-! ## `IntKit` helpers, `Decidable`, and `ite` eliminators -/

namespace IntKit

variable {env : Ix.Kernel.Env .anon}
  {wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd : KExpr}

private theorem wDec_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wDec := ik.decW ▸ ik.decAt.wClosed

private theorem wNot_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wNot := ik.notW ▸ ik.notAt.wClosed

private theorem wDecide_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wDecide := ik.decideW ▸ ik.decideAt.wClosed

private theorem wInt_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wInt := ik.intW ▸ ik.intAt.wClosed

private theorem wInt_lbb1 (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    wInt.looseBVarsBounded 1 = true :=
  looseBVarsBounded_mono wInt (Nat.zero_le 1) ik.wInt_cl.2

private theorem forallNatInt_lbb0 (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    (Ix.Kernel.Expr.forallE BaseKit.natT wInt { pw := .never }).looseBVarsBounded 0 = true := by
  simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_lbb1]

private theorem forallIntInt_lbb0 (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    (Ix.Kernel.Expr.forallE wInt wInt { pw := .never }).looseBVarsBounded 0 = true := by
  simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2, ik.wInt_lbb1]

private theorem wIntLe_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wIntLe := ik.intLeW ▸ ik.intLeAt.wClosed

private theorem wIntOfNat_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wIntOfNat := ik.intOfNatW ▸ ik.intOfNatAt.wClosed

private theorem wIntAdd_cl (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    TermClosed wIntAdd := ik.intAddW ▸ ik.intAddAt.wClosed

private theorem wDecide_red (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    Red env 0 wDecide (.const (.role .decidableDecide) []) := ik.decideW ▸ ik.decideAt.wRed

private theorem wDecide_defEq (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 wDecide (.const (.role .decidableDecide) []) := ik.decideW ▸ ik.decideAt.defEq_witness

private theorem wInt_defEq (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 wInt (.const (.role .int) []) := ik.intW ▸ ik.intAt.defEq_witness

private theorem wIntLe_defEq (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 wIntLe (.const (.role .intLe) []) := ik.intLeW ▸ ik.intLeAt.defEq_witness

private theorem wIntOfNat_defEq (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 wIntOfNat (.const (.role .intOfNat) []) := ik.intOfNatW ▸ ik.intOfNatAt.defEq_witness

private theorem wIntAdd_defEq (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 wIntAdd (.const (.role .intAdd) []) := ik.intAddW ▸ ik.intAddAt.defEq_witness

private def intType (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    ClosedType env wInt (.succ .zero) := by
  have h := ClosedType.ofClosedAt ik.intAt
  rwa [ik.intW] at h

private theorem intRed (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    Red env 0 wInt (.const (.role .int) []) := ik.intW ▸ ik.intAt.wRed

private def intLitAt (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) : ClosedAt env (intLitExpr x) wInt := by
  cases x with
  | ofNat n => exact ik.intOfNatAt.app_nondep (ik.bk.natLitAt n) ik.wInt_cl.2
  | negSucc n => exact ik.intNegSuccAt.app_nondep (ik.bk.natLitAt n) ik.wInt_cl.2

private abbrev specOneAt (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    ClosedAt env (.app BaseKit.natSuccE BaseKit.natZeroE) BaseKit.natT :=
  ik.bk.natSuccApp ik.bk.natZeroAt

private abbrev specTwoAt (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    ClosedAt env (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)) BaseKit.natT :=
  ik.bk.natSuccApp ik.specOneAt

private theorem red_one (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    Red env 0 (.app BaseKit.natSuccE BaseKit.natZeroE) (.lit (.natVal 1)) :=
  .trans (.appArg ik.bk.red_natZero_lit) (ik.bk.red_natSucc_lit 0)

private theorem red_two (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    Red env 0 (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)) (.lit (.natVal 2)) :=
  .trans (.appArg ik.red_one) (ik.bk.red_natSucc_lit 1)

private theorem defEq_one (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 (.app BaseKit.natSuccE BaseKit.natZeroE) (.lit (.natVal 1)) :=
  .ofRed ik.red_one

private theorem defEq_two (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd) :
    DefEq env 0 (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)) (.lit (.natVal 2)) :=
  .ofRed ik.red_two

private def boolExprAt (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (b : Bool) : ClosedAt env (if b then BaseKit.trueE else BaseKit.falseE) BaseKit.boolT := by
  cases b
  · exact ik.bk.boolFalseAt
  · exact ik.bk.boolTrueAt

private def decType (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p : KExpr} (hp : ClosedAt env p (.sort .zero)) :
    ClosedType env (.app wDec hp.witness) (.succ .zero) := by
  have h := ClosedType.ofClosedAt (ik.decAt.app_nondep hp rfl)
  simpa [ik.decW] using h

private def notType (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p : KExpr} (hp : ClosedAt env p (.sort .zero)) :
    ClosedType env (.app wNot hp.witness) .zero := by
  have h := ClosedType.ofClosedAt (ik.notAt.app_nondep hp rfl)
  simpa [ik.notW] using h

private def isTrueApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p h : KExpr} (hp : ClosedAt env p (.sort .zero)) (hh : ClosedAt env h hp.witness) :
    ClosedAt env (.app (.app (.const (.role .decidableIsTrue) []) p) h) (.app wDec hp.witness) := by
  have h1 := ik.isTrueAt.app_abs hp .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, looseBVarsBounded_abstract1' (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2] : (Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).looseBVarsBounded 0 = true)])
  simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1] at h1
  have h2 := h1.app_abs hh .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, hp.wClosed.2])
  simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar hp.wClosed.1] using h2

private def isFalseApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p h : KExpr} (hp : ClosedAt env p (.sort .zero)) (hh : ClosedAt env h (.app wNot hp.witness)) :
    ClosedAt env (.app (.app (.const (.role .decidableIsFalse) []) p) h) (.app wDec hp.witness) := by
  have h1 := ik.isFalseAt.app_abs hp .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wNot_cl.2,
      looseBVarsBounded_abstract1' (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2] : (Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))).looseBVarsBounded 0 = true)])
  simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at h1
  have h2 := h1.app_abs hh .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, hp.wClosed.2])
  simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar hp.wClosed.1] using h2

private def decideApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p inst : KExpr} (hp : ClosedAt env p (.sort .zero)) (hinst : ClosedAt env inst (.app wDec hp.witness)) :
    ClosedAt env (.app (.app (.const (.role .decidableDecide) []) p) inst) BaseKit.boolT := by
  have h1 := ik.decideAt.app_abs hp .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wDec_cl.2])
  simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1] at h1
  have h2 := h1.app_abs hinst .refl rfl
  simpa [fvarSubst] using h2

private theorem ofDecideTrueApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p inst : KExpr} (hp : ClosedAt env p (.sort .zero))
    (hinst : ClosedAt env inst (.app wDec hp.witness))
    (hTrue : DefEq env 0 (.app (.app (.const (.role .decidableDecide) []) p) inst) BaseKit.trueE) :
    ∃ proof, Nonempty (ClosedAt env proof hp.witness) := by
  have h1 := ik.ofDecideTrueAt.app_abs hp .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2,
      lbb_of_lbb0 ik.wDecide_cl.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) hp.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1] at h1
  have h2 := h1.app_abs hinst .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDecide_cl.2,
      lbb_of_lbb0 hp.wClosed.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hinst.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDecide_cl.1, fvarSubst_of_not_hasFvar hp.wClosed.1] at h2
  have hrefl := closedAt_eqRefl ik.bk.eqReflStored ik.bk.boolType ik.bk.boolTrueAt
  have hEqDe : DefEq env 0
      (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
        ik.bk.boolTrueAt.witness) ik.bk.boolTrueAt.witness)
      (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
        (.app (.app wDecide hp.witness) hinst.witness)) BaseKit.trueE) := by
    have hdecW : DefEq env 0 (.app (.app wDecide hp.witness) hinst.witness) BaseKit.trueE := by
      have h0 : Red env 0 (.app (.app wDecide hp.witness) hinst.witness)
          (.app (.app (.const (.role .decidableDecide) []) p) inst) :=
        .trans (.appFn (.trans (.appFn ik.wDecide_red) (.appArg hp.wRed))) (.appArg hinst.wRed)
      exact .redL h0 hTrue
    exact .app (.app (.app .refl .refl) (.redL ik.bk.boolTrueAt.wRed hdecW.symm))
      ik.bk.boolTrueAt.defEq_witness
  have h3 := h2.app_abs hrefl hEqDe hp.wClosed.2
  rw [fvarSubst_of_not_hasFvar hp.wClosed.1] at h3
  exact ⟨_, ⟨h3⟩⟩

private theorem ofDecideFalseApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p inst : KExpr} (hp : ClosedAt env p (.sort .zero))
    (hinst : ClosedAt env inst (.app wDec hp.witness))
    (hFalse : DefEq env 0 (.app (.app (.const (.role .decidableDecide) []) p) inst) BaseKit.falseE) :
    ∃ proof, Nonempty (ClosedAt env proof (.app wNot hp.witness)) := by
  have h1 := ik.ofDecideFalseAt.app_abs hp .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2,
      lbb_of_lbb0 ik.wDecide_cl.2, lbb_of_lbb0 ik.wNot_cl.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) hp.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
    fvarSubst_of_not_hasFvar ik.wNot_cl.1] at h1
  have h2 := h1.app_abs hinst .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDecide_cl.2,
      lbb_of_lbb0 ik.wNot_cl.2, lbb_of_lbb0 hp.wClosed.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hinst.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDecide_cl.1, fvarSubst_of_not_hasFvar hp.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wNot_cl.1] at h2
  have hrefl := closedAt_eqRefl ik.bk.eqReflStored ik.bk.boolType ik.bk.boolFalseAt
  have hEqDe : DefEq env 0
      (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
        ik.bk.boolFalseAt.witness) ik.bk.boolFalseAt.witness)
      (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
        (.app (.app wDecide hp.witness) hinst.witness)) BaseKit.falseE) := by
    have hdecW : DefEq env 0 (.app (.app wDecide hp.witness) hinst.witness) BaseKit.falseE := by
      have h0 : Red env 0 (.app (.app wDecide hp.witness) hinst.witness)
          (.app (.app (.const (.role .decidableDecide) []) p) inst) :=
        .trans (.appFn (.trans (.appFn ik.wDecide_red) (.appArg hp.wRed))) (.appArg hinst.wRed)
      exact .redL h0 hFalse
    exact .app (.app (.app .refl .refl) (.redL ik.bk.boolFalseAt.wRed hdecW.symm))
      ik.bk.boolFalseAt.defEq_witness
  have h3 := h2.app_abs hrefl hEqDe
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wNot_cl.2, hp.wClosed.2])
  rw [fvarSubst_of_not_hasFvar (by simp [Ix.Kernel.Expr.hasFvar, ik.wNot_cl.1, hp.wClosed.1])] at h3
  exact ⟨_, ⟨h3⟩⟩

private def iteIntApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {c inst t e : KExpr} (hc : ClosedAt env c (.sort .zero))
    (hinst : ClosedAt env inst (.app wDec hc.witness))
    (ht : ClosedAt env t wInt) (he : ClosedAt env e wInt) :
    ClosedAt env
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c) inst) t) e) wInt := by
  have h1 := ik.iteAt.app_abs ik.intAt .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2])
  rw [ik.intW] at h1
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
    ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1] at h1
  have h2 := h1.app_abs hc .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2,
      lbb_of_lbb0 ik.wInt_cl.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
    ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
    ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1] at h2
  have h3 := h2.app_abs hinst .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hinst.wClosed.1,
    ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hinst.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wInt_cl.1] at h3
  have h4 := h3.app_abs ht .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
  simp [fvarSubst,
    ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wInt_cl.1] at h4
  have h5 := h4.app_abs he .refl ik.wInt_cl.2
  simpa [fvarSubst_of_not_hasFvar ik.wInt_cl.1] using h5

/-! ### `decide` computation & extensionality (`decideEqns[0..2]`) -/

private theorem decide_isTrue (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p h : KExpr} (hp : ClosedAt env p (.sort .zero)) (hh : ClosedAt env h hp.witness) :
    DefEq env 0
      (.app (.app (.const (.role .decidableDecide) []) p)
        (.app (.app (.const (.role .decidableIsTrue) []) p) h))
      BaseKit.trueE := by
  have hv := eqnValid_of ik.shapes .decidableDecide (by decide) (by decide) (k := 0) rfl
  have hsc := ik.bk.storeClosed
  let Γ1 := fvarUpdate Γ₀ 0 (.sort .zero)
  let Γ2 := fvarUpdate Γ1 1 (.fvar 0 (.sort .zero))
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
  have hLhsO : OpenAt env 2 Γ2
      (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero)))
        (.app (.app (.const (.role .decidableIsTrue) []) (.fvar 0 (.sort .zero)))
          (.fvar 1 (.fvar 0 (.sort .zero)))))
      (.app (.app wDecide (.fvar 0 (.sort .zero)))
        (.app (.app ik.isTrueAt.witness (.fvar 0 (.sort .zero)))
          (.fvar 1 (.fvar 0 (.sort .zero)))))
      BaseKit.boolT := by
    have hIsT1 := (OpenAt.ofClosed hsc ik.isTrueAt ik.isTrueTy_nf).app_abs
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)) .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hIsT1
    have hIsT2 := hIsT1.app_abs (OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)) .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hIsT2
    have hDec1 := (OpenAt.ofClosed hsc ik.decideAt ik.decideTy_nf).app_abs
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)) .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wDec_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hDec1
    have hDec2 := hDec1.app_abs hIsT2 .refl rfl
    simpa [Γ2, Γ1, fvarUpdate, fvarSubst, ik.decideW] using hDec2
  have hLhsDe : DefEq env 0
      (.app (.app wDecide hp.witness) (.app (.app ik.isTrueAt.witness hp.witness) hh.witness))
      (.app (.app (.const (.role .decidableDecide) []) p)
        (.app (.app (.const (.role .decidableIsTrue) []) p) h)) :=
    .app (.app ik.wDecide_defEq hp.defEq_witness)
      (.app (.app ik.isTrueAt.defEq_witness hp.defEq_witness) hh.defEq_witness)
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp only [eqnsSideExact, Ix.Kernel.specEqn, List.zipIdx, List.foldr, bmeta,
      Ix.Kernel.Level.zeronessOf] at hde
    have hBool2 := OpenType.ofClosed hsc (d := 2) (Γ := Γ2) ik.bk.boolType
    have hDom1 : OpenType env 1 Γ1 (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero)) .zero :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 1) (idx := 0) (by omega))
    have hRhsO : OpenAt env 2 Γ2 BaseKit.trueE BaseKit.trueE BaseKit.boolT :=
      OpenAt.ofClosed hsc ik.bk.boolTrueAt rfl
    have hLamL1 := OpenAt.lam_abs_inner_id (pw := .never) hDom1 hLhsO hBool2.wInfer hBool2.wRed rfl rfl hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamL1
    have hLamR1 := OpenAt.lam_abs_inner_id (pw := .never) hDom1 hRhsO hBool2.wInfer hBool2.wRed rfl rfl hCtx1
    have hLamR0 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamR1
    have hpO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hp rfl
    have hhO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hh hp.wClosed.1
    have hAppL1 := hLamL0.app_abs hpO .refl (by decide)
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hhO .refl rfl
    have hAppR1 := hLamR0.app_abs hpO .refl (by decide)
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hhO .refl rfl
    have hRedL1 : Red env 0
        (.app (.lam (.sort .zero)
          ((Ix.Kernel.Expr.lam (.fvar 0 (.sort .zero))
            ((Ix.Kernel.Expr.app (.app wDecide (.fvar 0 (.sort .zero)))
              (.app (.app ik.isTrueAt.witness (.fvar 0 (.sort .zero)))
                (.fvar 1 (.fvar 0 (.sort .zero))))).abstract1 1) { pw := .never }).abstract1 0)
          { pw := .never }) hp.witness)
        (.lam hp.witness
          ((Ix.Kernel.Expr.app (.app wDecide hp.witness)
            (.app (.app ik.isTrueAt.witness hp.witness) (.fvar 1 (.fvar 0 (.sort .zero))))).abstract1 1)
          { pw := .never }) := by
      have h1 := Red.beta (env := env) (d := 0) (ty := .sort .zero) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.lam (.fvar 0 (.sort .zero))
          ((Ix.Kernel.Expr.app (.app wDecide (.fvar 0 (.sort .zero)))
            (.app (.app ik.isTrueAt.witness (.fvar 0 (.sort .zero)))
              (.fvar 1 (.fvar 0 (.sort .zero))))).abstract1 1) { pw := .never }).abstract1 0)
        hp.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDecide_cl.2, lbb_of_lbb0 ik.isTrueAt.wClosed.2])] at h1
      simpa [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
        fvarSubst_of_not_hasFvar ik.wDecide_cl.1, fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1] using h1
    have hRedL2 : Red env 0
        (.app (.lam hp.witness
          ((Ix.Kernel.Expr.app (.app wDecide hp.witness)
            (.app (.app ik.isTrueAt.witness hp.witness) (.fvar 1 (.fvar 0 (.sort .zero))))).abstract1 1)
          { pw := .never }) hh.witness)
        (.app (.app wDecide hp.witness) (.app (.app ik.isTrueAt.witness hp.witness) hh.witness)) := by
      have h1 := Red.beta (env := env) (d := 0) (ty := hp.witness) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.app (.app wDecide hp.witness)
          (.app (.app ik.isTrueAt.witness hp.witness) (.fvar 1 (.fvar 0 (.sort .zero))))).abstract1 1)
        hh.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDecide_cl.2, ik.isTrueAt.wClosed.2, hp.wClosed.2])] at h1
      simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
        fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1, fvarSubst_of_not_hasFvar hp.wClosed.1] using h1
    have hRedR1 : Red env 0
        (.app (.lam (.sort .zero)
          ((Ix.Kernel.Expr.lam (.fvar 0 (.sort .zero)) (BaseKit.trueE.abstract1 1) { pw := .never }).abstract1 0)
          { pw := .never }) hp.witness)
        (.lam hp.witness (BaseKit.trueE.abstract1 1) { pw := .never }) := by
      have h1 := Red.beta (env := env) (d := 0) (ty := .sort .zero) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.lam (.fvar 0 (.sort .zero)) (BaseKit.trueE.abstract1 1) { pw := .never }).abstract1 0)
        hp.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by decide)] at h1
      simpa [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1] using h1
    have hRedR2 : Red env 0
        (.app (.lam hp.witness (BaseKit.trueE.abstract1 1) { pw := .never }) hh.witness) BaseKit.trueE := by
      have h1 := Red.beta (env := env) (d := 0) (ty := hp.witness) (mb := { pw := .never })
        (body := BaseKit.trueE.abstract1 1) hh.wInfer.toIO .refl
      simpa [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1] using h1
    exact OpenAt.defEq_chain hAppL2 hAppR2 (.app (.app hde .refl) .refl)
      (.trans (.appFn hRedL1) hRedL2) hLhsDe (.trans (.appFn hRedR1) hRedR2) .refl
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans (by decide))
    have hEqO := OpenType.eq ik.bk.eqStored (OpenType.ofClosed hsc ik.bk.boolType) hLhsO .refl
      (OpenAt.ofClosed hsc ik.bk.boolTrueAt rfl) .refl
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero [])
      (OpenType.ofOpenAt (OpenAt.fvar (d := 1) (idx := 0) (by omega))) hEqO rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort .zero) hB1O rfl
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs hp .refl hB1O.wClosed
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wDecide_cl.1, fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1] at hp1
    have hp2 := hp1.app_abs hh .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDecide_cl.2, ik.isTrueAt.wClosed.2, hp.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
      fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1, fvarSubst_of_not_hasFvar hp.wClosed.1] at hp2
    exact defEq_of_eqProof_de hsc ik.bk.eqStored hp2
      (.app (.app (.app .refl .refl) hLhsDe) .refl)
      (ik.decideApp hp (ik.isTrueApp hp hh)) ik.bk.boolTrueAt ik.bk.boolType

private theorem decide_isFalse (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p h : KExpr} (hp : ClosedAt env p (.sort .zero))
    (hh : ClosedAt env h (.app wNot hp.witness)) :
    DefEq env 0
      (.app (.app (.const (.role .decidableDecide) []) p)
        (.app (.app (.const (.role .decidableIsFalse) []) p) h))
      BaseKit.falseE := by
  have hv := eqnValid_of ik.shapes .decidableDecide (by decide) (by decide) (k := 1) rfl
  have hsc := ik.bk.storeClosed
  let Γ1 := fvarUpdate Γ₀ 0 (.sort .zero)
  let Γ2 := fvarUpdate Γ1 1 (.app wNot (.fvar 0 (.sort .zero)))
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
  have hDom1 : OpenType env 1 Γ1
      (.app (.const (.role .notProp) []) (.fvar 0 (.sort .zero)))
      (.app wNot (.fvar 0 (.sort .zero))) .zero := by
    have h := OpenType.ofOpenAt
      ((OpenAt.ofClosed hsc ik.notAt rfl).app_nondep (OpenAt.fvar (d := 1) (idx := 0) (Γ := Γ1) (by omega)) .refl rfl)
    rwa [ik.notW] at h
  have hLhsO : OpenAt env 2 Γ2
      (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero)))
        (.app (.app (.const (.role .decidableIsFalse) []) (.fvar 0 (.sort .zero)))
          (.fvar 1 (.app wNot (.fvar 0 (.sort .zero))))))
      (.app (.app wDecide (.fvar 0 (.sort .zero)))
        (.app (.app ik.isFalseAt.witness (.fvar 0 (.sort .zero)))
          (.fvar 1 (.app wNot (.fvar 0 (.sort .zero))))))
      BaseKit.boolT := by
    have hIsF1 := (OpenAt.ofClosed hsc ik.isFalseAt ik.isFalseTy_nf).app_abs
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)) .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2, lbb_of_lbb0 ik.wDec_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hIsF1
    have hIsF2 := hIsF1.app_abs (OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)) .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hIsF2
    have hDec1 := (OpenAt.ofClosed hsc ik.decideAt ik.decideTy_nf).app_abs
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)) .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wDec_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hDec1
    have hDec2 := hDec1.app_abs hIsF2 .refl rfl
    simpa [Γ2, Γ1, fvarUpdate, fvarSubst, ik.decideW] using hDec2
  have hLhsDe : DefEq env 0
      (.app (.app wDecide hp.witness) (.app (.app ik.isFalseAt.witness hp.witness) hh.witness))
      (.app (.app (.const (.role .decidableDecide) []) p)
        (.app (.app (.const (.role .decidableIsFalse) []) p) h)) :=
    .app (.app ik.wDecide_defEq hp.defEq_witness)
      (.app (.app ik.isFalseAt.defEq_witness hp.defEq_witness) hh.defEq_witness)
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp only [eqnsSideExact, Ix.Kernel.specEqn, List.zipIdx, List.foldr, bmeta,
      Ix.Kernel.Level.zeronessOf] at hde
    have hBool2 := OpenType.ofClosed hsc (d := 2) (Γ := Γ2) ik.bk.boolType
    have hRhsO : OpenAt env 2 Γ2 BaseKit.falseE BaseKit.falseE BaseKit.boolT :=
      OpenAt.ofClosed hsc ik.bk.boolFalseAt rfl
    have hLamL1 := OpenAt.lam_abs_inner_id (pw := .never) hDom1 hLhsO hBool2.wInfer hBool2.wRed rfl rfl hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamL1
    have hLamR1 := OpenAt.lam_abs_inner_id (pw := .never) hDom1 hRhsO hBool2.wInfer hBool2.wRed rfl rfl hCtx1
    have hLamR0 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamR1
    have hpO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hp rfl
    have hhO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hh
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wNot_cl.1, hp.wClosed.1])
    have hAppL1 := hLamL0.app_abs hpO .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hhO .refl rfl
    have hAppR1 := hLamR0.app_abs hpO .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hhO .refl rfl
    have hRedL1 : Red env 0
        (.app (.lam (.sort .zero)
          ((Ix.Kernel.Expr.lam (.app wNot (.fvar 0 (.sort .zero)))
            ((Ix.Kernel.Expr.app (.app wDecide (.fvar 0 (.sort .zero)))
              (.app (.app ik.isFalseAt.witness (.fvar 0 (.sort .zero)))
                (.fvar 1 (.app wNot (.fvar 0 (.sort .zero)))))).abstract1 1) { pw := .never }).abstract1 0)
          { pw := .never }) hp.witness)
        (.lam (.app wNot hp.witness)
          ((Ix.Kernel.Expr.app (.app wDecide hp.witness)
            (.app (.app ik.isFalseAt.witness hp.witness)
              (.fvar 1 (.app wNot (.fvar 0 (.sort .zero)))))).abstract1 1)
          { pw := .never }) := by
      have h1 := Red.beta (env := env) (d := 0) (ty := .sort .zero) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.lam (.app wNot (.fvar 0 (.sort .zero)))
          ((Ix.Kernel.Expr.app (.app wDecide (.fvar 0 (.sort .zero)))
            (.app (.app ik.isFalseAt.witness (.fvar 0 (.sort .zero)))
              (.fvar 1 (.app wNot (.fvar 0 (.sort .zero)))))).abstract1 1) { pw := .never }).abstract1 0)
        hp.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2, lbb_of_lbb0 ik.wDecide_cl.2, lbb_of_lbb0 ik.isFalseAt.wClosed.2])] at h1
      simpa [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
        fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
        fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1] using h1
    have hRedL2 : Red env 0
        (.app (.lam (.app wNot hp.witness)
          ((Ix.Kernel.Expr.app (.app wDecide hp.witness)
            (.app (.app ik.isFalseAt.witness hp.witness)
              (.fvar 1 (.app wNot (.fvar 0 (.sort .zero)))))).abstract1 1)
          { pw := .never }) hh.witness)
        (.app (.app wDecide hp.witness) (.app (.app ik.isFalseAt.witness hp.witness) hh.witness)) := by
      have h1 := Red.beta (env := env) (d := 0) (ty := .app wNot hp.witness) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.app (.app wDecide hp.witness)
          (.app (.app ik.isFalseAt.witness hp.witness)
            (.fvar 1 (.app wNot (.fvar 0 (.sort .zero)))))).abstract1 1)
        hh.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDecide_cl.2, ik.isFalseAt.wClosed.2, hp.wClosed.2])] at h1
      simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
        fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1, fvarSubst_of_not_hasFvar hp.wClosed.1] using h1
    have hRedR1 : Red env 0
        (.app (.lam (.sort .zero)
          ((Ix.Kernel.Expr.lam (.app wNot (.fvar 0 (.sort .zero))) (BaseKit.falseE.abstract1 1) { pw := .never }).abstract1 0)
          { pw := .never }) hp.witness)
        (.lam (.app wNot hp.witness) (BaseKit.falseE.abstract1 1) { pw := .never }) := by
      have h1 := Red.beta (env := env) (d := 0) (ty := .sort .zero) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.lam (.app wNot (.fvar 0 (.sort .zero))) (BaseKit.falseE.abstract1 1) { pw := .never }).abstract1 0)
        hp.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2])] at h1
      simpa [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
        fvarSubst_of_not_hasFvar ik.wNot_cl.1] using h1
    have hRedR2 : Red env 0
        (.app (.lam (.app wNot hp.witness) (BaseKit.falseE.abstract1 1) { pw := .never }) hh.witness) BaseKit.falseE := by
      have h1 := Red.beta (env := env) (d := 0) (ty := .app wNot hp.witness) (mb := { pw := .never })
        (body := BaseKit.falseE.abstract1 1) hh.wInfer.toIO .refl
      simpa [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1] using h1
    exact OpenAt.defEq_chain hAppL2 hAppR2 (.app (.app hde .refl) .refl)
      (.trans (.appFn hRedL1) hRedL2) hLhsDe (.trans (.appFn hRedR1) hRedR2) .refl
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans (by decide))
    have hEqO := OpenType.eq ik.bk.eqStored (OpenType.ofClosed hsc ik.bk.boolType) hLhsO .refl
      (OpenAt.ofClosed hsc ik.bk.boolFalseAt rfl) .refl
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) hDom1 hEqO rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort .zero) hB1O rfl
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs hp .refl hB1O.wClosed
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
      fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1] at hp1
    have hp2 := hp1.app_abs hh .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDecide_cl.2, ik.isFalseAt.wClosed.2, hp.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
      fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1, fvarSubst_of_not_hasFvar hp.wClosed.1] at hp2
    exact defEq_of_eqProof_de hsc ik.bk.eqStored hp2
      (.app (.app (.app .refl .refl) hLhsDe) .refl)
      (ik.decideApp hp (ik.isFalseApp hp hh)) ik.bk.boolFalseAt ik.bk.boolType

private theorem decide_ext (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {p a b : KExpr} (hp : ClosedAt env p (.sort .zero))
    (ha : ClosedAt env a (.app wDec hp.witness)) (hb : ClosedAt env b (.app wDec hp.witness))
    (hEq : DefEq env 0
      (.app (.app (.const (.role .decidableDecide) []) p) a)
      (.app (.app (.const (.role .decidableDecide) []) p) b)) :
    DefEq env 0 a b := by
  have hv := eqnValid_of ik.shapes .decidableDecide (by decide) (by decide) (k := 2) rfl
  rcases hv with ⟨hemp, _⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp [Ix.Kernel.specCert] at hemp
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans (by decide))
    have hsc := ik.bk.storeClosed
    let Γ1 := fvarUpdate Γ₀ 0 (.sort .zero)
    let dec0 := Ix.Kernel.Expr.app wDec (.fvar 0 (.sort .zero))
    let Γ2 := fvarUpdate Γ1 1 dec0
    let Γ3 := fvarUpdate Γ2 2 dec0
    let hypW := Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
      (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar 1 dec0)))
      (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar 2 dec0))
    let Γ4 := fvarUpdate Γ3 3 hypW
    have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
    have hDec0Ws1 : dec0.wscopedB 1 = true := by
      simp [dec0, Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false wDec ik.wDec_cl.1]
    have hCtx2 : CtxWs 2 Γ2 := hCtx1.update hDec0Ws1
    have hDec0Ws2 : dec0.wscopedB 2 = true := by
      simp [dec0, Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false wDec ik.wDec_cl.1]
    have hCtx3 : CtxWs 3 Γ3 := hCtx2.update hDec0Ws2
    have hDecO : ∀ (d : Nat) (Γ : Nat → KExpr), 0 < d → Γ 0 = .sort .zero →
        OpenType env d Γ (.app (.const (.role .decidable) []) (.fvar 0 (.sort .zero))) dec0 (.succ .zero) := by
      intro d Γ h0 hΓ0
      have hf0 : OpenAt env d Γ (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero)) (.sort .zero) := by
        have h := OpenAt.fvar (env := env) (d := d) (idx := 0) (Γ := Γ) h0
        rwa [hΓ0] at h
      have h := OpenType.ofOpenAt ((OpenAt.ofClosed hsc ik.decAt rfl).app_nondep hf0 .refl rfl)
      rwa [ik.decW] at h
    have hDecideAt3 : ∀ (i : Nat), i < 3 → Γ3 i = dec0 →
        OpenAt env 3 Γ3
          (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero))) (.fvar i dec0))
          (.app (.app wDecide (.fvar 0 (.sort .zero))) (.fvar i dec0)) BaseKit.boolT := by
      intro i hi hΓi
      have hf0 : OpenAt env 3 Γ3 (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero)) (.sort .zero) :=
        OpenAt.fvar (d := 3) (idx := 0) (by omega)
      have hfi : OpenAt env 3 Γ3 (.fvar i dec0) (.fvar i dec0) dec0 := by
        have h := OpenAt.fvar (env := env) (d := 3) (idx := i) (Γ := Γ3) hi
        rwa [hΓi] at h
      have h1 := (OpenAt.ofClosed hsc ik.decideAt ik.decideTy_nf).app_abs hf0 .refl
        (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wDec_cl.2])
      simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
        fvarSubst_of_not_hasFvar ik.wDec_cl.1] at h1
      have h2 := h1.app_abs hfi .refl rfl
      simpa [fvarSubst, ik.decideW] using h2
    have hHypO : OpenType env 3 Γ3
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
          (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero))) (.fvar 1 dec0)))
          (.app (.app (.const (.role .decidableDecide) []) (.fvar 0 (.sort .zero))) (.fvar 2 dec0)))
        hypW .zero :=
      OpenType.eq ik.bk.eqStored (OpenType.ofClosed hsc ik.bk.boolType)
        (hDecideAt3 1 (by omega) rfl) .refl (hDecideAt3 2 (by omega) rfl) .refl
    have hEqO : OpenType env 4 Γ4
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero])
          (.app (.const (.role .decidable) []) (.fvar 0 (.sort .zero))))
          (.fvar 1 dec0)) (.fvar 2 dec0))
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) dec0)
          (.fvar 1 dec0)) (.fvar 2 dec0)) .zero :=
      OpenType.eq ik.bk.eqStored (hDecO 4 Γ4 (by omega) rfl)
        (OpenAt.fvar (d := 4) (idx := 1) (by omega)) .refl
        (OpenAt.fvar (d := 4) (idx := 2) (by omega)) .refl
    have hB3O := OpenType.forallE_abs_id (pw := .ifAllZero []) hHypO hEqO rfl hCtx3
    have hB2O := OpenType.forallE_abs_id (pw := .ifAllZero []) (hDecO 2 Γ2 (by omega) rfl) hB3O rfl hCtx2
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) (hDecO 1 Γ1 (by omega) rfl) hB2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort .zero) hB1O rfl
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs hp .refl hB1O.wClosed
    simp [dec0, hypW, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hp.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) hp.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) hp.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1] at hp1
    have hp2 := hp1.app_abs ha .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2,
        lbb_of_lbb0 ik.wDecide_cl.2, lbb_of_lbb0 hp.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) ha.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) ha.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
      fvarSubst_of_not_hasFvar hp.wClosed.1] at hp2
    have hp3 := hp2.app_abs hb .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2,
        lbb_of_lbb0 ik.wDecide_cl.2, lbb_of_lbb0 hp.wClosed.2, lbb_of_lbb0 ha.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hb.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wDecide_cl.1,
      fvarSubst_of_not_hasFvar hp.wClosed.1, fvarSubst_of_not_hasFvar ha.wClosed.1] at hp3
    have hDecA := ik.decideApp hp ha
    have hrefl := closedAt_eqRefl ik.bk.eqReflStored ik.bk.boolType hDecA
    have hDecA_w : DefEq env 0 hDecA.witness (.app (.app wDecide hp.witness) ha.witness) := by
      have h0 : DefEq env 0 (.app (.app wDecide hp.witness) ha.witness)
          (.app (.app (.const (.role .decidableDecide) []) p) a) :=
        .app (.app ik.wDecide_defEq hp.defEq_witness) ha.defEq_witness
      exact hDecA.defEq_trans hDecA.defEq_witness h0.symm
    have hDecB_w : DefEq env 0 hDecA.witness (.app (.app wDecide hp.witness) hb.witness) := by
      have h0 : DefEq env 0 (.app (.app wDecide hp.witness) hb.witness)
          (.app (.app (.const (.role .decidableDecide) []) p) b) :=
        .app (.app ik.wDecide_defEq hp.defEq_witness) hb.defEq_witness
      exact hDecA.defEq_trans hDecA.defEq_witness ((ik.decideApp hp hb).defEq_trans hEq h0.symm)
    have hp4 := hp3.app_abs hrefl (.app (.app (.app .refl .refl) hDecA_w) hDecB_w)
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, hp.wClosed.2, ha.wClosed.2, hb.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar hp.wClosed.1, fvarSubst_of_not_hasFvar ha.wClosed.1,
      fvarSubst_of_not_hasFvar hb.wClosed.1] at hp4
    exact defEq_of_eqProof_de hsc ik.bk.eqStored hp4
      (.app (.app (.app .refl .refl) ha.defEq_witness) hb.defEq_witness) ha hb (ik.decType hp)

/-! ### `ite.{1} Int` computation rules (`iteEqns[0..1]`) -/

private theorem red_beta5 {d2 bodyW a0 a1 a2 a3 a4 : KExpr} {mb : Ix.Kernel.BinderMeta}
    (hd2Bl : d2.looseBVarsBounded 0 = true)
    (hd2No0 : ∀ v, fvarSubst 0 v d2 = d2)
    (hbodyBl : bodyW.looseBVarsBounded 0 = true)
    (ha0 : ClosedAt env a0 (.sort (.succ .zero)))
    (ha1 : ClosedAt env a1 (.sort .zero))
    (ha2 : ClosedAt env a2 (fvarSubst 1 ha1.witness d2))
    (ha3 : ClosedAt env a3 ha0.witness)
    (ha4 : ClosedAt env a4 ha0.witness) :
    Red env 0
      (.app (.app (.app (.app (.app
        (.lam (.sort (.succ .zero))
          ((Ix.Kernel.Expr.lam (.sort .zero)
            ((Ix.Kernel.Expr.lam d2
              ((Ix.Kernel.Expr.lam (.fvar 0 (.sort (.succ .zero)))
                ((Ix.Kernel.Expr.lam (.fvar 0 (.sort (.succ .zero))) (bodyW.abstract1 4) mb).abstract1 3) mb).abstract1 2)
              mb).abstract1 1)
            mb).abstract1 0)
          mb)
        ha0.witness) ha1.witness) ha2.witness) ha3.witness) ha4.witness)
      (fvarSubst 4 ha4.witness (fvarSubst 3 ha3.witness (fvarSubst 2 ha2.witness
        (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW))))) := by
  let b4 := Ix.Kernel.Expr.lam (.fvar 0 (.sort (.succ .zero))) (bodyW.abstract1 4) mb
  let b3 := Ix.Kernel.Expr.lam (.fvar 0 (.sort (.succ .zero))) (b4.abstract1 3) mb
  let b2 := Ix.Kernel.Expr.lam d2 (b3.abstract1 2) mb
  let b1 := Ix.Kernel.Expr.lam (.sort .zero) (b2.abstract1 1) mb
  have hb4Bl : b4.looseBVarsBounded 0 = true := by
    simp [b4, Ix.Kernel.Expr.looseBVarsBounded, looseBVarsBounded_abstract1' hbodyBl]
  have hb3Bl : b3.looseBVarsBounded 0 = true := by
    simp [b3, Ix.Kernel.Expr.looseBVarsBounded, looseBVarsBounded_abstract1' hb4Bl]
  have hb2Bl : b2.looseBVarsBounded 0 = true := by
    simp [b2, Ix.Kernel.Expr.looseBVarsBounded, hd2Bl, looseBVarsBounded_abstract1' hb3Bl]
  have hb1Bl : b1.looseBVarsBounded 0 = true := by
    simp [b1, Ix.Kernel.Expr.looseBVarsBounded, looseBVarsBounded_abstract1' hb2Bl]
  have r0 : Red env 0 (.app (.lam (.sort (.succ .zero)) (b1.abstract1 0) mb) ha0.witness)
      (.lam (.sort .zero)
        ((Ix.Kernel.Expr.lam d2
          ((Ix.Kernel.Expr.lam ha0.witness
            ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 0 ha0.witness bodyW).abstract1 4) mb).abstract1 3)
            mb).abstract1 2) mb).abstract1 1) mb) := by
    have h := Red.beta (env := env) (d := 0) (ty := .sort (.succ .zero)) (body := b1.abstract1 0)
      (mb := mb) ha0.wInfer.toIO .refl
    rw [abstract1_instantiate1_eq_fvarSubst hb1Bl] at h
    simpa [b1, b2, b3, b4, fvarSubst, hd2No0,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha0.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha0.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ha0.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ha0.wClosed.1] using h
  have r1 : Red env 0
      (.app (.lam (.sort .zero)
        ((Ix.Kernel.Expr.lam d2
          ((Ix.Kernel.Expr.lam ha0.witness
            ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 0 ha0.witness bodyW).abstract1 4) mb).abstract1 3)
            mb).abstract1 2) mb).abstract1 1) mb) ha1.witness)
      (.lam (fvarSubst 1 ha1.witness d2)
        ((Ix.Kernel.Expr.lam ha0.witness
          ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)).abstract1 4) mb).abstract1 3)
          mb).abstract1 2) mb) := by
    have h := Red.beta (env := env) (d := 0) (ty := .sort .zero) (mb := mb)
      (body := (Ix.Kernel.Expr.lam d2
        ((Ix.Kernel.Expr.lam ha0.witness
          ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 0 ha0.witness bodyW).abstract1 4) mb).abstract1 3)
          mb).abstract1 2) mb).abstract1 1) ha1.wInfer.toIO .refl
    have hbl : (Ix.Kernel.Expr.lam d2
        ((Ix.Kernel.Expr.lam ha0.witness
          ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 0 ha0.witness bodyW).abstract1 4) mb).abstract1 3)
          mb).abstract1 2) mb).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, hd2Bl, lbb_of_lbb0 ha0.wClosed.2,
        lbb_of_lbb0 (fvarSubst_looseBVarsBounded ha0.wClosed.2 hbodyBl)]
    rw [abstract1_instantiate1_eq_fvarSubst hbl] at h
    simpa [fvarSubst, fvarSubst_of_not_hasFvar ha0.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) ha1.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) ha1.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) ha1.wClosed.1] using h
  have r2 : Red env 0
      (.app (.lam (fvarSubst 1 ha1.witness d2)
        ((Ix.Kernel.Expr.lam ha0.witness
          ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)).abstract1 4) mb).abstract1 3)
          mb).abstract1 2) mb) ha2.witness)
      (.lam ha0.witness
        ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW))).abstract1 4) mb).abstract1 3)
        mb) := by
    have h := Red.beta (env := env) (d := 0) (ty := fvarSubst 1 ha1.witness d2) (mb := mb)
      (body := (Ix.Kernel.Expr.lam ha0.witness
        ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)).abstract1 4) mb).abstract1 3)
        mb).abstract1 2) ha2.wInfer.toIO .refl
    have hbl : (Ix.Kernel.Expr.lam ha0.witness
        ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)).abstract1 4) mb).abstract1 3)
        mb).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ha0.wClosed.2,
        lbb_of_lbb0 (fvarSubst_looseBVarsBounded ha1.wClosed.2 (fvarSubst_looseBVarsBounded ha0.wClosed.2 hbodyBl))]
    rw [abstract1_instantiate1_eq_fvarSubst hbl] at h
    simpa [fvarSubst, fvarSubst_of_not_hasFvar ha0.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) ha2.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) ha2.wClosed.1] using h
  have r3 : Red env 0
      (.app (.lam ha0.witness
        ((Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW))).abstract1 4) mb).abstract1 3)
        mb) ha3.witness)
      (.lam ha0.witness
        ((fvarSubst 3 ha3.witness (fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)))).abstract1 4) mb) := by
    have h := Red.beta (env := env) (d := 0) (ty := ha0.witness) (mb := mb)
      (body := (Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW))).abstract1 4) mb).abstract1 3)
      ha3.wInfer.toIO .refl
    have hbl : (Ix.Kernel.Expr.lam ha0.witness ((fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW))).abstract1 4) mb).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ha0.wClosed.2,
        lbb_of_lbb0 (fvarSubst_looseBVarsBounded ha2.wClosed.2 (fvarSubst_looseBVarsBounded ha1.wClosed.2 (fvarSubst_looseBVarsBounded ha0.wClosed.2 hbodyBl)))]
    rw [abstract1_instantiate1_eq_fvarSubst hbl] at h
    simpa [fvarSubst, fvarSubst_of_not_hasFvar ha0.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ha3.wClosed.1] using h
  have r4 : Red env 0
      (.app (.lam ha0.witness
        ((fvarSubst 3 ha3.witness (fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)))).abstract1 4) mb)
        ha4.witness)
      (fvarSubst 4 ha4.witness (fvarSubst 3 ha3.witness (fvarSubst 2 ha2.witness
        (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW))))) := by
    have h := Red.beta (env := env) (d := 0) (ty := ha0.witness) (mb := mb)
      (body := (fvarSubst 3 ha3.witness (fvarSubst 2 ha2.witness (fvarSubst 1 ha1.witness (fvarSubst 0 ha0.witness bodyW)))).abstract1 4)
      ha4.wInfer.toIO .refl
    rwa [abstract1_instantiate1_eq_fvarSubst
      (fvarSubst_looseBVarsBounded ha3.wClosed.2 (fvarSubst_looseBVarsBounded ha2.wClosed.2
        (fvarSubst_looseBVarsBounded ha1.wClosed.2 (fvarSubst_looseBVarsBounded ha0.wClosed.2 hbodyBl))))] at h
  exact .trans (.appFn (.appFn (.appFn (.appFn r0))))
    (.trans (.appFn (.appFn (.appFn r1)))
      (.trans (.appFn (.appFn r2))
        (.trans (.appFn r3) r4)))

private theorem ite_int_isTrue (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {c h t e : KExpr} (hc : ClosedAt env c (.sort .zero)) (hh : ClosedAt env h hc.witness)
    (ht : ClosedAt env t wInt) (he : ClosedAt env e wInt) :
    DefEq env 0
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c)
        (.app (.app (.const (.role .decidableIsTrue) []) c) h)) t) e)
      t := by
  have hv := eqnValid_of ik.shapes .ifThenElse (by decide) (by decide) (k := 0) rfl
  have hsc := ik.bk.storeClosed
  let α0 : KExpr := Ix.Kernel.Expr.fvar 0 (.sort (.succ .zero))
  let c1 : KExpr := Ix.Kernel.Expr.fvar 1 (.sort .zero)
  let h2 : KExpr := Ix.Kernel.Expr.fvar 2 c1
  let t3 : KExpr := Ix.Kernel.Expr.fvar 3 α0
  let e4 : KExpr := Ix.Kernel.Expr.fvar 4 α0
  let Γ1 := fvarUpdate Γ₀ 0 (.sort (.succ .zero))
  let Γ2 := fvarUpdate Γ1 1 (.sort .zero)
  let Γ3 := fvarUpdate Γ2 2 c1
  let Γ4 := fvarUpdate Γ3 3 α0
  let Γ5 := fvarUpdate Γ4 4 α0
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
  have hCtx2 : CtxWs 2 Γ2 := hCtx1.update (by simp [Ix.Kernel.Expr.wscopedB])
  have hCtx3 : CtxWs 3 Γ3 := hCtx2.update (by simp [c1, Ix.Kernel.Expr.wscopedB])
  have hCtx4 : CtxWs 4 Γ4 := hCtx3.update (by simp [α0, Ix.Kernel.Expr.wscopedB])
  have hLhsO : OpenAt env 5 Γ5
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero]) α0) c1)
        (.app (.app (.const (.role .decidableIsTrue) []) c1) h2)) t3) e4)
      (.app (.app (.app (.app (.app ik.iteAt.witness α0) c1)
        (.app (.app ik.isTrueAt.witness c1) h2)) t3) e4) α0 := by
    have hf0 : OpenAt env 5 Γ5 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 5) (idx := 0) (Γ := Γ5) (by omega)
    have hf1 : OpenAt env 5 Γ5 c1 c1 (.sort .zero) := OpenAt.fvar (d := 5) (idx := 1) (Γ := Γ5) (by omega)
    have hf2 : OpenAt env 5 Γ5 h2 h2 c1 := OpenAt.fvar (d := 5) (idx := 2) (Γ := Γ5) (by omega)
    have hf3 : OpenAt env 5 Γ5 t3 t3 α0 := OpenAt.fvar (d := 5) (idx := 3) (Γ := Γ5) (by omega)
    have hf4 : OpenAt env 5 Γ5 e4 e4 α0 := OpenAt.fvar (d := 5) (idx := 4) (Γ := Γ5) (by omega)
    have hIsT1 := (OpenAt.ofClosed hsc ik.isTrueAt ik.isTrueTy_nf).app_dep hf1 .refl
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
      abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at hIsT1
    have hIsT2 := hIsT1.app_dep hf2 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2] at hIsT2
    have hα0_lbb : α0.looseBVarsBounded 0 = true := rfl
    have hI1 := (OpenAt.ofClosed hsc ik.iteAt ik.iteTy_nf).app_dep hf0 .refl
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
      abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at hI1
    have hI2 := hI1.app_dep hf1 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2, inst1_of_lbb0 hα0_lbb] at hI2
    have hI3 := hI2.app_dep hIsT2 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 hα0_lbb] at hI3
    have hI4 := hI3.app_dep hf3 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 hα0_lbb] at hI4
    have hI5 := hI4.app_dep hf4 .refl
    simpa [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 hα0_lbb] using hI5
  have hLhsDe : DefEq env 0
      (.app (.app (.app (.app (.app ik.iteAt.witness wInt) hc.witness)
        (.app (.app ik.isTrueAt.witness hc.witness) hh.witness)) ht.witness) he.witness)
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c)
        (.app (.app (.const (.role .decidableIsTrue) []) c) h)) t) e) :=
    .app (.app (.app (.app (.app ik.iteAt.defEq_witness ik.wInt_defEq)
      hc.defEq_witness) (.app (.app ik.isTrueAt.defEq_witness hc.defEq_witness) hh.defEq_witness))
      ht.defEq_witness) he.defEq_witness
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · have hinst := DefEq.instClosed (d := 0) (ks := [0]) (us := [.succ .zero]) rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hde
    simp only [eqnsSideExact, List.zipIdx, List.foldr,
      Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst.go,
      Ix.Kernel.Level.substPW, bmeta] at hinst
    have hD4 : OpenType env 4 Γ4 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (env := env) (d := 4) (idx := 0) (Γ := Γ4) (by omega))
    have hD3 : OpenType env 3 Γ3 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (env := env) (d := 3) (idx := 0) (Γ := Γ3) (by omega))
    have hD2 : OpenType env 2 Γ2 c1 c1 .zero :=
      OpenType.ofOpenAt (OpenAt.fvar (env := env) (d := 2) (idx := 1) (Γ := Γ2) (by omega))
    have hLamL4 := OpenAt.lam_abs_inner_id (pw := .never) hD4 hLhsO
      (Infer.fvar (by omega)) .refl rfl rfl hCtx4
    have hLamL3 := OpenAt.lam_abs_outer_id hD3 hLamL4 hCtx3
    have hLamL2 := OpenAt.lam_abs_outer_id hD2 hLamL3 hCtx2
    have hLamL1 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamL2 hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamL1
    have hRhsO : OpenAt env 5 Γ5 t3 t3 α0 := OpenAt.fvar (d := 5) (idx := 3) (by omega)
    have hLamR4 := OpenAt.lam_abs_inner_id (pw := .never) hD4 hRhsO
      (Infer.fvar (by omega)) .refl rfl rfl hCtx4
    have hLamR3 := OpenAt.lam_abs_outer_id hD3 hLamR4 hCtx3
    have hLamR2 := OpenAt.lam_abs_outer_id hD2 hLamR3 hCtx2
    have hLamR1 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamR2 hCtx1
    have hLamR0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamR1
    have hintO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ik.intAt rfl
    have hcO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hc rfl
    have hhO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hh hc.wClosed.1
    have htO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ht ik.wInt_cl.1
    have heO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) he ik.wInt_cl.1
    have hAppL1 := hLamL0.app_abs hintO .refl (by decide)
    rw [ik.intW] at hAppL1
    simp [α0, c1, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hcO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppL2
    have hAppL3 := hAppL2.app_abs hhO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hh.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hh.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppL3
    have hAppL4 := hAppL3.app_abs htO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppL4
    have hAppL5 := hAppL4.app_abs heO .refl ik.wInt_cl.2
    have hAppR1 := hLamR0.app_abs hintO .refl (by decide)
    rw [ik.intW] at hAppR1
    simp [α0, c1, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hcO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppR2
    have hAppR3 := hAppR2.app_abs hhO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hh.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hh.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppR3
    have hAppR4 := hAppR3.app_abs htO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppR4
    have hAppR5 := hAppR4.app_abs heO .refl ik.wInt_cl.2
    let ht' : ClosedAt env t ik.intAt.witness :=
      { closed := ht.closed, witness := ht.witness, wClosed := ht.wClosed,
        wInfer := by rw [ik.intW]; exact ht.wInfer, wRed := ht.wRed, wLamPw := ht.wLamPw }
    let he' : ClosedAt env e ik.intAt.witness :=
      { closed := he.closed, witness := he.witness, wClosed := he.wClosed,
        wInfer := by rw [ik.intW]; exact he.wInfer, wRed := he.wRed, wLamPw := he.wLamPw }
    have hRedL := red_beta5 (d2 := c1) (mb := { pw := .never }) rfl (fun _ => rfl)
      hLhsO.wClosed ik.intAt hc hh ht' he'
    simp [α0, c1, h2, t3, e4, ht', he', fvarSubst, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.intAt.wClosed.1, fvarSubst_of_not_hasFvar hc.wClosed.1,
      fvarSubst_of_not_hasFvar hh.wClosed.1, fvarSubst_of_not_hasFvar ht.wClosed.1] at hRedL
    rw [ik.intW] at hRedL
    have hRedR := red_beta5 (d2 := c1) (bodyW := t3) (mb := { pw := .never }) rfl (fun _ => rfl)
      rfl ik.intAt hc hh ht' he'
    simp [t3, ht', he', fvarSubst, fvarSubst_of_not_hasFvar ht.wClosed.1] at hRedR
    rw [ik.intW] at hRedR
    exact OpenAt.defEq_chain hAppL5 hAppR5
      (.app (.app (.app (.app (.app hinst .refl) .refl) .refl) .refl) .refl)
      hRedL hLhsDe hRedR ht.defEq_witness
  · have hlen : cv.levelParams.length = 1 := Option.some.inj (hlv.symm.trans (by decide))
    have hD5_0 : OpenType env 5 Γ5 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 5) (idx := 0) (Γ := Γ5) (by omega))
    have hRhs5 : OpenAt env 5 Γ5 t3 t3 α0 := OpenAt.fvar (d := 5) (idx := 3) (Γ := Γ5) (by omega)
    have hD4 : OpenType env 4 Γ4 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 4) (idx := 0) (Γ := Γ4) (by omega))
    have hD3 : OpenType env 3 Γ3 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega))
    have hD2 : OpenType env 2 Γ2 c1 c1 .zero :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega))
    have hEqO := OpenType.eq ik.bk.eqStored hD5_0 hLhsO .refl hRhs5 .refl
    have hB4O := OpenType.forallE_abs_id (pw := .ifAllZero []) hD4 hEqO rfl hCtx4
    have hB3O := OpenType.forallE_abs_id (pw := .ifAllZero []) hD3 hB4O rfl hCtx3
    have hB2O := OpenType.forallE_abs_id (pw := .ifAllZero []) hD2 hB3O rfl hCtx2
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort .zero) hB2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort (.succ .zero)) hB1O rfl
    have hPiRed := hStmtO.wPiRed
    have heq :
        (.forallE (.sort (.succ .zero))
          ((Ix.Kernel.Expr.forallE (.sort .zero)
            ((Ix.Kernel.Expr.forallE c1
              ((Ix.Kernel.Expr.forallE α0
                ((Ix.Kernel.Expr.forallE α0
                  ((Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) α0)
                    (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero]) α0) c1)
                      (.app (.app (.const (.role .decidableIsTrue) []) c1) h2)) t3) e4)) t3).abstract1 4)
                  { pw := .ifAllZero [] }).abstract1 3)
                { pw := .ifAllZero [] }).abstract1 2)
              { pw := .ifAllZero [] }).abstract1 1)
            { pw := .ifAllZero [] }).abstract1 0)
          { pw := .ifAllZero [] }) =
        (eqnsStmtExact (Ix.Kernel.iteEqns[0]'(by decide))).instantiateLevelParams [0] [.succ .zero] := by
      decide
    rw [heq] at hPiRed
    have hp0 := ClosedAt.ofThm1_de hsc ik.bk.wf hf hlen hde (by decide) ⟨by decide, by decide⟩
      hPiRed hStmtO.toClosedType
    have hp1 := hp0.app_abs ik.intAt .refl hB1O.wClosed
    rw [ik.intW] at hp1
    simp [α0, c1, h2, t3, e4, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1] at hp1
    have hp2 := hp1.app_abs hc .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2,
        lbb_of_lbb0 ik.iteAt.wClosed.2, lbb_of_lbb0 ik.isTrueAt.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
      fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hp2
    have hp3 := hp2.app_abs hh .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2,
        lbb_of_lbb0 ik.iteAt.wClosed.2, lbb_of_lbb0 ik.isTrueAt.wClosed.2, lbb_of_lbb0 hc.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hh.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hh.wClosed.1,
      fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar hc.wClosed.1] at hp3
    have hp4 := hp3.app_abs ht .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2,
        lbb_of_lbb0 ik.iteAt.wClosed.2, lbb_of_lbb0 ik.isTrueAt.wClosed.2, lbb_of_lbb0 hc.wClosed.2,
        lbb_of_lbb0 hh.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
      fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar hc.wClosed.1,
      fvarSubst_of_not_hasFvar hh.wClosed.1] at hp4
    have hp5 := hp4.app_abs he .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2, ik.iteAt.wClosed.2,
        ik.isTrueAt.wClosed.2, hc.wClosed.2, hh.wClosed.2, ht.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.isTrueAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar hc.wClosed.1, fvarSubst_of_not_hasFvar hh.wClosed.1,
      fvarSubst_of_not_hasFvar ht.wClosed.1] at hp5
    exact defEq_of_eqProof_de hsc ik.bk.eqStored hp5
      (.app (.app (.app .refl .refl) hLhsDe) ht.defEq_witness)
      (ik.iteIntApp hc (ik.isTrueApp hc hh) ht he) ht ik.intType

private theorem ite_int_isFalse (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {c h t e : KExpr} (hc : ClosedAt env c (.sort .zero))
    (hh : ClosedAt env h (.app wNot hc.witness))
    (ht : ClosedAt env t wInt) (he : ClosedAt env e wInt) :
    DefEq env 0
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c)
        (.app (.app (.const (.role .decidableIsFalse) []) c) h)) t) e)
      e := by
  have hv := eqnValid_of ik.shapes .ifThenElse (by decide) (by decide) (k := 1) rfl
  have hsc := ik.bk.storeClosed
  let α0 : KExpr := Ix.Kernel.Expr.fvar 0 (.sort (.succ .zero))
  let c1 : KExpr := Ix.Kernel.Expr.fvar 1 (.sort .zero)
  let notC1 : KExpr := Ix.Kernel.Expr.app wNot c1
  let h2 : KExpr := Ix.Kernel.Expr.fvar 2 notC1
  let t3 : KExpr := Ix.Kernel.Expr.fvar 3 α0
  let e4 : KExpr := Ix.Kernel.Expr.fvar 4 α0
  let Γ1 := fvarUpdate Γ₀ 0 (.sort (.succ .zero))
  let Γ2 := fvarUpdate Γ1 1 (.sort .zero)
  let Γ3 := fvarUpdate Γ2 2 notC1
  let Γ4 := fvarUpdate Γ3 3 α0
  let Γ5 := fvarUpdate Γ4 4 α0
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
  have hCtx2 : CtxWs 2 Γ2 := hCtx1.update (by simp [Ix.Kernel.Expr.wscopedB])
  have hCtx3 : CtxWs 3 Γ3 := hCtx2.update (by
    simp [notC1, c1, Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false wNot ik.wNot_cl.1])
  have hCtx4 : CtxWs 4 Γ4 := hCtx3.update (by simp [α0, Ix.Kernel.Expr.wscopedB])
  have hNotO : OpenType env 2 Γ2 (.app (.const (.role .notProp) []) c1) notC1 .zero := by
    have h := OpenType.ofOpenAt
      ((OpenAt.ofClosed hsc ik.notAt rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)) .refl rfl)
    rwa [ik.notW] at h
  have hLhsO : OpenAt env 5 Γ5
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero]) α0) c1)
        (.app (.app (.const (.role .decidableIsFalse) []) c1) h2)) t3) e4)
      (.app (.app (.app (.app (.app ik.iteAt.witness α0) c1)
        (.app (.app ik.isFalseAt.witness c1) h2)) t3) e4) α0 := by
    have hf0 : OpenAt env 5 Γ5 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 5) (idx := 0) (Γ := Γ5) (by omega)
    have hf1 : OpenAt env 5 Γ5 c1 c1 (.sort .zero) := OpenAt.fvar (d := 5) (idx := 1) (Γ := Γ5) (by omega)
    have hf2 : OpenAt env 5 Γ5 h2 h2 notC1 := OpenAt.fvar (d := 5) (idx := 2) (Γ := Γ5) (by omega)
    have hf3 : OpenAt env 5 Γ5 t3 t3 α0 := OpenAt.fvar (d := 5) (idx := 3) (Γ := Γ5) (by omega)
    have hf4 : OpenAt env 5 Γ5 e4 e4 α0 := OpenAt.fvar (d := 5) (idx := 4) (Γ := Γ5) (by omega)
    have hIsF1 := (OpenAt.ofClosed hsc ik.isFalseAt ik.isFalseTy_nf).app_dep hf1 .refl
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
      abstract1_eq_self wNot ik.wNot_cl.1, inst1_of_lbb0 ik.wNot_cl.2,
      abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at hIsF1
    have hIsF2 := hIsF1.app_dep hf2 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2] at hIsF2
    have hα0_lbb : α0.looseBVarsBounded 0 = true := rfl
    have hI1 := (OpenAt.ofClosed hsc ik.iteAt ik.iteTy_nf).app_dep hf0 .refl
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
      abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at hI1
    have hI2 := hI1.app_dep hf1 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2, inst1_of_lbb0 hα0_lbb] at hI2
    have hI3 := hI2.app_dep hIsF2 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 hα0_lbb] at hI3
    have hI4 := hI3.app_dep hf3 .refl
    simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 hα0_lbb] at hI4
    have hI5 := hI4.app_dep hf4 .refl
    simpa [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 hα0_lbb] using hI5
  have hLhsDe : DefEq env 0
      (.app (.app (.app (.app (.app ik.iteAt.witness wInt) hc.witness)
        (.app (.app ik.isFalseAt.witness hc.witness) hh.witness)) ht.witness) he.witness)
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c)
        (.app (.app (.const (.role .decidableIsFalse) []) c) h)) t) e) :=
    .app (.app (.app (.app (.app ik.iteAt.defEq_witness ik.wInt_defEq)
      hc.defEq_witness) (.app (.app ik.isFalseAt.defEq_witness hc.defEq_witness) hh.defEq_witness))
      ht.defEq_witness) he.defEq_witness
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · have hinst := DefEq.instClosed (d := 0) (ks := [0]) (us := [.succ .zero]) rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hde
    simp only [eqnsSideExact, List.zipIdx, List.foldr,
      Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst.go,
      Ix.Kernel.Level.substPW, bmeta] at hinst
    have hD4 : OpenType env 4 Γ4 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (env := env) (d := 4) (idx := 0) (Γ := Γ4) (by omega))
    have hD3 : OpenType env 3 Γ3 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (env := env) (d := 3) (idx := 0) (Γ := Γ3) (by omega))
    have hLamL4 := OpenAt.lam_abs_inner_id (pw := .never) hD4 hLhsO
      (Infer.fvar (by omega)) .refl rfl rfl hCtx4
    have hLamL3 := OpenAt.lam_abs_outer_id hD3 hLamL4 hCtx3
    have hLamL2 := OpenAt.lam_abs_outer_id hNotO hLamL3 hCtx2
    have hLamL1 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamL2 hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamL1
    have hRhsO : OpenAt env 5 Γ5 e4 e4 α0 := OpenAt.fvar (d := 5) (idx := 4) (by omega)
    have hLamR4 := OpenAt.lam_abs_inner_id (pw := .never) hD4 hRhsO
      (Infer.fvar (by omega)) .refl rfl rfl hCtx4
    have hLamR3 := OpenAt.lam_abs_outer_id hD3 hLamR4 hCtx3
    have hLamR2 := OpenAt.lam_abs_outer_id hNotO hLamR3 hCtx2
    have hLamR1 := OpenAt.lam_abs_outer_id (OpenType.sort .zero) hLamR2 hCtx1
    have hLamR0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamR1
    have hintO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ik.intAt rfl
    have hcO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hc rfl
    have hhO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hh
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wNot_cl.1, hc.wClosed.1])
    have htO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ht ik.wInt_cl.1
    have heO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) he ik.wInt_cl.1
    have hAppL1 := hLamL0.app_abs hintO .refl (by simp [notC1, c1, α0, Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wNot_cl.2])
    rw [ik.intW] at hAppL1
    simp [α0, c1, notC1, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hcO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppL2
    have hAppL3 := hAppL2.app_abs hhO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hh.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hh.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppL3
    have hAppL4 := hAppL3.app_abs htO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppL4
    have hAppL5 := hAppL4.app_abs heO .refl ik.wInt_cl.2
    have hAppR1 := hLamR0.app_abs hintO .refl (by simp [notC1, c1, α0, Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wNot_cl.2])
    rw [ik.intW] at hAppR1
    simp [α0, c1, notC1, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hcO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppR2
    have hAppR3 := hAppR2.app_abs hhO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hh.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hh.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppR3
    have hAppR4 := hAppR3.app_abs htO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hAppR4
    have hAppR5 := hAppR4.app_abs heO .refl ik.wInt_cl.2
    have hNotSub : fvarSubst 1 hc.witness notC1 = .app wNot hc.witness := by
      simp [notC1, c1, fvarSubst, fvarSubst_of_not_hasFvar ik.wNot_cl.1]
    let hh' : ClosedAt env h (fvarSubst 1 hc.witness notC1) :=
      { closed := hh.closed, witness := hh.witness, wClosed := hh.wClosed,
        wInfer := by rw [hNotSub]; exact hh.wInfer, wRed := hh.wRed, wLamPw := hh.wLamPw }
    let ht' : ClosedAt env t ik.intAt.witness :=
      { closed := ht.closed, witness := ht.witness, wClosed := ht.wClosed,
        wInfer := by rw [ik.intW]; exact ht.wInfer, wRed := ht.wRed, wLamPw := ht.wLamPw }
    let he' : ClosedAt env e ik.intAt.witness :=
      { closed := he.closed, witness := he.witness, wClosed := he.wClosed,
        wInfer := by rw [ik.intW]; exact he.wInfer, wRed := he.wRed, wLamPw := he.wLamPw }
    have hRedL := red_beta5 (d2 := notC1) (mb := { pw := .never })
      (by simp [notC1, c1, Ix.Kernel.Expr.looseBVarsBounded, ik.wNot_cl.2])
      (fun v => by simp [notC1, c1, fvarSubst, fvarSubst_of_not_hasFvar ik.wNot_cl.1])
      hLhsO.wClosed ik.intAt hc hh' ht' he'
    simp [α0, c1, h2, t3, e4, hh', ht', he', fvarSubst, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.intAt.wClosed.1, fvarSubst_of_not_hasFvar hc.wClosed.1,
      fvarSubst_of_not_hasFvar hh.wClosed.1, fvarSubst_of_not_hasFvar ht.wClosed.1] at hRedL
    rw [ik.intW] at hRedL
    have hRedR := red_beta5 (d2 := notC1) (bodyW := e4) (mb := { pw := .never })
      (by simp [notC1, c1, Ix.Kernel.Expr.looseBVarsBounded, ik.wNot_cl.2])
      (fun v => by simp [notC1, c1, fvarSubst, fvarSubst_of_not_hasFvar ik.wNot_cl.1])
      rfl ik.intAt hc hh' ht' he'
    simp [e4, hh', ht', he', fvarSubst] at hRedR
    rw [ik.intW] at hRedR
    exact OpenAt.defEq_chain hAppL5 hAppR5
      (.app (.app (.app (.app (.app hinst .refl) .refl) .refl) .refl) .refl)
      hRedL hLhsDe hRedR he.defEq_witness
  · have hlen : cv.levelParams.length = 1 := Option.some.inj (hlv.symm.trans (by decide))
    have hD5_0 : OpenType env 5 Γ5 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 5) (idx := 0) (Γ := Γ5) (by omega))
    have hRhs5 : OpenAt env 5 Γ5 e4 e4 α0 := OpenAt.fvar (d := 5) (idx := 4) (Γ := Γ5) (by omega)
    have hD4 : OpenType env 4 Γ4 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 4) (idx := 0) (Γ := Γ4) (by omega))
    have hD3 : OpenType env 3 Γ3 α0 α0 (.succ .zero) :=
      OpenType.ofOpenAt (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega))
    have hEqO := OpenType.eq ik.bk.eqStored hD5_0 hLhsO .refl hRhs5 .refl
    have hB4O := OpenType.forallE_abs_id (pw := .ifAllZero []) hD4 hEqO rfl hCtx4
    have hB3O := OpenType.forallE_abs_id (pw := .ifAllZero []) hD3 hB4O rfl hCtx3
    have hB2O := OpenType.forallE_abs_id (pw := .ifAllZero []) hNotO hB3O rfl hCtx2
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort .zero) hB2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort (.succ .zero)) hB1O rfl
    have hPiRed := hStmtO.wPiRed
    have heq :
        (.forallE (.sort (.succ .zero))
          ((Ix.Kernel.Expr.forallE (.sort .zero)
            ((Ix.Kernel.Expr.forallE (.app (.const (.role .notProp) []) c1)
              ((Ix.Kernel.Expr.forallE α0
                ((Ix.Kernel.Expr.forallE α0
                  ((Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) α0)
                    (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero]) α0) c1)
                      (.app (.app (.const (.role .decidableIsFalse) []) c1) h2)) t3) e4)) e4).abstract1 4)
                  { pw := .ifAllZero [] }).abstract1 3)
                { pw := .ifAllZero [] }).abstract1 2)
              { pw := .ifAllZero [] }).abstract1 1)
            { pw := .ifAllZero [] }).abstract1 0)
          { pw := .ifAllZero [] }) =
        (eqnsStmtExact (Ix.Kernel.iteEqns[1]'(by decide))).instantiateLevelParams [0] [.succ .zero] := by
      simp [α0, c1, h2, t3, e4, Ix.Kernel.Expr.abstract1]
      decide
    rw [heq] at hPiRed
    have hp0 := ClosedAt.ofThm1_de hsc ik.bk.wf hf hlen hde (by decide) ⟨by decide, by decide⟩
      hPiRed hStmtO.toClosedType
    have hp1 := hp0.app_abs ik.intAt .refl hB1O.wClosed
    rw [ik.intW] at hp1
    simp [α0, c1, notC1, h2, t3, e4, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) ik.wInt_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 4) ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1] at hp1
    have hp2 := hp1.app_abs hc .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wNot_cl.2,
        lbb_of_lbb0 ik.wInt_cl.2, lbb_of_lbb0 ik.iteAt.wClosed.2, lbb_of_lbb0 ik.isFalseAt.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) hc.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 4) hc.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wNot_cl.1, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1] at hp2
    have hp3 := hp2.app_abs hh .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2,
        lbb_of_lbb0 ik.iteAt.wClosed.2, lbb_of_lbb0 ik.isFalseAt.wClosed.2, lbb_of_lbb0 hc.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hh.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 4) hh.wClosed.1,
      fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar hc.wClosed.1] at hp3
    have hp4 := hp3.app_abs ht .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wInt_cl.2,
        lbb_of_lbb0 ik.iteAt.wClosed.2, lbb_of_lbb0 ik.isFalseAt.wClosed.2, lbb_of_lbb0 hc.wClosed.2,
        lbb_of_lbb0 hh.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (3 : Nat) ≠ 4) ht.wClosed.1,
      fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar hc.wClosed.1,
      fvarSubst_of_not_hasFvar hh.wClosed.1] at hp4
    have hp5 := hp4.app_abs he .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2, ik.iteAt.wClosed.2,
        ik.isFalseAt.wClosed.2, hc.wClosed.2, hh.wClosed.2, ht.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.isFalseAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar hc.wClosed.1, fvarSubst_of_not_hasFvar hh.wClosed.1,
      fvarSubst_of_not_hasFvar ht.wClosed.1] at hp5
    exact defEq_of_eqProof_de hsc ik.bk.eqStored hp5
      (.app (.app (.app .refl .refl) hLhsDe) he.defEq_witness)
      (ik.iteIntApp hc (ik.isFalseApp hc hh) ht he) he ik.intType

private theorem ite_int_of_decide_true (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {c inst t e : KExpr} (hc : ClosedAt env c (.sort .zero))
    (hinst : ClosedAt env inst (.app wDec hc.witness))
    (ht : ClosedAt env t wInt) (he : ClosedAt env e wInt)
    (hTrue : DefEq env 0 (.app (.app (.const (.role .decidableDecide) []) c) inst) BaseKit.trueE) :
    DefEq env 0
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c) inst) t) e) t := by
  obtain ⟨prf, ⟨hprf⟩⟩ := ik.ofDecideTrueApp hc hinst hTrue
  have hInstEq := ik.decide_ext hc hinst (ik.isTrueApp hc hprf)
    (ik.bk.boolTrueAt.defEq_trans hTrue (ik.decide_isTrue hc hprf).symm)
  exact (ik.iteIntApp hc (ik.isTrueApp hc hprf) ht he).defEq_trans
    (.app (.app (.app .refl hInstEq) .refl) .refl) (ik.ite_int_isTrue hc hprf ht he)

private theorem ite_int_of_decide_false (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {c inst t e : KExpr} (hc : ClosedAt env c (.sort .zero))
    (hinst : ClosedAt env inst (.app wDec hc.witness))
    (ht : ClosedAt env t wInt) (he : ClosedAt env e wInt)
    (hFalse : DefEq env 0 (.app (.app (.const (.role .decidableDecide) []) c) inst) BaseKit.falseE) :
    DefEq env 0
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) [])) c) inst) t) e) e := by
  obtain ⟨prf, ⟨hprf⟩⟩ := ik.ofDecideFalseApp hc hinst hFalse
  have hInstEq := ik.decide_ext hc hinst (ik.isFalseApp hc hprf)
    (ik.bk.boolFalseAt.defEq_trans hFalse (ik.decide_isFalse hc hprf).symm)
  exact (ik.iteIntApp hc (ik.isFalseApp hc hprf) ht he).defEq_trans
    (.app (.app (.app .refl hInstEq) .refl) .refl) (ik.ite_int_isFalse hc hprf ht he)

/-! ### `Int` arithmetic and decision-procedure equations -/

private theorem defEq_intNegOfNat (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (n : Nat) :
    DefEq env 0 (.app (.const (.role .intNegOfNat) []) (.lit (.natVal n)))
      (intLitExpr (Int.negOfNat n)) := by
  have hsc := ik.bk.storeClosed
  cases n with
  | zero =>
    have hLhsCl := ik.intNegOfNatAt.app_nondep ik.bk.natZeroAt ik.wInt_cl.2
    have hRhsCl := ik.intOfNatAt.app_nondep ik.bk.natZeroAt ik.wInt_cl.2
    have h0 := applyEqn0 ik.bk
      (eqnValid_of ik.shapes .intNegOfNat (by decide) (by decide) (k := 0) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed hLhsCl hRhsCl
    exact hLhsCl.defEq_trans (.app .refl ik.bk.defEq_natZero_lit.symm)
      (hRhsCl.defEq_trans h0 (.app .refl ik.bk.defEq_natZero_lit))
  | succ k =>
    have hLhsO := (OpenAt.ofClosed hsc ik.intNegOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
          (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl rfl)
        .refl ik.wInt_cl.2
    have hRhsO := (OpenAt.ofClosed hsc ik.intNegSuccAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2
    have hLhsCl := ik.intNegOfNatAt.app_nondep (ik.bk.natSuccApp (ik.bk.natLitAt k)) ik.wInt_cl.2
    have h1 := applyEqn1 ik.bk
      (eqnValid_of ik.shapes .intNegOfNat (by decide) (by decide) (k := 1) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) rfl rfl rfl rfl hLhsO hRhsO
      (ik.bk.natLitAt k) rfl rfl
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegOfNatAt.wClosed.1]
          exact .app ik.intNegOfNatAt.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl))
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
          exact .app ik.intNegSuccAt.defEq_witness .refl)
      hLhsCl (ik.intNegSuccAt.app_nondep (ik.bk.natLitAt k) ik.wInt_cl.2)
    exact hLhsCl.defEq_trans (.app .refl (ik.bk.defEq_natSucc_lit k).symm) h1

private theorem defEq_intSubNatNat (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Nat) :
    DefEq env 0 (.app (.app (.const (.role .intSubNatNat) []) (.lit (.natVal x))) (.lit (.natVal y)))
      (intLitExpr (Int.subNatNat x y)) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hBle⟩⟩ := ik.bk.natBinBoolAt (r := .natBle) (by decide) (Or.inr rfl)
  obtain ⟨_, _, ⟨hSub⟩⟩ := ik.bk.natBinNatAt (r := .natSub) (by decide) (by decide) (by decide)
  obtain ⟨_, ⟨hPred⟩⟩ := ik.bk.natPredAt
  let hx := ik.bk.natLitAt x
  let hy := ik.bk.natLitAt y
  have hBleO : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 BaseKit.natT) 1 BaseKit.natT)
      (.app (.app (.const (.role .natBle) []) (.fvar 1 BaseKit.natT)) (.fvar 0 BaseKit.natT))
      (.app (.app hBle.witness (.fvar 1 BaseKit.natT)) (.fvar 0 BaseKit.natT)) BaseKit.boolT :=
    ((OpenAt.ofClosed hsc hBle rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl
  have hSubInt : Int.subNatNat x y =
      if y ≤ x then Int.ofNat (x - y) else Int.negSucc (Nat.pred (y - x)) := by
    unfold Int.subNatNat
    split <;> rename_i h
    · have hle : y ≤ x := by omega
      simp [hle]
    · have hlt : ¬ (y ≤ x) := by omega
      simp [hlt]
      omega
  rw [hSubInt]
  by_cases hle : y ≤ x
  · simp only [hle, ↓reduceIte]
    have hBleRes : DefEq env 0 (.app (.app (.const (.role .natBle) []) (.lit (.natVal y))) (.lit (.natVal x)))
        BaseKit.trueE :=
      ik.bk.defEq_natOp (r := .natBle) (by decide) (by simp [Ix.Kernel.natOpResult, hle])
    have hSubRes : DefEq env 0 (.app (.app (.const (.role .natSub) []) (.lit (.natVal x))) (.lit (.natVal y)))
        (.lit (.natVal (x - y))) :=
      ik.bk.defEq_natOp (r := .natSub) (by decide) (by simp [Ix.Kernel.natOpResult])
    let Γ3 := fvarUpdate ΓNat2 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
      (.app (.app hBle.witness (.fvar 1 BaseKit.natT)) (.fvar 0 BaseKit.natT))) BaseKit.trueE)
    have hLhsO := ((OpenAt.ofClosed hsc ik.intSubNatNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl
        ik.forallNatInt_lbb0).app_nondep
        (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl ik.wInt_cl.2
    have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (((OpenAt.ofClosed hsc hSub rfl).app_nondep (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl rfl).app_nondep
          (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl rfl)
        .refl ik.wInt_cl.2
    have hRhsCl := ik.intOfNatAt.app_nondep ((hSub.app_nondep hx rfl).app_nondep hy rfl) ik.wInt_cl.2
    have hEq := applyEqn2Hyp1 ik.bk
      (eqnValid_of ik.shapes .intSubNatNat (by decide) (by decide) (k := 0) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
      rfl rfl rfl ik.bk.boolTrueAt rfl rfl hBleO hLhsO hRhsO
      (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1])
      (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                         fvarSubst_of_not_hasFvar hSub.wClosed.1])
      hx hy
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBle.wClosed.1]
          exact .redL (.appFn (.appFn hBle.wRed)) hBleRes)
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1]
          exact .app (.app ik.intSubNatNatAt.defEq_witness .refl) .refl)
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                fvarSubst_of_not_hasFvar hSub.wClosed.1]
          exact .app ik.intOfNatAt.defEq_witness (.app (.app hSub.defEq_witness .refl) .refl))
      ((ik.intSubNatNatAt.app_nondep hx ik.forallNatInt_lbb0).app_nondep
        hy ik.wInt_cl.2)
      hRhsCl
    exact hRhsCl.defEq_trans hEq (.app .refl hSubRes)
  · simp only [hle, ↓reduceIte]
    have hBleRes : DefEq env 0 (.app (.app (.const (.role .natBle) []) (.lit (.natVal y))) (.lit (.natVal x)))
        BaseKit.falseE :=
      ik.bk.defEq_natOp (r := .natBle) (by decide) (by simp [Ix.Kernel.natOpResult, hle])
    have hSubRed : Red env 0 (.app (.app (.const (.role .natSub) []) (.lit (.natVal y))) (.lit (.natVal x)))
        (.lit (.natVal (y - x))) :=
      ik.bk.red_natOp (r := .natSub) (by decide) (by simp [Ix.Kernel.natOpResult])
    have hPredRes : DefEq env 0
        (.app (.const Ix.Kernel.natPredName []) (.app (.app (.const (.role .natSub) []) (.lit (.natVal y))) (.lit (.natVal x))))
        (.lit (.natVal (Nat.pred (y - x)))) :=
      .ofRed (.trans (.appArg hSubRed) (ik.bk.red_natPred_lit (y - x)))
    let Γ3 := fvarUpdate ΓNat2 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
      (.app (.app hBle.witness (.fvar 1 BaseKit.natT)) (.fvar 0 BaseKit.natT))) BaseKit.falseE)
    have hLhsO := ((OpenAt.ofClosed hsc ik.intSubNatNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl
        ik.forallNatInt_lbb0).app_nondep
        (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl ik.wInt_cl.2
    have hRhsO := (OpenAt.ofClosed hsc ik.intNegSuccAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc hPred rfl).app_nondep
          (((OpenAt.ofClosed hsc hSub rfl).app_nondep (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl rfl).app_nondep
            (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl rfl) .refl rfl)
        .refl ik.wInt_cl.2
    have hRhsCl := ik.intNegSuccAt.app_nondep (hPred.app_nondep ((hSub.app_nondep hy rfl).app_nondep hx rfl) rfl) ik.wInt_cl.2
    have hEq := applyEqn2Hyp1 ik.bk
      (eqnValid_of ik.shapes .intSubNatNat (by decide) (by decide) (k := 1) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
      rfl rfl rfl ik.bk.boolFalseAt rfl rfl hBleO hLhsO hRhsO
      (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1])
      (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                         fvarSubst_of_not_hasFvar hPred.wClosed.1, fvarSubst_of_not_hasFvar hSub.wClosed.1])
      hx hy
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBle.wClosed.1]
          exact .redL (.appFn (.appFn hBle.wRed)) hBleRes)
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1]
          exact .app (.app ik.intSubNatNatAt.defEq_witness .refl) .refl)
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                fvarSubst_of_not_hasFvar hPred.wClosed.1, fvarSubst_of_not_hasFvar hSub.wClosed.1]
          exact .app ik.intNegSuccAt.defEq_witness
            (.app hPred.defEq_witness (.app (.app hSub.defEq_witness .refl) .refl)))
      ((ik.intSubNatNatAt.app_nondep hx ik.forallNatInt_lbb0).app_nondep
        hy ik.wInt_cl.2)
      hRhsCl
    exact hRhsCl.defEq_trans hEq (.app .refl hPredRes)

private theorem defEq_intNeg (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) :
    DefEq env 0 (.app (.const (.role .intNeg) []) (intLitExpr x)) (intLitExpr (-x)) := by
  have hsc := ik.bk.storeClosed
  cases x with
  | ofNat n =>
    have hLhsO := (OpenAt.ofClosed hsc ik.intNegAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.intOfNatAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2)
        .refl ik.wInt_cl.2
    have hRhsO := (OpenAt.ofClosed hsc ik.intNegOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2
    have hRhsCl := ik.intNegOfNatAt.app_nondep (ik.bk.natLitAt n) ik.wInt_cl.2
    have hEq := applyEqn1 ik.bk
      (eqnValid_of ik.shapes .intNeg (by decide) (by decide) (k := 0) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) rfl rfl rfl rfl hLhsO hRhsO
      (ik.bk.natLitAt n) rfl rfl
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegAt.wClosed.1,
                fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
          exact .app ik.intNegAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegOfNatAt.wClosed.1]
          exact .app ik.intNegOfNatAt.defEq_witness .refl)
      (ik.intNegAt.app_nondep (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
      hRhsCl
    exact hRhsCl.defEq_trans hEq (ik.defEq_intNegOfNat n)
  | negSucc n =>
    have hLhsO := (OpenAt.ofClosed hsc ik.intNegAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.intNegSuccAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2)
        .refl ik.wInt_cl.2
    have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
          (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl rfl)
        .refl ik.wInt_cl.2
    have hRhsCl := ik.intOfNatAt.app_nondep (ik.bk.natSuccApp (ik.bk.natLitAt n)) ik.wInt_cl.2
    have hEq := applyEqn1 ik.bk
      (eqnValid_of ik.shapes .intNeg (by decide) (by decide) (k := 1) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) rfl rfl rfl rfl hLhsO hRhsO
      (ik.bk.natLitAt n) rfl rfl
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegAt.wClosed.1,
                fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
          exact .app ik.intNegAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
          exact .app ik.intOfNatAt.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl))
      (ik.intNegAt.app_nondep (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
      hRhsCl
    exact hRhsCl.defEq_trans hEq (.app .refl (ik.bk.defEq_natSucc_lit n))

private theorem defEq_intNatAbs (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) :
    DefEq env 0 (.app (.const (.role .intNatAbs) []) (intLitExpr x)) (.lit (.natVal x.natAbs)) := by
  have hsc := ik.bk.storeClosed
  cases x with
  | ofNat n =>
    have hLhsO := (OpenAt.ofClosed hsc ik.intNatAbsAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.intOfNatAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2)
        .refl rfl
    exact applyEqn1 ik.bk
      (eqnValid_of ik.shapes .intNatAbs (by decide) (by decide) (k := 0) rfl)
      (by decide) rfl rfl rfl ik.bk.natType .refl rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) rfl rfl rfl rfl hLhsO
      (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega))
      (ik.bk.natLitAt n) rfl rfl
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNatAbsAt.wClosed.1,
                fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
          exact .app ik.intNatAbsAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
      (by simp [fvarSubst]; exact .refl)
      (ik.intNatAbsAt.app_nondep (ik.intLitAt (.ofNat n)) rfl)
      (ik.bk.natLitAt n)
  | negSucc n =>
    have hLhsO := (OpenAt.ofClosed hsc ik.intNatAbsAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.intNegSuccAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2)
        .refl rfl
    have hRhsO := (OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
      (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl rfl
    have hRhsCl := ik.bk.natSuccApp (ik.bk.natLitAt n)
    have hEq := applyEqn1 ik.bk
      (eqnValid_of ik.shapes .intNatAbs (by decide) (by decide) (k := 1) rfl)
      (by decide) rfl rfl rfl ik.bk.natType .refl rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) rfl rfl rfl rfl hLhsO hRhsO
      (ik.bk.natLitAt n) rfl rfl
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNatAbsAt.wClosed.1,
                fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
          exact .app ik.intNatAbsAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
      (by simp [fvarSubst]
          exact .app ik.bk.natSuccAt.defEq_witness .refl)
      (ik.intNatAbsAt.app_nondep (ik.intLitAt (.negSucc n)) rfl)
      hRhsCl
    exact hRhsCl.defEq_trans hEq (ik.bk.defEq_natSucc_lit n)

private theorem defEq_intAdd (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Int) :
    DefEq env 0 (.app (.app (.const (.role .intAdd) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x + y)) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hAdd⟩⟩ := ik.bk.natBinNatAt (r := .natAdd) (by decide) (by decide) (by decide)
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intAddAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hAdd rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hAdd.app_nondep hm rfl).app_nondep hn rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intAdd (by decide) (by decide) (k := 0) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intAddAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intAddAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hAdd.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness (.app (.app hAdd.defEq_witness .refl) .refl))
        ((ik.intAddAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.app .refl (ik.bk.defEq_natOp (r := .natAdd) (by decide) (by simp [Ix.Kernel.natOpResult])))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intAddAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := ((OpenAt.ofClosed hsc ik.intSubNatNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl
          ik.forallNatInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := (ik.intSubNatNatAt.app_nondep hm ik.forallNatInt_lbb0).app_nondep
        (ik.bk.natSuccApp hn) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intAdd (by decide) (by decide) (k := 1) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intAddAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intAddAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1]
            exact .app (.app ik.intSubNatNatAt.defEq_witness .refl)
              (.app ik.bk.natSuccAt.defEq_witness .refl))
        ((ik.intAddAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.redL (.appArg (ik.bk.red_natSucc_lit n)) (ik.defEq_intSubNatNat m (n + 1)))
  | negSucc m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intAddAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := ((OpenAt.ofClosed hsc ik.intSubNatNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl
          ik.forallNatInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := (ik.intSubNatNatAt.app_nondep hn ik.forallNatInt_lbb0).app_nondep
        (ik.bk.natSuccApp hm) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intAdd (by decide) (by decide) (k := 2) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intAddAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intAddAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1]
            exact .app (.app ik.intSubNatNatAt.defEq_witness .refl)
              (.app ik.bk.natSuccAt.defEq_witness .refl))
        ((ik.intAddAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.redL (.appArg (ik.bk.red_natSucc_lit m)) (ik.defEq_intSubNatNat n (m + 1)))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intAddAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intNegSuccAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (((OpenAt.ofClosed hsc hAdd rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl)
          .refl ik.wInt_cl.2
      have hRhsCl := ik.intNegSuccAt.app_nondep (ik.bk.natSuccApp ((hAdd.app_nondep hm rfl).app_nondep hn rfl)) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intAdd (by decide) (by decide) (k := 3) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intAddAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intAddAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hAdd.wClosed.1]
            exact .app ik.intNegSuccAt.defEq_witness
              (.app ik.bk.natSuccAt.defEq_witness (.app (.app hAdd.defEq_witness .refl) .refl)))
        ((ik.intAddAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hAddRed := ik.bk.red_natOp (r := .natAdd) (a := m) (b := n)
        (res := .lit (.natVal (m + n))) (by decide) rfl
      exact hRhsCl.defEq_trans hEq (.app .refl (.ofRed (.trans (.appArg hAddRed) (ik.bk.red_natSucc_lit (m + n)))))

private theorem defEq_intSub (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Int) :
    DefEq env 0 (.app (.app (.const (.role .intSub) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x - y)) := by
  have hsc := ik.bk.storeClosed
  have hx := ik.intLitAt x; have hy := ik.intLitAt y
  have hLhsO := ((OpenAt.ofClosed hsc ik.intSubAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 wInt) (by omega)) .refl
      ik.forallIntInt_lbb0).app_nondep
      (OpenAt.fvar (d := 2) (idx := 1) (Γ := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 wInt) (by omega)) .refl ik.wInt_cl.2
  have hRhsO := ((OpenAt.ofClosed hsc ik.intAddAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 wInt) (by omega)) .refl
      ik.forallIntInt_lbb0).app_nondep
      ((OpenAt.ofClosed hsc ik.intNegAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (OpenAt.fvar (d := 2) (idx := 1) (Γ := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 wInt) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
  have hIntO := OpenType.liftClosed hsc (d := 0) (Γ := Γ₀) ik.intType (.ofRed ik.intRed) ⟨rfl, rfl⟩
  have hRhsCl := (ik.intAddAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
    (ik.intNegAt.app_nondep hy ik.wInt_cl.2) ik.wInt_cl.2
  have hEq := applyEqn2 ik.bk
    (eqnValid_of ik.shapes .intSub (by decide) (by decide) (k := 0) rfl)
    (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
    hIntO hIntO rfl rfl rfl rfl rfl rfl hLhsO hRhsO hx hy
    (by cases x <;> rfl)
    (by cases x <;> rfl)
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubAt.wClosed.1,
              fvarSubst_of_not_hasFvar hx.wClosed.1]
        exact .app (.app ik.intSubAt.defEq_witness hx.defEq_witness) hy.defEq_witness)
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intAddAt.wClosed.1,
              fvarSubst_of_not_hasFvar ik.intNegAt.wClosed.1,
              fvarSubst_of_not_hasFvar hx.wClosed.1]
        exact .app (.app ik.intAddAt.defEq_witness hx.defEq_witness)
          (.app ik.intNegAt.defEq_witness hy.defEq_witness))
    ((ik.intSubAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
      hy ik.wInt_cl.2)
    hRhsCl
  have hMidCl := (ik.intAddAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
    (ik.intLitAt (-y)) ik.wInt_cl.2
  exact hRhsCl.defEq_trans hEq (hMidCl.defEq_trans (.app .refl (ik.defEq_intNeg y)) (ik.defEq_intAdd x (-y)))

private theorem defEq_intMul (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Int) :
    DefEq env 0 (.app (.app (.const (.role .intMul) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x * y)) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hMul⟩⟩ := ik.bk.natBinNatAt (r := .natMul) (by decide) (by decide) (by decide)
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intMulAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hMul rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hMul.app_nondep hm rfl).app_nondep hn rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intMul (by decide) (by decide) (k := 0) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intMulAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intMulAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hMul.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness (.app (.app hMul.defEq_witness .refl) .refl))
        ((ik.intMulAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.app .refl (ik.bk.defEq_natOp (r := .natMul) (by decide) (by simp [Ix.Kernel.natOpResult])))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intMulAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intNegOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hMul rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
            ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intNegOfNatAt.app_nondep ((hMul.app_nondep hm rfl).app_nondep (ik.bk.natSuccApp hn) rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intMul (by decide) (by decide) (k := 1) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intMulAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intMulAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hMul.wClosed.1]
            exact .app ik.intNegOfNatAt.defEq_witness
              (.app (.app hMul.defEq_witness .refl) (.app ik.bk.natSuccAt.defEq_witness .refl)))
        ((ik.intMulAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hMulRed : Red env 0
          (.app (.app (.const (.role .natMul) []) (.lit (.natVal m))) (.app BaseKit.natSuccE (.lit (.natVal n))))
          (.lit (.natVal (m * (n + 1)))) :=
        .trans (.appArg (ik.bk.red_natSucc_lit n))
          (ik.bk.red_natOp (r := .natMul) (by decide) (by simp [Ix.Kernel.natOpResult]))
      exact hRhsCl.defEq_trans hEq (.redL (.appArg hMulRed) (ik.defEq_intNegOfNat (m * (n + 1))))
  | negSucc m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intMulAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intNegOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hMul rfl).app_nondep
            ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intNegOfNatAt.app_nondep ((hMul.app_nondep (ik.bk.natSuccApp hm) rfl).app_nondep hn rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intMul (by decide) (by decide) (k := 2) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intMulAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intMulAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hMul.wClosed.1]
            exact .app ik.intNegOfNatAt.defEq_witness
              (.app (.app hMul.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl)) .refl))
        ((ik.intMulAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      have hMulRed : Red env 0
          (.app (.app (.const (.role .natMul) []) (.app BaseKit.natSuccE (.lit (.natVal m)))) (.lit (.natVal n)))
          (.lit (.natVal ((m + 1) * n))) :=
        .trans (.appFn (.appArg (ik.bk.red_natSucc_lit m)))
          (ik.bk.red_natOp (r := .natMul) (by decide) (by simp [Ix.Kernel.natOpResult]))
      exact hRhsCl.defEq_trans hEq (.redL (.appArg hMulRed) (ik.defEq_intNegOfNat ((m + 1) * n)))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intMulAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hMul rfl).app_nondep
            ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl).app_nondep
            ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hMul.app_nondep (ik.bk.natSuccApp hm) rfl).app_nondep (ik.bk.natSuccApp hn) rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intMul (by decide) (by decide) (k := 3) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intMulAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intMulAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hMul.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness
              (.app (.app hMul.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl))
                (.app ik.bk.natSuccAt.defEq_witness .refl)))
        ((ik.intMulAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hMulRed : Red env 0
          (.app (.app (.const (.role .natMul) []) (.app BaseKit.natSuccE (.lit (.natVal m))))
            (.app BaseKit.natSuccE (.lit (.natVal n))))
          (.lit (.natVal ((m + 1) * (n + 1)))) :=
        .trans (.appFn (.appArg (ik.bk.red_natSucc_lit m)))
          (.trans (.appArg (ik.bk.red_natSucc_lit n))
            (ik.bk.red_natOp (r := .natMul) (by decide) (by simp [Ix.Kernel.natOpResult])))
      exact hRhsCl.defEq_trans hEq (.app .refl (.ofRed hMulRed))

private theorem defEq_intEdiv (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Int) :
    DefEq env 0 (.app (.app (.const (.role .intEdiv) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x.ediv y)) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hDiv⟩⟩ := ik.bk.natBinNatAt (r := .natDiv) (by decide) (by decide) (by decide)
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEdivAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hDiv rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hDiv.app_nondep hm rfl).app_nondep hn rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEdiv (by decide) (by decide) (k := 0) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intEdivAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hDiv.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness (.app (.app hDiv.defEq_witness .refl) .refl))
        ((ik.intEdivAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.app .refl (ik.bk.defEq_natOp (r := .natDiv) (by decide) (by simp [Ix.Kernel.natOpResult])))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEdivAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intNegAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (((OpenAt.ofClosed hsc hDiv rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
                ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
                  (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl ik.wInt_cl.2)
          .refl ik.wInt_cl.2
      have hRhsCl := ik.intNegAt.app_nondep (ik.intOfNatAt.app_nondep
        ((hDiv.app_nondep hm rfl).app_nondep (ik.bk.natSuccApp hn) rfl) ik.wInt_cl.2) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEdiv (by decide) (by decide) (k := 1) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intEdivAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hDiv.wClosed.1]
            exact .app ik.intNegAt.defEq_witness (.app ik.intOfNatAt.defEq_witness
              (.app (.app hDiv.defEq_witness .refl) (.app ik.bk.natSuccAt.defEq_witness .refl))))
        ((ik.intEdivAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hDivRed : Red env 0
          (.app (.app (.const (.role .natDiv) []) (.lit (.natVal m))) (.app BaseKit.natSuccE (.lit (.natVal n))))
          (.lit (.natVal (m / (n + 1)))) :=
        .trans (.appArg (ik.bk.red_natSucc_lit n))
          (ik.bk.red_natOp (r := .natDiv) (by decide) (by simp [Ix.Kernel.natOpResult]))
      exact hRhsCl.defEq_trans hEq (.redL (.appArg (.appArg hDivRed)) (ik.defEq_intNeg (.ofNat (m / (n + 1)))))
  | negSucc m =>
    cases y with
    | ofNat n =>
      cases n with
      | zero =>
        let hm := ik.bk.natLitAt m
        have hLhsO := ((OpenAt.ofClosed hsc ik.intEdivAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            ((OpenAt.ofClosed hsc ik.intNegSuccAt
              (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
                (OpenAt.fvar (d := 1) (idx := 0) (Γ := ΓNat1) (by omega)) .refl ik.wInt_cl.2) .refl
            ik.forallIntInt_lbb0).app_nondep
            ((OpenAt.ofClosed hsc ik.intOfNatAt
              (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
                (OpenAt.ofClosed hsc ik.bk.natZeroAt rfl) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
        have hRhsO := (OpenAt.ofClosed hsc (d := 1) (Γ := ΓNat1) ik.intOfNatAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (OpenAt.ofClosed hsc ik.bk.natZeroAt rfl) .refl ik.wInt_cl.2
        have hLhsCl := (ik.intEdivAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intOfNatAt.app_nondep ik.bk.natZeroAt ik.wInt_cl.2) ik.wInt_cl.2
        have hRhsCl := ik.intOfNatAt.app_nondep ik.bk.natZeroAt ik.wInt_cl.2
        have hEq := applyEqn1 ik.bk
          (eqnValid_of ik.shapes .intEdiv (by decide) (by decide) (k := 2) rfl)
          (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
          (OpenType.ofClosed hsc ik.bk.natType) rfl rfl rfl rfl hLhsO hRhsO hm rfl rfl
          (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1,
                    fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                    fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
              exact .app (.app ik.intEdivAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
                (.app ik.intOfNatAt.defEq_witness ik.bk.natZeroAt.defEq_witness))
          (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
              exact .app ik.intOfNatAt.defEq_witness ik.bk.natZeroAt.defEq_witness)
          hLhsCl hRhsCl
        exact hLhsCl.defEq_trans (.app .refl (.app .refl ik.bk.defEq_natZero_lit.symm))
          (hRhsCl.defEq_trans hEq (.app .refl ik.bk.defEq_natZero_lit))
      | succ k =>
        let hm := ik.bk.natLitAt m; let hk := ik.bk.natLitAt k
        have hLhsO := ((OpenAt.ofClosed hsc ik.intEdivAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            ((OpenAt.ofClosed hsc ik.intNegSuccAt
              (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
                (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
            ik.forallIntInt_lbb0).app_nondep
            ((OpenAt.ofClosed hsc ik.intOfNatAt
              (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
                ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
                  (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
        have hRhsO := (OpenAt.ofClosed hsc ik.intNegSuccAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (((OpenAt.ofClosed hsc hDiv rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
              ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
                (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
        have hLhsCl := (ik.intEdivAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intOfNatAt.app_nondep (ik.bk.natSuccApp hk) ik.wInt_cl.2) ik.wInt_cl.2
        have hRhsCl := ik.intNegSuccAt.app_nondep ((hDiv.app_nondep hm rfl).app_nondep (ik.bk.natSuccApp hk) rfl) ik.wInt_cl.2
        have hEq := applyEqn2 ik.bk
          (eqnValid_of ik.shapes .intEdiv (by decide) (by decide) (k := 3) rfl)
          (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
          (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
          rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hk rfl rfl
          (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1,
                    fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                    fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
              exact .app (.app ik.intEdivAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
                (.app ik.intOfNatAt.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl)))
          (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                    fvarSubst_of_not_hasFvar hDiv.wClosed.1]
              exact .app ik.intNegSuccAt.defEq_witness
                (.app (.app hDiv.defEq_witness .refl) (.app ik.bk.natSuccAt.defEq_witness .refl)))
          hLhsCl hRhsCl
        have hDivRed : Red env 0
            (.app (.app (.const (.role .natDiv) []) (.lit (.natVal m))) (.app BaseKit.natSuccE (.lit (.natVal k))))
            (.lit (.natVal (m / (k + 1)))) :=
          .trans (.appArg (ik.bk.red_natSucc_lit k))
            (ik.bk.red_natOp (r := .natDiv) (by decide) (by simp [Ix.Kernel.natOpResult]))
        exact hLhsCl.defEq_trans (.app .refl (.app .refl (ik.bk.defEq_natSucc_lit k).symm))
          (hRhsCl.defEq_trans hEq (.app .refl (.ofRed hDivRed)))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEdivAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (((OpenAt.ofClosed hsc hDiv rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
              ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
                (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep (ik.bk.natSuccApp ((hDiv.app_nondep hm rfl).app_nondep (ik.bk.natSuccApp hn) rfl)) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEdiv (by decide) (by decide) (k := 4) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intEdivAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1, fvarSubst_of_not_hasFvar hDiv.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness (.app ik.bk.natSuccAt.defEq_witness
              (.app (.app hDiv.defEq_witness .refl) (.app ik.bk.natSuccAt.defEq_witness .refl))))
        ((ik.intEdivAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hDivRed : Red env 0
          (.app (.app (.const (.role .natDiv) []) (.lit (.natVal m))) (.app BaseKit.natSuccE (.lit (.natVal n))))
          (.lit (.natVal (m / (n + 1)))) :=
        .trans (.appArg (ik.bk.red_natSucc_lit n))
          (ik.bk.red_natOp (r := .natDiv) (by decide) (by simp [Ix.Kernel.natOpResult]))
      exact hRhsCl.defEq_trans hEq (.app .refl (.ofRed (.trans (.appArg hDivRed) (ik.bk.red_natSucc_lit (m / (n + 1))))))

private theorem defEq_intEmod (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Int) :
    DefEq env 0 (.app (.app (.const (.role .intEmod) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x.emod y)) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hMod⟩⟩ := ik.bk.natBinNatAt (r := .natMod) (by decide) (by decide) (by decide)
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEmodAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hMod rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hMod.app_nondep hm rfl).app_nondep hn rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEmod (by decide) (by decide) (k := 0) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEmodAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intEmodAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hMod.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness (.app (.app hMod.defEq_witness .refl) .refl))
        ((ik.intEmodAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.app .refl (ik.bk.defEq_natOp (r := .natMod) (by decide) (by simp [Ix.Kernel.natOpResult])))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEmodAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hMod rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
            ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hMod.app_nondep hm rfl).app_nondep (ik.bk.natSuccApp hn) rfl) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEmod (by decide) (by decide) (k := 1) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEmodAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intEmodAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hMod.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness
              (.app (.app hMod.defEq_witness .refl) (.app ik.bk.natSuccAt.defEq_witness .refl)))
        ((ik.intEmodAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hModRed : Red env 0
          (.app (.app (.const (.role .natMod) []) (.lit (.natVal m))) (.app BaseKit.natSuccE (.lit (.natVal n))))
          (.lit (.natVal (m % (n + 1)))) :=
        .trans (.appArg (ik.bk.red_natSucc_lit n))
          (ik.bk.red_natOp (r := .natMod) (by decide) (by simp [Ix.Kernel.natOpResult]))
      exact hRhsCl.defEq_trans hEq (.app .refl (.ofRed hModRed))
  | negSucc m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEmodAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := ((OpenAt.ofClosed hsc ik.intSubNatNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl
          ik.forallNatInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (((OpenAt.ofClosed hsc hMod rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := (ik.intSubNatNatAt.app_nondep hn ik.forallNatInt_lbb0).app_nondep
        (ik.bk.natSuccApp ((hMod.app_nondep hm rfl).app_nondep hn rfl)) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEmod (by decide) (by decide) (k := 2) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEmodAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
            exact .app (.app ik.intEmodAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intOfNatAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1, fvarSubst_of_not_hasFvar hMod.wClosed.1]
            exact .app (.app ik.intSubNatNatAt.defEq_witness .refl)
              (.app ik.bk.natSuccAt.defEq_witness (.app (.app hMod.defEq_witness .refl) .refl)))
        ((ik.intEmodAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.ofNat n)) ik.wInt_cl.2)
        hRhsCl
      have hModRed := ik.bk.red_natOp (r := .natMod) (a := m) (b := n)
        (res := .lit (.natVal (m % n))) (by decide) rfl
      exact hRhsCl.defEq_trans hEq
        (.redL (.appArg (.trans (.appArg hModRed) (ik.bk.red_natSucc_lit (m % n))))
          (ik.defEq_intSubNatNat n (m % n + 1)))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hLhsO := ((OpenAt.ofClosed hsc ik.intEmodAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallIntInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsO := ((OpenAt.ofClosed hsc ik.intSubNatNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl
          ik.forallNatInt_lbb0).app_nondep
          ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
            (((OpenAt.ofClosed hsc hMod rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
              ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
                (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl rfl) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := (ik.intSubNatNatAt.app_nondep (ik.bk.natSuccApp hn) ik.forallNatInt_lbb0).app_nondep
        (ik.bk.natSuccApp ((hMod.app_nondep hm rfl).app_nondep (ik.bk.natSuccApp hn) rfl)) ik.wInt_cl.2
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intEmod (by decide) (by decide) (k := 3) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intEmodAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intEmodAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
              (.app ik.intNegSuccAt.defEq_witness .refl))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intSubNatNatAt.wClosed.1, fvarSubst_of_not_hasFvar hMod.wClosed.1]
            exact .app (.app ik.intSubNatNatAt.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl))
              (.app ik.bk.natSuccAt.defEq_witness
                (.app (.app hMod.defEq_witness .refl) (.app ik.bk.natSuccAt.defEq_witness .refl))))
        ((ik.intEmodAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt (.negSucc n)) ik.wInt_cl.2)
        hRhsCl
      have hModRed : Red env 0
          (.app (.app (.const (.role .natMod) []) (.lit (.natVal m))) (.app BaseKit.natSuccE (.lit (.natVal n))))
          (.lit (.natVal (m % (n + 1)))) :=
        .trans (.appArg (ik.bk.red_natSucc_lit n))
          (ik.bk.red_natOp (r := .natMod) (by decide) (by simp [Ix.Kernel.natOpResult]))
      exact hRhsCl.defEq_trans hEq
        (.redL (.trans (.appFn (.appArg (ik.bk.red_natSucc_lit n)))
          (.appArg (.trans (.appArg hModRed) (ik.bk.red_natSucc_lit (m % (n + 1))))))
          (ik.defEq_intSubNatNat (n + 1) (m % (n + 1) + 1)))

private theorem defEq_intPow (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) (n : Nat) (hn : n ≤ 2 ^ 24) :
    DefEq env 0 (.app (.app (.const (.role .intPow) []) (intLitExpr x)) (.lit (.natVal n)))
      (intLitExpr (x ^ n)) := by
  have hsc := ik.bk.storeClosed
  have hn16 : ¬ (n > 16777216) := by omega
  obtain ⟨_, _, ⟨hPow⟩⟩ := ik.bk.natBinNatAt (r := .natPow) (by decide) (by decide) (by decide)
  obtain ⟨_, _, ⟨hMod⟩⟩ := ik.bk.natBinNatAt (r := .natMod) (by decide) (by decide) (by decide)
  obtain ⟨_, _, ⟨hBeq⟩⟩ := ik.bk.natBinBoolAt (r := .natBeq) (by decide) (Or.inl rfl)
  cases x with
  | ofNat m =>
    let hm := ik.bk.natLitAt m; let hnl := ik.bk.natLitAt n
    have hLhsO := ((OpenAt.ofClosed hsc ik.intPowAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        ((OpenAt.ofClosed hsc ik.intOfNatAt
          (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
            (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2) .refl
        ik.forallNatInt_lbb0).app_nondep
        (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2
    have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (((OpenAt.ofClosed hsc hPow rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
          (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl) .refl ik.wInt_cl.2
    have hRhsCl := ik.intOfNatAt.app_nondep ((hPow.app_nondep hm rfl).app_nondep hnl rfl) ik.wInt_cl.2
    have hEq := applyEqn2 ik.bk
      (eqnValid_of ik.shapes .intPow (by decide) (by decide) (k := 0) rfl)
      (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
      (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
      rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hnl rfl rfl
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intPowAt.wClosed.1,
                fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1]
          exact .app (.app ik.intPowAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl)) .refl)
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                fvarSubst_of_not_hasFvar hPow.wClosed.1]
          exact .app ik.intOfNatAt.defEq_witness (.app (.app hPow.defEq_witness .refl) .refl))
      ((ik.intPowAt.app_nondep (ik.intLitAt (.ofNat m)) ik.forallNatInt_lbb0).app_nondep
        hnl ik.wInt_cl.2)
      hRhsCl
    exact hRhsCl.defEq_trans hEq (.app .refl (ik.bk.defEq_natOp (r := .natPow) (by decide)
      (by simp [Ix.Kernel.natOpResult, hn16])))
  | negSucc m =>
    let hm := ik.bk.natLitAt m; let hnl := ik.bk.natLitAt n
    have hGuardO : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 BaseKit.natT) 1 BaseKit.natT)
        (.app (.app (.const (.role .natBeq) [])
          (.app (.app (.const (.role .natMod) []) (.fvar 1 BaseKit.natT))
            (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE))))
          BaseKit.natZeroE)
        (.app (.app hBeq.witness
          (.app (.app hMod.witness (.fvar 1 BaseKit.natT)) ik.specTwoAt.witness))
          ik.bk.natZeroAt.witness) BaseKit.boolT :=
      ((OpenAt.ofClosed hsc hBeq rfl).app_nondep
        (((OpenAt.ofClosed hsc hMod rfl).app_nondep (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
          (OpenAt.ofClosed hsc ik.specTwoAt rfl) .refl rfl) .refl rfl).app_nondep
        (OpenAt.ofClosed hsc ik.bk.natZeroAt rfl) .refl rfl
    have hMod2Red : Red env 0
        (.app (.app (.const (.role .natMod) []) (.lit (.natVal n)))
          (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))
        (.lit (.natVal (n % 2))) :=
      .trans (.appArg ik.red_two)
        (ik.bk.red_natOp (r := .natMod) (by decide) (by simp [Ix.Kernel.natOpResult]))
    have hPowRed : Red env 0
        (.app (.app (.const (.role .natPow) []) (.app BaseKit.natSuccE (.lit (.natVal m)))) (.lit (.natVal n)))
        (.lit (.natVal ((m + 1) ^ n))) :=
      .trans (.appFn (.appArg (ik.bk.red_natSucc_lit m)))
        (ik.bk.red_natOp (r := .natPow) (by decide) (by simp [Ix.Kernel.natOpResult, hn16]))
    have hPowDef : (Int.negSucc m) ^ n =
        if n % 2 = 0 then Int.ofNat ((m + 1) ^ n) else -(Int.ofNat ((m + 1) ^ n)) := rfl
    rw [hPowDef]
    by_cases hev : n % 2 = 0
    · simp only [hev, ↓reduceIte]
      have hGuardRed : Red env 0
          (.app (.app (.const (.role .natBeq) [])
            (.app (.app (.const (.role .natMod) []) (.lit (.natVal n)))
              (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE))))
            BaseKit.natZeroE) BaseKit.trueE :=
        .trans (.appFn (.appArg hMod2Red))
          (.trans (.appArg ik.bk.red_natZero_lit)
            (ik.bk.red_natOp (r := .natBeq) (by decide) (by simp [Ix.Kernel.natOpResult, hev])))
      let Γ3 := fvarUpdate ΓNat2 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
        (.app (.app hBeq.witness (.app (.app hMod.witness (.fvar 1 BaseKit.natT)) ik.specTwoAt.witness))
          ik.bk.natZeroAt.witness)) BaseKit.trueE)
      have hLhsO := ((OpenAt.ofClosed hsc ik.intPowAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallNatInt_lbb0).app_nondep
          (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intOfNatAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          (((OpenAt.ofClosed hsc hPow rfl).app_nondep
            ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
              (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl rfl) .refl rfl).app_nondep
            (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl rfl) .refl ik.wInt_cl.2
      have hRhsCl := ik.intOfNatAt.app_nondep ((hPow.app_nondep (ik.bk.natSuccApp hm) rfl).app_nondep hnl rfl) ik.wInt_cl.2
      have hEq := applyEqn2Hyp1 ik.bk
        (eqnValid_of ik.shapes .intPow (by decide) (by decide) (k := 1) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl ik.bk.boolTrueAt rfl rfl hGuardO hLhsO hRhsO
        (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intPowAt.wClosed.1,
                           fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1])
        (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                           fvarSubst_of_not_hasFvar hPow.wClosed.1])
        hm hnl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBeq.wClosed.1, fvarSubst_of_not_hasFvar hMod.wClosed.1]
            exact .redL (.trans (.appFn (.trans (.appFn hBeq.wRed)
              (.appArg (.trans (.appFn (.appFn hMod.wRed)) (.appArg ik.specTwoAt.wRed)))))
              (.appArg ik.bk.natZeroAt.wRed)) (.ofRed hGuardRed))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intPowAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intPowAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl)) .refl)
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hPow.wClosed.1]
            exact .app ik.intOfNatAt.defEq_witness
              (.app (.app hPow.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl)) .refl))
        ((ik.intPowAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallNatInt_lbb0).app_nondep
          hnl ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.app .refl (.ofRed hPowRed))
    · simp only [hev, ↓reduceIte]
      have hGuardRed : Red env 0
          (.app (.app (.const (.role .natBeq) [])
            (.app (.app (.const (.role .natMod) []) (.lit (.natVal n)))
              (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE))))
            BaseKit.natZeroE) BaseKit.falseE :=
        .trans (.appFn (.appArg hMod2Red))
          (.trans (.appArg ik.bk.red_natZero_lit)
            (ik.bk.red_natOp (r := .natBeq) (by decide) (by simp [Ix.Kernel.natOpResult, hev])))
      let Γ3 := fvarUpdate ΓNat2 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
        (.app (.app hBeq.witness (.app (.app hMod.witness (.fvar 1 BaseKit.natT)) ik.specTwoAt.witness))
          ik.bk.natZeroAt.witness)) BaseKit.falseE)
      have hLhsO := ((OpenAt.ofClosed hsc ik.intPowAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intNegSuccAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl ik.wInt_cl.2) .refl
          ik.forallNatInt_lbb0).app_nondep
          (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl ik.wInt_cl.2
      have hRhsO := (OpenAt.ofClosed hsc ik.intNegAt
        (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
          ((OpenAt.ofClosed hsc ik.intOfNatAt
            (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
              (((OpenAt.ofClosed hsc hPow rfl).app_nondep
                ((OpenAt.ofClosed hsc ik.bk.natSuccAt rfl).app_nondep
                  (OpenAt.fvar (d := 3) (idx := 0) (Γ := Γ3) (by omega)) .refl rfl) .refl rfl).app_nondep
                (OpenAt.fvar (d := 3) (idx := 1) (Γ := Γ3) (by omega)) .refl rfl) .refl ik.wInt_cl.2) .refl ik.wInt_cl.2
      have hRhsCl := ik.intNegAt.app_nondep (ik.intOfNatAt.app_nondep
        ((hPow.app_nondep (ik.bk.natSuccApp hm) rfl).app_nondep hnl rfl) ik.wInt_cl.2) ik.wInt_cl.2
      have hEq := applyEqn2Hyp1 ik.bk
        (eqnValid_of ik.shapes .intPow (by decide) (by decide) (k := 2) rfl)
        (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl ik.bk.boolFalseAt rfl rfl hGuardO hLhsO hRhsO
        (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intPowAt.wClosed.1,
                           fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1])
        (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegAt.wClosed.1,
                           fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                           fvarSubst_of_not_hasFvar hPow.wClosed.1])
        hm hnl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBeq.wClosed.1, fvarSubst_of_not_hasFvar hMod.wClosed.1]
            exact .redL (.trans (.appFn (.trans (.appFn hBeq.wRed)
              (.appArg (.trans (.appFn (.appFn hMod.wRed)) (.appArg ik.specTwoAt.wRed)))))
              (.appArg ik.bk.natZeroAt.wRed)) (.ofRed hGuardRed))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intPowAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1]
            exact .app (.app ik.intPowAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl)) .refl)
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intNegAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar hPow.wClosed.1]
            exact .app ik.intNegAt.defEq_witness (.app ik.intOfNatAt.defEq_witness
              (.app (.app hPow.defEq_witness (.app ik.bk.natSuccAt.defEq_witness .refl)) .refl)))
        ((ik.intPowAt.app_nondep (ik.intLitAt (.negSucc m)) ik.forallNatInt_lbb0).app_nondep
          hnl ik.wInt_cl.2)
        hRhsCl
      exact hRhsCl.defEq_trans hEq (.redL (.appArg (.appArg hPowRed)) (ik.defEq_intNeg (.ofNat ((m + 1) ^ n))))

/-! ### `Nat.decEq`, `Int.decLe`, `Int.decLt`, `Int.bmod`, and `Int.bdiv` -/

private def natDecEqApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {a b : KExpr} (ha : ClosedAt env a BaseKit.natT) (hb : ClosedAt env b BaseKit.natT) :
    ClosedAt env (.app (.app (.const (.role .natDecEq) []) a) b)
      (.app wDec (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
        ha.witness) hb.witness)) := by
  have h1 := ik.natDecEqAt.app_abs ha .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2])
  simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wDec_cl.1] at h1
  have h2 := h1.app_abs hb .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ha.wClosed.2])
  simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ha.wClosed.1] using h2

private def intDecLeApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {a b : KExpr} (ha : ClosedAt env a wInt) (hb : ClosedAt env b wInt) :
    ClosedAt env (.app (.app (.const (.role .intDecLe) []) a) b)
      (.app wDec (.app (.app wIntLe ha.witness) hb.witness)) := by
  have h1 := ik.intDecLeAt.app_abs ha .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wInt_cl.2,
      lbb_of_lbb0 ik.wDec_cl.2, lbb_of_lbb0 ik.wIntLe_cl.2])
  simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
    fvarSubst_of_not_hasFvar ik.wIntLe_cl.1] at h1
  have h2 := h1.app_abs hb .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2, ha.wClosed.2])
  simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wIntLe_cl.1,
    fvarSubst_of_not_hasFvar ha.wClosed.1] using h2

private def intDecLtApp (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {a b : KExpr} (ha : ClosedAt env a wInt) (hb : ClosedAt env b wInt) :
    ClosedAt env (.app (.app (.const (.role .intDecLt) []) a) b)
      (.app wDec (.app (.app wIntLe
        (.app (.app wIntAdd ha.witness) (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
        hb.witness)) := by
  have h1 := ik.intDecLtAt.app_abs ha .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wInt_cl.2,
      lbb_of_lbb0 ik.wDec_cl.2, lbb_of_lbb0 ik.wIntLe_cl.2,
      lbb_of_lbb0 ik.wIntAdd_cl.2, lbb_of_lbb0 ik.wIntOfNat_cl.2])
  simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
    fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
    fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1,
    fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1] at h1
  have h2 := h1.app_abs hb .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2, ik.wIntAdd_cl.2,
              ik.wIntOfNat_cl.2, ha.wClosed.2])
  simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wIntLe_cl.1,
    fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
    fvarSubst_of_not_hasFvar ha.wClosed.1] using h2

private theorem defEq_natDecEq_decide (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (m n : Nat) :
    DefEq env 0
      (.app (.app (.const (.role .decidableDecide) [])
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
          (.lit (.natVal m))) (.lit (.natVal n))))
        (.app (.app (.const (.role .natDecEq) []) (.lit (.natVal m))) (.lit (.natVal n))))
      (if m = n then BaseKit.trueE else BaseKit.falseE) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hBeq⟩⟩ := ik.bk.natBinBoolAt (r := .natBeq) (by decide) (Or.inl rfl)
  let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
  have hEq2 := OpenAt.eq ik.bk.eqStored (OpenType.ofClosed hsc ik.bk.natType)
    (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl
    (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl
  have hNd1 := (OpenAt.ofClosed hsc ik.natDecEqAt ik.natDecEqTy_nf).app_abs
    (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 ik.wDec_cl.2])
  simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
    fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hNd1
  have hNd2 := hNd1.app_abs (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2])
  simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hNd2
  have hDec1 := (OpenAt.ofClosed hsc ik.decideAt ik.decideTy_nf).app_abs hEq2 .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wDec_cl.2])
  simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hDec1
  have hLhsO := hDec1.app_abs hNd2 .refl rfl
  simp [fvarSubst] at hLhsO
  have hRhsO := ((OpenAt.ofClosed hsc hBeq rfl).app_nondep
    (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
    (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl
  let hPropEq : ClosedAt env
      (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
        (.lit (.natVal m))) (.lit (.natVal n))) (.sort .zero) :=
    let h := closedType_eq ik.bk.eqStored ik.bk.natType hm.wInfer hm.wClosed hn.wInfer hn.wClosed
    .ofInfer h.closed h.infer
  have hRhsCl := (hBeq.app_nondep hm rfl).app_nondep hn rfl
  have hEq := applyEqn2 ik.bk
    (eqnValid_of ik.shapes .natDecEq (by decide) (by decide) (k := 0) rfl)
    (by decide) rfl rfl rfl ik.bk.boolType .refl rfl rfl
    (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
    rfl rfl rfl rfl rfl rfl hLhsO hRhsO hm hn rfl rfl
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.decideAt.wClosed.1,
              fvarSubst_of_not_hasFvar ik.natDecEqAt.wClosed.1]
        exact .app (.app ik.decideAt.defEq_witness .refl)
          (.app (.app ik.natDecEqAt.defEq_witness .refl) .refl))
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBeq.wClosed.1]
        exact .app (.app hBeq.defEq_witness .refl) .refl)
    (ik.decideApp hPropEq (ik.natDecEqApp hm hn))
    hRhsCl
  exact hRhsCl.defEq_trans hEq (ik.bk.defEq_natOp (r := .natBeq) (by decide) (by
    by_cases hmn : m = n <;> simp [Ix.Kernel.natOpResult, hmn]))

private theorem defEq_intDecLe_decide (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x y : Int) :
    DefEq env 0
      (.app (.app (.const (.role .decidableDecide) [])
        (.app (.app (.const (.role .intLe) []) (intLitExpr x)) (intLitExpr y)))
        (.app (.app (.const (.role .intDecLe) []) (intLitExpr x)) (intLitExpr y)))
      (if x ≤ y then BaseKit.trueE else BaseKit.falseE) := by
  have hsc := ik.bk.storeClosed
  obtain ⟨_, _, ⟨hBle⟩⟩ := ik.bk.natBinBoolAt (r := .natBle) (by decide) (Or.inr rfl)
  -- Helper building `OpenAt` for `decide (Int.le (c0 x) (c1 y)) (Int.decLe (c0 x) (c1 y))` at depth 2
  have openDecLe : ∀ {e0 e1 : KExpr} (c0 : ClosedAt env e0 (.forallE BaseKit.natT wInt { pw := .never }))
      (c1 : ClosedAt env e1 (.forallE BaseKit.natT wInt { pw := .never })),
      OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 BaseKit.natT) 1 BaseKit.natT)
        (.app (.app (.const (.role .decidableDecide) [])
          (.app (.app (.const (.role .intLe) []) (.app e0 (.fvar 0 BaseKit.natT)))
            (.app e1 (.fvar 1 BaseKit.natT))))
          (.app (.app (.const (.role .intDecLe) []) (.app e0 (.fvar 0 BaseKit.natT)))
            (.app e1 (.fvar 1 BaseKit.natT))))
        (.app (.app ik.decideAt.witness
          (.app (.app wIntLe (.app c0.witness (.fvar 0 BaseKit.natT)))
            (.app c1.witness (.fvar 1 BaseKit.natT))))
          (.app (.app ik.intDecLeAt.witness (.app c0.witness (.fvar 0 BaseKit.natT)))
            (.app c1.witness (.fvar 1 BaseKit.natT))))
        BaseKit.boolT := by
    intro e0 e1 c0 c1
    have ha0 := (OpenAt.ofClosed hsc c0 (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2
    have ha1 := (OpenAt.ofClosed hsc c1 (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl ik.wInt_cl.2
    simp [ΓNat2, ΓNat1, fvarUpdate] at ha0 ha1
    have hLeO := ((OpenAt.ofClosed hsc ik.intLeAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep ha0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep ha1 .refl rfl
    rw [ik.intLeW] at hLeO
    have hDl1 := (OpenAt.ofClosed hsc ik.intDecLeAt ik.intDecLeTy_nf).app_abs
      ha0 .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wInt_cl.2,
        lbb_of_lbb0 ik.wDec_cl.2, lbb_of_lbb0 ik.wIntLe_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_gen (v := .app c0.witness (.fvar 0 BaseKit.natT))
      (by decide : (0 : Nat) ≠ 1)
      (fun k => by simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self c0.witness c0.wClosed.1]),
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntLe_cl.1] at hDl1
    have hDl2 := hDl1.app_abs ha1 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2, c0.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar c0.wClosed.1] at hDl2
    have hDec1 := (OpenAt.ofClosed hsc ik.decideAt ik.decideTy_nf).app_abs hLeO .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wDec_cl.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1] at hDec1
    have hDec2 := hDec1.app_abs hDl2 .refl rfl
    simpa [fvarSubst] using hDec2
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hxm := ik.intLitAt (.ofNat m); have hyn := ik.intLitAt (.ofNat n)
      let hProp := (ik.intLeAt.app_nondep hxm (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hyn rfl
      have hLhsCl : ClosedAt env
          (.app (.app (.const (.role .decidableDecide) [])
            (.app (.app (.const (.role .intLe) []) (intLitExpr (.ofNat m))) (intLitExpr (.ofNat n))))
            (.app (.app (.const (.role .intDecLe) []) (intLitExpr (.ofNat m))) (intLitExpr (.ofNat n))))
          BaseKit.boolT :=
        ik.decideApp hProp (by simpa [hProp, ik.intLeW] using ik.intDecLeApp hxm hyn)
      have hRhsO := ((OpenAt.ofClosed hsc hBle rfl).app_nondep
        (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
        (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl
      have hRhsCl := (hBle.app_nondep hm rfl).app_nondep hn rfl
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intDecLe (by decide) (by decide) (k := 0) rfl)
        (by decide) rfl rfl rfl ik.bk.boolType .refl rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl (openDecLe ik.intOfNatAt ik.intOfNatAt) hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.decideAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1]
            exact .app (.app ik.decideAt.defEq_witness
              (.app (.app ik.wIntLe_defEq (.app ik.intOfNatAt.defEq_witness .refl))
                (.app ik.intOfNatAt.defEq_witness .refl)))
              (.app (.app ik.intDecLeAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
                (.app ik.intOfNatAt.defEq_witness .refl)))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBle.wClosed.1]
            exact .app (.app hBle.defEq_witness .refl) .refl)
        hLhsCl hRhsCl
      exact hRhsCl.defEq_trans hEq (ik.bk.defEq_natOp (r := .natBle) (by decide) (by
        by_cases h : m ≤ n <;> simp [Ix.Kernel.natOpResult, h]))
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hxm := ik.intLitAt (.ofNat m); have hyn := ik.intLitAt (.negSucc n)
      let hProp := (ik.intLeAt.app_nondep hxm (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hyn rfl
      have hLhsCl : ClosedAt env
          (.app (.app (.const (.role .decidableDecide) [])
            (.app (.app (.const (.role .intLe) []) (intLitExpr (.ofNat m))) (intLitExpr (.negSucc n))))
            (.app (.app (.const (.role .intDecLe) []) (intLitExpr (.ofNat m))) (intLitExpr (.negSucc n))))
          BaseKit.boolT :=
        ik.decideApp hProp (by simpa [hProp, ik.intLeW] using ik.intDecLeApp hxm hyn)
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intDecLe (by decide) (by decide) (k := 1) rfl)
        (by decide) rfl rfl rfl ik.bk.boolType .refl rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl (openDecLe ik.intOfNatAt ik.intNegSuccAt)
        (OpenAt.ofClosed hsc ik.bk.boolFalseAt rfl) hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.decideAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1]
            exact .app (.app ik.decideAt.defEq_witness
              (.app (.app ik.wIntLe_defEq (.app ik.intOfNatAt.defEq_witness .refl))
                (.app ik.intNegSuccAt.defEq_witness .refl)))
              (.app (.app ik.intDecLeAt.defEq_witness (.app ik.intOfNatAt.defEq_witness .refl))
                (.app ik.intNegSuccAt.defEq_witness .refl)))
        (by simp [fvarSubst]
            exact ik.bk.boolFalseAt.defEq_witness)
        hLhsCl ik.bk.boolFalseAt
      have hNotLe : ¬ (Int.ofNat m ≤ Int.negSucc n) := by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      simp only [hNotLe, ↓reduceIte]; exact hEq
  | negSucc m =>
    cases y with
    | ofNat n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hxm := ik.intLitAt (.negSucc m); have hyn := ik.intLitAt (.ofNat n)
      let hProp := (ik.intLeAt.app_nondep hxm (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hyn rfl
      have hLhsCl : ClosedAt env
          (.app (.app (.const (.role .decidableDecide) [])
            (.app (.app (.const (.role .intLe) []) (intLitExpr (.negSucc m))) (intLitExpr (.ofNat n))))
            (.app (.app (.const (.role .intDecLe) []) (intLitExpr (.negSucc m))) (intLitExpr (.ofNat n))))
          BaseKit.boolT :=
        ik.decideApp hProp (by simpa [hProp, ik.intLeW] using ik.intDecLeApp hxm hyn)
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intDecLe (by decide) (by decide) (k := 2) rfl)
        (by decide) rfl rfl rfl ik.bk.boolType .refl rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl (openDecLe ik.intNegSuccAt ik.intOfNatAt)
        (OpenAt.ofClosed hsc ik.bk.boolTrueAt rfl) hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.decideAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intOfNatAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1]
            exact .app (.app ik.decideAt.defEq_witness
              (.app (.app ik.wIntLe_defEq (.app ik.intNegSuccAt.defEq_witness .refl))
                (.app ik.intOfNatAt.defEq_witness .refl)))
              (.app (.app ik.intDecLeAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
                (.app ik.intOfNatAt.defEq_witness .refl)))
        (by simp [fvarSubst]
            exact ik.bk.boolTrueAt.defEq_witness)
        hLhsCl ik.bk.boolTrueAt
      have hLe : Int.negSucc m ≤ Int.ofNat n := by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      simp only [hLe, ↓reduceIte]; exact hEq
    | negSucc n =>
      let hm := ik.bk.natLitAt m; let hn := ik.bk.natLitAt n
      have hxm := ik.intLitAt (.negSucc m); have hyn := ik.intLitAt (.negSucc n)
      let hProp := (ik.intLeAt.app_nondep hxm (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hyn rfl
      have hLhsCl : ClosedAt env
          (.app (.app (.const (.role .decidableDecide) [])
            (.app (.app (.const (.role .intLe) []) (intLitExpr (.negSucc m))) (intLitExpr (.negSucc n))))
            (.app (.app (.const (.role .intDecLe) []) (intLitExpr (.negSucc m))) (intLitExpr (.negSucc n))))
          BaseKit.boolT :=
        ik.decideApp hProp (by simpa [hProp, ik.intLeW] using ik.intDecLeApp hxm hyn)
      have hRhsO := ((OpenAt.ofClosed hsc hBle rfl).app_nondep
        (OpenAt.fvar (d := 2) (idx := 1) (Γ := ΓNat2) (by omega)) .refl rfl).app_nondep
        (OpenAt.fvar (d := 2) (idx := 0) (Γ := ΓNat2) (by omega)) .refl rfl
      have hRhsCl := (hBle.app_nondep hn rfl).app_nondep hm rfl
      have hEq := applyEqn2 ik.bk
        (eqnValid_of ik.shapes .intDecLe (by decide) (by decide) (k := 3) rfl)
        (by decide) rfl rfl rfl ik.bk.boolType .refl rfl rfl
        (OpenType.ofClosed hsc ik.bk.natType) (OpenType.ofClosed hsc ik.bk.natType)
        rfl rfl rfl rfl rfl rfl (openDecLe ik.intNegSuccAt ik.intNegSuccAt) hRhsO hm hn rfl rfl
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.decideAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.intNegSuccAt.wClosed.1,
                  fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1]
            exact .app (.app ik.decideAt.defEq_witness
              (.app (.app ik.wIntLe_defEq (.app ik.intNegSuccAt.defEq_witness .refl))
                (.app ik.intNegSuccAt.defEq_witness .refl)))
              (.app (.app ik.intDecLeAt.defEq_witness (.app ik.intNegSuccAt.defEq_witness .refl))
                (.app ik.intNegSuccAt.defEq_witness .refl)))
        (by simp [fvarSubst, fvarSubst_of_not_hasFvar hBle.wClosed.1]
            exact .app (.app hBle.defEq_witness .refl) .refl)
        hLhsCl hRhsCl
      have hleIff : (Int.negSucc m ≤ Int.negSucc n) ↔ (n ≤ m) := by simp [Int.negSucc_eq]; omega
      exact hRhsCl.defEq_trans hEq (ik.bk.defEq_natOp (r := .natBle) (by decide) (by
        by_cases h : n ≤ m <;> simp [Ix.Kernel.natOpResult, h, hleIff]))

private theorem defEq_intDecLt (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {a b : KExpr} (ha : ClosedAt env a wInt) (hb : ClosedAt env b wInt) :
    DefEq env 0
      (.app (.app (.const (.role .intDecLt) []) a) b)
      (.app (.app (.const (.role .intDecLe) [])
        (.app (.app (.const (.role .intAdd) []) a)
          (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) b) := by
  have hv := eqnValid_of ik.shapes .intDecLt (by decide) (by decide) (k := 0) rfl
  have hsc := ik.bk.storeClosed
  let Γ1 := fvarUpdate Γ₀ 0 wInt
  let Γ2 := fvarUpdate Γ1 1 wInt
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (wscopedB_of_hasFvar_false wInt ik.wInt_cl.1)
  have hInt0 := OpenType.liftClosed hsc (d := 0) (Γ := Γ₀) ik.intType (.ofRed ik.intRed) ⟨rfl, rfl⟩
  have hInt1 := OpenType.liftClosed hsc (d := 1) (Γ := Γ1) ik.intType (.ofRed ik.intRed) ⟨rfl, rfl⟩
  have hOne2 : OpenAt env 2 Γ2 (.app BaseKit.natSuccE BaseKit.natZeroE)
      (.app BaseKit.natSuccE BaseKit.natZeroE) BaseKit.natT :=
    OpenAt.ofClosed hsc ik.specOneAt rfl
  have hf0 : OpenAt env 2 Γ2 (.fvar 0 wInt) (.fvar 0 wInt) wInt :=
    OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)
  have hf1 : OpenAt env 2 Γ2 (.fvar 1 wInt) (.fvar 1 wInt) wInt :=
    OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)
  have hOfOne2 := (OpenAt.ofClosed hsc ik.intOfNatAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hOne2 .refl ik.wInt_cl.2
  rw [ik.intOfNatW] at hOfOne2
  have hAdd2 := ((OpenAt.ofClosed hsc ik.intAddAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      hf0 .refl ik.forallIntInt_lbb0).app_nondep hOfOne2 .refl ik.wInt_cl.2
  rw [ik.intAddW] at hAdd2
  have hLe2 := ((OpenAt.ofClosed hsc ik.intLeAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hAdd2 .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hf1 .refl rfl
  rw [ik.intLeW] at hLe2
  have hCarrO := OpenType.ofOpenAt
    ((OpenAt.ofClosed hsc ik.decAt rfl).app_nondep hLe2 .refl rfl)
  rw [ik.decW] at hCarrO
  have hLhsO : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intDecLt) []) (.fvar 0 wInt)) (.fvar 1 wInt))
      (.app (.app ik.intDecLtAt.witness (.fvar 0 wInt)) (.fvar 1 wInt))
      (.app wDec (.app (.app wIntLe
        (.app (.app wIntAdd (.fvar 0 wInt))
          (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
        (.fvar 1 wInt))) := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 wInt) (.fvar 0 wInt) wInt :=
      OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 wInt) (.fvar 1 wInt) wInt :=
      OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)
    have h1 := (OpenAt.ofClosed hsc ik.intDecLtAt ik.intDecLtTy_nf).app_abs hf0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wInt_cl.2,
        lbb_of_lbb0 ik.wDec_cl.2, lbb_of_lbb0 ik.wIntLe_cl.2,
        lbb_of_lbb0 ik.wIntAdd_cl.2, lbb_of_lbb0 ik.wIntOfNat_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1] at h1
    have h2 := h1.app_abs hf1 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2,
                ik.wIntAdd_cl.2, ik.wIntOfNat_cl.2])
    simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wIntLe_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1] using h2
  have hRhsO : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intDecLe) [])
        (.app (.app (.const (.role .intAdd) []) (.fvar 0 wInt))
          (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))))
        (.fvar 1 wInt))
      (.app (.app ik.intDecLeAt.witness
        (.app (.app wIntAdd (.fvar 0 wInt))
          (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
        (.fvar 1 wInt))
      (.app wDec (.app (.app wIntLe
        (.app (.app wIntAdd (.fvar 0 wInt))
          (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
        (.fvar 1 wInt))) := by
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 wInt) (.fvar 1 wInt) wInt :=
      OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)
    have h1 := (OpenAt.ofClosed hsc ik.intDecLeAt ik.intDecLeTy_nf).app_abs
      hAdd2 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, ik.wInt_cl.2,
        lbb_of_lbb0 ik.wDec_cl.2, lbb_of_lbb0 ik.wIntLe_cl.2])
    simp [fvarSubst, ← fvarSubst_abstract1_comm_gen
      (v := .app (.app wIntAdd (.fvar 0 wInt)) (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (by decide : (0 : Nat) ≠ 1)
      (fun k => by simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self wIntAdd ik.wIntAdd_cl.1,
        abstract1_eq_self wIntOfNat ik.wIntOfNat_cl.1]),
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntLe_cl.1] at h1
    have h2 := h1.app_abs hf1 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2,
                ik.wIntAdd_cl.2, ik.wIntOfNat_cl.2])
    simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wIntLe_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1] using h2
  have hLhsDe : DefEq env 0 (.app (.app ik.intDecLtAt.witness ha.witness) hb.witness)
      (.app (.app (.const (.role .intDecLt) []) a) b) :=
    .app (.app ik.intDecLtAt.defEq_witness ha.defEq_witness) hb.defEq_witness
  have hRhsDe : DefEq env 0
      (.app (.app ik.intDecLeAt.witness
        (.app (.app wIntAdd ha.witness) (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
        hb.witness)
      (.app (.app (.const (.role .intDecLe) [])
        (.app (.app (.const (.role .intAdd) []) a)
          (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) b) :=
    .app (.app ik.intDecLeAt.defEq_witness
      (.app (.app ik.wIntAdd_defEq ha.defEq_witness) (.app ik.wIntOfNat_defEq .refl)))
      hb.defEq_witness
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp only [eqnsSideExact, Ix.Kernel.specEqn, List.zipIdx, List.foldr, bmeta,
      Ix.Kernel.Level.zeronessOf] at hde
    have hLamL1 := OpenAt.lam_abs_inner_id (pw := .never) hInt1 hLhsO hCarrO.wInfer hCarrO.wRed rfl rfl hCtx1
    have hLamR1 := OpenAt.lam_abs_inner_id (pw := .never) hInt1 hRhsO hCarrO.wInfer hCarrO.wRed rfl rfl hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id hInt0 hLamL1
    have hLamR0 := OpenAt.lam_abs_outer_id hInt0 hLamR1
    have haO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ha ik.wInt_cl.1
    have hbO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hb ik.wInt_cl.1
    have hTy1Bl : (Ix.Kernel.Expr.forallE wInt
        ((Ix.Kernel.Expr.app wDec (.app (.app wIntLe
          (.app (.app wIntAdd (.fvar 0 wInt))
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.fvar 1 wInt))).abstract1 1) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2, looseBVarsBounded_abstract1' hCarrO.wClosed]
    have hAppL1 := hLamL0.app_abs haO .refl hTy1Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wIntLe_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hbO .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2,
        ik.wIntAdd_cl.2, ik.wIntOfNat_cl.2, ha.wClosed.2])
    have hAppR1 := hLamR0.app_abs haO .refl hTy1Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
      fvarSubst_of_not_hasFvar ik.wDec_cl.1, fvarSubst_of_not_hasFvar ik.wIntLe_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hbO .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2,
        ik.wIntAdd_cl.2, ik.wIntOfNat_cl.2, ha.wClosed.2])
    have hRedL1 : Red env 0
        (.app (.lam wInt ((Ix.Kernel.Expr.lam wInt
          ((Ix.Kernel.Expr.app (.app ik.intDecLtAt.witness (.fvar 0 wInt)) (.fvar 1 wInt)).abstract1 1)
          { pw := .never }).abstract1 0) { pw := .never }) ha.witness)
        (.lam wInt ((Ix.Kernel.Expr.app (.app ik.intDecLtAt.witness ha.witness) (.fvar 1 wInt)).abstract1 1) { pw := .never }) := by
      have h := Red.beta (env := env) (d := 0) (ty := wInt)
        (body := (Ix.Kernel.Expr.lam wInt ((Ix.Kernel.Expr.app (.app ik.intDecLtAt.witness (.fvar 0 wInt)) (.fvar 1 wInt)).abstract1 1)
          { pw := .never }).abstract1 0)
        (mb := { pw := .never }) ha.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by
        simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2, looseBVarsBounded_abstract1' hLhsO.wClosed])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
        fvarSubst_of_not_hasFvar ik.intDecLtAt.wClosed.1,
        ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] using h
    have hRedL2 : Red env 0
        (.app (.lam wInt ((Ix.Kernel.Expr.app (.app ik.intDecLtAt.witness ha.witness) (.fvar 1 wInt)).abstract1 1) { pw := .never })
          hb.witness)
        (.app (.app ik.intDecLtAt.witness ha.witness) hb.witness) := by
      have h := Red.beta (env := env) (d := 0) (ty := wInt)
        (body := (Ix.Kernel.Expr.app (.app ik.intDecLtAt.witness ha.witness) (.fvar 1 wInt)).abstract1 1)
        (mb := { pw := .never }) hb.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by
        simp [Ix.Kernel.Expr.looseBVarsBounded, ik.intDecLtAt.wClosed.2, ha.wClosed.2])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.intDecLtAt.wClosed.1,
        fvarSubst_of_not_hasFvar ha.wClosed.1] using h
    have hRedR1 : Red env 0
        (.app (.lam wInt ((Ix.Kernel.Expr.lam wInt
          ((Ix.Kernel.Expr.app (.app ik.intDecLeAt.witness
            (.app (.app wIntAdd (.fvar 0 wInt))
              (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
            (.fvar 1 wInt)).abstract1 1)
          { pw := .never }).abstract1 0) { pw := .never }) ha.witness)
        (.lam wInt ((Ix.Kernel.Expr.app (.app ik.intDecLeAt.witness
          (.app (.app wIntAdd ha.witness)
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.fvar 1 wInt)).abstract1 1) { pw := .never }) := by
      have h := Red.beta (env := env) (d := 0) (ty := wInt)
        (body := (Ix.Kernel.Expr.lam wInt ((Ix.Kernel.Expr.app (.app ik.intDecLeAt.witness
          (.app (.app wIntAdd (.fvar 0 wInt))
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.fvar 1 wInt)).abstract1 1) { pw := .never }).abstract1 0)
        (mb := { pw := .never }) ha.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by
        simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2, looseBVarsBounded_abstract1' hRhsO.wClosed])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
        fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1,
        fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
        ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] using h
    have hRedR2 : Red env 0
        (.app (.lam wInt ((Ix.Kernel.Expr.app (.app ik.intDecLeAt.witness
          (.app (.app wIntAdd ha.witness)
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.fvar 1 wInt)).abstract1 1) { pw := .never }) hb.witness)
        (.app (.app ik.intDecLeAt.witness
          (.app (.app wIntAdd ha.witness)
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          hb.witness) := by
      have h := Red.beta (env := env) (d := 0) (ty := wInt)
        (body := (Ix.Kernel.Expr.app (.app ik.intDecLeAt.witness
          (.app (.app wIntAdd ha.witness)
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.fvar 1 wInt)).abstract1 1)
        (mb := { pw := .never }) hb.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by
        simp [Ix.Kernel.Expr.looseBVarsBounded, ik.intDecLeAt.wClosed.2,
          ik.wIntAdd_cl.2, ik.wIntOfNat_cl.2, ha.wClosed.2])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1,
        fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
        fvarSubst_of_not_hasFvar ha.wClosed.1] using h
    exact OpenAt.defEq_chain hAppL2 hAppR2 (.app (.app hde .refl) .refl)
      ((Red.appFn hRedL1).trans hRedL2) hLhsDe ((Red.appFn hRedR1).trans hRedR2) hRhsDe
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans (by decide))
    have hEqO := OpenType.eq ik.bk.eqStored hCarrO hLhsO .refl hRhsO .refl
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) hInt1 hEqO rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) hInt0 hB1O rfl
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hB1O.wClosed
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
      fvarSubst_of_not_hasFvar ik.wInt_cl.1, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1, fvarSubst_of_not_hasFvar ik.intDecLtAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1] at hp1
    have hp2 := hp1.app_abs hb .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wDec_cl.2, ik.wIntLe_cl.2,
        ik.wIntAdd_cl.2, ik.wIntOfNat_cl.2, ik.intDecLtAt.wClosed.2,
        ik.intDecLeAt.wClosed.2, ha.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1,
      fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1, fvarSubst_of_not_hasFvar ik.intDecLtAt.wClosed.1,
      fvarSubst_of_not_hasFvar ik.intDecLeAt.wClosed.1, fvarSubst_of_not_hasFvar ha.wClosed.1] at hp2
    let hOfOne := ik.intOfNatAt.app_nondep ik.specOneAt ik.wInt_cl.2
    let hAddCl := (ik.intAddAt.app_nondep ha ik.forallIntInt_lbb0).app_nondep
      hOfOne ik.wInt_cl.2
    let hPropCl := (ik.intLeAt.app_nondep hAddCl (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hb rfl
    have hCarrTy : ClosedType env
        (.app wDec (.app (.app wIntLe
          (.app (.app wIntAdd ha.witness) (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          hb.witness)) (.succ .zero) := by
      have h := ik.decType hPropCl
      simpa [hPropCl, hAddCl, hOfOne, ik.intLeW, ik.intAddW, ik.intOfNatW] using h
    have hRhsCl : ClosedAt env
        (.app (.app (.const (.role .intDecLe) [])
          (.app (.app (.const (.role .intAdd) []) a)
            (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) b)
        (.app wDec (.app (.app wIntLe
          (.app (.app wIntAdd ha.witness) (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
          hb.witness)) := by
      have h := ik.intDecLeApp hAddCl hb
      simpa [hAddCl, hOfOne, ik.intAddW, ik.intOfNatW] using h
    exact defEq_of_eqProof_de hsc ik.bk.eqStored hp2
      (.app (.app (.app .refl .refl) hLhsDe) hRhsDe) (ik.intDecLtApp ha hb) hRhsCl hCarrTy

/-- Shared open-term builder for `bmodIte x m t e` at depth 2 (`x : Int`, `m : Nat`). -/
private theorem open_bmodIte (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    {t tw e ew : KExpr}
    (ht : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 BaseKit.natT) t tw wInt)
    (he : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 BaseKit.natT) e ew wInt) :
    let x0 := Ix.Kernel.Expr.fvar 0 wInt
    let m1 := Ix.Kernel.Expr.fvar 1 BaseKit.natT
    let r := Ix.Kernel.Expr.app (.app (.const (.role .intEmod) []) x0) (.app (.const (.role .intOfNat) []) m1)
    let rW := Ix.Kernel.Expr.app (.app ik.intEmodAt.witness x0) (.app wIntOfNat m1)
    let q := Ix.Kernel.Expr.app (.app (.const (.role .intEdiv) [])
      (.app (.app (.const (.role .intAdd) []) (.app (.const (.role .intOfNat) []) m1))
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))))
      (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))
    let qW := Ix.Kernel.Expr.app (.app ik.intEdivAt.witness
      (.app (.app wIntAdd (.app wIntOfNat m1))
        (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))))
      (.app wIntOfNat (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))
    OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 BaseKit.natT)
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) []))
        (.app (.app (.const (.role .intLe) [])
          (.app (.app (.const (.role .intAdd) []) r)
            (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q))
        (.app (.app (.const (.role .intDecLt) []) r) q)) t) e)
      (.app (.app (.app (.app (.app ik.iteAt.witness wInt)
        (.app (.app wIntLe
          (.app (.app wIntAdd rW)
            (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE)))) qW))
        (.app (.app ik.intDecLtAt.witness rW) qW)) tw) ew) wInt := by
  intro x0 m1 r rW q qW
  have hsc := ik.bk.storeClosed
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 BaseKit.natT
  have hf0 : OpenAt env 2 Γ2 x0 x0 wInt := OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)
  have hf1 : OpenAt env 2 Γ2 m1 m1 BaseKit.natT := OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)
  have hOfM : OpenAt env 2 Γ2 (.app (.const (.role .intOfNat) []) m1) (.app wIntOfNat m1) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hf1 .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hR : OpenAt env 2 Γ2 r rW wInt :=
    ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intEmodAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hf0 .refl
        ik.forallIntInt_lbb0).app_nondep hOfM .refl ik.wInt_cl.2
  have hOfOne : OpenAt env 2 Γ2
      (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))
      (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE)) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.specOneAt rfl) .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hOfTwo : OpenAt env 2 Γ2
      (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (.app wIntOfNat (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE))) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.specTwoAt rfl) .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hAddM1 : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intAdd) []) (.app (.const (.role .intOfNat) []) m1))
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (.app (.app wIntAdd (.app wIntOfNat m1))
        (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))) wInt := by
    have h := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intAddAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hOfM .refl
      ik.forallIntInt_lbb0).app_nondep hOfOne .refl ik.wInt_cl.2
    rwa [ik.intAddW] at h
  have hQ : OpenAt env 2 Γ2 q qW wInt :=
    ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intEdivAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hAddM1 .refl
      ik.forallIntInt_lbb0).app_nondep hOfTwo .refl ik.wInt_cl.2
  have hRAdd1 : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intAdd) []) r)
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (.app (.app wIntAdd rW)
        (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))) wInt := by
    have h := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intAddAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hR .refl
      ik.forallIntInt_lbb0).app_nondep hOfOne .refl ik.wInt_cl.2
    rwa [ik.intAddW] at h
  have hCond : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intLe) [])
        (.app (.app (.const (.role .intAdd) []) r)
          (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q)
      (.app (.app wIntLe
        (.app (.app wIntAdd rW)
          (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE)))) qW) (.sort .zero) := by
    have h := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intLeAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hRAdd1 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep hQ .refl rfl
    rwa [ik.intLeW] at h
  have hDecLt : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intDecLt) []) r) q)
      (.app (.app ik.intDecLtAt.witness rW) qW)
      (.app wDec (.app (.app wIntLe
        (.app (.app wIntAdd rW)
          (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE)))) qW)) := by
    have h1' := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intDecLtAt ik.intDecLtTy_nf).app_dep hR .refl
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
      inst1_of_lbb0 ik.wInt_cl.2, inst1_of_lbb0 ik.wDec_cl.2,
      inst1_of_lbb0 ik.wIntLe_cl.2, inst1_of_lbb0 ik.wIntAdd_cl.2,
      inst1_of_lbb0 ik.wIntOfNat_cl.2,
      abstract1_eq_self wInt ik.wInt_cl.1, abstract1_eq_self wDec ik.wDec_cl.1,
      abstract1_eq_self wIntLe ik.wIntLe_cl.1, abstract1_eq_self wIntAdd ik.wIntAdd_cl.1,
      abstract1_eq_self wIntOfNat ik.wIntOfNat_cl.1] at h1'
    have h2' := h1'.app_dep hQ .refl
    simpa [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2,
      inst1_of_lbb0 ik.wIntLe_cl.2, inst1_of_lbb0 ik.wIntAdd_cl.2,
      inst1_of_lbb0 ik.wIntOfNat_cl.2, inst1_of_lbb0 hR.wClosed] using h2'
  -- Apply `iteAt` to `wInt`, `hCond`, `hDecLt`, `ht`, `he` using `app_dep` (zero `fvar` capture!)
  have hI1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.iteAt ik.iteTy_nf).app_dep
      (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intAt rfl) .refl
  simp [ik.intW, Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
    abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at hI1
  have hI2 := hI1.app_dep hCond .refl
  simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2,
    inst1_of_lbb0 ik.wInt_cl.2] at hI2
  have hI3 := hI2.app_dep hDecLt .refl
  simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wInt_cl.2] at hI3
  have hI4 := hI3.app_dep ht .refl
  simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wInt_cl.2] at hI4
  have hI5 := hI4.app_dep he .refl
  simpa [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wInt_cl.2] using hI5

private theorem defEq_bmodIte (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) (m : Nat) {t e : KExpr} (ht : ClosedAt env t wInt) (he : ClosedAt env e wInt) :
    let a := intLitExpr x
    let b := Ix.Kernel.Expr.lit (.natVal m)
    let r := Ix.Kernel.Expr.app (.app (.const (.role .intEmod) []) a) (.app (.const (.role .intOfNat) []) b)
    let q := Ix.Kernel.Expr.app (.app (.const (.role .intEdiv) [])
      (.app (.app (.const (.role .intAdd) []) (.app (.const (.role .intOfNat) []) b))
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))))
      (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))
    DefEq env 0
      (.app (.app (.app (.app (.app (.const (.role .ifThenElse) [.succ .zero])
        (.const (.role .int) []))
        (.app (.app (.const (.role .intLe) [])
          (.app (.app (.const (.role .intAdd) []) r)
            (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q))
        (.app (.app (.const (.role .intDecLt) []) r) q)) t) e)
      (if x.emod (Int.ofNat m) < ((Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)) then t else e) := by
  intro a b r q
  have hx := ik.intLitAt x
  let hm := ik.bk.natLitAt m
  let hOfM := ik.intOfNatAt.app_nondep hm ik.wInt_cl.2
  let hRCl := (ik.intEmodAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
    hOfM ik.wInt_cl.2
  let hOfOne := ik.intOfNatAt.app_nondep ik.specOneAt ik.wInt_cl.2
  let hOfTwo := ik.intOfNatAt.app_nondep ik.specTwoAt ik.wInt_cl.2
  let hAddM1 := (ik.intAddAt.app_nondep hOfM ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hQCl := (ik.intEdivAt.app_nondep hAddM1 ik.forallIntInt_lbb0).app_nondep
    hOfTwo ik.wInt_cl.2
  let hRAdd1 := (ik.intAddAt.app_nondep hRCl ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hCondCl := (ik.intLeAt.app_nondep hRAdd1 (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep
    hQCl rfl
  have hInstCl : ClosedAt env (.app (.app (.const (.role .intDecLt) []) r) q) (.app wDec hCondCl.witness) := by
    have h := ik.intDecLtApp hRCl hQCl
    simpa [hCondCl, hRAdd1, hOfOne, ik.intLeW, ik.intAddW, ik.intOfNatW] using h
  -- Evaluate `r`, `q`, `r + 1`, and `decide (intLtP r q) (Int.decLt r q)`
  let rVal := x.emod (Int.ofNat m)
  let qVal := (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)
  have hRDe : DefEq env 0 r (intLitExpr rVal) := ik.defEq_intEmod x (.ofNat m)
  have hAddM1De : DefEq env 0
      (.app (.app (.const (.role .intAdd) []) (.app (.const (.role .intOfNat) []) b))
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (intLitExpr (Int.ofNat m + Int.ofNat 1)) :=
    DefEq.redL (.appArg (.appArg ik.red_one)) (ik.defEq_intAdd (.ofNat m) (.ofNat 1))
  have hQMid := (ik.intEdivAt.app_nondep (ik.intLitAt (Int.ofNat m + Int.ofNat 1))
    ik.forallIntInt_lbb0).app_nondep
    (ik.intLitAt (.ofNat 2)) ik.wInt_cl.2
  have hQDe : DefEq env 0 q (intLitExpr qVal) :=
    hQMid.defEq_trans (.app (.app .refl hAddM1De) (.app .refl ik.defEq_two))
      (ik.defEq_intEdiv (Int.ofNat m + Int.ofNat 1) (.ofNat 2))
  have hRAdd1Mid := (ik.intAddAt.app_nondep (ik.intLitAt rVal)
    ik.forallIntInt_lbb0).app_nondep
    (ik.intLitAt (.ofNat 1)) ik.wInt_cl.2
  have hRAdd1De : DefEq env 0
      (.app (.app (.const (.role .intAdd) []) r)
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (intLitExpr (rVal + Int.ofNat 1)) :=
    hRAdd1Mid.defEq_trans (.app (.app .refl hRDe) (.app .refl ik.defEq_one))
      (ik.defEq_intAdd rVal (.ofNat 1))
  have hDecideDe : DefEq env 0
      (.app (.app (.const (.role .decidableDecide) [])
        (.app (.app (.const (.role .intLe) [])
          (.app (.app (.const (.role .intAdd) []) r)
            (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q))
        (.app (.app (.const (.role .intDecLt) []) r) q))
      (if rVal + Int.ofNat 1 ≤ qVal then BaseKit.trueE else BaseKit.falseE) := by
    have hMid1 : ClosedAt env
        (.app (.app (.const (.role .decidableDecide) [])
          (.app (.app (.const (.role .intLe) [])
            (.app (.app (.const (.role .intAdd) []) r)
              (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q))
          (.app (.app (.const (.role .intDecLe) [])
            (.app (.app (.const (.role .intAdd) []) r)
              (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q))
        BaseKit.boolT :=
      ik.decideApp hCondCl (by simpa [hCondCl, ik.intLeW] using ik.intDecLeApp hRAdd1 hQCl)
    let hProp2 := (ik.intLeAt.app_nondep (ik.intLitAt (rVal + Int.ofNat 1))
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep
      (ik.intLitAt qVal) rfl
    have hMid2 : ClosedAt env
        (.app (.app (.const (.role .decidableDecide) [])
          (.app (.app (.const (.role .intLe) []) (intLitExpr (rVal + Int.ofNat 1))) (intLitExpr qVal)))
          (.app (.app (.const (.role .intDecLe) []) (intLitExpr (rVal + Int.ofNat 1))) (intLitExpr qVal)))
        BaseKit.boolT :=
      ik.decideApp hProp2 (by simpa [hProp2, ik.intLeW] using ik.intDecLeApp (ik.intLitAt (rVal + Int.ofNat 1)) (ik.intLitAt qVal))
    have h1 : DefEq env 0
        (.app (.app (.const (.role .decidableDecide) [])
          (.app (.app (.const (.role .intLe) [])
            (.app (.app (.const (.role .intAdd) []) r)
              (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))) q))
          (.app (.app (.const (.role .intDecLt) []) r) q))
        (.app (.app (.const (.role .decidableDecide) [])
          (.app (.app (.const (.role .intLe) []) (intLitExpr (rVal + Int.ofNat 1))) (intLitExpr qVal)))
          (.app (.app (.const (.role .intDecLe) []) (intLitExpr (rVal + Int.ofNat 1))) (intLitExpr qVal))) :=
      hMid1.defEq_trans (.app .refl (ik.defEq_intDecLt hRCl hQCl))
        (.app (.app .refl (.app (.app .refl hRAdd1De) hQDe)) (.app (.app .refl hRAdd1De) hQDe))
    exact hMid2.defEq_trans h1 (ik.defEq_intDecLe_decide (rVal + Int.ofNat 1) qVal)
  have hLtIff : (rVal < qVal) ↔ (rVal + Int.ofNat 1 ≤ qVal) := Int.lt_iff_add_one_le
  by_cases hlt : rVal < qVal
  · have hle : rVal + Int.ofNat 1 ≤ qVal := hLtIff.mp hlt
    have hlt' : x.emod (Int.ofNat m) < (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2) := hlt
    simp only [hlt', ↓reduceIte]
    simp only [hle, ↓reduceIte] at hDecideDe
    exact ik.ite_int_of_decide_true hCondCl hInstCl ht he hDecideDe
  · have hnle : ¬ (rVal + Int.ofNat 1 ≤ qVal) := fun h => hlt (hLtIff.mpr h)
    have hlt' : ¬ (x.emod (Int.ofNat m) < (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)) := hlt
    simp only [hlt', ↓reduceIte]
    simp only [hnle, ↓reduceIte] at hDecideDe
    exact ik.ite_int_of_decide_false hCondCl hInstCl ht he hDecideDe

private theorem defEq_intBmod (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) (m : Nat) :
    DefEq env 0 (.app (.app (.const (.role .intBmod) []) (intLitExpr x)) (.lit (.natVal m)))
      (intLitExpr (x.bmod m)) := by
  have hsc := ik.bk.storeClosed
  have hx := ik.intLitAt x; let hm := ik.bk.natLitAt m
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 BaseKit.natT
  have hf0 : OpenAt env 2 Γ2 (.fvar 0 wInt) (.fvar 0 wInt) wInt :=
    OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)
  have hf1 : OpenAt env 2 Γ2 (.fvar 1 BaseKit.natT) (.fvar 1 BaseKit.natT) BaseKit.natT :=
    OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)
  have hLhsO := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intBmodAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      hf0 .refl ik.forallNatInt_lbb0).app_nondep hf1 .refl ik.wInt_cl.2
  have hOfM2 : OpenAt env 2 Γ2
      (.app (.const (.role .intOfNat) []) (.fvar 1 BaseKit.natT))
      (.app wIntOfNat (.fvar 1 BaseKit.natT)) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hf1 .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hR2 := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intEmodAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      hf0 .refl ik.forallIntInt_lbb0).app_nondep hOfM2 .refl ik.wInt_cl.2
  have hSubR2 := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intSubAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hR2 .refl
      ik.forallIntInt_lbb0).app_nondep hOfM2 .refl ik.wInt_cl.2
  have hRhsO := ik.open_bmodIte hR2 hSubR2
  -- Closed types for LHS and RHS
  let hOfM := ik.intOfNatAt.app_nondep hm ik.wInt_cl.2
  let hRCl := (ik.intEmodAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
    hOfM ik.wInt_cl.2
  have hSubCl := (ik.intSubAt.app_nondep hRCl ik.forallIntInt_lbb0).app_nondep
    hOfM ik.wInt_cl.2
  let hOfOne := ik.intOfNatAt.app_nondep ik.specOneAt ik.wInt_cl.2
  let hOfTwo := ik.intOfNatAt.app_nondep ik.specTwoAt ik.wInt_cl.2
  let hAddM1 := (ik.intAddAt.app_nondep hOfM ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hQCl := (ik.intEdivAt.app_nondep hAddM1 ik.forallIntInt_lbb0).app_nondep
    hOfTwo ik.wInt_cl.2
  let hRAdd1 := (ik.intAddAt.app_nondep hRCl ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hCondCl := (ik.intLeAt.app_nondep hRAdd1 (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep
    hQCl rfl
  have hInstCl : ClosedAt env
      (.app (.app (.const (.role .intDecLt) [])
        (.app (.app (.const (.role .intEmod) []) (intLitExpr x)) (.app (.const (.role .intOfNat) []) (.lit (.natVal m)))))
        (.app (.app (.const (.role .intEdiv) [])
          (.app (.app (.const (.role .intAdd) []) (.app (.const (.role .intOfNat) []) (.lit (.natVal m))))
            (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))))
      (.app wDec hCondCl.witness) := by
    have h := ik.intDecLtApp hRCl hQCl
    simpa [hCondCl, hRAdd1, hOfOne, ik.intLeW, ik.intAddW, ik.intOfNatW] using h
  have hIntO := OpenType.liftClosed hsc (d := 0) (Γ := Γ₀) ik.intType (.ofRed ik.intRed) ⟨rfl, rfl⟩
  have hIteCl := ik.iteIntApp hCondCl hInstCl hRCl hSubCl
  have hEq := applyEqn2 ik.bk
    (eqnValid_of ik.shapes .intBmod (by decide) (by decide) (k := 0) rfl)
    (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
    hIntO (OpenType.ofClosed hsc ik.bk.natType)
    rfl rfl rfl rfl rfl rfl hLhsO hRhsO hx hm
    (by cases x <;> rfl)
    (by cases x <;> rfl)
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intBmodAt.wClosed.1,
              fvarSubst_of_not_hasFvar hx.wClosed.1]
        exact .app (.app ik.intBmodAt.defEq_witness hx.defEq_witness) .refl)
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
              fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1,
              fvarSubst_of_not_hasFvar ik.intEmodAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
              fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1, fvarSubst_of_not_hasFvar ik.intDecLtAt.wClosed.1,
              fvarSubst_of_not_hasFvar ik.intSubAt.wClosed.1,
              fvarSubst_of_not_hasFvar hx.wClosed.1]
        let rm := DefEq.refl (env := env) (d := 0) (a := .lit (.natVal m))
        let r1 := DefEq.refl (env := env) (d := 0) (a := .app BaseKit.natSuccE BaseKit.natZeroE)
        let r2 := DefEq.refl (env := env) (d := 0)
          (a := .app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE))
        have hRde := DefEq.app (.app ik.intEmodAt.defEq_witness hx.defEq_witness)
          (.app ik.wIntOfNat_defEq rm)
        have hQde := DefEq.app (.app ik.intEdivAt.defEq_witness
          (.app (.app ik.wIntAdd_defEq (.app ik.wIntOfNat_defEq rm))
            (.app ik.wIntOfNat_defEq r1))) (.app ik.wIntOfNat_defEq r2)
        exact .app (.app (.app (.app (.app ik.iteAt.defEq_witness ik.wInt_defEq)
          (.app (.app ik.wIntLe_defEq
            (.app (.app ik.wIntAdd_defEq hRde) (.app ik.wIntOfNat_defEq r1))) hQde))
          (.app (.app ik.intDecLtAt.defEq_witness hRde) hQde)) hRde)
          (.app (.app ik.intSubAt.defEq_witness hRde) (.app ik.wIntOfNat_defEq rm)))
    ((ik.intBmodAt.app_nondep hx ik.forallNatInt_lbb0).app_nondep
      hm ik.wInt_cl.2)
    hIteCl
  have hIte := ik.defEq_bmodIte x m hRCl hSubCl
  have hBmodDef : x.bmod m =
      let r := x.emod (Int.ofNat m)
      if r < (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2) then r else r - Int.ofNat m := by
    unfold Int.bmod
    have hq : ((Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)) = (↑m + 1) / 2 := rfl
    rw [hq]; rfl
  rw [hBmodDef]
  by_cases hlt : x.emod (Int.ofNat m) < (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)
  · simp only [hlt, ↓reduceIte] at hIte ⊢
    exact hIteCl.defEq_trans hEq (hRCl.defEq_trans hIte (ik.defEq_intEmod x (.ofNat m)))
  · simp only [hlt, ↓reduceIte] at hIte ⊢
    have hSubMid := (ik.intSubAt.app_nondep (ik.intLitAt (x.emod (Int.ofNat m)))
      ik.forallIntInt_lbb0).app_nondep
      (ik.intLitAt (.ofNat m)) ik.wInt_cl.2
    exact hIteCl.defEq_trans hEq (hSubCl.defEq_trans hIte
      (hSubMid.defEq_trans (.app (.app .refl (ik.defEq_intEmod x (.ofNat m))) .refl)
        (ik.defEq_intSub (x.emod (Int.ofNat m)) (.ofNat m))))

private theorem defEq_intBdiv (ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd)
    (x : Int) (m : Nat) :
    DefEq env 0 (.app (.app (.const (.role .intBdiv) []) (intLitExpr x)) (.lit (.natVal m)))
      (intLitExpr (x.bdiv m)) := by
  have hsc := ik.bk.storeClosed
  have hx := ik.intLitAt x; let hm := ik.bk.natLitAt m
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 wInt) 1 BaseKit.natT
  have hf0 : OpenAt env 2 Γ2 (.fvar 0 wInt) (.fvar 0 wInt) wInt :=
    OpenAt.fvar (d := 2) (idx := 0) (Γ := Γ2) (by omega)
  have hf1 : OpenAt env 2 Γ2 (.fvar 1 BaseKit.natT) (.fvar 1 BaseKit.natT) BaseKit.natT :=
    OpenAt.fvar (d := 2) (idx := 1) (Γ := Γ2) (by omega)
  have hLhsO := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intBdivAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      hf0 .refl ik.forallNatInt_lbb0).app_nondep hf1 .refl ik.wInt_cl.2
  have hOfM2 : OpenAt env 2 Γ2
      (.app (.const (.role .intOfNat) []) (.fvar 1 BaseKit.natT))
      (.app wIntOfNat (.fvar 1 BaseKit.natT)) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hf1 .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hOfZero2 : OpenAt env 2 Γ2
      (.app (.const (.role .intOfNat) []) BaseKit.natZeroE)
      (.app wIntOfNat BaseKit.natZeroE) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.bk.natZeroAt rfl) .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hOfOne2 : OpenAt env 2 Γ2
      (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))
      (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE)) wInt := by
    have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intOfNatAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
        (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.specOneAt rfl) .refl ik.wInt_cl.2
    rwa [ik.intOfNatW] at h
  have hQ2 := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intEdivAt
    (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep
      hf0 .refl ik.forallIntInt_lbb0).app_nondep hOfM2 .refl ik.wInt_cl.2
  have hQAdd1_2 : OpenAt env 2 Γ2
      (.app (.app (.const (.role .intAdd) [])
        (.app (.app (.const (.role .intEdiv) []) (.fvar 0 wInt))
          (.app (.const (.role .intOfNat) []) (.fvar 1 BaseKit.natT))))
        (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE)))
      (.app (.app wIntAdd
        (.app (.app ik.intEdivAt.witness (.fvar 0 wInt))
          (.app wIntOfNat (.fvar 1 BaseKit.natT))))
        (.app wIntOfNat (.app BaseKit.natSuccE BaseKit.natZeroE))) wInt := by
    have h := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intAddAt
      (by simp [Ix.Kernel.Expr.hasFvar, ik.wInt_cl.1])).app_nondep hQ2 .refl
      ik.forallIntInt_lbb0).app_nondep hOfOne2 .refl ik.wInt_cl.2
    rwa [ik.intAddW] at h
  have hInnerO := ik.open_bmodIte hQ2 hQAdd1_2
  have hEqM0_2 := OpenAt.eq ik.bk.eqStored (OpenType.ofClosed hsc ik.bk.natType)
    hf1 .refl (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.bk.natZeroAt rfl) .refl
  have hDecM0_2 : OpenAt env 2 Γ2
      (.app (.app (.const (.role .natDecEq) []) (.fvar 1 BaseKit.natT)) BaseKit.natZeroE)
      (.app (.app ik.natDecEqAt.witness (.fvar 1 BaseKit.natT)) BaseKit.natZeroE)
      (.app wDec (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
        (.fvar 1 BaseKit.natT)) BaseKit.natZeroE)) := by
    have h1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.natDecEqAt ik.natDecEqTy_nf).app_dep
        hf1 .refl
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
      abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at h1
    have h2 := h1.app_dep (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.bk.natZeroAt rfl) .refl
    simpa [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2] using h2
  have hI1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.iteAt ik.iteTy_nf).app_dep
      (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) ik.intAt rfl) .refl
  simp [ik.intW, Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1,
    abstract1_eq_self wDec ik.wDec_cl.1, inst1_of_lbb0 ik.wDec_cl.2] at hI1
  have hI2 := hI1.app_dep hEqM0_2 .refl
  simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wDec_cl.2,
    inst1_of_lbb0 ik.wInt_cl.2] at hI2
  have hI3 := hI2.app_dep hDecM0_2 .refl
  simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wInt_cl.2] at hI3
  have hI4 := hI3.app_dep hOfZero2 .refl
  simp [Ix.Kernel.Expr.instantiate1, inst1_of_lbb0 ik.wInt_cl.2] at hI4
  have hRhsO := hI4.app_dep hInnerO .refl
  simp [inst1_of_lbb0 ik.wInt_cl.2] at hRhsO
  -- Closed types for LHS and RHS
  let hOfM := ik.intOfNatAt.app_nondep hm ik.wInt_cl.2
  let hOfZero := ik.intOfNatAt.app_nondep ik.bk.natZeroAt ik.wInt_cl.2
  let hOfOne := ik.intOfNatAt.app_nondep ik.specOneAt ik.wInt_cl.2
  let hOfTwo := ik.intOfNatAt.app_nondep ik.specTwoAt ik.wInt_cl.2
  let hQCl := (ik.intEdivAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
    hOfM ik.wInt_cl.2
  let hQAdd1Cl := (ik.intAddAt.app_nondep hQCl ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hRCl := (ik.intEmodAt.app_nondep hx ik.forallIntInt_lbb0).app_nondep
    hOfM ik.wInt_cl.2
  let hAddM1 := (ik.intAddAt.app_nondep hOfM ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hCCl := (ik.intEdivAt.app_nondep hAddM1 ik.forallIntInt_lbb0).app_nondep
    hOfTwo ik.wInt_cl.2
  let hRAdd1 := (ik.intAddAt.app_nondep hRCl ik.forallIntInt_lbb0).app_nondep
    hOfOne ik.wInt_cl.2
  let hInnerCondCl := (ik.intLeAt.app_nondep hRAdd1 (by simp [Ix.Kernel.Expr.looseBVarsBounded, ik.wInt_cl.2])).app_nondep
    hCCl rfl
  have hInnerInstCl : ClosedAt env
      (.app (.app (.const (.role .intDecLt) [])
        (.app (.app (.const (.role .intEmod) []) (intLitExpr x)) (.app (.const (.role .intOfNat) []) (.lit (.natVal m)))))
        (.app (.app (.const (.role .intEdiv) [])
          (.app (.app (.const (.role .intAdd) []) (.app (.const (.role .intOfNat) []) (.lit (.natVal m))))
            (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE BaseKit.natZeroE))))
          (.app (.const (.role .intOfNat) []) (.app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE)))))
      (.app wDec hInnerCondCl.witness) := by
    have h := ik.intDecLtApp hRCl hCCl
    simpa [hInnerCondCl, hRAdd1, hOfOne, ik.intLeW, ik.intAddW, ik.intOfNatW] using h
  have hInnerCl := ik.iteIntApp hInnerCondCl hInnerInstCl hQCl hQAdd1Cl
  let hEqM0Cl : ClosedAt env
      (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
        (.lit (.natVal m))) BaseKit.natZeroE) (.sort .zero) :=
    let h := closedType_eq ik.bk.eqStored ik.bk.natType hm.wInfer hm.wClosed
      ik.bk.natZeroAt.wInfer ik.bk.natZeroAt.wClosed
    .ofInfer h.closed h.infer
  have hDecM0Cl := ik.natDecEqApp hm ik.bk.natZeroAt
  have hIntO := OpenType.liftClosed hsc (d := 0) (Γ := Γ₀) ik.intType (.ofRed ik.intRed) ⟨rfl, rfl⟩
  have hOuterIteCl := ik.iteIntApp hEqM0Cl hDecM0Cl hOfZero hInnerCl
  have hEq := applyEqn2 ik.bk
    (eqnValid_of ik.shapes .intBdiv (by decide) (by decide) (k := 0) rfl)
    (by decide) rfl rfl rfl ik.intType ik.intRed rfl rfl
    hIntO (OpenType.ofClosed hsc ik.bk.natType)
    rfl rfl rfl rfl rfl rfl hLhsO hRhsO hx hm
    (by cases x <;> rfl)
    (by cases x <;> rfl)
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.intBdivAt.wClosed.1,
              fvarSubst_of_not_hasFvar hx.wClosed.1]
        exact .app (.app ik.intBdivAt.defEq_witness hx.defEq_witness) .refl)
    (by simp [fvarSubst, fvarSubst_of_not_hasFvar ik.iteAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wInt_cl.1,
              fvarSubst_of_not_hasFvar ik.natDecEqAt.wClosed.1, fvarSubst_of_not_hasFvar ik.wIntOfNat_cl.1,
              fvarSubst_of_not_hasFvar ik.wIntLe_cl.1, fvarSubst_of_not_hasFvar ik.wIntAdd_cl.1,
              fvarSubst_of_not_hasFvar ik.intEmodAt.wClosed.1, fvarSubst_of_not_hasFvar ik.intEdivAt.wClosed.1,
              fvarSubst_of_not_hasFvar ik.intDecLtAt.wClosed.1,
              fvarSubst_of_not_hasFvar hx.wClosed.1]
        let rm := DefEq.refl (env := env) (d := 0) (a := .lit (.natVal m))
        let r0 := DefEq.refl (env := env) (d := 0) (a := BaseKit.natZeroE)
        let r1 := DefEq.refl (env := env) (d := 0) (a := .app BaseKit.natSuccE BaseKit.natZeroE)
        let r2 := DefEq.refl (env := env) (d := 0)
          (a := .app BaseKit.natSuccE (.app BaseKit.natSuccE BaseKit.natZeroE))
        have hRde := DefEq.app (.app ik.intEmodAt.defEq_witness hx.defEq_witness)
          (.app ik.wIntOfNat_defEq rm)
        have hQde := DefEq.app (.app ik.intEdivAt.defEq_witness hx.defEq_witness)
          (.app ik.wIntOfNat_defEq rm)
        have hCde := DefEq.app (.app ik.intEdivAt.defEq_witness
          (.app (.app ik.wIntAdd_defEq (.app ik.wIntOfNat_defEq rm))
            (.app ik.wIntOfNat_defEq r1))) (.app ik.wIntOfNat_defEq r2)
        have hInnerDe := DefEq.app (.app (.app (.app (.app ik.iteAt.defEq_witness ik.wInt_defEq)
          (.app (.app ik.wIntLe_defEq
            (.app (.app ik.wIntAdd_defEq hRde) (.app ik.wIntOfNat_defEq r1))) hCde))
          (.app (.app ik.intDecLtAt.defEq_witness hRde) hCde)) hQde)
          (.app (.app ik.wIntAdd_defEq hQde) (.app ik.wIntOfNat_defEq r1))
        exact .app (.app (.app (.app (.app ik.iteAt.defEq_witness ik.wInt_defEq) .refl)
          (.app (.app ik.natDecEqAt.defEq_witness rm) r0))
          (.app ik.wIntOfNat_defEq r0)) hInnerDe)
    ((ik.intBdivAt.app_nondep hx ik.forallNatInt_lbb0).app_nondep
      hm ik.wInt_cl.2)
    hOuterIteCl
  have hDecM0De : DefEq env 0
      (.app (.app (.const (.role .decidableDecide) [])
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.natT)
          (.lit (.natVal m))) BaseKit.natZeroE))
        (.app (.app (.const (.role .natDecEq) []) (.lit (.natVal m))) BaseKit.natZeroE))
      (if m = 0 then BaseKit.trueE else BaseKit.falseE) :=
    DefEq.redL
      (.trans (.appFn (.appArg (.appArg ik.bk.red_natZero_lit))) (.appArg (.appArg ik.bk.red_natZero_lit)))
      (ik.defEq_natDecEq_decide m 0)
  have hBdivDef : x.bdiv m =
      if m = 0 then Int.ofNat 0
      else
        let q := x.ediv (Int.ofNat m)
        if x.emod (Int.ofNat m) < (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2) then q
        else q + Int.ofNat 1 := by
    unfold Int.bdiv
    have hq : ((Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)) = (↑m + 1) / 2 := rfl
    rw [hq]; rfl
  rw [hBdivDef]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte] at hDecM0De ⊢
    exact hOuterIteCl.defEq_trans hEq
      (hOfZero.defEq_trans (ik.ite_int_of_decide_true hEqM0Cl hDecM0Cl hOfZero hInnerCl hDecM0De)
        (.app .refl ik.bk.defEq_natZero_lit))
  · simp only [hm0, ↓reduceIte] at hDecM0De ⊢
    have hOuter := ik.ite_int_of_decide_false hEqM0Cl hDecM0Cl hOfZero hInnerCl hDecM0De
    have hInner := ik.defEq_bmodIte x m hQCl hQAdd1Cl
    by_cases hlt : x.emod (Int.ofNat m) < (Int.ofNat m + Int.ofNat 1).ediv (Int.ofNat 2)
    · simp only [hlt, ↓reduceIte] at hInner ⊢
      exact hOuterIteCl.defEq_trans hEq
        (hInnerCl.defEq_trans hOuter (hQCl.defEq_trans hInner (ik.defEq_intEdiv x (.ofNat m))))
    · simp only [hlt, ↓reduceIte] at hInner ⊢
      have hQAdd1Mid := (ik.intAddAt.app_nondep (ik.intLitAt (x.ediv (Int.ofNat m)))
        ik.forallIntInt_lbb0).app_nondep
        (ik.intLitAt (.ofNat 1)) ik.wInt_cl.2
      exact hOuterIteCl.defEq_trans hEq (hInnerCl.defEq_trans hOuter (hQAdd1Cl.defEq_trans hInner
        (hQAdd1Mid.defEq_trans (.app (.app .refl (ik.defEq_intEdiv x (.ofNat m))) (.app .refl ik.defEq_one))
          (ik.defEq_intAdd (x.ediv (Int.ofNat m)) (.ofNat 1)))))

end IntKit

/-! ## Assembling `Core.PrimEqnEnv` from `BaseKit` and `Shapes (· < 77)` -/

theorem primEqnEnv_of_shapes {env : Ix.Kernel.Env .anon}
    (bk : BaseKit env) (hs : Shapes (· < 77) env) : Core.PrimEqnEnv env := by
  obtain ⟨wDec, wNot, wDecide, wInt, wIntLe, wIntOfNat, wIntAdd, ⟨ik⟩⟩ := intKit_exists bk hs
  have hOfNatS : ∃ ci, env.find? (.role .intOfNat) = some ci := by
    obtain ⟨ci, _, hf, -⟩ := roleExact_anchor_of hs .intNegOfNat .intOfNat (by decide) (by decide) (by decide)
    exact ⟨ci, hf⟩
  have hNegSuccS : ∃ ci, env.find? (.role .intNegSucc) = some ci := by
    obtain ⟨ci, _, hf, -⟩ := roleExact_anchor_of hs .intNegOfNat .intNegSucc (by decide) (by decide) (by decide)
    exact ⟨ci, hf⟩
  have hOpS : ∀ r : Role,
      r ∈ [.intNeg, .intNatAbs, .intAdd, .intSub, .intMul, .intEdiv, .intEmod, .intPow, .intBmod, .intBdiv] →
      ∃ ci, env.find? (.role r) = some ci := by
    intro r hr
    have h46 : 46 ≤ Ix.SpecDigest.groupOf r := by
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · cases hr
    have h5 : RoleVal.roleSpecKindNat r = 5 := by
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr <;> [decide; skip]
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · cases hr
    obtain ⟨ci, _, hf, -⟩ := roleExact_eqns hs r h46 h5
    exact ⟨ci, hf⟩
  exact {
    intOfNatStored := hOfNatS
    intNegSuccStored := hNegSuccS
    intOpStored := hOpS
    intNeg := fun d x =>
      ClosedAt.red_of_defEq rfl (ik.intNegAt.app_nondep (ik.intLitAt x) ik.wInt_cl.2)
        (ik.intLitAt (-x)) (ik.defEq_intNeg x) d
    intNatAbs := fun d x =>
      ClosedAt.red_of_defEq rfl (ik.intNatAbsAt.app_nondep (ik.intLitAt x) rfl)
        (bk.natLitAt x.natAbs) (ik.defEq_intNatAbs x) d
    intAdd := fun d x y =>
      ClosedAt.red_of_defEq rfl
        ((ik.intAddAt.app_nondep (ik.intLitAt x) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt y) ik.wInt_cl.2)
        (ik.intLitAt (x + y)) (ik.defEq_intAdd x y) d
    intSub := fun d x y =>
      ClosedAt.red_of_defEq rfl
        ((ik.intSubAt.app_nondep (ik.intLitAt x) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt y) ik.wInt_cl.2)
        (ik.intLitAt (x - y)) (ik.defEq_intSub x y) d
    intMul := fun d x y =>
      ClosedAt.red_of_defEq rfl
        ((ik.intMulAt.app_nondep (ik.intLitAt x) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt y) ik.wInt_cl.2)
        (ik.intLitAt (x * y)) (ik.defEq_intMul x y) d
    intEdiv := fun d x y =>
      ClosedAt.red_of_defEq rfl
        ((ik.intEdivAt.app_nondep (ik.intLitAt x) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt y) ik.wInt_cl.2)
        (ik.intLitAt (x.ediv y)) (ik.defEq_intEdiv x y) d
    intEmod := fun d x y =>
      ClosedAt.red_of_defEq rfl
        ((ik.intEmodAt.app_nondep (ik.intLitAt x) ik.forallIntInt_lbb0).app_nondep
          (ik.intLitAt y) ik.wInt_cl.2)
        (ik.intLitAt (x.emod y)) (ik.defEq_intEmod x y) d
    intPow := fun d x n hn =>
      ClosedAt.red_of_defEq rfl
        ((ik.intPowAt.app_nondep (ik.intLitAt x) ik.forallNatInt_lbb0).app_nondep
          (bk.natLitAt n) ik.wInt_cl.2)
        (ik.intLitAt (x ^ n)) (ik.defEq_intPow x n hn) d
    intBmod := fun d x m =>
      ClosedAt.red_of_defEq rfl
        ((ik.intBmodAt.app_nondep (ik.intLitAt x) ik.forallNatInt_lbb0).app_nondep
          (bk.natLitAt m) ik.wInt_cl.2)
        (ik.intLitAt (x.bmod m)) (ik.defEq_intBmod x m) d
    intBdiv := fun d x m =>
      ClosedAt.red_of_defEq rfl
        ((ik.intBdivAt.app_nondep (ik.intLitAt x) ik.forallNatInt_lbb0).app_nondep
          (bk.natLitAt m) ik.wInt_cl.2)
        (ik.intLitAt (x.bdiv m)) (ik.defEq_intBdiv x m) d }

/-! ## Extracting `BaseKit` and `Core.PrimEqnEnv` at group 76 of the binding fold -/

section FoldTail

universe u

open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

set_option maxRecDepth 100000 in
private theorem baseKit_groups :
    Ix.SpecDigest.groupOf .nat < 46 ∧ Ix.SpecDigest.groupOf .natZero < 46 ∧
    Ix.SpecDigest.groupOf .natSucc < 46 ∧ Ix.SpecDigest.groupOf .bool < 76 ∧
    Ix.SpecDigest.groupOf .natPred < 76 ∧
    (∀ r : Role, (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
      r ∈ RoleOps.opRoles ∧ Ix.SpecDigest.groupOf r < 76) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro r hm
    have hmem : r ∈ Role.all := Role.mem_all r
    have hall : Role.all.all (fun r =>
        decide (((.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames) →
          r ∈ RoleOps.opRoles ∧ Ix.SpecDigest.groupOf r < 76)) = true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp hall r hmem) hm

private theorem valLimit_76 : valLimit 76 = 46 := by decide

private theorem find?_of_mem_nodup :
    ∀ (cs : List (Ix.Kernel.ConstantInfo .anon)) (ci : Ix.Kernel.ConstantInfo .anon),
      ci ∈ cs → (cs.map (·.name)).Nodup → (⟨cs⟩ : Ix.Kernel.Env .anon).find? ci.name = some ci
  | [], _, hm, _ => by cases hm
  | c :: cs, ci, hm, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [Ix.Kernel.Env.find?, List.find?_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp
    · have hne : (c.name == ci.name) = false :=
        beq_false_of_ne fun he => hnd.1 (he ▸ List.mem_map.mpr ⟨ci, hm', rfl⟩)
      rw [hne]
      exact find?_of_mem_nodup cs ci hm' hnd.2

/-- Extract `BaseKit env` from `BndOver.{u} L t (· < 76) R env`. -/
theorem baseKit_of_bndOver {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hall : AllBound t) (hb : BndOver.{u} L t (· < 76) R env) :
    BaseKit env := by
  obtain ⟨E, hE⟩ := OpInstall.recordsFor_exists hb.shape.committed
  have hinv := hb.inv hE (carried_valLimit 76) (limWithin_below t 76)
  have hnodup := hb.shape.reading.nodup
  have hEqMem : (Ix.Kernel.eqA : Ix.Kernel.ConstantInfo .anon) ∈ env.consts :=
    hb.shape.pins .eqK _ (List.Mem.head _)
  have hEqReflMem : (Ix.Kernel.eqReflA : Ix.Kernel.ConstantInfo .anon) ∈ env.consts :=
    hb.shape.pins .eqK _ (List.Mem.tail _ (List.Mem.head _))
  have hNatMem : (Ix.Kernel.natA : Ix.Kernel.ConstantInfo .anon) ∈ env.consts :=
    hb.shape.pins .natK _ (List.Mem.head _)
  have hNatZeroMem : (Ix.Kernel.natZeroA : Ix.Kernel.ConstantInfo .anon) ∈ env.consts :=
    hb.shape.pins .natK _ (List.Mem.tail _ (List.Mem.head _))
  have hNatSuccMem : (Ix.Kernel.natSuccA : Ix.Kernel.ConstantInfo .anon) ∈ env.consts :=
    hb.shape.pins .natK _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  obtain ⟨hN, hZ, hS, hB, hP, hBin⟩ := baseKit_groups
  have hforce : ∀ X : Role, Ix.SpecDigest.groupOf X < 46 →
      Core.Ctx.inForce ⟨E, env, t, some (valLimit 76)⟩ X := fun X hX =>
    ⟨hall X, fun n hn => by
      rw [valLimit_76] at hn
      obtain rfl := Option.some.inj hn
      exact hX⟩
  have hnatLit : Ix.Kernel.natLitSupported env = true :=
    hinv.companions.natLit (hforce _ hN) (hforce _ hZ) (hforce _ hS)
  have hOpOk : ∀ r : Role, r ∈ RoleOps.opRoles → Ix.SpecDigest.groupOf r < 76 →
      Ix.Kernel.natOpStoredOk env (.role r) = true := by
    intro r hop hlt
    have hnN : (Ix.Kernel.Key.role r : Core.KKey) ∈ RoleOps.opNames := by
      rw [RoleOps.opNames_eq_map]
      exact List.mem_map.mpr ⟨r, hop, rfl⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall r)
    obtain ⟨ci, hci, -⟩ := hb.shape.kept _ r a hlt (role_mem_roleGroup r) (OpInstall.op_kept hop).1 ha
    exact hb.facts.opsPinned (.role r) hnN (by rw [hci]; rfl)
  obtain ⟨hbp, hbc, hbt⟩ := hb.facts.shapes.bool hB
  exact {
    storeClosed := hinv.scopedCoreFacts.env.storeClosed
    wf := hinv.store.store.wf
    eqStored := find?_of_mem_nodup env.consts _ hEqMem hnodup
    eqReflStored := find?_of_mem_nodup env.consts _ hEqReflMem hnodup
    natStored := find?_of_mem_nodup env.consts _ hNatMem hnodup
    natZeroStored := find?_of_mem_nodup env.consts _ hNatZeroMem hnodup
    natSuccStored := find?_of_mem_nodup env.consts _ hNatSuccMem hnodup
    natLit := hnatLit
    natPredOk := hOpOk .natPred (by decide) hP
    natOpsOk := fun r hm =>
      let ⟨hop, hlt⟩ := hBin r hm
      hOpOk r hop hlt
    boolPinned := hbp
    boolCtorsStored := hbc
    boolCtorsTyped := hbt }

/-- **Certified `PrimEqnEnv` at group 76 of the binding fold**, from the invariant below group 76
and the validated equation shapes below group 77. -/
theorem primEqnEnv_of_bndOver {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hall : AllBound t) (hb : BndOver.{u} L t (· < 76) R env)
    (hshapes : Shapes (· < 77) env) : Core.PrimEqnEnv env :=
  primEqnEnv_of_shapes (baseKit_of_bndOver hall hb) hshapes

end FoldTail

end IxVM.Refinement.Binding
