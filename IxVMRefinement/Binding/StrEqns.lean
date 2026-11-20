import IxVMRefinement.Binding.IntEqns

/-! # Certified `String` and `Char` primitive equations (`PrimEqnEnv`)

Derives the `String` and `Char` fields of `Core.PrimEqnEnv env` from `BaseKit env`,
`Ix.Kernel.strLitSupported env = true`, and `Shapes (· < 77) env`, turning the validated equations
of `Char.utf8Size`, `String.utf8ByteSize`, `String.back`, `String.toByteArray`, `String.decEq`,
`List.append`, and `String.append` into closed kernel `Red` derivations at every depth, and
combines them with `IntPrimEqns` to build `Core.PrimEqnEnv env`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Rules (Red DefEq Infer PiRed Grade)

/-! ## Additional generic equation eliminators -/

section StrEqnElim

variable {env : Ix.Kernel.Env .anon}

/-- Eliminate a 1-variable, 1-`Bool`-equality-hypothesis, 0-level conditional equation `e` at
closed argument `a` when the guard reduces to `gR`. -/
theorem applyEqn1Hyp1 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    {T₀ T₀w Cw gL gLw gR lhsW rhsW a lhsA rhsA : KExpr} {u₀ : KLevel}
    (hvars : e.vars = [T₀])
    (hhyps : e.hyps = [.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gL) gR])
    (hlev : e.level = .succ .zero)
    (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hCcl : e.carrier.hasFvar = false) (hCbl : e.carrier.looseBVarsBounded 0 = true)
    (hDom0 : OpenType env 0 Γ₀ T₀ T₀w u₀)
    (hgLbl : gL.looseBVarsBounded 0 = true) (hgRcl : ClosedAt env gR BaseKit.boolT)
    (hLhsBl : e.lhs.looseBVarsBounded 0 = true) (hRhsBl : e.rhs.looseBVarsBounded 0 = true)
    (hgLO : OpenAt env 1 (fvarUpdate Γ₀ 0 T₀w)
      (fvarSubst 0 (.fvar 0 T₀w) gL) gLw BaseKit.boolT)
    (hLhsO : OpenAt env 2
      (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
      (fvarSubst 1 (.fvar 1 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
        (fvarSubst 0 (.fvar 0 T₀w) e.lhs))
      lhsW Cw)
    (hRhsO : OpenAt env 2
      (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
      (fvarSubst 1 (.fvar 1 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness))
        (fvarSubst 0 (.fvar 0 T₀w) e.rhs))
      rhsW Cw)
    (hLhsNo1 : ∀ v, fvarSubst 1 v lhsW = lhsW)
    (hRhsNo1 : ∀ v, fvarSubst 1 v rhsW = rhsW)
    (ha : ClosedAt env a T₀w)
    (hGuard : DefEq env 0 (fvarSubst 0 ha.witness gLw) hgRcl.witness)
    (hLhsInst : DefEq env 0 (fvarSubst 0 ha.witness lhsW) lhsA)
    (hRhsInst : DefEq env 0 (fvarSubst 0 ha.witness rhsW) rhsA)
    (hLhsCl : ClosedAt env lhsA Cw) (hRhsCl : ClosedAt env rhsA Cw) :
    DefEq env 0 lhsA rhsA := by
  have hsc := bk.storeClosed
  have hT0wCl : T₀w.hasFvar = false := hDom0.wOk.hasFvar_false
  rcases hv with ⟨hemp, _⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp [hhyps] at hemp
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    let Γ1 := fvarUpdate Γ₀ 0 T₀w
    have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (wscopedB_of_hasFvar_false T₀w hT0wCl)
    let hypRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gL) gR
    let hypW : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) gLw) hgRcl.witness
    let Γ2 := fvarUpdate Γ1 1 hypW
    let eqRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs
    let eqW : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW
    have hEqBl : eqRaw.looseBVarsBounded 0 = true := by
      simp [eqRaw, Ix.Kernel.Expr.looseBVarsBounded, hCbl, hLhsBl, hRhsBl]
    have hHypBl : hypRaw.looseBVarsBounded 0 = true := by
      simp [hypRaw, Ix.Kernel.Expr.looseBVarsBounded, hgLbl, hgRcl.closed.2]
    have hBool1 := OpenType.ofClosed hsc (d := 1) (Γ := Γ1) bk.boolType
    have hgRO1 : OpenAt env 1 Γ1 gR hgRcl.witness BaseKit.boolT := OpenAt.ofClosed hsc hgRcl rfl
    have hHypO : OpenType env 1 Γ1 (fvarSubst 0 (.fvar 0 T₀w) hypRaw) hypW .zero := by
      simp [hypRaw, fvarSubst, fvarSubst_of_not_hasFvar hgRcl.closed.1]
      exact OpenType.eq bk.eqStored hBool1 hgLO .refl hgRO1 .refl
    have hCO2 := OpenType.liftClosed hsc (d := 2) (Γ := Γ2) hC (.ofRed hCred) ⟨hCcl, hCbl⟩
    have hEqO : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 hypW) (fvarSubst 0 (.fvar 0 T₀w) eqRaw)) eqW .zero := by
      simp [eqRaw, fvarSubst, fvarSubst_of_not_hasFvar hCcl]
      exact OpenType.eq bk.eqStored hCO2 hLhsO .refl hRhsO .refl
    let hBody1Raw : KExpr := .forallE hypRaw (eqRaw.abstract1 1) { pw := .ifAllZero [] }
    have hBody1Bl : hBody1Raw.looseBVarsBounded 0 = true := by
      simp [hBody1Raw, Ix.Kernel.Expr.looseBVarsBounded, hHypBl, looseBVarsBounded_abstract1' hEqBl]
    have hBody1O : OpenType env 1 Γ1
        (fvarSubst 0 (.fvar 0 T₀w) hBody1Raw)
        (.forallE hypW (eqW.abstract1 1) { pw := .ifAllZero [] }) (.imax .zero .zero) := by
      simp [hBody1Raw, fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]
      exact OpenType.forallE_abs (fvarSubst_looseBVarsBounded rfl hEqBl) hHypO hEqO rfl hCtx1
    have hStmtO := OpenType.forallE_abs (pw := .ifAllZero []) hBody1Bl hDom0 hBody1O rfl
    have hStmtEq : eqnsStmtExact e = .forallE T₀ (hBody1Raw.abstract1 0) { pw := .ifAllZero [] } := by
      simp [eqnsStmtExact, hBody1Raw, hypRaw, eqRaw, hvars, hhyps, hlev]
    rw [← hStmtEq] at hStmtO
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hBody1O.wClosed
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] at hp1
    have hrefl := closedAt_eqRefl bk.eqReflStored bk.boolType hgRcl
    have hHypMatch : DefEq env 0
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) hgRcl.witness) hgRcl.witness)
        (fvarSubst 0 ha.witness hypW) := by
      simp only [hypW, fvarSubst, fvarSubst_of_not_hasFvar hgRcl.wClosed.1]
      exact .app (.app (.app .refl .refl) (.symm hGuard)) .refl
    have hp2 := hp1.app_abs hrefl hHypMatch (fvarSubst_looseBVarsBounded ha.wClosed.2 hEqO.wClosed)
    have hEqClean :
        fvarSubst 1 hrefl.witness (fvarSubst 0 ha.witness eqW) =
          .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw)
            (fvarSubst 0 ha.witness lhsW))
            (fvarSubst 0 ha.witness rhsW) := by
      simp only [eqW, fvarSubst, fvarSubst_of_not_hasFvar hC.closed.1]
      rw [fvarSubst_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1 hrefl.wClosed.1, hLhsNo1,
          fvarSubst_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1 hrefl.wClosed.1, hRhsNo1]
    rw [hEqClean] at hp2
    exact defEq_of_eqProof_de hsc bk.eqStored hp2
      (.app (.app (.app .refl .refl) hLhsInst) hRhsInst) hLhsCl hRhsCl hC

/-- Eliminate a 1-variable, 2-`Bool`-equality-hypothesis, 0-level conditional equation `e` at
closed argument `a` when both guards reduce to `g1R` and `g2R`. -/
theorem applyEqn1Hyp2 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    {T₀ T₀w Cw g1L g1Lw g1R g2L g2Lw g2R lhsW rhsW a lhsA rhsA : KExpr} {u₀ : KLevel}
    (hvars : e.vars = [T₀])
    (hhyps : e.hyps =
      [.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1L) g1R,
       .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2L) g2R])
    (hlev : e.level = .succ .zero)
    (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hCcl : e.carrier.hasFvar = false) (hCbl : e.carrier.looseBVarsBounded 0 = true)
    (hDom0 : OpenType env 0 Γ₀ T₀ T₀w u₀)
    (hg1Lbl : g1L.looseBVarsBounded 0 = true) (hg1Rcl : ClosedAt env g1R BaseKit.boolT)
    (hg2Lbl : g2L.looseBVarsBounded 0 = true) (hg2Rcl : ClosedAt env g2R BaseKit.boolT)
    (hLhsBl : e.lhs.looseBVarsBounded 0 = true) (hRhsBl : e.rhs.looseBVarsBounded 0 = true)
    (hg1LO : OpenAt env 1 (fvarUpdate Γ₀ 0 T₀w)
      (fvarSubst 0 (.fvar 0 T₀w) g1L) g1Lw BaseKit.boolT)
    (hg2LO : OpenAt env 2
      (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness))
      (fvarSubst 1 (.fvar 1 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness))
        (fvarSubst 0 (.fvar 0 T₀w) g2L))
      g2Lw BaseKit.boolT)
    (hg2No1 : ∀ v, fvarSubst 1 v g2Lw = g2Lw)
    (hLhsO : OpenAt env 3
      (fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness)) 2
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2Lw) hg2Rcl.witness))
      (fvarSubst 2 (.fvar 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2Lw) hg2Rcl.witness))
        (fvarSubst 1 (.fvar 1 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness))
          (fvarSubst 0 (.fvar 0 T₀w) e.lhs)))
      lhsW Cw)
    (hRhsO : OpenAt env 3
      (fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness)) 2
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2Lw) hg2Rcl.witness))
      (fvarSubst 2 (.fvar 2 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2Lw) hg2Rcl.witness))
        (fvarSubst 1 (.fvar 1 (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness))
          (fvarSubst 0 (.fvar 0 T₀w) e.rhs)))
      rhsW Cw)
    (hLhsNo1 : ∀ v, fvarSubst 1 v lhsW = lhsW) (hLhsNo2 : ∀ v, fvarSubst 2 v lhsW = lhsW)
    (hRhsNo1 : ∀ v, fvarSubst 1 v rhsW = rhsW) (hRhsNo2 : ∀ v, fvarSubst 2 v rhsW = rhsW)
    (ha : ClosedAt env a T₀w)
    (hGuard1 : DefEq env 0 (fvarSubst 0 ha.witness g1Lw) hg1Rcl.witness)
    (hGuard2 : DefEq env 0 (fvarSubst 0 ha.witness g2Lw) hg2Rcl.witness)
    (hLhsInst : DefEq env 0 (fvarSubst 0 ha.witness lhsW) lhsA)
    (hRhsInst : DefEq env 0 (fvarSubst 0 ha.witness rhsW) rhsA)
    (hLhsCl : ClosedAt env lhsA Cw) (hRhsCl : ClosedAt env rhsA Cw) :
    DefEq env 0 lhsA rhsA := by
  have hsc := bk.storeClosed
  have hT0wCl : T₀w.hasFvar = false := hDom0.wOk.hasFvar_false
  rcases hv with ⟨hemp, _⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp [hhyps] at hemp
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    let Γ1 := fvarUpdate Γ₀ 0 T₀w
    have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (wscopedB_of_hasFvar_false T₀w hT0wCl)
    let hyp1Raw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1L) g1R
    let hyp1W : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) hg1Rcl.witness
    let Γ2 := fvarUpdate Γ1 1 hyp1W
    let hyp2Raw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2L) g2R
    let hyp2W : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2Lw) hg2Rcl.witness
    let Γ3 := fvarUpdate Γ2 2 hyp2W
    let eqRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs
    let eqW : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW
    have hEqBl : eqRaw.looseBVarsBounded 0 = true := by
      simp [eqRaw, Ix.Kernel.Expr.looseBVarsBounded, hCbl, hLhsBl, hRhsBl]
    have hHyp1Bl : hyp1Raw.looseBVarsBounded 0 = true := by
      simp [hyp1Raw, Ix.Kernel.Expr.looseBVarsBounded, hg1Lbl, hg1Rcl.closed.2]
    have hHyp2Bl : hyp2Raw.looseBVarsBounded 0 = true := by
      simp [hyp2Raw, Ix.Kernel.Expr.looseBVarsBounded, hg2Lbl, hg2Rcl.closed.2]
    have hBool1 := OpenType.ofClosed hsc (d := 1) (Γ := Γ1) bk.boolType
    have hg1RO1 : OpenAt env 1 Γ1 g1R hg1Rcl.witness BaseKit.boolT := OpenAt.ofClosed hsc hg1Rcl rfl
    have hHyp1O : OpenType env 1 Γ1 (fvarSubst 0 (.fvar 0 T₀w) hyp1Raw) hyp1W .zero := by
      simp [hyp1Raw, fvarSubst, fvarSubst_of_not_hasFvar hg1Rcl.closed.1]
      exact OpenType.eq bk.eqStored hBool1 hg1LO .refl hg1RO1 .refl
    have hCtx2 : CtxWs 2 Γ2 := hCtx1.update (FVarOk.wscopedB hCtx1 _ hHyp1O.wOk)
    have hBool2 := OpenType.ofClosed hsc (d := 2) (Γ := Γ2) bk.boolType
    have hg2RO2 : OpenAt env 2 Γ2 g2R hg2Rcl.witness BaseKit.boolT := OpenAt.ofClosed hsc hg2Rcl rfl
    have hHyp2O : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 hyp1W) (fvarSubst 0 (.fvar 0 T₀w) hyp2Raw)) hyp2W .zero := by
      simp [hyp2Raw, fvarSubst, fvarSubst_of_not_hasFvar hg2Rcl.closed.1]
      exact OpenType.eq bk.eqStored hBool2 hg2LO .refl hg2RO2 .refl
    have hCO3 := OpenType.liftClosed hsc (d := 3) (Γ := Γ3) hC (.ofRed hCred) ⟨hCcl, hCbl⟩
    have hEqO : OpenType env 3 Γ3
        (fvarSubst 2 (.fvar 2 hyp2W) (fvarSubst 1 (.fvar 1 hyp1W) (fvarSubst 0 (.fvar 0 T₀w) eqRaw)))
        eqW .zero := by
      simp [eqRaw, fvarSubst, fvarSubst_of_not_hasFvar hCcl]
      exact OpenType.eq bk.eqStored hCO3 hLhsO .refl hRhsO .refl
    let hBody2Raw : KExpr := .forallE hyp2Raw (eqRaw.abstract1 2) { pw := .ifAllZero [] }
    have hBody2Bl : hBody2Raw.looseBVarsBounded 0 = true := by
      simp [hBody2Raw, Ix.Kernel.Expr.looseBVarsBounded, hHyp2Bl, looseBVarsBounded_abstract1' hEqBl]
    have hBody2O : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 hyp1W) (fvarSubst 0 (.fvar 0 T₀w) hBody2Raw))
        (.forallE hyp2W (eqW.abstract1 2) { pw := .ifAllZero [] }) (.imax .zero .zero) := by
      simp [hBody2Raw, fvarSubst,
        ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 2),
        ← fvarSubst_abstract1_comm_fvar (by decide : (1 : Nat) ≠ 2)]
      exact OpenType.forallE_abs
        (fvarSubst_looseBVarsBounded rfl (fvarSubst_looseBVarsBounded rfl hEqBl))
        hHyp2O hEqO rfl hCtx2
    let hBody1Raw : KExpr := .forallE hyp1Raw (hBody2Raw.abstract1 1) { pw := .ifAllZero [] }
    have hBody1Bl : hBody1Raw.looseBVarsBounded 0 = true := by
      simp [hBody1Raw, Ix.Kernel.Expr.looseBVarsBounded, hHyp1Bl, looseBVarsBounded_abstract1' hBody2Bl]
    have hBody1O : OpenType env 1 Γ1
        (fvarSubst 0 (.fvar 0 T₀w) hBody1Raw)
        (.forallE hyp1W ((Ix.Kernel.Expr.forallE hyp2W (eqW.abstract1 2) { pw := .ifAllZero [] }).abstract1 1)
          { pw := .ifAllZero [] })
        (.imax .zero (.imax .zero .zero)) := by
      simp [hBody1Raw, fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]
      exact OpenType.forallE_abs (fvarSubst_looseBVarsBounded rfl hBody2Bl) hHyp1O hBody2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs (pw := .ifAllZero []) hBody1Bl hDom0 hBody1O rfl
    have hStmtEq : eqnsStmtExact e = .forallE T₀ (hBody1Raw.abstract1 0) { pw := .ifAllZero [] } := by
      simp [eqnsStmtExact, hBody1Raw, hBody2Raw, hyp1Raw, hyp2Raw, eqRaw, hvars, hhyps, hlev]
    rw [← hStmtEq] at hStmtO
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hBody1O.wClosed
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1] at hp1
    have hrefl1 := closedAt_eqRefl bk.eqReflStored bk.boolType hg1Rcl
    have hHyp1Match : DefEq env 0
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) hg1Rcl.witness) hg1Rcl.witness)
        (fvarSubst 0 ha.witness hyp1W) := by
      simp only [hyp1W, fvarSubst, fvarSubst_of_not_hasFvar hg1Rcl.wClosed.1]
      exact .app (.app (.app .refl .refl) (.symm hGuard1)) .refl
    have hp2 := hp1.app_abs hrefl1 hHyp1Match (fvarSubst_looseBVarsBounded ha.wClosed.2 hBody2O.wClosed)
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hrefl1.wClosed.1] at hp2
    have hrefl2 := closedAt_eqRefl bk.eqReflStored bk.boolType hg2Rcl
    have hHyp2Match : DefEq env 0
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) hg2Rcl.witness) hg2Rcl.witness)
        (fvarSubst 1 hrefl1.witness (fvarSubst 0 ha.witness hyp2W)) := by
      simp only [hyp2W, fvarSubst, fvarSubst_of_not_hasFvar hg2Rcl.wClosed.1]
      rw [fvarSubst_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1 hrefl1.wClosed.1, hg2No1]
      exact .app (.app (.app .refl .refl) (.symm hGuard2)) .refl
    have hp3 := hp2.app_abs hrefl2 hHyp2Match
      (fvarSubst_looseBVarsBounded hrefl1.wClosed.2 (fvarSubst_looseBVarsBounded ha.wClosed.2 hEqO.wClosed))
    have hEqClean :
        fvarSubst 2 hrefl2.witness (fvarSubst 1 hrefl1.witness (fvarSubst 0 ha.witness eqW)) =
          .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw)
            (fvarSubst 0 ha.witness lhsW))
            (fvarSubst 0 ha.witness rhsW) := by
      simp only [eqW, fvarSubst, fvarSubst_of_not_hasFvar hC.closed.1]
      rw [fvarSubst_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1 hrefl1.wClosed.1, hLhsNo1,
          fvarSubst_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1 hrefl2.wClosed.1, hLhsNo2,
          fvarSubst_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1 hrefl1.wClosed.1, hRhsNo1,
          fvarSubst_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1 hrefl2.wClosed.1, hRhsNo2]
    rw [hEqClean] at hp3
    exact defEq_of_eqProof_de hsc bk.eqStored hp3
      (.app (.app (.app .refl .refl) hLhsInst) hRhsInst) hLhsCl hRhsCl hC

/-- Eliminate a 3-variable (non-dependent domains), 0-hypothesis, 0-level equation `e` at closed
arguments `a, b, c`. -/
theorem applyEqn3 (bk : BaseKit env) {r : Role} {e : Ix.Kernel.Equation .anon}
    (hv : EqnValid env r e) (hlv0 : roleSpecLevels r = some 0)
    {T₀ T₀w T₁ T₁w T₂ T₂w Cw lhsW rhsW a b c lhsABC rhsABC : KExpr} {u₀ u₁ u₂ : KLevel}
    (hvars : e.vars = [T₀, T₁, T₂]) (hhyps : e.hyps = []) (hlev : e.level = .succ .zero)
    (hC : ClosedType env Cw (.succ .zero)) (hCred : Red env 0 Cw e.carrier)
    (hCcl : e.carrier.hasFvar = false) (hCbl : e.carrier.looseBVarsBounded 0 = true)
    (hDom0 : OpenType env 0 Γ₀ T₀ T₀w u₀)
    (hDom1 : OpenType env 0 Γ₀ T₁ T₁w u₁)
    (hDom2 : OpenType env 0 Γ₀ T₂ T₂w u₂)
    (hT1cl : T₁.hasFvar = false) (hT1bl : T₁.looseBVarsBounded 0 = true)
    (hT2cl : T₂.hasFvar = false) (hT2bl : T₂.looseBVarsBounded 0 = true)
    (hLhsBl : e.lhs.looseBVarsBounded 0 = true) (hRhsBl : e.rhs.looseBVarsBounded 0 = true)
    (hLhsO : OpenAt env 3 (fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w) 2 T₂w)
      (fvarSubst 2 (.fvar 2 T₂w) (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) e.lhs)))
      lhsW Cw)
    (hRhsO : OpenAt env 3 (fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 T₀w) 1 T₁w) 2 T₂w)
      (fvarSubst 2 (.fvar 2 T₂w) (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) e.rhs)))
      rhsW Cw)
    (ha : ClosedAt env a T₀w) (hb : ClosedAt env b T₁w) (hc : ClosedAt env c T₂w)
    (hLhsInst : DefEq env 0 (fvarSubst 2 hc.witness (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness lhsW))) lhsABC)
    (hRhsInst : DefEq env 0 (fvarSubst 2 hc.witness (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness rhsW))) rhsABC)
    (hLhsCl : ClosedAt env lhsABC Cw) (hRhsCl : ClosedAt env rhsABC Cw)
    (hLhsNL : lhsW.lamPw = none := by rfl) (hRhsNL : rhsW.lamPw = none := by rfl) :
    DefEq env 0 lhsABC rhsABC := by
  have hsc := bk.storeClosed
  have hT0wCl : T₀w.hasFvar = false := hDom0.wOk.hasFvar_false
  have hT1wCl : T₁w.hasFvar = false := hDom1.wOk.hasFvar_false
  have hT2wCl : T₂w.hasFvar = false := hDom2.wOk.hasFvar_false
  let Γ1 := fvarUpdate Γ₀ 0 T₀w
  let Γ2 := fvarUpdate Γ1 1 T₁w
  let Γ3 := fvarUpdate Γ2 2 T₂w
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (wscopedB_of_hasFvar_false T₀w hT0wCl)
  have hCtx2 : CtxWs 2 Γ2 := hCtx1.update (wscopedB_of_hasFvar_false T₁w hT1wCl)
  have hDom1_1 : OpenType env 1 Γ1 T₁ T₁w u₁ :=
    OpenType.liftClosed hsc (d := 1) (Γ := Γ1) hDom1.toClosedType hDom1.wPiRed ⟨hT1cl, hT1bl⟩
  have hDom2_2 : OpenType env 2 Γ2 T₂ T₂w u₂ :=
    OpenType.liftClosed hsc (d := 2) (Γ := Γ2) hDom2.toClosedType hDom2.wPiRed ⟨hT2cl, hT2bl⟩
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · simp only [eqnsSideExact, hvars, hlev, List.zipIdx, List.foldr, bmeta,
      Ix.Kernel.Level.zeronessOf] at hde
    have hCO := OpenType.ofClosed hsc (d := 3) (Γ := Γ3) hC
    have hLamL2 := OpenAt.lam_abs_inner (pw := .never)
      (fvarSubst_looseBVarsBounded rfl (fvarSubst_looseBVarsBounded rfl hLhsBl))
      hDom2_2 hLhsO hCO.wInfer hCO.wRed rfl hLhsNL hCtx2
    have hLamR2 := OpenAt.lam_abs_inner (pw := .never)
      (fvarSubst_looseBVarsBounded rfl (fvarSubst_looseBVarsBounded rfl hRhsBl))
      hDom2_2 hRhsO hCO.wInfer hCO.wRed rfl hRhsNL hCtx2
    have hL2bl : (Ix.Kernel.Expr.lam T₂ (e.lhs.abstract1 2) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT2bl, looseBVarsBounded_abstract1' hLhsBl]
    have hR2bl : (Ix.Kernel.Expr.lam T₂ (e.rhs.abstract1 2) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT2bl, looseBVarsBounded_abstract1' hRhsBl]
    have hLamL1 := OpenAt.lam_abs_outer
      (bodyRaw := fvarSubst 0 (.fvar 0 T₀w) (.lam T₂ (e.lhs.abstract1 2) { pw := .never }))
      (fvarSubst_looseBVarsBounded rfl hL2bl) hDom1_1
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hT2cl,
            ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 2),
            ← fvarSubst_abstract1_comm_fvar (by decide : (1 : Nat) ≠ 2)]; exact hLamL2) hCtx1
    have hLamR1 := OpenAt.lam_abs_outer
      (bodyRaw := fvarSubst 0 (.fvar 0 T₀w) (.lam T₂ (e.rhs.abstract1 2) { pw := .never }))
      (fvarSubst_looseBVarsBounded rfl hR2bl) hDom1_1
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hT2cl,
            ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 2),
            ← fvarSubst_abstract1_comm_fvar (by decide : (1 : Nat) ≠ 2)]; exact hLamR2) hCtx1
    have hL1bl : (Ix.Kernel.Expr.lam T₁ ((Ix.Kernel.Expr.lam T₂ (e.lhs.abstract1 2) { pw := .never }).abstract1 1)
        { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hL2bl]
    have hR1bl : (Ix.Kernel.Expr.lam T₁ ((Ix.Kernel.Expr.lam T₂ (e.rhs.abstract1 2) { pw := .never }).abstract1 1)
        { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hR2bl]
    have hLamL0 := OpenAt.lam_abs_outer hL1bl hDom0
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
            ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]; exact hLamL1)
    have hLamR0 := OpenAt.lam_abs_outer hR1bl hDom0
      (by simp [fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
            ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]; exact hLamR1)
    have haO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) ha hT0wCl
    have hbO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hb hT1wCl
    have hcO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hc hT2wCl
    have hTy2Bl : (Ix.Kernel.Expr.forallE T₂w (Cw.abstract1 2) { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hDom2.wClosed, looseBVarsBounded_abstract1' hC.closed.2]
    have hTy1Bl : (Ix.Kernel.Expr.forallE T₁w ((Ix.Kernel.Expr.forallE T₂w (Cw.abstract1 2) { pw := .never }).abstract1 1)
        { pw := .never }).looseBVarsBounded 0 = true := by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hDom1.wClosed, looseBVarsBounded_abstract1' hTy2Bl]
    have hAppL1 := hLamL0.app_abs haO .refl hTy1Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl, fvarSubst_of_not_hasFvar hT2wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1,
      fvarSubst_of_not_hasFvar hC.closed.1] at hAppL1
    have hAppL2 := hAppL1.app_abs hbO .refl hTy2Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT2wCl,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1,
      fvarSubst_of_not_hasFvar hC.closed.1] at hAppL2
    have hAppL3 := hAppL2.app_abs hcO .refl hC.closed.2
    have hAppR1 := hLamR0.app_abs haO .refl hTy1Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl, fvarSubst_of_not_hasFvar hT2wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1,
      fvarSubst_of_not_hasFvar hC.closed.1] at hAppR1
    have hAppR2 := hAppR1.app_abs hbO .refl hTy2Bl
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT2wCl,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1,
      fvarSubst_of_not_hasFvar hC.closed.1] at hAppR2
    have hAppR3 := hAppR2.app_abs hcO .refl hC.closed.2
    have mkBeta3 : ∀ (bodyW : KExpr) (hbl : bodyW.looseBVarsBounded 0 = true),
        Red env 0
          (.app (.app (.app (.lam T₀w ((Ix.Kernel.Expr.lam T₁w ((Ix.Kernel.Expr.lam T₂w (bodyW.abstract1 2) { pw := .never }).abstract1 1) { pw := .never }).abstract1 0) { pw := .never })
            ha.witness) hb.witness) hc.witness)
          (fvarSubst 2 hc.witness (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness bodyW))) := by
      intro bodyW hbl
      have h1 : Red env 0
          (.app (.lam T₀w ((Ix.Kernel.Expr.lam T₁w ((Ix.Kernel.Expr.lam T₂w (bodyW.abstract1 2) { pw := .never }).abstract1 1) { pw := .never }).abstract1 0) { pw := .never }) ha.witness)
          (.lam T₁w ((Ix.Kernel.Expr.lam T₂w ((fvarSubst 0 ha.witness bodyW).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }) := by
        have h := Red.beta (env := env) (d := 0) (ty := T₀w)
          (body := (Ix.Kernel.Expr.lam T₁w ((Ix.Kernel.Expr.lam T₂w (bodyW.abstract1 2) { pw := .never }).abstract1 1) { pw := .never }).abstract1 0)
          (mb := { pw := .never }) ha.wInfer.toIO .refl
        rw [abstract1_instantiate1_eq_fvarSubst (by
          simp [Ix.Kernel.Expr.looseBVarsBounded, hDom1.wClosed, hDom2.wClosed,
            looseBVarsBounded_abstract1' hbl, looseBVarsBounded_abstract1'])] at h
        simpa [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl, fvarSubst_of_not_hasFvar hT2wCl,
          ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
          ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1] using h
      have h2 : Red env 0
          (.app (.lam T₁w ((Ix.Kernel.Expr.lam T₂w ((fvarSubst 0 ha.witness bodyW).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }) hb.witness)
          (.lam T₂w ((fvarSubst 1 hb.witness (fvarSubst 0 ha.witness bodyW)).abstract1 2) { pw := .never }) := by
        have h := Red.beta (env := env) (d := 0) (ty := T₁w)
          (body := (Ix.Kernel.Expr.lam T₂w ((fvarSubst 0 ha.witness bodyW).abstract1 2) { pw := .never }).abstract1 1)
          (mb := { pw := .never }) hb.wInfer.toIO .refl
        rw [abstract1_instantiate1_eq_fvarSubst (by
          simp [Ix.Kernel.Expr.looseBVarsBounded, hDom2.wClosed,
            looseBVarsBounded_abstract1' (fvarSubst_looseBVarsBounded ha.wClosed.2 hbl)])] at h
        simpa [fvarSubst, fvarSubst_of_not_hasFvar hT2wCl,
          ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1] using h
      have h3 : Red env 0
          (.app (.lam T₂w ((fvarSubst 1 hb.witness (fvarSubst 0 ha.witness bodyW)).abstract1 2) { pw := .never }) hc.witness)
          (fvarSubst 2 hc.witness (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness bodyW))) := by
        have h := Red.beta (env := env) (d := 0) (ty := T₂w)
          (body := (fvarSubst 1 hb.witness (fvarSubst 0 ha.witness bodyW)).abstract1 2)
          (mb := { pw := .never }) hc.wInfer.toIO .refl
        rwa [abstract1_instantiate1_eq_fvarSubst
          (fvarSubst_looseBVarsBounded hb.wClosed.2 (fvarSubst_looseBVarsBounded ha.wClosed.2 hbl))] at h
      exact .trans (.appFn (.appFn h1)) (.trans (.appFn h2) h3)
    exact OpenAt.defEq_chain hAppL3 hAppR3 (.app (.app (.app hde .refl) .refl) .refl)
      (mkBeta3 lhsW hLhsO.wClosed) hLhsInst (mkBeta3 rhsW hRhsO.wClosed) hRhsInst
  · have hlen : cv.levelParams.length = 0 := Option.some.inj (hlv.symm.trans hlv0)
    let eqRaw : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) e.carrier) e.lhs) e.rhs
    let eqW : KExpr :=
      .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) Cw) lhsW) rhsW
    have hEqBl : eqRaw.looseBVarsBounded 0 = true := by
      simp [eqRaw, Ix.Kernel.Expr.looseBVarsBounded, hCbl, hLhsBl, hRhsBl]
    have hCO := OpenType.liftClosed hsc (d := 3) (Γ := Γ3) hC (.ofRed hCred) ⟨hCcl, hCbl⟩
    have hEqO : OpenType env 3 Γ3
        (fvarSubst 2 (.fvar 2 T₂w) (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) eqRaw)))
        eqW .zero := by
      simp [eqRaw, fvarSubst, fvarSubst_of_not_hasFvar hCcl]
      exact OpenType.eq bk.eqStored hCO hLhsO .refl hRhsO .refl
    let b2Raw : KExpr := .forallE T₂ (eqRaw.abstract1 2) { pw := .ifAllZero [] }
    have hb2Bl : b2Raw.looseBVarsBounded 0 = true := by
      simp [b2Raw, Ix.Kernel.Expr.looseBVarsBounded, hT2bl, looseBVarsBounded_abstract1' hEqBl]
    have hBody2O : OpenType env 2 Γ2
        (fvarSubst 1 (.fvar 1 T₁w) (fvarSubst 0 (.fvar 0 T₀w) b2Raw))
        (.forallE T₂w (eqW.abstract1 2) { pw := .ifAllZero [] }) (.imax u₂ .zero) := by
      simp [b2Raw, fvarSubst, fvarSubst_of_not_hasFvar hT2cl,
        ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 2),
        ← fvarSubst_abstract1_comm_fvar (by decide : (1 : Nat) ≠ 2)]
      exact OpenType.forallE_abs
        (fvarSubst_looseBVarsBounded rfl (fvarSubst_looseBVarsBounded rfl hEqBl))
        hDom2_2 hEqO rfl hCtx2
    let b1Raw : KExpr := .forallE T₁ (b2Raw.abstract1 1) { pw := .ifAllZero [] }
    have hb1Bl : b1Raw.looseBVarsBounded 0 = true := by
      simp [b1Raw, Ix.Kernel.Expr.looseBVarsBounded, hT1bl, looseBVarsBounded_abstract1' hb2Bl]
    have hBody1O : OpenType env 1 Γ1
        (fvarSubst 0 (.fvar 0 T₀w) b1Raw)
        (.forallE T₁w ((Ix.Kernel.Expr.forallE T₂w (eqW.abstract1 2) { pw := .ifAllZero [] }).abstract1 1)
          { pw := .ifAllZero [] })
        (.imax u₁ (.imax u₂ .zero)) := by
      simp [b1Raw, fvarSubst, fvarSubst_of_not_hasFvar hT1cl,
        ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1)]
      exact OpenType.forallE_abs (fvarSubst_looseBVarsBounded rfl hb2Bl) hDom1_1 hBody2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs (pw := .ifAllZero []) hb1Bl hDom0 hBody1O rfl
    have hStmtEq : eqnsStmtExact e = .forallE T₀ (b1Raw.abstract1 0) { pw := .ifAllZero [] } := by
      simp [eqnsStmtExact, b1Raw, b2Raw, eqRaw, hvars, hhyps, hlev]
    rw [← hStmtEq] at hStmtO
    have hp0 := ClosedAt.ofThm0_open hsc hf hlen hde hStmtO
    have hp1 := hp0.app_abs ha .refl hBody1O.wClosed
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT1wCl, fvarSubst_of_not_hasFvar hT2wCl,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) ha.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) ha.wClosed.1] at hp1
    have hp2 := hp1.app_abs hb .refl (by
      simp [Ix.Kernel.Expr.looseBVarsBounded, hDom2.wClosed,
        looseBVarsBounded_abstract1' (fvarSubst_looseBVarsBounded ha.wClosed.2 hEqO.wClosed)])
    simp [fvarSubst, fvarSubst_of_not_hasFvar hT2wCl,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) hb.wClosed.1] at hp2
    have hp3 := hp2.app_abs hc .refl
      (fvarSubst_looseBVarsBounded hb.wClosed.2 (fvarSubst_looseBVarsBounded ha.wClosed.2 hEqO.wClosed))
    simp [eqW, fvarSubst, fvarSubst_of_not_hasFvar hC.closed.1] at hp3
    exact defEq_of_eqProof_de hsc bk.eqStored hp3
      (.app (.app (.app .refl .refl) hLhsInst) hRhsInst) hLhsCl hRhsCl hC

end StrEqnElim

/-! ## Reducing `specNum` -/

section SpecNum

variable {env : Ix.Kernel.Env .anon}

def specNumVal : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n == 0 then 0
    else if n % 2 == 0 then 2 * specNumVal fuel (n / 2)
    else specNumVal fuel (n - 1) + 1

theorem specNumGo_red (bk : BaseKit env) :
    ∀ (fuel n : Nat),
      Red env 0 (Ix.Kernel.specNumGo fuel n) (.lit (.natVal (specNumVal fuel n)))
  | 0, _ => bk.red_natZero_lit
  | fuel + 1, n => by
    simp only [Ix.Kernel.specNumGo, specNumVal]
    by_cases h0 : (n == 0) = true
    · simp only [h0, ↓reduceIte]; exact bk.red_natZero_lit
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (n % 2 == 0) = true
      · simp only [he, ↓reduceIte]
        have h2 : Red env 0 (Ix.Kernel.specTwo (md := .anon)) (.lit (.natVal 2)) :=
          .trans (.appArg (.trans (.appArg bk.red_natZero_lit) (bk.red_natSucc_lit 0)))
            (bk.red_natSucc_lit 1)
        exact .trans (.appFn (.appArg h2))
          (.trans (.appArg (specNumGo_red bk fuel (n / 2)))
            (bk.red_natOp (r := .natMul) (by decide) (a := 2) (b := specNumVal fuel (n / 2)) rfl))
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact .trans (.appArg (specNumGo_red bk fuel (n - 1)))
          (bk.red_natSucc_lit (specNumVal fuel (n - 1)))

private theorem substPW_nil (pw : Ix.Kernel.PropWhen) :
    Ix.Kernel.Level.substPW [] [] pw = pw :=
  Ix.Kernel.PropWhen.eq_of_holds fun _ => by
    rw [Ix.Kernel.Level.holds_substPW]; rfl

private theorem natBinNat_infer (bk : BaseKit env) {r : Role}
    (hm : (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames)
    (hneBeq : (.role r : Core.KKey) ≠ Ix.Kernel.natBeqName)
    (hneBle : (.role r : Core.KKey) ≠ Ix.Kernel.natBleName) :
    ∃ mb1 mb2, Infer env .full 0 (.const (.role r) [])
      (.forallE BaseKit.natT (.forallE BaseKit.natT BaseKit.natT mb2) mb1) := by
  obtain ⟨cv, v, hint, hf, hlp, hpin⟩ := RoleOps.natOpStoredOk_inv (bk.natOpsOk r hm)
  have hnePred : (.role r : Core.KKey) ≠ Ix.Kernel.natPredName := by
    intro h; rw [h] at hm; exact absurd hm (by decide)
  unfold Ix.Kernel.natOpTyPinned at hpin
  simp only [hnePred, ↓reduceIte] at hpin
  cases hty : cv.type with
  | forallE dom rest mb1 =>
    rw [hty] at hpin
    cases rest with
    | forallE dom2 body mb2 =>
      simp [Ix.Kernel.natOpCod, hneBeq, hneBle] at hpin
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpin
      refine ⟨mb1, mb2, ?_⟩
      have h1 := Infer.const (g := .full) (d := 0) (ci := .defnInfo cv v hint) hf rfl (us := [])
        (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlp])
      simpa [Ix.Kernel.ConstantInfo.toConstantVal, hlp, hty, Ix.Kernel.Expr.instantiateLevelParams,
        substPW_nil] using h1
    | _ => simp at hpin
  | _ => rw [hty] at hpin; cases hpin

private theorem natBinBool_infer (bk : BaseKit env) {r : Role}
    (hm : (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames)
    (hcmp : (.role r : Core.KKey) = Ix.Kernel.natBeqName ∨ (.role r : Core.KKey) = Ix.Kernel.natBleName) :
    ∃ mb1 mb2, Infer env .full 0 (.const (.role r) [])
      (.forallE BaseKit.natT (.forallE BaseKit.natT BaseKit.boolT mb2) mb1) := by
  obtain ⟨cv, v, hint, hf, hlp, hpin⟩ := RoleOps.natOpStoredOk_inv (bk.natOpsOk r hm)
  have hnePred : (.role r : Core.KKey) ≠ Ix.Kernel.natPredName := by
    rcases hcmp with h | h <;> rw [h] <;> decide
  unfold Ix.Kernel.natOpTyPinned at hpin
  simp only [hnePred, ↓reduceIte] at hpin
  cases hty : cv.type with
  | forallE dom rest mb1 =>
    rw [hty] at hpin
    cases rest with
    | forallE dom2 body mb2 =>
      have hor : ((.role r : Core.KKey) = Ix.Kernel.natBeqName || (.role r : Core.KKey) = Ix.Kernel.natBleName) = true := by
        rcases hcmp with h | h <;> simp [h]
      simp only [Ix.Kernel.natOpCod, hor, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hpin
      obtain ⟨⟨rfl, rfl⟩, rfl, -⟩ := hpin
      refine ⟨mb1, mb2, ?_⟩
      have h1 := Infer.const (g := .full) (d := 0) (ci := .defnInfo cv v hint) hf rfl (us := [])
        (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlp])
      simpa [Ix.Kernel.ConstantInfo.toConstantVal, hlp, hty, Ix.Kernel.Expr.instantiateLevelParams,
        substPW_nil] using h1
    | _ => simp at hpin
  | _ => rw [hty] at hpin; cases hpin

theorem specNumGo_closed : ∀ (fuel n : Nat), TermClosed (Ix.Kernel.specNumGo fuel n)
  | 0, _ => .const _ _
  | fuel + 1, n => by
    simp only [Ix.Kernel.specNumGo]
    by_cases h0 : (n == 0) = true
    · simp only [h0, ↓reduceIte]; exact .const _ _
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (n % 2 == 0) = true
      · simp only [he, ↓reduceIte]
        exact ((TermClosed.const _ _).app ⟨by decide, by decide⟩).app (specNumGo_closed fuel (n / 2))
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact (TermClosed.const _ _).app (specNumGo_closed fuel (n - 1))

theorem specNumGo_infer (bk : BaseKit env) {mb1 mb2 : Ix.Kernel.BinderMeta}
    (hMul : Infer env .full 0 (.const (.role .natMul) [])
      (.forallE BaseKit.natT (.forallE BaseKit.natT BaseKit.natT mb2) mb1)) :
    ∀ (fuel n : Nat), Infer env .full 0 (Ix.Kernel.specNumGo fuel n) BaseKit.natT
  | 0, _ => bk.natZeroAt.wInfer
  | fuel + 1, n => by
    simp only [Ix.Kernel.specNumGo]
    by_cases h0 : (n == 0) = true
    · simp only [h0, ↓reduceIte]; exact bk.natZeroAt.wInfer
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (n % 2 == 0) = true
      · simp only [he, ↓reduceIte]
        have hTwo := (bk.natSuccApp (bk.natSuccApp bk.natZeroAt)).wInfer
        have h1 := Infer.app hMul .refl hTwo .refl
        exact Infer.app h1 .refl (specNumGo_infer bk hMul fuel (n / 2)) .refl
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact Infer.app bk.natSuccAt.wInfer .refl (specNumGo_infer bk hMul fuel (n - 1)) .refl

theorem specNumGo_lamPw : ∀ (fuel n : Nat), (Ix.Kernel.specNumGo (md := .anon) fuel n).lamPw = none
  | 0, _ => rfl
  | fuel + 1, n => by
    simp only [Ix.Kernel.specNumGo]
    by_cases h0 : (n == 0) = true
    · simp only [h0, ↓reduceIte]; rfl
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (n % 2 == 0) = true
      · simp only [he, ↓reduceIte]; rfl
      · simp only [he, Bool.false_eq_true, ↓reduceIte]; rfl

abbrev specNumGo_closedAt (bk : BaseKit env) {mb1 mb2 : Ix.Kernel.BinderMeta}
    (hMul : Infer env .full 0 (.const (.role .natMul) [])
      (.forallE BaseKit.natT (.forallE BaseKit.natT BaseKit.natT mb2) mb1))
    (fuel n : Nat) : ClosedAt env (Ix.Kernel.specNumGo fuel n) BaseKit.natT :=
  .ofInfer (specNumGo_closed fuel n) (specNumGo_infer bk hMul fuel n) (specNumGo_lamPw fuel n)

theorem specNum_red (bk : BaseKit env) {n : Nat} (h : specNumVal 64 n = n) :
    Red env 0 (Ix.Kernel.specNum n) (.lit (.natVal n)) := by
  simpa [Ix.Kernel.specNum, h] using specNumGo_red bk 64 n

end SpecNum

/-! ## `StrKit`: typing kit for `String`, `Char`, `List Char`, and the 6 accelerated roles -/

section StrKitSec

variable {env : Ix.Kernel.Env .anon}

abbrev stringT : KExpr := .const (.role .string) []
abbrev charT : KExpr := .const (.role .char) []
abbrev charListT : KExpr := .app (.const (.role .list) [.zero]) charT
abbrev charOfNatE : KExpr := .const (.role .charOfNat) []
abbrev listNilCharE : KExpr := .app (.const (.role .listNil) [.zero]) charT
abbrev listConsCharE : KExpr := .app (.const (.role .listCons) [.zero]) charT
abbrev stringOfListE : KExpr := .const (.role .stringOfList) []

def charExpr (c : Char) : KExpr := .app charOfNatE (.lit (.natVal c.toNat))

def charListExpr : List Char → KExpr
  | [] => listNilCharE
  | c :: cs => .app (.app listConsCharE (charExpr c)) (charListExpr cs)

theorem strLitToConstructor_eq_charListExpr (s : String) :
    Ix.Kernel.strLitToConstructor (md := .anon) s = .app stringOfListE (charListExpr s.toList) := by
  unfold Ix.Kernel.strLitToConstructor
  congr 1
  induction s.toList with
  | nil => rfl
  | cons c cs ih => simp [charListExpr, charExpr, ih, listConsCharE, charOfNatE, charT]

private theorem isTowerEntry_false_of_role {ci : Ix.Kernel.ConstantInfo .anon} {r : Role}
    (hf : env.find? (.role r) = some ci) : ci.isTowerEntry = false := by
  have hnm : ci.name = .role r := by
    have h1 := List.find?_some (p := fun c : Ix.Kernel.ConstantInfo .anon => c.name == .role r) hf
    exact beq_iff_eq.mp h1
  cases ci with
  | projInfo tbl =>
    simp [Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal,
      Ix.Kernel.projTableName, Ix.Kernel.auxKey] at hnm
  | _ => rfl

/-- Extract the seven literal-support typing facts directly from `strLitSupported env = true`. -/
structure StrLitKit (env : Ix.Kernel.Env .anon) where
  bk : BaseKit env
  strLit : Ix.Kernel.strLitSupported env = true
  stringStored : ∃ ci, env.find? (.role .string) = some ci
  charOfNatStored : ∃ ci, env.find? (.role .charOfNat) = some ci
  stringInfer : Infer env .full 0 stringT (.sort (.succ .zero))
  charInfer : Infer env .full 0 charT (.sort (.succ .zero))
  mbCon : Ix.Kernel.BinderMeta
  charOfNatInfer : Infer env .full 0 charOfNatE (.forallE BaseKit.natT charT mbCon)
  mbL : Ix.Kernel.BinderMeta
  list0Infer : Infer env .full 0 (.const (.role .list) [.zero])
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)) mbL)
  mbN : Ix.Kernel.BinderMeta
  listNil0Infer : Infer env .full 0 (.const (.role .listNil) [.zero])
    (.forallE (.sort (.succ .zero)) (.app (.const (.role .list) [.zero]) (.bvar 0)) mbN)
  mbC1 : Ix.Kernel.BinderMeta
  mbC2 : Ix.Kernel.BinderMeta
  mbC3 : Ix.Kernel.BinderMeta
  listCons0Infer : Infer env .full 0 (.const (.role .listCons) [.zero])
    (.forallE (.sort (.succ .zero))
      (.forallE (.bvar 0)
        (.forallE (.app (.const (.role .list) [.zero]) (.bvar 1))
          (.app (.const (.role .list) [.zero]) (.bvar 2)) mbC3) mbC2) mbC1)
  mbSol : Ix.Kernel.BinderMeta
  stringOfListInfer : Infer env .full 0 stringOfListE (.forallE charListT stringT mbSol)

theorem strLitKit_of (bk : BaseKit env) (hsup : Ix.Kernel.strLitSupported env = true) :
    Nonempty (StrLitKit env) := by
  have hparts :
      Ix.Kernel.stringTyOk (env.find? Ix.Kernel.stringName) = true ∧
      Ix.Kernel.stringOfListTyOk (env.find? Ix.Kernel.stringOfListName) = true ∧
      Ix.Kernel.listTyOk (env.find? Ix.Kernel.listName) = true ∧
      Ix.Kernel.listNilTyOk (env.find? Ix.Kernel.listNilName) = true ∧
      Ix.Kernel.listConsTyOk (env.find? Ix.Kernel.listConsName) = true ∧
      Ix.Kernel.charTyOk (env.find? Ix.Kernel.charName) = true ∧
      Ix.Kernel.charOfNatTyOk (env.find? Ix.Kernel.charOfNatName) = true := by
    unfold Ix.Kernel.strLitSupported at hsup
    simp only [Bool.and_eq_true] at hsup
    exact ⟨hsup.1.1.1.1.1.1.2, hsup.1.1.1.1.1.2, hsup.1.1.1.1.2, hsup.1.1.1.2,
      hsup.1.1.2, hsup.1.2, hsup.2⟩
  obtain ⟨hStrOk, hSolOk, hListOk, hNilOk, hConsOk, hCharOk, hConOk⟩ := hparts
  -- String
  obtain ⟨ciStr, hfStr⟩ : ∃ ci, env.find? Ix.Kernel.stringName = some ci := by
    cases h : env.find? Ix.Kernel.stringName with
    | none => simp [h, Ix.Kernel.stringTyOk] at hStrOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfStr] at hStrOk
  simp only [Ix.Kernel.stringTyOk, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hStrOk
  have hStrInf : Infer env .full 0 stringT (.sort (.succ .zero)) := by
    have h1 := Infer.const (g := .full) (d := 0) hfStr (isTowerEntry_false_of_role hfStr)
      (us := []) (by simp [hStrOk.1])
    simpa [hStrOk.1, hStrOk.2, Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go] using h1
  -- Char
  obtain ⟨ciChar, hfChar⟩ : ∃ ci, env.find? Ix.Kernel.charName = some ci := by
    cases h : env.find? Ix.Kernel.charName with
    | none => simp [h, Ix.Kernel.charTyOk] at hCharOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfChar] at hCharOk
  simp only [Ix.Kernel.charTyOk, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hCharOk
  have hCharInf : Infer env .full 0 charT (.sort (.succ .zero)) := by
    have h1 := Infer.const (g := .full) (d := 0) hfChar (isTowerEntry_false_of_role hfChar)
      (us := []) (by simp [hCharOk.1])
    simpa [hCharOk.1, hCharOk.2, Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go] using h1
  -- Char.ofNat
  obtain ⟨ciCon, hfCon⟩ : ∃ ci, env.find? Ix.Kernel.charOfNatName = some ci := by
    cases h : env.find? Ix.Kernel.charOfNatName with
    | none => simp [h, Ix.Kernel.charOfNatTyOk] at hConOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfCon] at hConOk
  simp only [Ix.Kernel.charOfNatTyOk, Bool.and_eq_true, List.isEmpty_iff] at hConOk
  obtain ⟨mbCon, hConTy⟩ : ∃ mb, ciCon.toConstantVal.type = .forallE BaseKit.natT charT mb := by
    cases ht : ciCon.toConstantVal.type with
    | forallE d b mb =>
      rw [ht] at hConOk
      cases d with
      | const c1 us1 =>
        cases us1 with
        | nil =>
          cases b with
          | const c2 us2 =>
            cases us2 with
            | nil =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hConOk
              exact ⟨mb, by rw [hConOk.2.1, hConOk.2.2]⟩
            | cons _ _ => simp at hConOk
          | _ => simp at hConOk
        | cons _ _ => simp at hConOk
      | _ => simp at hConOk
    | _ => rw [ht] at hConOk; simp at hConOk
  have hConInf : Infer env .full 0 charOfNatE (.forallE BaseKit.natT charT mbCon) := by
    have h1 := Infer.const (g := .full) (d := 0) hfCon (isTowerEntry_false_of_role hfCon)
      (us := []) (by simp [hConOk.1])
    rw [hConOk.1, hConTy] at h1
    simpa [Ix.Kernel.Expr.instantiateLevelParams, substPW_nil] using h1
  -- List.{0}
  obtain ⟨ciList, hfList⟩ : ∃ ci, env.find? Ix.Kernel.listName = some ci := by
    cases h : env.find? Ix.Kernel.listName with
    | none => simp [h, Ix.Kernel.listTyOk] at hListOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfList] at hListOk
  obtain ⟨pL, mbL, hpL, hListTy⟩ : ∃ p mb, ciList.toConstantVal.levelParams = [p] ∧
      ciList.toConstantVal.type = .forallE (.sort (.succ (.param p))) (.sort (.succ (.param p))) mb := by
    simp only [Ix.Kernel.listTyOk] at hListOk
    cases hlp : ciList.toConstantVal.levelParams with
    | nil => rw [hlp] at hListOk; simp at hListOk
    | cons p rest =>
      cases rest with
      | cons _ _ => rw [hlp] at hListOk; simp at hListOk
      | nil =>
        rw [hlp] at hListOk
        cases ht : ciList.toConstantVal.type with
        | forallE d b mb =>
          rw [ht] at hListOk
          cases d with
          | sort u1 =>
            cases b with
            | sort u2 =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hListOk
              exact ⟨p, mb, rfl, by rw [hListOk.1, hListOk.2]⟩
            | _ => simp at hListOk
          | _ => simp at hListOk
        | _ => rw [ht] at hListOk; simp at hListOk
  let mbL' : Ix.Kernel.BinderMeta := { pw := Ix.Kernel.Level.substPW [pL] [.zero] mbL.pw, display := mbL.display }
  have hList0Inf : Infer env .full 0 (.const (.role .list) [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)) mbL') := by
    have h1 := Infer.const (g := .full) (d := 0) hfList (isTowerEntry_false_of_role hfList)
      (us := [.zero]) (by simp [hpL])
    rw [hpL, hListTy] at h1
    simpa [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go, mbL'] using h1
  -- List.nil.{0}
  obtain ⟨ciNil, hfNil⟩ : ∃ ci, env.find? Ix.Kernel.listNilName = some ci := by
    cases h : env.find? Ix.Kernel.listNilName with
    | none => simp [h, Ix.Kernel.listNilTyOk] at hNilOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfNil] at hNilOk
  obtain ⟨pN, mbN, hpN, hNilTy⟩ : ∃ p mb, ciNil.toConstantVal.levelParams = [p] ∧
      ciNil.toConstantVal.type = .forallE (.sort (.succ (.param p)))
        (.app (.const Ix.Kernel.listName [.param p]) (.bvar 0)) mb := by
    simp only [Ix.Kernel.listNilTyOk] at hNilOk
    cases hlp : ciNil.toConstantVal.levelParams with
    | nil => rw [hlp] at hNilOk; simp at hNilOk
    | cons p rest =>
      cases rest with
      | cons _ _ => rw [hlp] at hNilOk; simp at hNilOk
      | nil =>
        rw [hlp] at hNilOk
        cases ht : ciNil.toConstantVal.type with
        | forallE d b mb =>
          rw [ht] at hNilOk
          cases d with
          | sort u1 =>
            cases b with
            | app f a =>
              cases f with
              | const l1 us1 =>
                cases a with
                | bvar idx =>
                  cases idx with
                  | zero =>
                    simp only [Bool.and_eq_true, beq_iff_eq] at hNilOk
                    exact ⟨p, mb, rfl, by rw [hNilOk.1.1, hNilOk.1.2, hNilOk.2]⟩
                  | succ _ => simp at hNilOk
                | _ => simp at hNilOk
              | _ => simp at hNilOk
            | _ => simp at hNilOk
          | _ => simp at hNilOk
        | _ => rw [ht] at hNilOk; simp at hNilOk
  let mbN' : Ix.Kernel.BinderMeta := { pw := Ix.Kernel.Level.substPW [pN] [.zero] mbN.pw, display := mbN.display }
  have hNil0Inf : Infer env .full 0 (.const (.role .listNil) [.zero])
      (.forallE (.sort (.succ .zero)) (.app (.const (.role .list) [.zero]) (.bvar 0)) mbN') := by
    have h1 := Infer.const (g := .full) (d := 0) hfNil (isTowerEntry_false_of_role hfNil)
      (us := [.zero]) (by simp [hpN])
    rw [hpN, hNilTy] at h1
    simpa [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go, Ix.Kernel.listName, mbN'] using h1
  -- List.cons.{0}
  obtain ⟨ciCons, hfCons⟩ : ∃ ci, env.find? Ix.Kernel.listConsName = some ci := by
    cases h : env.find? Ix.Kernel.listConsName with
    | none => simp [h, Ix.Kernel.listConsTyOk] at hConsOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfCons] at hConsOk
  obtain ⟨pC, mb1, mb2, mb3, hpC, hConsTy⟩ : ∃ p mb1 mb2 mb3,
      ciCons.toConstantVal.levelParams = [p] ∧
      ciCons.toConstantVal.type =
        .forallE (.sort (.succ (.param p)))
          (.forallE (.bvar 0)
            (.forallE (.app (.const Ix.Kernel.listName [.param p]) (.bvar 1))
              (.app (.const Ix.Kernel.listName [.param p]) (.bvar 2)) mb3) mb2) mb1 := by
    simp only [Ix.Kernel.listConsTyOk] at hConsOk
    cases hlp : ciCons.toConstantVal.levelParams with
    | nil => rw [hlp] at hConsOk; simp at hConsOk
    | cons p rest =>
      cases rest with
      | cons _ _ => rw [hlp] at hConsOk; simp at hConsOk
      | nil =>
        rw [hlp] at hConsOk
        cases ht : ciCons.toConstantVal.type with
        | forallE d1 b1 mb1 =>
          rw [ht] at hConsOk
          cases d1 with
          | sort u1 =>
            cases b1 with
            | forallE d2 b2 mb2 =>
              cases d2 with
              | bvar j0 =>
                cases j0 with
                | zero =>
                  cases b2 with
                  | forallE d3 b3 mb3 =>
                    cases d3 with
                    | app f1 a1 =>
                      cases f1 with
                      | const l1 us1 =>
                        cases a1 with
                        | bvar j1 =>
                          cases j1 with
                          | succ j1' =>
                            cases j1' with
                            | zero =>
                              cases b3 with
                              | app f2 a2 =>
                                cases f2 with
                                | const l2 us2 =>
                                  cases a2 with
                                  | bvar j2 =>
                                    cases j2 with
                                    | succ j2' =>
                                      cases j2' with
                                      | succ j2'' =>
                                        cases j2'' with
                                        | zero =>
                                          simp only [Bool.and_eq_true, beq_iff_eq] at hConsOk
                                          exact ⟨p, mb1, mb2, mb3, rfl, by
                                            rw [hConsOk.1.1.1.1, hConsOk.1.1.1.2, hConsOk.1.1.2,
                                              hConsOk.1.2, hConsOk.2]⟩
                                        | succ _ => simp at hConsOk
                                      | zero => simp at hConsOk
                                    | zero => simp at hConsOk
                                  | _ => simp at hConsOk
                                | _ => simp at hConsOk
                              | _ => simp at hConsOk
                            | succ _ => simp at hConsOk
                          | zero => simp at hConsOk
                        | _ => simp at hConsOk
                      | _ => simp at hConsOk
                    | _ => simp at hConsOk
                  | _ => simp at hConsOk
                | succ _ => simp at hConsOk
              | _ => simp at hConsOk
            | _ => simp at hConsOk
          | _ => simp at hConsOk
        | _ => rw [ht] at hConsOk; simp at hConsOk
  let mbC1' : Ix.Kernel.BinderMeta := { pw := Ix.Kernel.Level.substPW [pC] [.zero] mb1.pw, display := mb1.display }
  let mbC2' : Ix.Kernel.BinderMeta := { pw := Ix.Kernel.Level.substPW [pC] [.zero] mb2.pw, display := mb2.display }
  let mbC3' : Ix.Kernel.BinderMeta := { pw := Ix.Kernel.Level.substPW [pC] [.zero] mb3.pw, display := mb3.display }
  have hCons0Inf : Infer env .full 0 (.const (.role .listCons) [.zero])
      (.forallE (.sort (.succ .zero))
        (.forallE (.bvar 0)
          (.forallE (.app (.const (.role .list) [.zero]) (.bvar 1))
            (.app (.const (.role .list) [.zero]) (.bvar 2)) mbC3') mbC2') mbC1') := by
    have h1 := Infer.const (g := .full) (d := 0) hfCons (isTowerEntry_false_of_role hfCons)
      (us := [.zero]) (by simp [hpC])
    rw [hpC, hConsTy] at h1
    simpa [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go, Ix.Kernel.listName, mbC1', mbC2', mbC3'] using h1
  -- String.ofList
  obtain ⟨ciSol, hfSol⟩ : ∃ ci, env.find? Ix.Kernel.stringOfListName = some ci := by
    cases h : env.find? Ix.Kernel.stringOfListName with
    | none => simp [h, Ix.Kernel.stringOfListTyOk] at hSolOk
    | some ci => exact ⟨ci, rfl⟩
  rw [hfSol] at hSolOk
  simp only [Ix.Kernel.stringOfListTyOk, Bool.and_eq_true, List.isEmpty_iff] at hSolOk
  obtain ⟨mbSol, hSolTy⟩ : ∃ mb, ciSol.toConstantVal.type = .forallE charListT stringT mb := by
    cases ht : ciSol.toConstantVal.type with
    | forallE d b mb =>
      rw [ht] at hSolOk
      cases d with
      | app f a =>
        cases f with
        | const l1 us1 =>
          cases a with
          | const c1 us2 =>
            cases us2 with
            | nil =>
              cases b with
              | const c2 us3 =>
                cases us3 with
                | nil =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hSolOk
                  exact ⟨mb, by
                    rw [hSolOk.2.1.1.1, hSolOk.2.1.1.2, hSolOk.2.1.2, hSolOk.2.2]⟩
                | cons _ _ => simp at hSolOk
              | _ => simp at hSolOk
            | cons _ _ => simp at hSolOk
          | _ => simp at hSolOk
        | _ => simp at hSolOk
      | _ => simp at hSolOk
    | _ => rw [ht] at hSolOk; simp at hSolOk
  have hSolInf : Infer env .full 0 stringOfListE (.forallE charListT stringT mbSol) := by
    have h1 := Infer.const (g := .full) (d := 0) hfSol (isTowerEntry_false_of_role hfSol)
      (us := []) (by simp [hSolOk.1])
    rw [hSolOk.1, hSolTy] at h1
    simpa [Ix.Kernel.Expr.instantiateLevelParams, substPW_nil, Ix.Kernel.Level.subst,
      Ix.Kernel.Level.subst.go] using h1
  exact ⟨{
    bk := bk
    strLit := hsup
    stringStored := ⟨ciStr, hfStr⟩
    charOfNatStored := ⟨ciCon, hfCon⟩
    stringInfer := hStrInf
    charInfer := hCharInf
    mbCon := mbCon
    charOfNatInfer := hConInf
    mbL := mbL'
    list0Infer := hList0Inf
    mbN := mbN'
    listNil0Infer := hNil0Inf
    mbC1 := mbC1'
    mbC2 := mbC2'
    mbC3 := mbC3'
    listCons0Infer := hCons0Inf
    mbSol := mbSol
    stringOfListInfer := hSolInf }⟩

namespace StrLitKit

variable (sl : StrLitKit env)
include sl

def stringType : ClosedType env stringT (.succ .zero) :=
  ⟨.const _ _, .sort (.succ .zero), sl.stringInfer, .refl⟩

def charType : ClosedType env charT (.succ .zero) :=
  ⟨.const _ _, .sort (.succ .zero), sl.charInfer, .refl⟩

def charAtType : ClosedAt env charT (.sort (.succ .zero)) :=
  .ofInfer (.const _ _) sl.charInfer

def charOfNatAt : ClosedAt env charOfNatE (.forallE BaseKit.natT charT sl.mbCon) :=
  .ofInfer (.const _ _) sl.charOfNatInfer

def list0At : ClosedAt env (.const (.role .list) [.zero])
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)) sl.mbL) :=
  .ofInfer (.const _ _) sl.list0Infer

def listNil0At : ClosedAt env (.const (.role .listNil) [.zero])
    (.forallE (.sort (.succ .zero)) (.app (.const (.role .list) [.zero]) (.bvar 0)) sl.mbN) :=
  .ofInfer (.const _ _) sl.listNil0Infer

def listCons0At : ClosedAt env (.const (.role .listCons) [.zero])
    (.forallE (.sort (.succ .zero))
      (.forallE (.bvar 0)
        (.forallE (.app (.const (.role .list) [.zero]) (.bvar 1))
          (.app (.const (.role .list) [.zero]) (.bvar 2)) sl.mbC3) sl.mbC2) sl.mbC1) :=
  .ofInfer (.const _ _) sl.listCons0Infer

def listNilCharAt : ClosedAt env listNilCharE charListT :=
  sl.listNil0At.app_dep_raw sl.charAtType .refl

def listConsCharAt : ClosedAt env listConsCharE (.forallE charT (.forallE charListT charListT sl.mbC3) sl.mbC2) :=
  sl.listCons0At.app_dep_raw sl.charAtType .refl

def stringOfListAt : ClosedAt env stringOfListE (.forallE charListT stringT sl.mbSol) :=
  .ofInfer (.const _ _) sl.stringOfListInfer

def charListType : ClosedType env charListT (.succ .zero) :=
  ⟨TermClosed.app (.const _ _) (.const _ _), .sort (.succ .zero),
    (sl.list0At.app_nondep sl.charAtType rfl).wInfer, .refl⟩

def charAt (c : Char) : ClosedAt env (charExpr c) charT :=
  sl.charOfNatAt.app_nondep (sl.bk.natLitAt c.toNat) rfl

def charListAt : (cs : List Char) → ClosedAt env (charListExpr cs) charListT
  | [] => sl.listNilCharAt
  | c :: cs => (sl.listConsCharAt.app_nondep (sl.charAt c) rfl).app_nondep (charListAt cs) rfl

@[simp] theorem charAtType_w : sl.charAtType.witness = charT := rfl
@[simp] theorem charOfNatAt_w : sl.charOfNatAt.witness = charOfNatE := rfl
@[simp] theorem list0At_w : sl.list0At.witness = .const (.role .list) [.zero] := rfl
@[simp] theorem listNil0At_w : sl.listNil0At.witness = .const (.role .listNil) [.zero] := rfl
@[simp] theorem listCons0At_w : sl.listCons0At.witness = .const (.role .listCons) [.zero] := rfl
@[simp] theorem listNilCharAt_w : sl.listNilCharAt.witness = listNilCharE := rfl
@[simp] theorem listConsCharAt_w : sl.listConsCharAt.witness = listConsCharE := rfl
@[simp] theorem stringOfListAt_w : sl.stringOfListAt.witness = stringOfListE := rfl
@[simp] theorem charAt_w (c : Char) : (sl.charAt c).witness = charExpr c := rfl
@[simp] theorem charListAt_w : ∀ cs, (sl.charListAt cs).witness = charListExpr cs
  | [] => rfl
  | c :: cs => by
    simp [charListAt, charListExpr, ClosedAt.app_nondep, ClosedAt.app_nondep_de, charListAt_w cs]

def strOfListApp {l : KExpr} (hl : ClosedAt env l charListT) :
    ClosedAt env (.app stringOfListE l) stringT :=
  sl.stringOfListAt.app_nondep hl rfl

def strLitAt (s : String) : ClosedAt env (.lit (.strVal s)) stringT :=
  .ofInfer (.lit _) (.strLit sl.strLit)

@[simp] theorem strLitAt_w (s : String) : (sl.strLitAt s).witness = .lit (.strVal s) := rfl

def stringType_open (d : Nat) (Γ : Nat → KExpr) :
    OpenType env d Γ stringT stringT (.succ .zero) :=
  OpenType.ofClosed sl.bk.storeClosed sl.stringType

def charType_open (d : Nat) (Γ : Nat → KExpr) :
    OpenType env d Γ charT charT (.succ .zero) :=
  OpenType.ofClosed sl.bk.storeClosed sl.charType

def charListType_open (d : Nat) (Γ : Nat → KExpr) :
    OpenType env d Γ charListT charListT (.succ .zero) :=
  OpenType.ofClosed sl.bk.storeClosed sl.charListType

end StrLitKit

/-- Full typing kit for the six accelerated `String`/`Char` equation roles. -/
structure StrKit (env : Ix.Kernel.Env .anon)
    (wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd wBA : KExpr) where
  ik : IntKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd
  sl : StrLitKit env
  baAt : ClosedAt env (.const (.role .byteArray) []) (.sort (.succ .zero))
  baW : baAt.witness = wBA
  wBA_cl : TermClosed wBA
  baEmptyAt : ClosedAt env (.const (.role .byteArrayEmpty) []) wBA
  charUtf8SizeAt : ClosedAt env (.const (.role .charUtf8Size) [])
    (.forallE charT BaseKit.natT { pw := .never })
  strUtf8ByteSizeAt : ClosedAt env (.const (.role .stringUtf8ByteSize) [])
    (.forallE stringT BaseKit.natT { pw := .never })
  strBackAt : ClosedAt env (.const (.role .stringBack) [])
    (.forallE stringT charT { pw := .never })
  strToByteArrayAt : ClosedAt env (.const (.role .stringToByteArray) [])
    (.forallE stringT wBA { pw := .never })
  strDecEqAt : ClosedAt env (.const (.role .stringDecEq) [])
    (.forallE stringT
      ((Ix.Kernel.Expr.forallE stringT
        ((Ix.Kernel.Expr.app wDec
          (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT)
            (.fvar 0 stringT)) (.fvar 1 stringT))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  strDecEqTy_nf :
    (Ix.Kernel.Expr.forallE stringT
      ((Ix.Kernel.Expr.forallE stringT
        ((Ix.Kernel.Expr.app wDec
          (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT)
            (.fvar 0 stringT)) (.fvar 1 stringT))).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  listAppend0At : ClosedAt env (.const (.role .listAppend) [.zero])
    (.forallE (.sort (.succ .zero))
      ((Ix.Kernel.Expr.forallE (.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero))))
        ((Ix.Kernel.Expr.forallE (.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero))))
          ((Ix.Kernel.Expr.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero)))).abstract1 2)
          { pw := .never }).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  strAppendAt : ClosedAt env (.const (.role .stringAppend) [])
    (.forallE stringT (.forallE stringT stringT { pw := .never }) { pw := .never })

theorem strKit_exists (bk : BaseKit env) (hsup : Ix.Kernel.strLitSupported env = true)
    (hs : Shapes (· < 77) env) :
    ∃ wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd wBA,
      Nonempty (StrKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd wBA) := by
  obtain ⟨wDec, wNot, wDecide, wInt, wIntLe, wIntOfNat, wIntAdd, ⟨ik⟩⟩ := intKit_exists bk hs
  obtain ⟨sl⟩ := strLitKit_of bk hsup
  have hsc := bk.storeClosed
  have hwf := bk.wf
  -- ByteArray & ByteArray.empty
  have baAt : ClosedAt env (.const (.role .byteArray) []) (.sort (.succ .zero)) :=
    ClosedAt.ofRole0 hsc
      (roleExact_anchor_of hs .stringToByteArray .byteArray (by decide) (by decide) (by decide))
      (by decide) rfl (ClosedType.sort env (.succ .zero))
  let wBA := baAt.witness
  have hwBACl : TermClosed wBA := baAt.wClosed
  have hBAType : ClosedType env wBA (.succ .zero) := ⟨hwBACl, .sort (.succ .zero), baAt.wInfer, .refl⟩
  have baEmptyAt : ClosedAt env (.const (.role .byteArrayEmpty) []) wBA :=
    ClosedAt.ofRole0_open hsc
      (roleExact_anchor_of hs .stringToByteArray .byteArrayEmpty (by decide) (by decide) (by decide))
      (by decide) rfl (OpenType.ofOpenAt (OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) baAt rfl))
  -- Char.utf8Size : Char → Nat
  have charUtf8SizeAt : ClosedAt env (.const (.role .charUtf8Size) [])
      (.forallE charT BaseKit.natT { pw := .never }) :=
    ClosedAt.ofRole0 hsc (roleExact_eqns hs .charUtf8Size (by decide) (by decide)) (by decide) rfl
      (ClosedType.forall_nondep hsc sl.charType bk.natType)
  -- String.utf8ByteSize : String → Nat
  have strUtf8ByteSizeAt : ClosedAt env (.const (.role .stringUtf8ByteSize) [])
      (.forallE stringT BaseKit.natT { pw := .never }) :=
    ClosedAt.ofRole0 hsc (roleExact_eqns hs .stringUtf8ByteSize (by decide) (by decide)) (by decide) rfl
      (ClosedType.forall_nondep hsc sl.stringType bk.natType)
  -- String.back : String → Char
  have strBackAt : ClosedAt env (.const (.role .stringBack) [])
      (.forallE stringT charT { pw := .never }) :=
    ClosedAt.ofRole0 hsc (roleExact_eqns hs .stringBack (by decide) (by decide)) (by decide) rfl
      (ClosedType.forall_nondep hsc sl.stringType sl.charType)
  -- String.toByteArray : String → ByteArray
  have hBAPi1 : PiRed env 1 wBA (.const (.role .byteArray) []) := by
    have h := Red.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := 1) baAt.wRed
    rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar hwBACl.1,
        Ix.Kernel.Expr.renFV_of_not_hasFvar rfl] at h
    exact .ofRed h
  have hStrBATy := ClosedType.forall_nondep hsc sl.stringType hBAType
  have hStrBAPi : PiRed env 0
      (.forallE stringT wBA { pw := .never })
      (.forallE stringT (.const (.role .byteArray) []) { pw := .never }) :=
    .forallE (by simp [Ix.Kernel.Expr.wscopedB]) (.ofRed .refl)
      (by simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self wBA hwBACl.2] using hBAPi1)
  have strToByteArrayAt : ClosedAt env (.const (.role .stringToByteArray) [])
      (.forallE stringT wBA { pw := .never }) :=
    ClosedAt.ofRole0_de hsc (roleExact_eqns hs .stringToByteArray (by decide) (by decide))
      (by decide) rfl ⟨rfl, rfl⟩ hStrBAPi hStrBATy
  -- String.decEq : (a b : String) → Decidable (Eq.{1} String a b)
  have strDecEqO : OpenType env 0 Γ₀
      (.forallE stringT
        (.forallE stringT
          (.app (.const (.role .decidable) [])
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT) (.bvar 1)) (.bvar 0)))
          { pw := .never })
        { pw := .never })
      (.forallE stringT
        ((Ix.Kernel.Expr.forallE stringT
          ((Ix.Kernel.Expr.app wDec
            (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT)
              (.fvar 0 stringT)) (.fvar 1 stringT))).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (sl.stringType_open 0 Γ₀) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (sl.stringType_open 1 _) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    have hEqO : OpenAt env 2 (fvarUpdate (fvarUpdate Γ₀ 0 stringT) 1 stringT)
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT) (.fvar 0 stringT)) (.fvar 1 stringT))
        (.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT) (.fvar 0 stringT)) (.fvar 1 stringT))
        (.sort .zero) :=
      OpenAt.eq bk.eqStored (sl.stringType_open 2 _)
        (OpenAt.fvar (d := 2) (idx := 0) (by omega)) .refl
        (OpenAt.fvar (d := 2) (idx := 1) (by omega)) .refl
    have hDec2 := (OpenAt.ofClosed hsc ik.decAt rfl).app_nondep hEqO .refl rfl
    rw [ik.decW] at hDec2
    exact OpenType.ofOpenAt hDec2
  have strDecEqAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .stringDecEq (by decide) (by decide)) (by decide) rfl strDecEqO
  -- List.append.{0} : ∀ (α : Type 0), List.{0} α → List.{0} α → List.{0} α
  have listAppend0O : OpenType env 0 Γ₀
      (.forallE (.sort (.succ .zero))
        (.forallE (.app (.const (.role .list) [.zero]) (.bvar 0))
          (.forallE (.app (.const (.role .list) [.zero]) (.bvar 1))
            (.app (.const (.role .list) [.zero]) (.bvar 2)) { pw := .never })
          { pw := .never })
        { pw := .never })
      (.forallE (.sort (.succ .zero))
        ((Ix.Kernel.Expr.forallE (.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero))))
          ((Ix.Kernel.Expr.forallE (.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero))))
            ((Ix.Kernel.Expr.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero)))).abstract1 2)
            { pw := .never }).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) := by
    have hListApp : ∀ (d : Nat) (Γ : Nat → KExpr), 0 < d → Γ 0 = .sort (.succ .zero) →
        OpenType env d Γ
          (.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero))))
          (.app (.const (.role .list) [.zero]) (.fvar 0 (.sort (.succ .zero)))) (.succ .zero) := by
      intro d Γ hd hΓ0
      have hf0 : OpenAt env d Γ (.fvar 0 (.sort (.succ .zero))) (.fvar 0 (.sort (.succ .zero)))
          (.sort (.succ .zero)) := by
        have h := OpenAt.fvar (env := env) (d := d) (idx := 0) (Γ := Γ) hd
        rwa [hΓ0] at h
      exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc sl.list0At rfl).app_nondep hf0 .refl rfl)
    refine OpenType.forallE (OpenType.sort (.succ .zero)) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (hListApp 1 _ (by omega) rfl) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (hListApp 2 _ (by omega) rfl) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    exact hListApp 3 _ (by omega) rfl
  have listAppend0At := ClosedAt.ofRole1_open hsc hwf
    (roleExact_eqns hs .listAppend (by decide) (by decide))
    (by decide) rfl (by decide) ⟨by decide, by decide⟩ listAppend0O
  -- String.append : String → String → String
  have strAppendAt : ClosedAt env (.const (.role .stringAppend) [])
      (.forallE stringT (.forallE stringT stringT { pw := .never }) { pw := .never }) :=
    ClosedAt.ofRole0 hsc (roleExact_eqns hs .stringAppend (by decide) (by decide)) (by decide) rfl
      (ClosedType.forall_nondep hsc sl.stringType
        (ClosedType.forall_nondep hsc sl.stringType sl.stringType))
  exact ⟨wDec, wNot, wDecide, wInt, wIntLe, wIntOfNat, wIntAdd, wBA, ⟨{
    ik := ik
    sl := sl
    baAt := baAt
    baW := rfl
    wBA_cl := hwBACl
    baEmptyAt := baEmptyAt
    charUtf8SizeAt := charUtf8SizeAt
    strUtf8ByteSizeAt := strUtf8ByteSizeAt
    strBackAt := strBackAt
    strToByteArrayAt := strToByteArrayAt
    strDecEqAt := strDecEqAt
    strDecEqTy_nf := strDecEqO.wOk.hasFvar_false
    listAppend0At := listAppend0At
    strAppendAt := strAppendAt }⟩⟩

/-! ## Deriving the six `String`/`Char` `DefEq`s inside `StrKit` -/

namespace StrKit

variable {wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd wBA : KExpr}
variable (sk : StrKit env wDec wNot wDecide wInt wIntLe wIntOfNat wIntAdd wBA)
include sk

private abbrev bk : BaseKit env := sk.sl.bk
private abbrev hs : Shapes (· < 77) env := sk.ik.shapes

def baType : ClosedType env wBA (.succ .zero) :=
  ⟨sk.wBA_cl, .sort (.succ .zero), sk.baW ▸ sk.baAt.wInfer, .refl⟩

def listAppendCharAt :
    ClosedAt env (.app (.const (.role .listAppend) [.zero]) charT)
      (.forallE charListT (.forallE charListT charListT { pw := .never }) { pw := .never }) := by
  have h := sk.listAppend0At.app_abs sk.sl.charAtType .refl (by decide)
  simpa [fvarSubst, Ix.Kernel.Expr.abstract1, StrLitKit.charAtType, charListT, charT] using h

def listAppendCharApp {xs ys : KExpr} (hxs : ClosedAt env xs charListT)
    (hys : ClosedAt env ys charListT) :
    ClosedAt env (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) xs) ys) charListT :=
  (sk.listAppendCharAt.app_nondep hxs rfl).app_nondep hys rfl

/-! ### 1. `Char.utf8Size` -/

private theorem defEq_charUtf8Size_range1 (c : Char) (hhi : c.toNat < 0x80) :
    DefEq env 0 (.app (.const (.role .charUtf8Size) []) (charExpr c)) (.lit (.natVal 1)) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .charUtf8Size (by decide) (by decide) (k := 0) rfl
  obtain ⟨_, _, hMulI⟩ := natBinNat_infer sk.bk (r := .natMul) (by decide) (by decide) (by decide)
  obtain ⟨_, _, hBleI⟩ := natBinBool_infer sk.bk (r := .natBle) (by decide) (Or.inr rfl)
  let hBle : ClosedAt env (.const (.role .natBle) []) _ := .ofInfer (.const _ _) hBleI
  have hNatO : OpenType env 0 Γ₀ BaseKit.natT BaseKit.natT (.succ .zero) :=
    OpenType.ofClosed hsc sk.bk.natType
  have hgLO : OpenAt env 1 (fvarUpdate Γ₀ 0 BaseKit.natT)
      (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.specNatOp .natBle (Ix.Kernel.specSucc (Ix.Kernel.specVar 0 BaseKit.natT))
          (Ix.Kernel.specNum 0x80)))
      (.app (.app (.const (.role .natBle) []) (.app BaseKit.natSuccE (.fvar 0 BaseKit.natT)))
        (Ix.Kernel.specNum 0x80))
      BaseKit.boolT := by
    have hf0 : OpenAt env 1 (fvarUpdate Γ₀ 0 BaseKit.natT) (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 1) (idx := 0) (by omega)
    have hsucc := (OpenAt.ofClosed hsc (d := 1) (Γ := fvarUpdate Γ₀ 0 BaseKit.natT) sk.bk.natSuccAt rfl).app_nondep hf0 .refl rfl
    have hnum := OpenAt.ofClosed hsc (d := 1) (Γ := fvarUpdate Γ₀ 0 BaseKit.natT) (specNumGo_closedAt sk.bk hMulI 64 0x80) rfl
    have hble := ((OpenAt.ofClosed hsc (d := 1) (Γ := fvarUpdate Γ₀ 0 BaseKit.natT) hBle rfl).app_nondep hsucc .refl rfl).app_nondep hnum .refl rfl
    simpa [Ix.Kernel.specNatOp, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specSucc,
      Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specVar, Ix.Kernel.specNum,
      fvarSubst, fvarSubst_of_not_hasFvar (specNumGo_closed 64 0x80).1, BaseKit.natSuccE, hBle] using hble
  let hypW := Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT)
    (.app (.app (.const (.role .natBle) []) (.app BaseKit.natSuccE (.fvar 0 BaseKit.natT)))
      (Ix.Kernel.specNum 0x80))) BaseKit.trueE
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 BaseKit.natT) 1 hypW
  have hLhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 hypW) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (.app (.const (.role .charUtf8Size) []) (.app charOfNatE (Ix.Kernel.specVar 0 BaseKit.natT)))))
      (.app sk.charUtf8SizeAt.witness (.app charOfNatE (.fvar 0 BaseKit.natT))) BaseKit.natT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hch := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.charOfNatAt rfl).app_nondep hf0 .refl rfl
    have hsz := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.charUtf8SizeAt rfl).app_nondep hch .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, charOfNatE] using hsz
  have hRhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 hypW) (fvarSubst 0 (.fvar 0 BaseKit.natT) (Ix.Kernel.specNum 1)))
      (Ix.Kernel.specNum 1) BaseKit.natT := by
    have h := OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) (specNumGo_closedAt sk.bk hMulI 64 1) rfl
    have hcl := (specNumGo_closed 64 1).1
    simpa [Ix.Kernel.specNum, fvarSubst_of_not_hasFvar hcl] using h
  have hGuard : DefEq env 0
      (fvarSubst 0 (.lit (.natVal c.toNat))
        (.app (.app (.const (.role .natBle) []) (.app BaseKit.natSuccE (.fvar 0 BaseKit.natT)))
          (Ix.Kernel.specNum 0x80)))
      BaseKit.trueE := by
    have hcl := (specNumGo_closed 64 0x80).1
    simp only [fvarSubst, fvarSubst_of_not_hasFvar hcl, ↓reduceIte, BaseKit.natSuccE, Ix.Kernel.specNum]
    have hr1 : Red env 0 (.app (.const (.role .natSucc) []) (.lit (.natVal c.toNat))) (.lit (.natVal (c.toNat + 1))) :=
      sk.bk.red_natSucc_lit c.toNat
    have hr2 : Red env 0 (Ix.Kernel.specNum 0x80) (.lit (.natVal 0x80)) := specNum_red sk.bk rfl
    have hble : Red env 0 (.app (.app (.const (.role .natBle) []) (.lit (.natVal (c.toNat + 1)))) (.lit (.natVal 0x80)))
        BaseKit.trueE :=
      sk.bk.red_natOp (r := .natBle) (by decide) (a := c.toNat + 1) (b := 0x80) (res := BaseKit.trueE) (by
        simp [Ix.Kernel.natOpResult, show c.toNat + 1 ≤ 0x80 by omega])
    exact .redL (.trans (.appFn (.appArg hr1)) (.trans (.appArg hr2) hble)) .refl
  have hDe := applyEqn1Hyp1 sk.bk hv (by decide)
    (T₀ := BaseKit.natT) (T₀w := BaseKit.natT) (Cw := BaseKit.natT)
    (gL := Ix.Kernel.specNatOp .natBle (Ix.Kernel.specSucc (Ix.Kernel.specVar 0 BaseKit.natT)) (Ix.Kernel.specNum 0x80))
    (gLw := .app (.app (.const (.role .natBle) []) (.app BaseKit.natSuccE (.fvar 0 BaseKit.natT))) (Ix.Kernel.specNum 0x80))
    (gR := BaseKit.trueE)
    (lhsW := .app sk.charUtf8SizeAt.witness (.app charOfNatE (.fvar 0 BaseKit.natT)))
    (rhsW := Ix.Kernel.specNum 1)
    (a := .lit (.natVal c.toNat))
    (lhsA := .app (.const (.role .charUtf8Size) []) (charExpr c))
    (rhsA := Ix.Kernel.specNum 1)
    rfl rfl rfl sk.bk.natType .refl rfl rfl hNatO
    (by decide) sk.bk.boolTrueAt (by decide) (by decide)
    hgLO hLhsO hRhsO
    (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar sk.charUtf8SizeAt.wClosed.1, charOfNatE])
    (fun v => fvarSubst_of_not_hasFvar (specNumGo_closed 64 1).1)
    (sk.bk.natLitAt c.toNat)
    hGuard
    (by
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.charUtf8SizeAt.wClosed.1, ↓reduceIte, charOfNatE, charExpr]
      exact .app sk.charUtf8SizeAt.defEq_witness .refl)
    (by
      simp only [Ix.Kernel.specNum, fvarSubst_of_not_hasFvar (specNumGo_closed 64 1).1]
      exact .refl)
    (sk.charUtf8SizeAt.app_nondep (sk.sl.charAt c) rfl)
    (specNumGo_closedAt sk.bk hMulI 64 1)
  exact (specNumGo_closedAt sk.bk hMulI 64 1).defEq_trans hDe (.redL (specNum_red sk.bk rfl) .refl)

private theorem defEq_charUtf8Size_range2 (c : Char) {k lo hi res : Nat}
    (hk : (eqnsOfRole .charUtf8Size)[k]? = some
      (Ix.Kernel.specCert [BaseKit.natT]
        [Ix.Kernel.specEq1 BaseKit.boolT (Ix.Kernel.specNatOp .natBle (Ix.Kernel.specNum lo) (Ix.Kernel.specVar 0 BaseKit.natT)) BaseKit.trueE,
         Ix.Kernel.specEq1 BaseKit.boolT (Ix.Kernel.specNatOp .natBle (Ix.Kernel.specSucc (Ix.Kernel.specVar 0 BaseKit.natT)) (Ix.Kernel.specNum hi)) BaseKit.trueE]
        BaseKit.natT
        (.app (.const (.role .charUtf8Size) []) (.app charOfNatE (Ix.Kernel.specVar 0 BaseKit.natT)))
        (Ix.Kernel.specNum res)))
    (hlo_val : specNumVal 64 lo = lo) (hhi_val : specNumVal 64 hi = hi)
    (hres_val : specNumVal 64 res = res)
    (hlo : lo ≤ c.toNat) (hhi : c.toNat < hi) :
    DefEq env 0 (.app (.const (.role .charUtf8Size) []) (charExpr c)) (.lit (.natVal res)) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .charUtf8Size (by decide) (by decide) hk
  obtain ⟨_, _, hMulI⟩ := natBinNat_infer sk.bk (r := .natMul) (by decide) (by decide) (by decide)
  obtain ⟨_, _, hBleI⟩ := natBinBool_infer sk.bk (r := .natBle) (by decide) (Or.inr rfl)
  let hBle : ClosedAt env (.const (.role .natBle) []) _ := .ofInfer (.const _ _) hBleI
  have hNatO : OpenType env 0 Γ₀ BaseKit.natT BaseKit.natT (.succ .zero) :=
    OpenType.ofClosed hsc sk.bk.natType
  have hLoCl := specNumGo_closed 64 lo
  have hHiCl := specNumGo_closed 64 hi
  have hResCl := specNumGo_closed 64 res
  let g1Lw : KExpr := .app (.app (.const (.role .natBle) []) (Ix.Kernel.specNum lo)) (.fvar 0 BaseKit.natT)
  let hyp1W : KExpr := .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g1Lw) BaseKit.trueE
  let g2Lw : KExpr := .app (.app (.const (.role .natBle) []) (.app BaseKit.natSuccE (.fvar 0 BaseKit.natT))) (Ix.Kernel.specNum hi)
  let hyp2W : KExpr := .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) BaseKit.boolT) g2Lw) BaseKit.trueE
  let Γ1 := fvarUpdate Γ₀ 0 BaseKit.natT
  let Γ2 := fvarUpdate Γ1 1 hyp1W
  let Γ3 := fvarUpdate Γ2 2 hyp2W
  have hg1LO : OpenAt env 1 Γ1
      (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.specNatOp .natBle (Ix.Kernel.specNum lo) (Ix.Kernel.specVar 0 BaseKit.natT)))
      g1Lw BaseKit.boolT := by
    have hf0 : OpenAt env 1 Γ1 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 1) (idx := 0) (by omega)
    have hnum := OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) (specNumGo_closedAt sk.bk hMulI 64 lo) rfl
    have hble := ((OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) hBle rfl).app_nondep hnum .refl rfl).app_nondep hf0 .refl rfl
    simpa [Ix.Kernel.specNatOp, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specVar,
      Ix.Kernel.specNum, fvarSubst, fvarSubst_of_not_hasFvar hLoCl.1, g1Lw, hBle] using hble
  have hg2LO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 hyp1W) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.specNatOp .natBle (Ix.Kernel.specSucc (Ix.Kernel.specVar 0 BaseKit.natT)) (Ix.Kernel.specNum hi))))
      g2Lw BaseKit.boolT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hsucc := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.bk.natSuccAt rfl).app_nondep hf0 .refl rfl
    have hnum := OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) (specNumGo_closedAt sk.bk hMulI 64 hi) rfl
    have hble := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) hBle rfl).app_nondep hsucc .refl rfl).app_nondep hnum .refl rfl
    simpa [Ix.Kernel.specNatOp, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specSucc,
      Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specVar, Ix.Kernel.specNum,
      fvarSubst, fvarSubst_of_not_hasFvar hHiCl.1, BaseKit.natSuccE, g2Lw, hBle] using hble
  have hLhsO : OpenAt env 3 Γ3
      (fvarSubst 2 (.fvar 2 hyp2W) (fvarSubst 1 (.fvar 1 hyp1W) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (.app (.const (.role .charUtf8Size) []) (.app charOfNatE (Ix.Kernel.specVar 0 BaseKit.natT))))))
      (.app sk.charUtf8SizeAt.witness (.app charOfNatE (.fvar 0 BaseKit.natT))) BaseKit.natT := by
    have hf0 : OpenAt env 3 Γ3 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 0) (by omega)
    have hch := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.sl.charOfNatAt rfl).app_nondep hf0 .refl rfl
    have hsz := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.charUtf8SizeAt rfl).app_nondep hch .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, charOfNatE] using hsz
  have hRhsO : OpenAt env 3 Γ3
      (fvarSubst 2 (.fvar 2 hyp2W) (fvarSubst 1 (.fvar 1 hyp1W) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.specNum res))))
      (Ix.Kernel.specNum res) BaseKit.natT := by
    have h := OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) (specNumGo_closedAt sk.bk hMulI 64 res) rfl
    simpa [Ix.Kernel.specNum, fvarSubst_of_not_hasFvar hResCl.1] using h
  have hGuard1 : DefEq env 0 (fvarSubst 0 (.lit (.natVal c.toNat)) g1Lw) BaseKit.trueE := by
    simp only [g1Lw, fvarSubst, fvarSubst_of_not_hasFvar hLoCl.1, ↓reduceIte, Ix.Kernel.specNum]
    have hr1 : Red env 0 (Ix.Kernel.specNum lo) (.lit (.natVal lo)) := specNum_red sk.bk hlo_val
    have hble : Red env 0 (.app (.app (.const (.role .natBle) []) (.lit (.natVal lo))) (.lit (.natVal c.toNat)))
        BaseKit.trueE :=
      sk.bk.red_natOp (r := .natBle) (by decide) (a := lo) (b := c.toNat) (res := BaseKit.trueE) (by
        simp [Ix.Kernel.natOpResult, hlo])
    exact .redL (.trans (.appFn (.appArg hr1)) hble) .refl
  have hGuard2 : DefEq env 0 (fvarSubst 0 (.lit (.natVal c.toNat)) g2Lw) BaseKit.trueE := by
    simp only [g2Lw, fvarSubst, fvarSubst_of_not_hasFvar hHiCl.1, ↓reduceIte, BaseKit.natSuccE, Ix.Kernel.specNum]
    have hr1 : Red env 0 (.app (.const (.role .natSucc) []) (.lit (.natVal c.toNat))) (.lit (.natVal (c.toNat + 1))) :=
      sk.bk.red_natSucc_lit c.toNat
    have hr2 : Red env 0 (Ix.Kernel.specNum hi) (.lit (.natVal hi)) := specNum_red sk.bk hhi_val
    have hble : Red env 0 (.app (.app (.const (.role .natBle) []) (.lit (.natVal (c.toNat + 1)))) (.lit (.natVal hi)))
        BaseKit.trueE :=
      sk.bk.red_natOp (r := .natBle) (by decide) (a := c.toNat + 1) (b := hi) (res := BaseKit.trueE) (by
        simp [Ix.Kernel.natOpResult, show c.toNat + 1 ≤ hi by omega])
    exact .redL (.trans (.appFn (.appArg hr1)) (.trans (.appArg hr2) hble)) .refl
  have hDe := applyEqn1Hyp2 sk.bk hv (by decide)
    (T₀ := BaseKit.natT) (T₀w := BaseKit.natT) (Cw := BaseKit.natT)
    (g1L := Ix.Kernel.specNatOp .natBle (Ix.Kernel.specNum lo) (Ix.Kernel.specVar 0 BaseKit.natT))
    (g1Lw := g1Lw) (g1R := BaseKit.trueE)
    (g2L := Ix.Kernel.specNatOp .natBle (Ix.Kernel.specSucc (Ix.Kernel.specVar 0 BaseKit.natT)) (Ix.Kernel.specNum hi))
    (g2Lw := g2Lw) (g2R := BaseKit.trueE)
    (lhsW := .app sk.charUtf8SizeAt.witness (.app charOfNatE (.fvar 0 BaseKit.natT)))
    (rhsW := Ix.Kernel.specNum res)
    (a := .lit (.natVal c.toNat))
    (lhsA := .app (.const (.role .charUtf8Size) []) (charExpr c))
    (rhsA := Ix.Kernel.specNum res)
    rfl rfl rfl sk.bk.natType .refl rfl rfl hNatO
    (by simp [Ix.Kernel.specNatOp, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specNum,
      Ix.Kernel.specVar, Ix.Kernel.Expr.looseBVarsBounded, hLoCl.2])
    sk.bk.boolTrueAt
    (by simp [Ix.Kernel.specNatOp, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specSucc,
      Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specNum, Ix.Kernel.specVar,
      Ix.Kernel.Expr.looseBVarsBounded, hHiCl.2])
    sk.bk.boolTrueAt
    (by simp [Ix.Kernel.specCert, Ix.Kernel.specVar, Ix.Kernel.Expr.looseBVarsBounded, charOfNatE])
    hResCl.2
    hg1LO hg2LO
    (fun v => by simp [g2Lw, Ix.Kernel.specNum, fvarSubst, fvarSubst_of_not_hasFvar hHiCl.1, BaseKit.natSuccE])
    hLhsO hRhsO
    (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar sk.charUtf8SizeAt.wClosed.1, charOfNatE])
    (fun v => by simp [fvarSubst, fvarSubst_of_not_hasFvar sk.charUtf8SizeAt.wClosed.1, charOfNatE])
    (fun v => fvarSubst_of_not_hasFvar hResCl.1)
    (fun v => fvarSubst_of_not_hasFvar hResCl.1)
    (sk.bk.natLitAt c.toNat)
    hGuard1 hGuard2
    (by
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.charUtf8SizeAt.wClosed.1, ↓reduceIte, charOfNatE, charExpr]
      exact .app sk.charUtf8SizeAt.defEq_witness .refl)
    (by simp only [Ix.Kernel.specNum, fvarSubst_of_not_hasFvar hResCl.1]; exact .refl)
    (sk.charUtf8SizeAt.app_nondep (sk.sl.charAt c) rfl)
    (specNumGo_closedAt sk.bk hMulI 64 res)
  exact (specNumGo_closedAt sk.bk hMulI 64 res).defEq_trans hDe (.redL (specNum_red sk.bk hres_val) .refl)

theorem defEq_charUtf8Size (c : Char) :
    DefEq env 0 (.app (.const (.role .charUtf8Size) []) (charExpr c)) (.lit (.natVal c.utf8Size)) := by
  have hv : c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat < 0x110000) := c.valid
  have hsz : c.utf8Size =
      if c.toNat < 0x80 then 1
      else if c.toNat < 0x800 then 2
      else if c.toNat < 0x10000 then 3
      else 4 := by
    have hdef : c.utf8Size =
        if c.val ≤ 0x7f then 1
        else if c.val ≤ 0x7ff then 2
        else if c.val ≤ 0xffff then 3
        else 4 := rfl
    rw [hdef]
    change (if c.toNat ≤ 127 then 1
      else if c.toNat ≤ 2047 then 2
      else if c.toNat ≤ 65535 then 3
      else 4) = _
    by_cases h1 : c.toNat ≤ 127
    · have h1' : c.toNat < 128 := by omega
      simp [h1, h1']
    · have h1' : ¬ c.toNat < 128 := by omega
      by_cases h2 : c.toNat ≤ 2047
      · have h2' : c.toNat < 2048 := by omega
        simp [h1, h1', h2, h2']
      · have h2' : ¬ c.toNat < 2048 := by omega
        by_cases h3 : c.toNat ≤ 65535
        · have h3' : c.toNat < 65536 := by omega
          simp [h1, h1', h2, h2', h3, h3']
        · have h3' : ¬ c.toNat < 65536 := by omega
          simp [h1, h1', h2, h2', h3, h3']
  rw [hsz]
  by_cases h1 : c.toNat < 0x80
  · simp only [h1, ↓reduceIte]; exact sk.defEq_charUtf8Size_range1 c h1
  · simp only [h1, ↓reduceIte]
    by_cases h2 : c.toNat < 0x800
    · simp only [h2, ↓reduceIte]
      exact sk.defEq_charUtf8Size_range2 c (k := 1) (lo := 0x80) (hi := 0x800) (res := 2)
        rfl rfl rfl rfl (by omega) h2
    · simp only [h2, ↓reduceIte]
      by_cases h3 : c.toNat < 0x10000
      · simp only [h3, ↓reduceIte]
        rcases hv with h3a | ⟨h3b, _⟩
        · exact sk.defEq_charUtf8Size_range2 c (k := 2) (lo := 0x800) (hi := 0xD800) (res := 3)
            rfl rfl rfl rfl (by omega) h3a
        · exact sk.defEq_charUtf8Size_range2 c (k := 3) (lo := 0xE000) (hi := 0x10000) (res := 3)
            rfl rfl rfl rfl h3b h3
      · simp only [h3, ↓reduceIte]
        have h4 : c.toNat < 0x110000 := by rcases hv with h | ⟨_, h⟩ <;> omega
        exact sk.defEq_charUtf8Size_range2 c (k := 4) (lo := 0x10000) (hi := 0x110000) (res := 4)
          rfl rfl rfl rfl (by omega) h4

/-! ### 2. `String.utf8ByteSize` -/

private theorem defEq_strUtf8ByteSize_nil :
    DefEq env 0 (.app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE listNilCharE))
      (.lit (.natVal 0)) := by
  have hv := eqnValid_of sk.hs .stringUtf8ByteSize (by decide) (by decide) (k := 0) rfl
  have h0 := applyEqn0 sk.bk hv (by decide) rfl rfl rfl sk.bk.natType .refl
    (sk.strUtf8ByteSizeAt.app_nondep (sk.sl.strOfListApp sk.sl.listNilCharAt) rfl)
    sk.bk.natZeroAt
  exact sk.bk.natZeroAt.defEq_trans h0 (.redL sk.bk.red_natZero_lit .refl)

private theorem defEq_strUtf8ByteSize_cons (c : Char) (cs : List Char) :
    DefEq env 0
      (.app (.const (.role .stringUtf8ByteSize) [])
        (.app stringOfListE (charListExpr (c :: cs))))
      (.app (.app (.const (.role .natAdd) []) (.app (.const (.role .charUtf8Size) []) (charExpr c)))
        (.app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE (charListExpr cs)))) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .stringUtf8ByteSize (by decide) (by decide) (k := 1) rfl
  obtain ⟨_, _, hAddI⟩ := natBinNat_infer sk.bk (r := .natAdd) (by decide) (by decide) (by decide)
  let hAdd : ClosedAt env (.const (.role .natAdd) []) _ := .ofInfer (.const _ _) hAddI
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 charT) 1 charListT
  have hLhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 charListT) (fvarSubst 0 (.fvar 0 charT)
        (.app (.const (.role .stringUtf8ByteSize) [])
          (.app stringOfListE (.app (.app listConsCharE (Ix.Kernel.specVar 0 charT)) (Ix.Kernel.specVar 1 charListT))))))
      (.app sk.strUtf8ByteSizeAt.witness
        (.app stringOfListE (.app (.app listConsCharE (.fvar 0 charT)) (.fvar 1 charListT))))
      BaseKit.natT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 charT) (.fvar 0 charT) charT :=
      OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 charListT) (.fvar 1 charListT) charListT :=
      OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have hcons := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.listConsCharAt rfl).app_nondep hf0 .refl rfl).app_nondep hf1 .refl rfl
    have hsol := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.stringOfListAt rfl).app_nondep hcons .refl rfl
    have hsz := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.strUtf8ByteSizeAt rfl).app_nondep hsol .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, stringOfListE, listConsCharE] using hsz
  have hRhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 charListT) (fvarSubst 0 (.fvar 0 charT)
        (Ix.Kernel.specNatOp .natAdd
          (.app (.const (.role .charUtf8Size) []) (Ix.Kernel.specVar 0 charT))
          (.app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE (Ix.Kernel.specVar 1 charListT))))))
      (.app (.app (.const (.role .natAdd) [])
        (.app sk.charUtf8SizeAt.witness (.fvar 0 charT)))
        (.app sk.strUtf8ByteSizeAt.witness (.app stringOfListE (.fvar 1 charListT))))
      BaseKit.natT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 charT) (.fvar 0 charT) charT :=
      OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 charListT) (.fvar 1 charListT) charListT :=
      OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have hcSz := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.charUtf8SizeAt rfl).app_nondep hf0 .refl rfl
    have hsSz := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.strUtf8ByteSizeAt rfl).app_nondep
      ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.stringOfListAt rfl).app_nondep hf1 .refl rfl) .refl rfl
    have hadd := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) hAdd rfl).app_nondep hcSz .refl rfl).app_nondep hsSz .refl rfl
    simpa [Ix.Kernel.specNatOp, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specVar,
      fvarSubst, stringOfListE, hAdd] using hadd
  let hcA := sk.sl.charAt c
  let hcsA := sk.sl.charListAt cs
  have hcW : hcA.witness = charExpr c := sk.sl.charAt_w c
  have hcsW : hcsA.witness = charListExpr cs := sk.sl.charListAt_w cs
  exact applyEqn2 sk.bk hv (by decide)
    (T₀ := charT) (T₀w := charT) (T₁ := charListT) (T₁w := charListT) (Cw := BaseKit.natT)
    (lhsW := .app sk.strUtf8ByteSizeAt.witness
      (.app stringOfListE (.app (.app listConsCharE (.fvar 0 charT)) (.fvar 1 charListT))))
    (rhsW := .app (.app (.const (.role .natAdd) [])
      (.app sk.charUtf8SizeAt.witness (.fvar 0 charT)))
      (.app sk.strUtf8ByteSizeAt.witness (.app stringOfListE (.fvar 1 charListT))))
    (a := charExpr c) (b := charListExpr cs)
    (lhsAB := .app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE (charListExpr (c :: cs))))
    (rhsAB := .app (.app (.const (.role .natAdd) []) (.app (.const (.role .charUtf8Size) []) (charExpr c)))
      (.app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE (charListExpr cs))))
    rfl rfl rfl sk.bk.natType .refl rfl rfl
    (sk.sl.charType_open 0 Γ₀) (sk.sl.charListType_open 0 Γ₀) rfl rfl
    (by decide) (by decide) (by decide) (by decide)
    hLhsO hRhsO hcA hcsA
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specOfList, Ix.Kernel.specCharCons, Ix.Kernel.specChar,
      Ix.Kernel.specVar, Ix.Kernel.BasisDSL.ap3, Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specC,
      fvarSubst, charListExpr, charExpr, stringOfListE, listConsCharE, charOfNatE, charT])
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specNatOp, Ix.Kernel.specOfList, Ix.Kernel.specVar,
      Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specC,
      fvarSubst, charExpr, stringOfListE, charOfNatE])
    (by
      rw [hcW, hcsW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.strUtf8ByteSizeAt.wClosed.1, ↓reduceIte,
        stringOfListE, listConsCharE, charListExpr, charExpr, charOfNatE, charT]
      exact .app sk.strUtf8ByteSizeAt.defEq_witness .refl)
    (by
      rw [hcW, hcsW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.charUtf8SizeAt.wClosed.1,
        fvarSubst_of_not_hasFvar sk.strUtf8ByteSizeAt.wClosed.1, ↓reduceIte, stringOfListE, charExpr, charOfNatE]
      exact .app (.app .refl (.app sk.charUtf8SizeAt.defEq_witness .refl))
        (.app sk.strUtf8ByteSizeAt.defEq_witness .refl))
    (sk.strUtf8ByteSizeAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt (c :: cs))) rfl)
    ((hAdd.app_nondep (sk.charUtf8SizeAt.app_nondep (sk.sl.charAt c) rfl) rfl).app_nondep
      (sk.strUtf8ByteSizeAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt cs)) rfl) rfl)

omit sk in
private theorem list_toByteArray_loop_size (xs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop xs acc).size = acc.size + xs.length := by
  induction xs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih =>
    simp only [List.toByteArray.loop, ih, ByteArray.size_push, List.length_cons]
    omega

omit sk in
private theorem sum_utf8Size_eq (cs : List Char) :
    (cs.map Char.utf8Size).sum = (String.ofList cs).utf8ByteSize := by
  have h1 : (String.ofList cs).utf8ByteSize = (String.ofList cs).toByteArray.size := rfl
  rw [h1, String.toByteArray_ofList]
  have h2 : cs.utf8Encode.size = (cs.flatMap String.utf8EncodeChar).length := by
    simp [List.utf8Encode, List.toByteArray, list_toByteArray_loop_size, ByteArray.size_empty]
  rw [h2]
  clear h1 h2
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih]
    congr 1
    simp only [Char.utf8Size, String.utf8EncodeChar, UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]
    by_cases h1 : c.toNat ≤ 127
    · simp [h1]
    · by_cases h2 : c.toNat ≤ 2047
      · simp [h1, h2]
      · by_cases h3 : c.toNat ≤ 65535 <;> simp [h1, h2, h3]

private theorem defEq_strUtf8ByteSize_list : ∀ (cs : List Char),
    DefEq env 0
      (.app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE (charListExpr cs)))
      (.lit (.natVal (cs.map Char.utf8Size).sum))
  | [] => sk.defEq_strUtf8ByteSize_nil
  | c :: cs => by
    obtain ⟨_, _, ⟨hAdd⟩⟩ := sk.bk.natBinNatAt (r := .natAdd) (by decide) (by decide) (by decide)
    have hstep := sk.defEq_strUtf8ByteSize_cons c cs
    have hc := sk.defEq_charUtf8Size c
    have hcs := defEq_strUtf8ByteSize_list cs
    have hadd : Red env 0
        (.app (.app (.const (.role .natAdd) []) (.lit (.natVal c.utf8Size)))
          (.lit (.natVal (cs.map Char.utf8Size).sum)))
        (.lit (.natVal (c.utf8Size + (cs.map Char.utf8Size).sum))) :=
      sk.bk.red_natOp (r := .natAdd) (by decide) (a := c.utf8Size)
        (b := (cs.map Char.utf8Size).sum) rfl
    have hMid1 : ClosedAt env
        (.app (.app (.const (.role .natAdd) []) (.app (.const (.role .charUtf8Size) []) (charExpr c)))
          (.app (.const (.role .stringUtf8ByteSize) []) (.app stringOfListE (charListExpr cs))))
        BaseKit.natT :=
      (hAdd.app_nondep (sk.charUtf8SizeAt.app_nondep (sk.sl.charAt c) rfl) rfl).app_nondep
        (sk.strUtf8ByteSizeAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt cs)) rfl) rfl
    have hMid2 : ClosedAt env
        (.app (.app (.const (.role .natAdd) []) (.lit (.natVal c.utf8Size)))
          (.lit (.natVal (cs.map Char.utf8Size).sum)))
        BaseKit.natT :=
      (hAdd.app_nondep (sk.bk.natLitAt c.utf8Size) rfl).app_nondep
        (sk.bk.natLitAt (cs.map Char.utf8Size).sum) rfl
    exact hMid1.defEq_trans hstep (hMid2.defEq_trans (.app (.app .refl hc) hcs) (.redL hadd .refl))

theorem defEq_strUtf8ByteSize (s : String) :
    DefEq env 0 (.app (.const (.role .stringUtf8ByteSize) []) (.lit (.strVal s)))
      (.lit (.natVal s.utf8ByteSize)) := by
  have h1 := sk.defEq_strUtf8ByteSize_list s.toList
  rw [sum_utf8Size_eq, String.ofList_toList] at h1
  have hred : Red env 0 (.lit (.strVal s)) (.app stringOfListE (charListExpr s.toList)) := by
    rw [← strLitToConstructor_eq_charListExpr]
    exact .strLit sk.sl.strLit
  exact .redL (.appArg hred) h1

/-! ### 3. `String.back` -/

private theorem defEq_strBack_nil :
    DefEq env 0 (.app (.const (.role .stringBack) []) (.app stringOfListE listNilCharE))
      (charExpr 'A') := by
  have hv := eqnValid_of sk.hs .stringBack (by decide) (by decide) (k := 0) rfl
  obtain ⟨_, _, hMulI⟩ := natBinNat_infer sk.bk (r := .natMul) (by decide) (by decide) (by decide)
  have hMid : ClosedAt env (.app charOfNatE (Ix.Kernel.specNum 65)) charT :=
    sk.sl.charOfNatAt.app_nondep (specNumGo_closedAt sk.bk hMulI 64 65) rfl
  have h0 := applyEqn0 sk.bk hv (by decide) rfl rfl rfl sk.sl.charType .refl
    (sk.strBackAt.app_nondep (sk.sl.strOfListApp sk.sl.listNilCharAt) rfl)
    hMid
  have hr65 : Red env 0 (.app charOfNatE (Ix.Kernel.specNum 65)) (charExpr 'A') :=
    .appArg (specNum_red sk.bk rfl)
  exact hMid.defEq_trans h0 (.redL hr65 .refl)

private theorem defEq_strBack_singleton (c : Char) :
    DefEq env 0 (.app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr [c])))
      (charExpr c) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .stringBack (by decide) (by decide) (k := 1) rfl
  let Γ1 := fvarUpdate Γ₀ 0 charT
  have hLhsO : OpenAt env 1 Γ1
      (fvarSubst 0 (.fvar 0 charT)
        (.app (.const (.role .stringBack) [])
          (.app stringOfListE (.app (.app listConsCharE (Ix.Kernel.specVar 0 charT)) listNilCharE))))
      (.app sk.strBackAt.witness
        (.app stringOfListE (.app (.app listConsCharE (.fvar 0 charT)) listNilCharE)))
      charT := by
    have hf0 : OpenAt env 1 Γ1 (.fvar 0 charT) (.fvar 0 charT) charT :=
      OpenAt.fvar (d := 1) (idx := 0) (by omega)
    have hnil := OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) sk.sl.listNilCharAt rfl
    have hcons := ((OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) sk.sl.listConsCharAt rfl).app_nondep hf0 .refl rfl).app_nondep hnil .refl rfl
    have hsol := (OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) sk.sl.stringOfListAt rfl).app_nondep hcons .refl rfl
    have hbk := (OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) sk.strBackAt rfl).app_nondep hsol .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, stringOfListE, listConsCharE, listNilCharE] using hbk
  have hRhsO : OpenAt env 1 Γ1
      (fvarSubst 0 (.fvar 0 charT) (Ix.Kernel.specVar 0 charT)) (.fvar 0 charT) charT := by
    simpa [Ix.Kernel.specVar, fvarSubst, Γ1, fvarUpdate] using
      OpenAt.fvar (env := env) (d := 1) (Γ := Γ1) (idx := 0) (by omega)
  let hcA := sk.sl.charAt c
  have hcW : hcA.witness = charExpr c := sk.sl.charAt_w c
  exact applyEqn1 sk.bk hv (by decide)
    (T₀ := charT) (T₀w := charT) (Cw := charT)
    (lhsW := .app sk.strBackAt.witness (.app stringOfListE (.app (.app listConsCharE (.fvar 0 charT)) listNilCharE)))
    (rhsW := .fvar 0 charT)
    (a := charExpr c)
    (lhsA := .app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr [c])))
    (rhsA := charExpr c)
    rfl rfl rfl sk.sl.charType .refl rfl rfl (sk.sl.charType_open 0 Γ₀)
    (by decide) (by decide) (by decide) (by decide)
    hLhsO hRhsO hcA
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specOfList, Ix.Kernel.specCharCons, Ix.Kernel.specCharNil,
      Ix.Kernel.specChar, Ix.Kernel.specVar, Ix.Kernel.BasisDSL.ap3, Ix.Kernel.BasisDSL.cnst,
      Ix.Kernel.specC, fvarSubst, charListExpr, charExpr, stringOfListE, listConsCharE,
      listNilCharE, charOfNatE, charT])
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specVar, fvarSubst])
    (by
      rw [hcW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.strBackAt.wClosed.1, ↓reduceIte,
        stringOfListE, listConsCharE, listNilCharE, charListExpr, charExpr, charOfNatE, charT]
      exact .app sk.strBackAt.defEq_witness .refl)
    (by rw [hcW]; simp [fvarSubst]; exact .refl)
    (sk.strBackAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt [c])) rfl)
    hcA

private theorem defEq_strBack_cons2 (c d : Char) (ds : List Char) :
    DefEq env 0
      (.app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr (c :: d :: ds))))
      (.app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr (d :: ds)))) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .stringBack (by decide) (by decide) (k := 2) rfl
  let Γ3 := fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 charT) 1 charT) 2 charListT
  have hLhsO : OpenAt env 3 Γ3
      (fvarSubst 2 (.fvar 2 charListT) (fvarSubst 1 (.fvar 1 charT) (fvarSubst 0 (.fvar 0 charT)
        (.app (.const (.role .stringBack) [])
          (.app stringOfListE (.app (.app listConsCharE (Ix.Kernel.specVar 0 charT))
            (.app (.app listConsCharE (Ix.Kernel.specVar 1 charT)) (Ix.Kernel.specVar 2 charListT))))))))
      (.app sk.strBackAt.witness
        (.app stringOfListE (.app (.app listConsCharE (.fvar 0 charT))
          (.app (.app listConsCharE (.fvar 1 charT)) (.fvar 2 charListT)))))
      charT := by
    have hf0 : OpenAt env 3 Γ3 (.fvar 0 charT) (.fvar 0 charT) charT := OpenAt.fvar (d := 3) (idx := 0) (by omega)
    have hf1 : OpenAt env 3 Γ3 (.fvar 1 charT) (.fvar 1 charT) charT := OpenAt.fvar (d := 3) (idx := 1) (by omega)
    have hf2 : OpenAt env 3 Γ3 (.fvar 2 charListT) (.fvar 2 charListT) charListT := OpenAt.fvar (d := 3) (idx := 2) (by omega)
    have hc2 := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.sl.listConsCharAt rfl).app_nondep hf1 .refl rfl).app_nondep hf2 .refl rfl
    have hc1 := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.sl.listConsCharAt rfl).app_nondep hf0 .refl rfl).app_nondep hc2 .refl rfl
    have hsol := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.sl.stringOfListAt rfl).app_nondep hc1 .refl rfl
    have hbk := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.strBackAt rfl).app_nondep hsol .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, stringOfListE, listConsCharE] using hbk
  have hRhsO : OpenAt env 3 Γ3
      (fvarSubst 2 (.fvar 2 charListT) (fvarSubst 1 (.fvar 1 charT) (fvarSubst 0 (.fvar 0 charT)
        (.app (.const (.role .stringBack) [])
          (.app stringOfListE (.app (.app listConsCharE (Ix.Kernel.specVar 1 charT)) (Ix.Kernel.specVar 2 charListT)))))))
      (.app sk.strBackAt.witness
        (.app stringOfListE (.app (.app listConsCharE (.fvar 1 charT)) (.fvar 2 charListT))))
      charT := by
    have hf1 : OpenAt env 3 Γ3 (.fvar 1 charT) (.fvar 1 charT) charT := OpenAt.fvar (d := 3) (idx := 1) (by omega)
    have hf2 : OpenAt env 3 Γ3 (.fvar 2 charListT) (.fvar 2 charListT) charListT := OpenAt.fvar (d := 3) (idx := 2) (by omega)
    have hc2 := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.sl.listConsCharAt rfl).app_nondep hf1 .refl rfl).app_nondep hf2 .refl rfl
    have hsol := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.sl.stringOfListAt rfl).app_nondep hc2 .refl rfl
    have hbk := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) sk.strBackAt rfl).app_nondep hsol .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, stringOfListE, listConsCharE] using hbk
  let hcA := sk.sl.charAt c
  let hdA := sk.sl.charAt d
  let hdsA := sk.sl.charListAt ds
  have hcW : hcA.witness = charExpr c := sk.sl.charAt_w c
  have hdW : hdA.witness = charExpr d := sk.sl.charAt_w d
  have hdsW : hdsA.witness = charListExpr ds := sk.sl.charListAt_w ds
  exact applyEqn3 sk.bk hv (by decide)
    (T₀ := charT) (T₀w := charT) (T₁ := charT) (T₁w := charT) (T₂ := charListT) (T₂w := charListT) (Cw := charT)
    (lhsW := .app sk.strBackAt.witness (.app stringOfListE (.app (.app listConsCharE (.fvar 0 charT)) (.app (.app listConsCharE (.fvar 1 charT)) (.fvar 2 charListT)))))
    (rhsW := .app sk.strBackAt.witness (.app stringOfListE (.app (.app listConsCharE (.fvar 1 charT)) (.fvar 2 charListT))))
    (a := charExpr c) (b := charExpr d) (c := charListExpr ds)
    (lhsABC := .app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr (c :: d :: ds))))
    (rhsABC := .app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr (d :: ds))))
    rfl rfl rfl sk.sl.charType .refl rfl rfl
    (sk.sl.charType_open 0 Γ₀) (sk.sl.charType_open 0 Γ₀) (sk.sl.charListType_open 0 Γ₀)
    rfl rfl rfl rfl (by decide) (by decide)
    hLhsO hRhsO hcA hdA hdsA
    (by
      rw [hcW, hdW, hdsW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.strBackAt.wClosed.1,
        stringOfListE, listConsCharE, charListExpr, charExpr, charOfNatE, charT]
      exact .app sk.strBackAt.defEq_witness .refl)
    (by
      rw [hcW, hdW, hdsW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.strBackAt.wClosed.1,
        stringOfListE, listConsCharE, charListExpr, charExpr, charOfNatE, charT]
      exact .app sk.strBackAt.defEq_witness .refl)
    (sk.strBackAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt (c :: d :: ds))) rfl)
    (sk.strBackAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt (d :: ds))) rfl)

private theorem defEq_strBack_list : ∀ (cs : List Char),
    DefEq env 0 (.app (.const (.role .stringBack) []) (.app stringOfListE (charListExpr cs)))
      (charExpr (cs.getLastD 'A'))
  | [] => sk.defEq_strBack_nil
  | [c] => sk.defEq_strBack_singleton c
  | c :: d :: ds =>
    (sk.strBackAt.app_nondep (sk.sl.strOfListApp (sk.sl.charListAt (d :: ds))) rfl).defEq_trans
      (sk.defEq_strBack_cons2 c d ds)
      (defEq_strBack_list (d :: ds))

theorem defEq_strBack (s : String) :
    DefEq env 0 (.app (.const (.role .stringBack) []) (.lit (.strVal s)))
      (charExpr (s.toList.getLastD 'A')) := by
  have hred : Red env 0 (.lit (.strVal s)) (.app stringOfListE (charListExpr s.toList)) := by
    rw [← strLitToConstructor_eq_charListExpr]
    exact .strLit sk.sl.strLit
  exact .redL (.appArg hred) (sk.defEq_strBack_list s.toList)

/-! ### 4. `String.toByteArray ""` -/

theorem defEq_strToByteArrayEmpty :
    DefEq env 0 (.app (.const (.role .stringToByteArray) []) (.lit (.strVal "")))
      (.const (.role .byteArrayEmpty) []) := by
  have hv := eqnValid_of sk.hs .stringToByteArray (by decide) (by decide) (k := 0) rfl
  have h0 := applyEqn0 sk.bk hv (by decide) rfl rfl rfl sk.baType
    (sk.baW ▸ sk.baAt.wRed)
    (sk.strToByteArrayAt.app_nondep (sk.sl.strOfListApp sk.sl.listNilCharAt) sk.wBA_cl.2)
    sk.baEmptyAt
  have hred : Red env 0 (.lit (.strVal "")) (.app stringOfListE listNilCharE) := by
    have h := Red.strLit (env := env) (d := 0) (s := "") sk.sl.strLit
    simpa [strLitToConstructor_eq_charListExpr, charListExpr] using h
  exact .redL (.appArg hred) h0

/-! ### 5. `String.decEq s s` -/

theorem defEq_strDecEqRefl (s : String) :
    DefEq env 0
      (.app (.app (.const (.role .stringDecEq) []) (.lit (.strVal s))) (.lit (.strVal s)))
      (.app (.app (.const (.role .decidableIsTrue) [])
        (.app (.app (.app (.const (.role .eq) [.succ .zero]) stringT) (.lit (.strVal s))) (.lit (.strVal s))))
        (.app (.app (.const (.role .eqRefl) [.succ .zero]) stringT) (.lit (.strVal s)))) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .stringDecEq (by decide) (by decide) (k := 0) rfl
  let Γ1 := fvarUpdate Γ₀ 0 stringT
  let s0 : KExpr := .fvar 0 stringT
  let eqP0 : KExpr := .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT) s0) s0
  have hEqP0 : OpenAt env 1 Γ1 eqP0 eqP0 (.sort .zero) :=
    OpenAt.eq sk.bk.eqStored (sk.sl.stringType_open 1 Γ1)
      (OpenAt.fvar (d := 1) (idx := 0) (by omega)) .refl
      (OpenAt.fvar (d := 1) (idx := 0) (by omega)) .refl
  have hLhsO : OpenAt env 1 Γ1
      (fvarSubst 0 s0
        (Ix.Kernel.specDecide
          (Ix.Kernel.specEq1 stringT (Ix.Kernel.specVar 0 stringT) (Ix.Kernel.specVar 0 stringT))
          (.app (.app (.const (.role .stringDecEq) []) (Ix.Kernel.specVar 0 stringT)) (Ix.Kernel.specVar 0 stringT))))
      (.app (.app wDecide eqP0) (.app (.app sk.strDecEqAt.witness s0) s0))
      BaseKit.boolT := by
    have hf0 : OpenAt env 1 Γ1 s0 s0 stringT := OpenAt.fvar (d := 1) (idx := 0) (by omega)
    have hd1 := (OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) sk.strDecEqAt sk.strDecEqTy_nf).app_abs hf0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 sk.ik.wDec_cl.2, stringT])
    simp [s0, fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1, stringT] at hd1
    have hd2 := hd1.app_abs hf0 .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, sk.ik.wDec_cl.2])
    simp [s0, fvarSubst, fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1, stringT] at hd2
    have hdec1 := (OpenAt.ofClosed hsc (d := 1) (Γ := Γ1) sk.ik.decideAt sk.ik.decideTy_nf).app_abs hEqP0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, sk.ik.wDec_cl.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1] at hdec1
    have hdec2 := hdec1.app_abs hd2 .refl rfl
    simpa [Ix.Kernel.specDecide, Ix.Kernel.specEq1, Ix.Kernel.specVar, Ix.Kernel.BasisDSL.ap2,
      Ix.Kernel.BasisDSL.ap3, Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specC, fvarSubst,
      sk.ik.decideW, eqP0, s0, stringT] using hdec2
  have hRhsO : OpenAt env 1 Γ1 (fvarSubst 0 s0 BaseKit.trueE) BaseKit.trueE BaseKit.boolT :=
    OpenAt.ofClosed hsc sk.bk.boolTrueAt rfl
  let sLit : KExpr := .lit (.strVal s)
  let eqPS : KExpr := .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT) sLit) sLit
  let hsAt : ClosedAt env sLit stringT := sk.sl.strLitAt s
  let hEqCT := closedType_eq sk.bk.eqStored sk.sl.stringType hsAt.wInfer hsAt.wClosed hsAt.wInfer hsAt.wClosed
  let hEqPS : ClosedAt env eqPS (.sort .zero) := .ofInfer hEqCT.closed hEqCT.infer
  have hDecEqS : ClosedAt env (.app (.app (.const (.role .stringDecEq) []) sLit) sLit) (.app wDec eqPS) := by
    have h1 := sk.strDecEqAt.app_abs hsAt .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 sk.ik.wDec_cl.2, stringT])
    simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hsAt.wClosed.1,
      fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1, stringT] at h1
    have h2 := h1.app_abs hsAt .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, sk.ik.wDec_cl.2, hsAt.wClosed.2])
    simpa [fvarSubst, fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1,
      fvarSubst_of_not_hasFvar hsAt.wClosed.1, eqPS, sLit, hsAt] using h2
  have hDecideEq : DefEq env 0
      (.app (.app (.const (.role .decidableDecide) []) eqPS)
        (.app (.app (.const (.role .stringDecEq) []) sLit) sLit))
      BaseKit.trueE :=
    applyEqn1 sk.bk hv (by decide)
      (T₀ := stringT) (T₀w := stringT) (Cw := BaseKit.boolT)
      (lhsW := .app (.app wDecide eqP0) (.app (.app sk.strDecEqAt.witness s0) s0))
      (rhsW := BaseKit.trueE)
      (a := sLit)
      (lhsA := .app (.app (.const (.role .decidableDecide) []) eqPS)
        (.app (.app (.const (.role .stringDecEq) []) sLit) sLit))
      (rhsA := BaseKit.trueE)
      rfl rfl rfl sk.bk.boolType .refl rfl rfl (sk.sl.stringType_open 0 Γ₀)
      (by decide) (by decide) (by decide) (by decide)
      hLhsO hRhsO hsAt
      (by simp [Ix.Kernel.specEqn, Ix.Kernel.specDecide, Ix.Kernel.specEq1, Ix.Kernel.specString,
        Ix.Kernel.specC, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.ap3, Ix.Kernel.BasisDSL.cnst,
        Ix.Kernel.specVar, fvarSubst, eqPS, sLit, stringT])
      rfl
      (by
        simp only [eqP0, s0, fvarSubst, fvarSubst_of_not_hasFvar sk.ik.wDecide_cl.1,
          fvarSubst_of_not_hasFvar sk.strDecEqAt.wClosed.1, ↓reduceIte, eqPS, sLit, stringT, hsAt,
          StrLitKit.strLitAt_w]
        exact .app (.app sk.ik.wDecide_defEq .refl) (.app (.app sk.strDecEqAt.defEq_witness .refl) .refl))
      .refl
      (sk.ik.decideApp hEqPS hDecEqS) sk.bk.boolTrueAt
  have hRefl : ClosedAt env (.app (.app (.const (.role .eqRefl) [.succ .zero]) stringT) sLit) eqPS :=
    closedAt_eqRefl sk.bk.eqReflStored sk.sl.stringType hsAt
  have hIsTrue : ClosedAt env
      (.app (.app (.const (.role .decidableIsTrue) []) eqPS)
        (.app (.app (.const (.role .eqRefl) [.succ .zero]) stringT) sLit))
      (.app wDec eqPS) :=
    sk.ik.isTrueApp hEqPS hRefl
  have hDecideIsTrue := sk.ik.decide_isTrue hEqPS hRefl
  exact sk.ik.decide_ext hEqPS hDecEqS hIsTrue
    (sk.bk.boolTrueAt.defEq_trans hDecideEq (.symm hDecideIsTrue))

/-! ### 6. `List.append.{0} Char` & `String.append` -/

private theorem defEq_listAppend_nil (ys : List Char) :
    DefEq env 0
      (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) listNilCharE) (charListExpr ys))
      (charListExpr ys) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .listAppend (by decide) (by decide) (k := 0) rfl
  let α0 : KExpr := .fvar 0 (.sort (.succ .zero))
  let L0 : KExpr := .app (.const (.role .list) [.zero]) α0
  let ys1 : KExpr := .fvar 1 L0
  let Γ1 := fvarUpdate Γ₀ 0 (.sort (.succ .zero))
  let Γ2 := fvarUpdate Γ1 1 L0
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
  have hL0O : OpenType env 1 Γ1 L0 L0 (.succ .zero) := by
    have hf0 : OpenAt env 1 Γ1 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 1) (idx := 0) (by omega)
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc sk.sl.list0At rfl).app_nondep hf0 .refl rfl)
  have hL0O2 : OpenType env 2 Γ2 L0 L0 (.succ .zero) := by
    have hf0 : OpenAt env 2 Γ2 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 2) (idx := 0) (by omega)
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc sk.sl.list0At rfl).app_nondep hf0 .refl rfl)
  let hCharAt : ClosedAt env charT (.sort (.succ .zero)) := sk.sl.charAtType
  let hysA := sk.sl.charListAt ys
  have hysW : hysA.witness = charListExpr ys := sk.sl.charListAt_w ys
  have hLhsO : OpenAt env 2 Γ2
      (.app (.app (.app (.const (.role .listAppend) [.zero]) α0) (.app (.const (.role .listNil) [.zero]) α0)) ys1)
      (.app (.app (.app sk.listAppend0At.witness α0) (.app (.const (.role .listNil) [.zero]) α0)) ys1) L0 := by
    have hf0 : OpenAt env 2 Γ2 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 ys1 ys1 L0 := OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have hnilO : OpenAt env 2 Γ2 (.app (.const (.role .listNil) [.zero]) α0)
        (.app (.const (.role .listNil) [.zero]) α0) L0 := by
      have h := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.listNil0At rfl).app_dep hf0 .refl
      simpa [Ix.Kernel.Expr.instantiate1, L0, α0] using h
    have ha1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.listAppend0At rfl).app_abs hf0 .refl (by decide)
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, α0] at ha1
    have ha2 := ha1.app_nondep hnilO .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded])
    have ha3 := ha2.app_nondep hf1 .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded])
    simpa [L0, α0] using ha3
  have hRhsO : OpenAt env 2 Γ2 ys1 ys1 L0 := OpenAt.fvar (d := 2) (idx := 1) (by omega)
  have hLhsDe : DefEq env 0
      (.app (.app (.app sk.listAppend0At.witness charT) listNilCharE) (charListExpr ys))
      (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) listNilCharE) (charListExpr ys)) :=
    .app (.app (.app sk.listAppend0At.defEq_witness .refl) .refl) .refl
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · have hinst := DefEq.instClosed (d := 0) (ks := [0]) (us := [.zero]) rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hde
    simp only [eqnsSideExact, List.zipIdx, List.foldr,
      Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst.go,
      Ix.Kernel.Level.substPW, bmeta] at hinst
    have hLamL1 := OpenAt.lam_abs_inner_id (pw := .never) hL0O hLhsO hL0O2.wInfer hL0O2.wRed rfl rfl hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamL1
    have hLamR1 := OpenAt.lam_abs_inner_id (pw := .never) hL0O hRhsO hL0O2.wInfer hL0O2.wRed rfl rfl hCtx1
    have hLamR0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamR1
    have hChO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hCharAt rfl
    have hYsO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hysA rfl
    have hAppL1 := hLamL0.app_abs hChO .refl (by decide)
    simp [α0, L0, ys1, fvarSubst, Ix.Kernel.Expr.abstract1, charT, hCharAt] at hAppL1
    have hAppL2 := hAppL1.app_nondep hYsO .refl rfl
    have hAppR1 := hLamR0.app_abs hChO .refl (by decide)
    simp [α0, L0, ys1, fvarSubst, Ix.Kernel.Expr.abstract1, charT, hCharAt] at hAppR1
    have hAppR2 := hAppR1.app_nondep hYsO .refl rfl
    have hRedL1 : Red env 0
        (.app (.lam (.sort (.succ .zero))
          ((Ix.Kernel.Expr.lam L0
            ((Ix.Kernel.Expr.app (.app (.app sk.listAppend0At.witness α0) (.app (.const (.role .listNil) [.zero]) α0)) ys1).abstract1 1)
            { pw := .never }).abstract1 0) { pw := .never }) charT)
        (.lam charListT
          ((Ix.Kernel.Expr.app (.app (.app sk.listAppend0At.witness charT) listNilCharE) ys1).abstract1 1)
          { pw := .never }) := by
      have h := Red.beta (env := env) (d := 0) (ty := .sort (.succ .zero)) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.lam L0
          ((Ix.Kernel.Expr.app (.app (.app sk.listAppend0At.witness α0) (.app (.const (.role .listNil) [.zero]) α0)) ys1).abstract1 1)
          { pw := .never }).abstract1 0) hCharAt.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by
        simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 sk.listAppend0At.wClosed.2, L0, α0, ys1])] at h
      simpa [L0, α0, ys1, fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) (by decide : charT.hasFvar = false),
        fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1, listNilCharE, charListT, charT, hCharAt] using h
    have hRedL2 : Red env 0
        (.app (.lam charListT
          ((Ix.Kernel.Expr.app (.app (.app sk.listAppend0At.witness charT) listNilCharE) ys1).abstract1 1)
          { pw := .never }) hysA.witness)
        (.app (.app (.app sk.listAppend0At.witness charT) listNilCharE) (charListExpr ys)) := by
      have h := Red.beta (env := env) (d := 0) (ty := charListT) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.app (.app (.app sk.listAppend0At.witness charT) listNilCharE) ys1).abstract1 1)
        hysA.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by
        simp [Ix.Kernel.Expr.looseBVarsBounded, sk.listAppend0At.wClosed.2, ys1])] at h
      simpa [fvarSubst, fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1, listNilCharE, ys1, hysW, charT] using h
    have hRedR1 : Red env 0
        (.app (.lam (.sort (.succ .zero)) ((Ix.Kernel.Expr.lam L0 (ys1.abstract1 1) { pw := .never }).abstract1 0) { pw := .never }) charT)
        (.lam charListT (ys1.abstract1 1) { pw := .never }) := by
      have h := Red.beta (env := env) (d := 0) (ty := .sort (.succ .zero)) (mb := { pw := .never })
        (body := (Ix.Kernel.Expr.lam L0 (ys1.abstract1 1) { pw := .never }).abstract1 0)
        hCharAt.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, L0, α0, ys1])] at h
      simpa [L0, α0, ys1, fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) (by decide : charT.hasFvar = false),
        charListT, charT, hCharAt] using h
    have hRedR2 : Red env 0 (.app (.lam charListT (ys1.abstract1 1) { pw := .never }) hysA.witness) (charListExpr ys) := by
      have h := Red.beta (env := env) (d := 0) (ty := charListT) (mb := { pw := .never })
        (body := ys1.abstract1 1) hysA.wInfer.toIO .refl
      rw [abstract1_instantiate1_eq_fvarSubst (by simp [Ix.Kernel.Expr.looseBVarsBounded, ys1])] at h
      simpa [ys1, fvarSubst, hysW] using h
    exact OpenAt.defEq_chain hAppL2 hAppR2 (.app (.app hinst .refl) .refl)
      (.trans (.appFn hRedL1) hRedL2) hLhsDe (.trans (.appFn hRedR1) hRedR2) .refl
  · have hlen : cv.levelParams.length = 1 := Option.some.inj (hlv.symm.trans (by decide))
    have hEqO := OpenType.eq sk.bk.eqStored hL0O2 hLhsO .refl hRhsO .refl
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) hL0O hEqO rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort (.succ .zero)) hB1O rfl
    have hPiRed := hStmtO.wPiRed
    have heqStmt :
        (Ix.Kernel.Expr.forallE (.sort (.succ .zero))
          ((Ix.Kernel.Expr.forallE L0
            ((Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) L0)
              (.app (.app (.app (.const (.role .listAppend) [.zero]) α0)
                (.app (.const (.role .listNil) [.zero]) α0)) ys1)) ys1).abstract1 1)
            { pw := .ifAllZero [] }).abstract1 0)
          { pw := .ifAllZero [] }) =
        ((eqnsStmtExact (eqnsOfRole .listAppend)[0]!).instantiateLevelParams [0] [.zero]) := by
      decide
    rw [heqStmt] at hPiRed
    have hp0 := ClosedAt.ofThm1_de hsc sk.bk.wf hf hlen hde (by decide) ⟨by decide, by decide⟩
      hPiRed hStmtO.toClosedType
    have hp1 := hp0.app_abs hCharAt .refl hB1O.wClosed
    simp [α0, L0, ys1, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) (by decide : charT.hasFvar = false),
      fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1, hCharAt] at hp1
    have hp2 := hp1.app_abs hysA .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, sk.listAppend0At.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1, hysW,
      charListT, charT] at hp2
    exact defEq_of_eqProof_de hsc sk.bk.eqStored hp2
      (.app (.app (.app .refl .refl) hLhsDe) .refl)
      (sk.listAppendCharApp sk.sl.listNilCharAt hysA) hysA sk.sl.charListType

private theorem defEq_listAppend_cons (a : Char) (as ys : List Char) :
    DefEq env 0
      (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr (a :: as))) (charListExpr ys))
      (.app (.app listConsCharE (charExpr a))
        (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr as)) (charListExpr ys))) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .listAppend (by decide) (by decide) (k := 1) rfl
  let α0 : KExpr := .fvar 0 (.sort (.succ .zero))
  let L0 : KExpr := .app (.const (.role .list) [.zero]) α0
  let a1 : KExpr := .fvar 1 α0
  let as2 : KExpr := .fvar 2 L0
  let ys3 : KExpr := .fvar 3 L0
  let Γ1 := fvarUpdate Γ₀ 0 (.sort (.succ .zero))
  let Γ2 := fvarUpdate Γ1 1 α0
  let Γ3 := fvarUpdate Γ2 2 L0
  let Γ4 := fvarUpdate Γ3 3 L0
  have hCtx1 : CtxWs 1 Γ1 := (CtxWs.zero Γ₀).update (by simp [Ix.Kernel.Expr.wscopedB])
  have hCtx2 : CtxWs 2 Γ2 := hCtx1.update (by simp [α0, Ix.Kernel.Expr.wscopedB])
  have hL0O : ∀ (d : Nat) (Γ : Nat → KExpr), 0 < d → Γ 0 = .sort (.succ .zero) →
      OpenType env d Γ L0 L0 (.succ .zero) := by
    intro d Γ hd hΓ0
    have hf0 : OpenAt env d Γ α0 α0 (.sort (.succ .zero)) := by
      have h := OpenAt.fvar (env := env) (d := d) (idx := 0) (Γ := Γ) hd
      rwa [hΓ0] at h
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc (d := d) (Γ := Γ) sk.sl.list0At rfl).app_nondep hf0 .refl rfl)
  have hCtx3 : CtxWs 3 Γ3 := hCtx2.update (FVarOk.wscopedB hCtx2 _ (hL0O 2 Γ2 (by omega) rfl).wOk)
  let hCharAt : ClosedAt env charT (.sort (.succ .zero)) := sk.sl.charAtType
  let haA := sk.sl.charAt a
  let hasA := sk.sl.charListAt as
  let hysA := sk.sl.charListAt ys
  have haW : haA.witness = charExpr a := sk.sl.charAt_w a
  have hasW : hasA.witness = charListExpr as := sk.sl.charListAt_w as
  have hysW : hysA.witness = charListExpr ys := sk.sl.charListAt_w ys
  have mkConsO : ∀ {x y xw yw : KExpr},
      OpenAt env 4 Γ4 x xw α0 → OpenAt env 4 Γ4 y yw L0 →
      OpenAt env 4 Γ4 (.app (.app (.app (.const (.role .listCons) [.zero]) α0) x) y)
        (.app (.app (.app (.const (.role .listCons) [.zero]) α0) xw) yw) L0 := by
    intro x y xw yw hx hy
    have hf0 : OpenAt env 4 Γ4 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 4) (idx := 0) (by omega)
    have h1 := (OpenAt.ofClosed hsc (d := 4) (Γ := Γ4) sk.sl.listCons0At rfl).app_dep hf0 .refl
    simp [Ix.Kernel.Expr.instantiate1, α0] at h1
    exact (h1.app_nondep hx .refl rfl).app_nondep hy .refl rfl
  have mkAppO : ∀ {x y xw yw : KExpr},
      OpenAt env 4 Γ4 x xw L0 → OpenAt env 4 Γ4 y yw L0 →
      OpenAt env 4 Γ4 (.app (.app (.app (.const (.role .listAppend) [.zero]) α0) x) y)
        (.app (.app (.app sk.listAppend0At.witness α0) xw) yw) L0 := by
    intro x y xw yw hx hy
    have hf0 : OpenAt env 4 Γ4 α0 α0 (.sort (.succ .zero)) := OpenAt.fvar (d := 4) (idx := 0) (by omega)
    have ha1 := (OpenAt.ofClosed hsc (d := 4) (Γ := Γ4) sk.listAppend0At rfl).app_abs hf0 .refl (by decide)
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, α0] at ha1
    have ha2 := ha1.app_nondep hx .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded])
    have ha3 := ha2.app_nondep hy .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded])
    simpa [L0, α0] using ha3
  have hf1 : OpenAt env 4 Γ4 a1 a1 α0 := OpenAt.fvar (d := 4) (idx := 1) (by omega)
  have hf2 : OpenAt env 4 Γ4 as2 as2 L0 := OpenAt.fvar (d := 4) (idx := 2) (by omega)
  have hf3 : OpenAt env 4 Γ4 ys3 ys3 L0 := OpenAt.fvar (d := 4) (idx := 3) (by omega)
  have hLhsO := mkAppO (mkConsO hf1 hf2) hf3
  have hRhsO := mkConsO hf1 (mkAppO hf2 hf3)
  let lhsW : KExpr := .app (.app (.app sk.listAppend0At.witness α0) (.app (.app (.app (.const (.role .listCons) [.zero]) α0) a1) as2)) ys3
  let rhsW : KExpr := .app (.app (.app (.const (.role .listCons) [.zero]) α0) a1) (.app (.app (.app sk.listAppend0At.witness α0) as2) ys3)
  have hLhsDe : DefEq env 0
      (.app (.app (.app sk.listAppend0At.witness charT) (charListExpr (a :: as))) (charListExpr ys))
      (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr (a :: as))) (charListExpr ys)) :=
    .app (.app (.app sk.listAppend0At.defEq_witness .refl) .refl) .refl
  have hRhsDe : DefEq env 0
      (.app (.app listConsCharE (charExpr a)) (.app (.app (.app sk.listAppend0At.witness charT) (charListExpr as)) (charListExpr ys)))
      (.app (.app listConsCharE (charExpr a)) (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr as)) (charListExpr ys))) :=
    .app .refl (.app (.app (.app sk.listAppend0At.defEq_witness .refl) .refl) .refl)
  have hD1 : OpenType env 1 Γ1 α0 α0 (.succ .zero) :=
    OpenType.ofOpenAt (OpenAt.fvar (d := 1) (idx := 0) (by omega))
  rcases hv with ⟨_, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · have hinst := DefEq.instClosed (d := 0) (ks := [0]) (us := [.zero]) rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hde
    simp only [eqnsSideExact, List.zipIdx, List.foldr,
      Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst.go,
      Ix.Kernel.Level.substPW, bmeta] at hinst
    have hL0O4 := hL0O 4 Γ4 (by omega) rfl
    have hLamL3 := OpenAt.lam_abs_inner_id (pw := .never) (hL0O 3 Γ3 (by omega) rfl) hLhsO hL0O4.wInfer hL0O4.wRed rfl rfl hCtx3
    have hLamL2 := OpenAt.lam_abs_outer_id (hL0O 2 Γ2 (by omega) rfl) hLamL3 hCtx2
    have hLamL1 := OpenAt.lam_abs_outer_id hD1 hLamL2 hCtx1
    have hLamL0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamL1
    have hLamR3 := OpenAt.lam_abs_inner_id (pw := .never) (hL0O 3 Γ3 (by omega) rfl) hRhsO hL0O4.wInfer hL0O4.wRed rfl rfl hCtx3
    have hLamR2 := OpenAt.lam_abs_outer_id (hL0O 2 Γ2 (by omega) rfl) hLamR3 hCtx2
    have hLamR1 := OpenAt.lam_abs_outer_id hD1 hLamR2 hCtx1
    have hLamR0 := OpenAt.lam_abs_outer_id (OpenType.sort (.succ .zero)) hLamR1
    have hChO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hCharAt rfl
    have haO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) haA rfl
    have hasO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hasA rfl
    have hysO := OpenAt.ofClosed hsc (d := 0) (Γ := Γ₀) hysA rfl
    have hAppL1 := hLamL0.app_abs hChO .refl (by decide)
    simp [α0, L0, fvarSubst, Ix.Kernel.Expr.abstract1, charT, hCharAt] at hAppL1
    have hAppL2 := hAppL1.app_nondep haO .refl rfl
    have hAppL3 := hAppL2.app_nondep hasO .refl rfl
    have hAppL4 := hAppL3.app_nondep hysO .refl rfl
    have hAppR1 := hLamR0.app_abs hChO .refl (by decide)
    simp [α0, L0, fvarSubst, Ix.Kernel.Expr.abstract1, charT, hCharAt] at hAppR1
    have hAppR2 := hAppR1.app_nondep haO .refl rfl
    have hAppR3 := hAppR2.app_nondep hasO .refl rfl
    have hAppR4 := hAppR3.app_nondep hysO .refl rfl
    have mkBeta4 : ∀ (bW : KExpr) (hbl : bW.looseBVarsBounded 0 = true),
        Red env 0
          (.app (.app (.app (.app (.lam (.sort (.succ .zero))
            ((Ix.Kernel.Expr.lam α0 ((Ix.Kernel.Expr.lam L0 ((Ix.Kernel.Expr.lam L0 (bW.abstract1 3) { pw := .never }).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }).abstract1 0)
            { pw := .never }) charT) haA.witness) hasA.witness) hysA.witness)
          (fvarSubst 3 hysA.witness (fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT bW)))) := by
      intro bW hbl
      have h1 : Red env 0
          (.app (.lam (.sort (.succ .zero))
            ((Ix.Kernel.Expr.lam α0 ((Ix.Kernel.Expr.lam L0 ((Ix.Kernel.Expr.lam L0 (bW.abstract1 3) { pw := .never }).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }).abstract1 0)
            { pw := .never }) charT)
          (.lam charT ((Ix.Kernel.Expr.lam charListT ((Ix.Kernel.Expr.lam charListT ((fvarSubst 0 charT bW).abstract1 3) { pw := .never }).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }) := by
        have h := Red.beta (env := env) (d := 0) (ty := .sort (.succ .zero)) (mb := { pw := .never })
          (body := (Ix.Kernel.Expr.lam α0 ((Ix.Kernel.Expr.lam L0 ((Ix.Kernel.Expr.lam L0 (bW.abstract1 3) { pw := .never }).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }).abstract1 0)
          hCharAt.wInfer.toIO .refl
        rw [abstract1_instantiate1_eq_fvarSubst (by
          simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 hbl, α0, L0])] at h
        simpa [α0, L0, fvarSubst,
          ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) (by decide : charT.hasFvar = false),
          ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) (by decide : charT.hasFvar = false),
          ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) (by decide : charT.hasFvar = false),
          charListT, charT, hCharAt] using h
      have hbl0 : (fvarSubst 0 charT bW).looseBVarsBounded 0 = true :=
        fvarSubst_looseBVarsBounded rfl hbl
      have h2 : Red env 0
          (.app (.lam charT ((Ix.Kernel.Expr.lam charListT ((Ix.Kernel.Expr.lam charListT ((fvarSubst 0 charT bW).abstract1 3) { pw := .never }).abstract1 2) { pw := .never }).abstract1 1) { pw := .never }) haA.witness)
          (.lam charListT ((Ix.Kernel.Expr.lam charListT ((fvarSubst 1 haA.witness (fvarSubst 0 charT bW)).abstract1 3) { pw := .never }).abstract1 2) { pw := .never }) := by
        have h := Red.beta (env := env) (d := 0) (ty := charT) (mb := { pw := .never })
          (body := (Ix.Kernel.Expr.lam charListT ((Ix.Kernel.Expr.lam charListT ((fvarSubst 0 charT bW).abstract1 3) { pw := .never }).abstract1 2) { pw := .never }).abstract1 1)
          haA.wInfer.toIO .refl
        rw [abstract1_instantiate1_eq_fvarSubst (by
          simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 hbl0, charListT, charT])] at h
        simpa [fvarSubst,
          ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) haA.wClosed.1,
          ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) haA.wClosed.1,
          charListT, charT] using h
      have hbl1 : (fvarSubst 1 haA.witness (fvarSubst 0 charT bW)).looseBVarsBounded 0 = true :=
        fvarSubst_looseBVarsBounded haA.wClosed.2 hbl0
      have h3 : Red env 0
          (.app (.lam charListT ((Ix.Kernel.Expr.lam charListT ((fvarSubst 1 haA.witness (fvarSubst 0 charT bW)).abstract1 3) { pw := .never }).abstract1 2) { pw := .never }) hasA.witness)
          (.lam charListT ((fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT bW))).abstract1 3) { pw := .never }) := by
        have h := Red.beta (env := env) (d := 0) (ty := charListT) (mb := { pw := .never })
          (body := (Ix.Kernel.Expr.lam charListT ((fvarSubst 1 haA.witness (fvarSubst 0 charT bW)).abstract1 3) { pw := .never }).abstract1 2)
          hasA.wInfer.toIO .refl
        rw [abstract1_instantiate1_eq_fvarSubst (by
          simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 hbl1, charT])] at h
        simpa [fvarSubst,
          ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hasA.wClosed.1,
          charListT, charT] using h
      have hbl2 : (fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT bW))).looseBVarsBounded 0 = true :=
        fvarSubst_looseBVarsBounded hasA.wClosed.2 hbl1
      have h4 : Red env 0
          (.app (.lam charListT ((fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT bW))).abstract1 3) { pw := .never }) hysA.witness)
          (fvarSubst 3 hysA.witness (fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT bW)))) := by
        have h := Red.beta (env := env) (d := 0) (ty := charListT) (mb := { pw := .never })
          (body := (fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT bW))).abstract1 3)
          hysA.wInfer.toIO .refl
        rwa [abstract1_instantiate1_eq_fvarSubst hbl2] at h
      exact .trans (.appFn (.appFn (.appFn h1))) (.trans (.appFn (.appFn h2)) (.trans (.appFn h3) h4))
    have hRL := mkBeta4 lhsW (by simp [lhsW, Ix.Kernel.Expr.looseBVarsBounded, sk.listAppend0At.wClosed.2, α0, a1, as2, ys3])
    have hRR := mkBeta4 rhsW (by simp [rhsW, Ix.Kernel.Expr.looseBVarsBounded, sk.listAppend0At.wClosed.2, α0, a1, as2, ys3])
    have hLclean : fvarSubst 3 hysA.witness (fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT lhsW))) =
        .app (.app (.app sk.listAppend0At.witness charT) (charListExpr (a :: as))) (charListExpr ys) := by
      simp [lhsW, α0, a1, as2, ys3, fvarSubst, fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1,
        fvarSubst_of_not_hasFvar hasA.closed.1, haW, hasW, hysW, charListExpr, charExpr, charOfNatE,
        listConsCharE, charT]
    have hRclean : fvarSubst 3 hysA.witness (fvarSubst 2 hasA.witness (fvarSubst 1 haA.witness (fvarSubst 0 charT rhsW))) =
        .app (.app listConsCharE (charExpr a)) (.app (.app (.app sk.listAppend0At.witness charT) (charListExpr as)) (charListExpr ys)) := by
      simp [rhsW, α0, a1, as2, ys3, fvarSubst, fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1,
        fvarSubst_of_not_hasFvar hasA.closed.1, haW, hasW, hysW, charExpr, charOfNatE,
        listConsCharE, charT]
    rw [hLclean] at hRL
    rw [hRclean] at hRR
    exact OpenAt.defEq_chain hAppL4 hAppR4 (.app (.app (.app (.app hinst .refl) .refl) .refl) .refl)
      hRL hLhsDe hRR hRhsDe
  · have hlen : cv.levelParams.length = 1 := Option.some.inj (hlv.symm.trans (by decide))
    have hEqO := OpenType.eq sk.bk.eqStored (hL0O 4 Γ4 (by omega) rfl) hLhsO .refl hRhsO .refl
    have hB3O := OpenType.forallE_abs_id (pw := .ifAllZero []) (hL0O 3 Γ3 (by omega) rfl) hEqO rfl hCtx3
    have hB2O := OpenType.forallE_abs_id (pw := .ifAllZero []) (hL0O 2 Γ2 (by omega) rfl) hB3O rfl hCtx2
    have hB1O := OpenType.forallE_abs_id (pw := .ifAllZero []) hD1 hB2O rfl hCtx1
    have hStmtO := OpenType.forallE_abs_id (pw := .ifAllZero []) (OpenType.sort (.succ .zero)) hB1O rfl
    have hPiRed := hStmtO.wPiRed
    have heqStmt :
        (Ix.Kernel.Expr.forallE (.sort (.succ .zero))
          ((Ix.Kernel.Expr.forallE α0
            ((Ix.Kernel.Expr.forallE L0
              ((Ix.Kernel.Expr.forallE L0
                ((Ix.Kernel.Expr.app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) L0)
                  (.app (.app (.app (.const (.role .listAppend) [.zero]) α0)
                    (.app (.app (.app (.const (.role .listCons) [.zero]) α0) a1) as2)) ys3))
                  (.app (.app (.app (.const (.role .listCons) [.zero]) α0) a1)
                    (.app (.app (.app (.const (.role .listAppend) [.zero]) α0) as2) ys3))).abstract1 3)
                { pw := .ifAllZero [] }).abstract1 2)
              { pw := .ifAllZero [] }).abstract1 1)
            { pw := .ifAllZero [] }).abstract1 0)
          { pw := .ifAllZero [] }) =
        ((eqnsStmtExact (eqnsOfRole .listAppend)[1]!).instantiateLevelParams [0] [.zero]) := by
      decide
    rw [heqStmt] at hPiRed
    have hp0 := ClosedAt.ofThm1_de hsc sk.bk.wf hf hlen hde (by decide) ⟨by decide, by decide⟩
      hPiRed hStmtO.toClosedType
    have hp1 := hp0.app_abs hCharAt .refl hB1O.wClosed
    simp [α0, L0, a1, as2, ys3, fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) (by decide : charT.hasFvar = false),
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 2) (by decide : charT.hasFvar = false),
      ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 3) (by decide : charT.hasFvar = false),
      fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1, hCharAt] at hp1
    have hp2 := hp1.app_abs haA .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ,
        lbb_of_lbb0 sk.listAppend0At.wClosed.2, charT])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 2) haA.wClosed.1,
      ← fvarSubst_abstract1_comm (by decide : (1 : Nat) ≠ 3) haA.wClosed.1,
      fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1, charT] at hp2
    have hp3 := hp2.app_abs hasA .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ,
        lbb_of_lbb0 sk.listAppend0At.wClosed.2, lbb_of_lbb0 haA.wClosed.2])
    simp [fvarSubst,
      ← fvarSubst_abstract1_comm (by decide : (2 : Nat) ≠ 3) hasA.wClosed.1,
      fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1,
      fvarSubst_of_not_hasFvar haA.wClosed.1] at hp3
    have hp4 := hp3.app_abs hysA .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, sk.listAppend0At.wClosed.2,
        haA.wClosed.2, hasA.wClosed.2])
    simp [fvarSubst, fvarSubst_of_not_hasFvar sk.listAppend0At.wClosed.1,
      fvarSubst_of_not_hasFvar haA.closed.1, fvarSubst_of_not_hasFvar hasA.closed.1,
      haW, hasW, hysW, charListT, charT] at hp4
    exact defEq_of_eqProof_de hsc sk.bk.eqStored hp4
      (.app (.app (.app .refl .refl) hLhsDe) hRhsDe)
      (sk.listAppendCharApp (sk.sl.charListAt (a :: as)) hysA)
      ((sk.sl.listConsCharAt.app_nondep haA rfl).app_nondep (sk.listAppendCharApp hasA hysA) rfl)
      sk.sl.charListType

private theorem defEq_listAppend_chars : ∀ (xs ys : List Char),
    DefEq env 0
      (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr xs)) (charListExpr ys))
      (charListExpr (xs ++ ys))
  | [], ys => sk.defEq_listAppend_nil ys
  | a :: as, ys =>
    ((sk.sl.listConsCharAt.app_nondep (sk.sl.charAt a) rfl).app_nondep
      (sk.listAppendCharApp (sk.sl.charListAt as) (sk.sl.charListAt ys)) rfl).defEq_trans
      (sk.defEq_listAppend_cons a as ys)
      (.app .refl (defEq_listAppend_chars as ys))

private theorem defEq_strAppend_ofList (xs ys : List Char) :
    DefEq env 0
      (.app (.app (.const (.role .stringAppend) []) (.app stringOfListE (charListExpr xs)))
        (.app stringOfListE (charListExpr ys)))
      (.app stringOfListE
        (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr xs)) (charListExpr ys))) := by
  have hsc := sk.bk.storeClosed
  have hv := eqnValid_of sk.hs .stringAppend (by decide) (by decide) (k := 0) rfl
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 charListT) 1 charListT
  have hLhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 charListT) (fvarSubst 0 (.fvar 0 charListT)
        (.app (.app (.const (.role .stringAppend) []) (.app stringOfListE (Ix.Kernel.specVar 0 charListT)))
          (.app stringOfListE (Ix.Kernel.specVar 1 charListT)))))
      (.app (.app sk.strAppendAt.witness (.app stringOfListE (.fvar 0 charListT)))
        (.app stringOfListE (.fvar 1 charListT))) stringT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 charListT) (.fvar 0 charListT) charListT := OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 charListT) (.fvar 1 charListT) charListT := OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have hs0 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.stringOfListAt rfl).app_nondep hf0 .refl rfl
    have hs1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.stringOfListAt rfl).app_nondep hf1 .refl rfl
    have ha := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.strAppendAt rfl).app_nondep hs0 .refl rfl).app_nondep hs1 .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, stringOfListE] using ha
  have hRhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 charListT) (fvarSubst 0 (.fvar 0 charListT)
        (.app stringOfListE (.app (.app (.app (.const (.role .listAppend) [.zero]) charT)
          (Ix.Kernel.specVar 0 charListT)) (Ix.Kernel.specVar 1 charListT)))))
      (.app stringOfListE (.app (.app sk.listAppendCharAt.witness (.fvar 0 charListT)) (.fvar 1 charListT)))
      stringT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 charListT) (.fvar 0 charListT) charListT := OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 charListT) (.fvar 1 charListT) charListT := OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have hla := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.listAppendCharAt rfl).app_nondep hf0 .refl rfl).app_nondep hf1 .refl rfl
    have hsol := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) sk.sl.stringOfListAt rfl).app_nondep hla .refl rfl
    simpa [Ix.Kernel.specVar, fvarSubst, stringOfListE, charT] using hsol
  let hxsA := sk.sl.charListAt xs
  let hysA := sk.sl.charListAt ys
  have hxsW : hxsA.witness = charListExpr xs := sk.sl.charListAt_w xs
  have hysW : hysA.witness = charListExpr ys := sk.sl.charListAt_w ys
  exact applyEqn2 sk.bk hv (by decide)
    (T₀ := charListT) (T₀w := charListT) (T₁ := charListT) (T₁w := charListT) (Cw := stringT)
    (lhsW := .app (.app sk.strAppendAt.witness (.app stringOfListE (.fvar 0 charListT))) (.app stringOfListE (.fvar 1 charListT)))
    (rhsW := .app stringOfListE (.app (.app sk.listAppendCharAt.witness (.fvar 0 charListT)) (.fvar 1 charListT)))
    (a := charListExpr xs) (b := charListExpr ys)
    (lhsAB := .app (.app (.const (.role .stringAppend) []) (.app stringOfListE (charListExpr xs))) (.app stringOfListE (charListExpr ys)))
    (rhsAB := .app stringOfListE (.app (.app (.app (.const (.role .listAppend) [.zero]) charT) (charListExpr xs)) (charListExpr ys)))
    rfl rfl rfl sk.sl.stringType .refl rfl rfl
    (sk.sl.charListType_open 0 Γ₀) (sk.sl.charListType_open 0 Γ₀) rfl rfl
    (by decide) (by decide) (by decide) (by decide)
    hLhsO hRhsO hxsA hysA
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specOfList, Ix.Kernel.specCharList, Ix.Kernel.specC,
      Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specVar, fvarSubst,
      fvarSubst_of_not_hasFvar hxsA.closed.1, stringOfListE])
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specOfList, Ix.Kernel.specCharList, Ix.Kernel.specC,
      Ix.Kernel.BasisDSL.ap3, Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specVar, fvarSubst,
      fvarSubst_of_not_hasFvar hxsA.closed.1, stringOfListE, charT])
    (by
      rw [hxsW, hysW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.strAppendAt.wClosed.1,
        fvarSubst_of_not_hasFvar hxsA.closed.1, ↓reduceIte, stringOfListE]
      exact .app (.app sk.strAppendAt.defEq_witness .refl) .refl)
    (by
      rw [hxsW, hysW]
      simp only [fvarSubst, fvarSubst_of_not_hasFvar sk.listAppendCharAt.wClosed.1,
        fvarSubst_of_not_hasFvar hxsA.closed.1, ↓reduceIte, stringOfListE]
      exact .app .refl (.app (.app sk.listAppendCharAt.defEq_witness .refl) .refl))
    ((sk.strAppendAt.app_nondep (sk.sl.strOfListApp hxsA) rfl).app_nondep (sk.sl.strOfListApp hysA) rfl)
    (sk.sl.strOfListApp (sk.listAppendCharApp hxsA hysA))

theorem defEq_strAppend (s₁ s₂ : String) :
    DefEq env 0
      (.app (.app (.const (.role .stringAppend) []) (.lit (.strVal s₁))) (.lit (.strVal s₂)))
      (.lit (.strVal (s₁ ++ s₂))) := by
  have h1 : Red env 0 (.lit (.strVal s₁)) (.app stringOfListE (charListExpr s₁.toList)) := by
    rw [← strLitToConstructor_eq_charListExpr]; exact .strLit sk.sl.strLit
  have h2 : Red env 0 (.lit (.strVal s₂)) (.app stringOfListE (charListExpr s₂.toList)) := by
    rw [← strLitToConstructor_eq_charListExpr]; exact .strLit sk.sl.strLit
  have h3 : Red env 0 (.app stringOfListE (charListExpr (s₁.toList ++ s₂.toList)))
      (.lit (.strVal (s₁ ++ s₂))) := by
    have hl : (s₁ ++ s₂).toList = s₁.toList ++ s₂.toList := by simp
    rw [← hl, ← strLitToConstructor_eq_charListExpr]
    exact .strLitFold sk.sl.strLit
  have hMid1 := sk.sl.strOfListApp (sk.listAppendCharApp (sk.sl.charListAt s₁.toList) (sk.sl.charListAt s₂.toList))
  have hMid2 := sk.sl.strOfListApp (sk.sl.charListAt (s₁.toList ++ s₂.toList))
  have hmid := hMid1.defEq_trans
    (sk.defEq_strAppend_ofList s₁.toList s₂.toList)
    (.app .refl (sk.defEq_listAppend_chars s₁.toList s₂.toList))
  exact .redL (.trans (.appFn (.appArg h1)) (.appArg h2))
    (hMid2.defEq_trans hmid (.redL h3 .refl))

end StrKit

end StrKitSec

/-! ## Assembling `String`/`Char` equation reductions from `BaseKit`, `strLitSupported`, and `Shapes (· < 77)` -/

structure StrPrimEqns (env : Ix.Kernel.Env .anon) : Prop where
  strOpStored : ∀ r : Role,
    r ∈ [.stringUtf8ByteSize, .stringBack, .stringToByteArray, .stringDecEq, .stringAppend,
      .charUtf8Size] →
    ∃ ci, env.find? (.role r) = some ci
  charOfNatStored : ∃ ci, env.find? (.role .charOfNat) = some ci
  byteArrayEmptyStored : ∃ ci, env.find? (.role .byteArrayEmpty) = some ci
  stringStored : ∃ ci, env.find? (.role .string) = some ci
  eqStored : ∃ ci, env.find? (.role .eq) = some ci
  eqReflStored : ∃ ci, env.find? (.role .eqRefl) = some ci
  decidableIsTrueStored : ∃ ci, env.find? (.role .decidableIsTrue) = some ci
  charUtf8Size : ∀ d (c : Char),
    Red env d
      (.app (.const (.role .charUtf8Size) []) (.app (.const (.role .charOfNat) []) (.lit (.natVal c.toNat))))
      (.lit (.natVal c.utf8Size))
  strUtf8ByteSize : ∀ d (s : String),
    Red env d (.app (.const (.role .stringUtf8ByteSize) []) (.lit (.strVal s)))
      (.lit (.natVal s.utf8ByteSize))
  strBack : ∀ d (s : String),
    Red env d (.app (.const (.role .stringBack) []) (.lit (.strVal s)))
      (.app (.const (.role .charOfNat) []) (.lit (.natVal (s.toList.getLastD 'A').toNat)))
  strToByteArrayEmpty : ∀ d,
    Red env d (.app (.const (.role .stringToByteArray) []) (.lit (.strVal "")))
      (.const (.role .byteArrayEmpty) [])
  strDecEqRefl : ∀ d (s : String),
    Red env d (.app (.app (.const (.role .stringDecEq) []) (.lit (.strVal s))) (.lit (.strVal s)))
      (.app (.app (.const (.role .decidableIsTrue) [])
        (.app (.app (.app (.const (.role .eq) [.succ .zero]) (.const (.role .string) []))
          (.lit (.strVal s))) (.lit (.strVal s))))
        (.app (.app (.const (.role .eqRefl) [.succ .zero]) (.const (.role .string) []))
          (.lit (.strVal s))))
  strAppend : ∀ d (s₁ s₂ : String),
    Red env d (.app (.app (.const (.role .stringAppend) []) (.lit (.strVal s₁))) (.lit (.strVal s₂)))
      (.lit (.strVal (s₁ ++ s₂)))

theorem strPrimEqns_of_shapes {env : Ix.Kernel.Env .anon}
    (bk : BaseKit env) (hsup : Ix.Kernel.strLitSupported env = true)
    (hs : Shapes (· < 77) env) : StrPrimEqns env := by
  obtain ⟨wDec, wNot, wDecide, wInt, wIntLe, wIntOfNat, wIntAdd, wBA, ⟨sk⟩⟩ :=
    strKit_exists bk hsup hs
  have hStrOpS : ∀ r : Role,
      r ∈ [.stringUtf8ByteSize, .stringBack, .stringToByteArray, .stringDecEq, .stringAppend,
        .charUtf8Size] →
      ∃ ci, env.find? (.role r) = some ci := by
    intro r hr
    have h46 : 46 ≤ Ix.SpecDigest.groupOf r := by
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
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · cases hr
    obtain ⟨ci, _, hf, -⟩ := roleExact_eqns hs r h46 h5
    exact ⟨ci, hf⟩
  have hBAEmptyS : ∃ ci, env.find? (.role .byteArrayEmpty) = some ci := by
    obtain ⟨ci, _, hf, -⟩ := roleExact_anchor_of hs .stringToByteArray .byteArrayEmpty
      (by decide) (by decide) (by decide)
    exact ⟨ci, hf⟩
  have hDecIsTrueS : ∃ ci, env.find? (.role .decidableIsTrue) = some ci := by
    obtain ⟨ci, _, hf, -⟩ := roleExact_anchor_of hs .decidableDecide .decidableIsTrue
      (by decide) (by decide) (by decide)
    exact ⟨ci, hf⟩
  exact {
    strOpStored := hStrOpS
    charOfNatStored := sk.sl.charOfNatStored
    byteArrayEmptyStored := hBAEmptyS
    stringStored := sk.sl.stringStored
    eqStored := ⟨_, bk.eqStored⟩
    eqReflStored := ⟨_, bk.eqReflStored⟩
    decidableIsTrueStored := hDecIsTrueS
    charUtf8Size := fun d c =>
      ClosedAt.red_of_defEq rfl (sk.charUtf8SizeAt.app_nondep (sk.sl.charAt c) rfl)
        (bk.natLitAt c.utf8Size) (sk.defEq_charUtf8Size c) d
    strUtf8ByteSize := fun d s =>
      ClosedAt.red_of_defEq rfl (sk.strUtf8ByteSizeAt.app_nondep (sk.sl.strLitAt s) rfl)
        (bk.natLitAt s.utf8ByteSize) (sk.defEq_strUtf8ByteSize s) d
    strBack := fun d s =>
      ClosedAt.red_of_defEq rfl (sk.strBackAt.app_nondep (sk.sl.strLitAt s) rfl)
        (sk.sl.charAt (s.toList.getLastD 'A')) (sk.defEq_strBack s) d
    strToByteArrayEmpty := fun d =>
      ClosedAt.red_of_defEq rfl
        (sk.strToByteArrayAt.app_nondep (sk.sl.strLitAt "") sk.wBA_cl.2)
        sk.baEmptyAt sk.defEq_strToByteArrayEmpty d
    strDecEqRefl := fun d s => by
      let sLit : KExpr := .lit (.strVal s)
      let eqPS : KExpr := .app (.app (.app (.const Ix.Kernel.eqName [.succ .zero]) stringT) sLit) sLit
      let hsAt : ClosedAt env sLit stringT := sk.sl.strLitAt s
      let hEqCT := closedType_eq bk.eqStored sk.sl.stringType hsAt.wInfer hsAt.wClosed hsAt.wInfer hsAt.wClosed
      let hEqPS : ClosedAt env eqPS (.sort .zero) := .ofInfer hEqCT.closed hEqCT.infer
      have hLhs : ClosedAt env (.app (.app (.const (.role .stringDecEq) []) sLit) sLit) (.app wDec eqPS) := by
        have h1 := sk.strDecEqAt.app_abs hsAt .refl
          (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 sk.ik.wDec_cl.2, stringT])
        simp [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hsAt.wClosed.1,
          fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1, stringT] at h1
        have h2 := h1.app_abs hsAt .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, sk.ik.wDec_cl.2, hsAt.wClosed.2])
        simpa [fvarSubst, fvarSubst_of_not_hasFvar sk.ik.wDec_cl.1,
          fvarSubst_of_not_hasFvar hsAt.wClosed.1, eqPS, sLit, hsAt] using h2
      have hRhs : ClosedAt env
          (.app (.app (.const (.role .decidableIsTrue) []) eqPS)
            (.app (.app (.const (.role .eqRefl) [.succ .zero]) stringT) sLit))
          (.app wDec eqPS) :=
        sk.ik.isTrueApp hEqPS (closedAt_eqRefl bk.eqReflStored sk.sl.stringType hsAt)
      exact ClosedAt.red_of_defEq rfl hLhs hRhs (sk.defEq_strDecEqRefl s) d
    strAppend := fun d s₁ s₂ =>
      ClosedAt.red_of_defEq rfl
        ((sk.strAppendAt.app_nondep (sk.sl.strLitAt s₁) rfl).app_nondep (sk.sl.strLitAt s₂) rfl)
        (sk.sl.strLitAt (s₁ ++ s₂)) (sk.defEq_strAppend s₁ s₂) d }

end IxVM.Refinement.Binding
