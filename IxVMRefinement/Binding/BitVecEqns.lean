import IxVMRefinement.Binding.StrEqns

/-! # Certified `BitVec` equation reductions and `PrimEqnEnv` assembly

Derives `BitVec.toNat` and `BitVec.ult` reductions from the validated equations (`bitVecToNatEqns`,
`bitVecUltEqns`) and `Red.natOp` (with the `w ≤ 2^24` cap on `Nat.pow`), then assembles the
complete `Core.PrimEqnEnv` (`Int`, `String`/`Char`, `BitVec`) at group 76 of the binding fold. -/

namespace IxVM.Refinement.Binding

open Ix.Kernel (Role)
open Ix.Kernel.Rules (Red DefEq Infer)
open IxVM.Refinement.Core (KExpr KLevel)

section BitVecKitSec

variable {env : Ix.Kernel.Env .anon}

/-- Typing kit for the `BitVec` roles (`BitVec`, `BitVec.ofNat`, `BitVec.toNat`, `BitVec.ult`). -/
structure BitVecKit (env : Ix.Kernel.Env .anon) (wBV : KExpr) where
  bk : BaseKit env
  hs : Shapes (· < 77) env
  bvAt : ClosedAt env (.const (.role .bitVec) []) (.forallE BaseKit.natT (.sort (.succ .zero)) { pw := .never })
  bvW : bvAt.witness = wBV
  wBV_cl : TermClosed wBV
  bvOfNatAt : ClosedAt env (.const (.role .bitVecOfNat) [])
    (.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE BaseKit.natT
        ((Ix.Kernel.Expr.app wBV (.fvar 0 BaseKit.natT)).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  bvOfNatTy_nf :
    (Ix.Kernel.Expr.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE BaseKit.natT
        ((Ix.Kernel.Expr.app wBV (.fvar 0 BaseKit.natT)).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  bvToNatAt : ClosedAt env (.const (.role .bitVecToNat) [])
    (.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT)) BaseKit.natT { pw := .never }).abstract1 0)
      { pw := .never })
  bvToNatTy_nf :
    (Ix.Kernel.Expr.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT)) BaseKit.natT { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false
  bvUltAt : ClosedAt env (.const (.role .bitVecUlt) [])
    (.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT))
        ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT)) BaseKit.boolT { pw := .never }).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never })
  bvUltTy_nf :
    (Ix.Kernel.Expr.forallE BaseKit.natT
      ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT))
        ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT)) BaseKit.boolT { pw := .never }).abstract1 1)
        { pw := .never }).abstract1 0)
      { pw := .never }).hasFvar = false

theorem bitVecKit_exists (bk : BaseKit env) (hs : Shapes (· < 77) env) :
    ∃ wBV, Nonempty (BitVecKit env wBV) := by
  have hsc := bk.storeClosed
  have bvAt : ClosedAt env (.const (.role .bitVec) [])
      (.forallE BaseKit.natT (.sort (.succ .zero)) { pw := .never }) :=
    ClosedAt.ofRole0 hsc
      (roleExact_anchor_of hs .bitVecToNat .bitVec (by decide) (by decide) (by decide))
      (by decide) rfl
      (ClosedType.forall_nondep hsc bk.natType (ClosedType.sort env (.succ .zero)))
  let wBV := bvAt.witness
  have hwBVCl : TermClosed wBV := bvAt.wClosed
  have hBVApp : ∀ (d : Nat) (Γ : Nat → KExpr), 0 < d → Γ 0 = BaseKit.natT →
      OpenType env d Γ
        (.app (.const (.role .bitVec) []) (.fvar 0 BaseKit.natT))
        (.app wBV (.fvar 0 BaseKit.natT)) (.succ .zero) := by
    intro d Γ hd hΓ0
    have hf0 : OpenAt env d Γ (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT := by
      have h := OpenAt.fvar (env := env) (d := d) (idx := 0) (Γ := Γ) hd
      rwa [hΓ0] at h
    exact OpenType.ofOpenAt ((OpenAt.ofClosed hsc bvAt rfl).app_nondep hf0 .refl rfl)
  -- BitVec.ofNat : (n : Nat) → Nat → BitVec n
  have bvOfNatO : OpenType env 0 Γ₀
      (.forallE BaseKit.natT
        (.forallE BaseKit.natT (.app (.const (.role .bitVec) []) (.bvar 1)) { pw := .never })
        { pw := .never })
      (.forallE BaseKit.natT
        ((Ix.Kernel.Expr.forallE BaseKit.natT
          ((Ix.Kernel.Expr.app wBV (.fvar 0 BaseKit.natT)).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (OpenType.ofClosed hsc bk.natType) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (OpenType.ofClosed hsc bk.natType) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    exact hBVApp 2 _ (by omega) rfl
  have bvOfNatAt := ClosedAt.ofRole0_open hsc
    (roleExact_anchor_of hs .bitVecToNat .bitVecOfNat (by decide) (by decide) (by decide))
    (by decide) rfl bvOfNatO
  -- BitVec.toNat : {w : Nat} → BitVec w → Nat
  have bvToNatO : OpenType env 0 Γ₀
      (.forallE BaseKit.natT
        (.forallE (.app (.const (.role .bitVec) []) (.bvar 0)) BaseKit.natT { pw := .never })
        { pw := .never })
      (.forallE BaseKit.natT
        ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT)) BaseKit.natT { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) := by
    refine OpenType.forallE (OpenType.ofClosed hsc bk.natType) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    show OpenType env 1 _
      (.forallE (.app (.const (.role .bitVec) []) (.fvar 0 BaseKit.natT)) BaseKit.natT { pw := .never })
      (.forallE (.app wBV (.fvar 0 BaseKit.natT)) (BaseKit.natT.abstract1 1) { pw := .never })
      (.imax (.succ .zero) (.succ .zero))
    refine OpenType.forallE (hBVApp 1 _ (by omega) rfl) ?_ rfl
    exact OpenType.ofClosed hsc bk.natType
  have bvToNatAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .bitVecToNat (by decide) (by decide)) (by decide) rfl bvToNatO
  -- BitVec.ult : {n : Nat} → BitVec n → BitVec n → Bool
  have bvUltO : OpenType env 0 Γ₀
      (.forallE BaseKit.natT
        (.forallE (.app (.const (.role .bitVec) []) (.bvar 0))
          (.forallE (.app (.const (.role .bitVec) []) (.bvar 1)) BaseKit.boolT { pw := .never })
          { pw := .never })
        { pw := .never })
      (.forallE BaseKit.natT
        ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT))
          ((Ix.Kernel.Expr.forallE (.app wBV (.fvar 0 BaseKit.natT)) BaseKit.boolT { pw := .never }).abstract1 1)
          { pw := .never }).abstract1 0)
        { pw := .never })
      (.imax (.succ .zero) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) := by
    refine OpenType.forallE (OpenType.ofClosed hsc bk.natType) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    refine OpenType.forallE (hBVApp 1 _ (by omega) rfl) ?_ rfl
    simp only [Ix.Kernel.Expr.instantiate1]
    show OpenType env 2 _
      (.forallE (.app (.const (.role .bitVec) []) (.fvar 0 BaseKit.natT)) BaseKit.boolT { pw := .never })
      (.forallE (.app wBV (.fvar 0 BaseKit.natT)) (BaseKit.boolT.abstract1 2) { pw := .never })
      (.imax (.succ .zero) (.succ .zero))
    refine OpenType.forallE (hBVApp 2 _ (by omega) rfl) ?_ rfl
    exact OpenType.ofClosed hsc bk.boolType
  have bvUltAt := ClosedAt.ofRole0_open hsc
    (roleExact_eqns hs .bitVecUlt (by decide) (by decide)) (by decide) rfl bvUltO
  exact ⟨wBV, ⟨{
    bk := bk, hs := hs, bvAt := bvAt, bvW := rfl, wBV_cl := hwBVCl
    bvOfNatAt := bvOfNatAt, bvOfNatTy_nf := bvOfNatO.wOk.hasFvar_false
    bvToNatAt := bvToNatAt, bvToNatTy_nf := bvToNatO.wOk.hasFvar_false
    bvUltAt := bvUltAt, bvUltTy_nf := bvUltO.wOk.hasFvar_false }⟩⟩

namespace BitVecKit

variable {wBV : KExpr} (bvk : BitVecKit env wBV)
include bvk

private def bvOfNatApp (w n : Nat) :
    ClosedAt env
      (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n)))
      (.app wBV (.lit (.natVal w))) := by
  let hw := bvk.bk.natLitAt w
  let hn := bvk.bk.natLitAt n
  have h1 := bvk.bvOfNatAt.app_abs hw .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 bvk.wBV_cl.2])
  simp only [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hw.wClosed.1,
    fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at h1
  have h2 := h1.app_abs hn .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2, hw.wClosed.2])
  simpa [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1, fvarSubst_of_not_hasFvar hw.wClosed.1] using h2

private def bvToNatApp (w n : Nat) :
    ClosedAt env
      (.app (.app (.const (.role .bitVecToNat) []) (.lit (.natVal w)))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n))))
      BaseKit.natT := by
  let hw := bvk.bk.natLitAt w
  have h1 := bvk.bvToNatAt.app_abs hw .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2])
  simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at h1
  exact h1.app_nondep (bvk.bvOfNatApp w n) rfl

private def bvUltApp (w n₁ n₂ : Nat) :
    ClosedAt env
      (.app (.app (.app (.const (.role .bitVecUlt) []) (.lit (.natVal w)))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₁))))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₂))))
      BaseKit.boolT := by
  let hw := bvk.bk.natLitAt w
  have h1 := bvk.bvUltAt.app_abs hw .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 bvk.wBV_cl.2])
  simp only [fvarSubst, ← fvarSubst_abstract1_comm (by decide : (0 : Nat) ≠ 1) hw.wClosed.1,
    fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at h1
  have h2 := h1.app_abs (bvk.bvOfNatApp w n₁) .refl
    (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2, hw.wClosed.2])
  simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1,
    fvarSubst_of_not_hasFvar hw.wClosed.1] at h2
  exact h2.app_nondep (bvk.bvOfNatApp w n₂) rfl

private theorem red_specTwo : Red env 0 (Ix.Kernel.specTwo (md := .anon)) (.lit (.natVal 2)) :=
  .trans (.appArg (.trans (.appArg bvk.bk.red_natZero_lit) (bvk.bk.red_natSucc_lit 0)))
    (bvk.bk.red_natSucc_lit 1)

private def specTwoAt : ClosedAt env (Ix.Kernel.specTwo (md := .anon)) BaseKit.natT :=
  bvk.bk.natSuccApp (bvk.bk.natSuccApp bvk.bk.natZeroAt)

private theorem red_specMod2Pow (x w : Nat) (hw : w ≤ 2 ^ 24) :
    Red env 0 (Ix.Kernel.specMod2Pow (.lit (.natVal x)) (.lit (.natVal w)))
      (.lit (.natVal (x % 2 ^ w))) := by
  have hpowRes : Ix.Kernel.natOpResult (md := .anon) (.role .natPow) 2 w =
      some (.lit (.natVal (2 ^ w))) := by
    have hng : ¬ (w > 16777216) := by omega
    simp [Ix.Kernel.natOpResult, Ix.Kernel.natPowName, hng]
  have hpow : Red env 0
      (.app (.app (.const (.role .natPow) []) (Ix.Kernel.specTwo (md := .anon))) (.lit (.natVal w)))
      (.lit (.natVal (2 ^ w))) :=
    .trans (.appFn (.appArg bvk.red_specTwo))
      (bvk.bk.red_natOp (r := .natPow) (by decide) hpowRes)
  exact .trans (.appArg hpow)
    (bvk.bk.red_natOp (r := .natMod) (by decide) (a := x) (b := 2 ^ w) rfl)

theorem defEq_bitVecToNat (w n : Nat) (hw : w ≤ 2 ^ 24) :
    DefEq env 0
      (.app (.app (.const (.role .bitVecToNat) []) (.lit (.natVal w)))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n))))
      (.lit (.natVal (n % 2 ^ w))) := by
  have hsc := bvk.bk.storeClosed
  have hv := eqnValid_of bvk.hs .bitVecToNat (by decide) (by decide) (k := 0) rfl
  obtain ⟨_, _, ⟨hMod⟩⟩ := bvk.bk.natBinNatAt (r := .natMod) (by decide) (by decide) (by decide)
  obtain ⟨_, _, ⟨hPow⟩⟩ := bvk.bk.natBinNatAt (r := .natPow) (by decide) (by decide) (by decide)
  let Γ2 := fvarUpdate (fvarUpdate Γ₀ 0 BaseKit.natT) 1 BaseKit.natT
  have hLhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 BaseKit.natT) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.BasisDSL.ap2 (Ix.Kernel.specC .bitVecToNat) (Ix.Kernel.specVar 0 BaseKit.natT)
          (Ix.Kernel.BasisDSL.ap2 (Ix.Kernel.specC .bitVecOfNat)
            (Ix.Kernel.specVar 0 BaseKit.natT) (Ix.Kernel.specVar 1 BaseKit.natT)))))
      (.app (.app bvk.bvToNatAt.witness (.fvar 0 BaseKit.natT))
        (.app (.app bvk.bvOfNatAt.witness (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT)))
      BaseKit.natT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 BaseKit.natT) (.fvar 1 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have hon1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) bvk.bvOfNatAt bvk.bvOfNatTy_nf).app_abs hf0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 bvk.wBV_cl.2])
    simp only [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at hon1
    have hon2 := hon1.app_abs hf1 .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2])
    simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1,
      (by decide : ¬ (0 : Nat) = 1), ↓reduceIte] at hon2
    have htn1 := (OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) bvk.bvToNatAt bvk.bvToNatTy_nf).app_abs hf0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2])
    simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at htn1
    have htn2 := htn1.app_nondep hon2 .refl rfl
    simpa [Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specVar,
      fvarSubst] using htn2
  have hRhsO : OpenAt env 2 Γ2
      (fvarSubst 1 (.fvar 1 BaseKit.natT) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.specMod2Pow (Ix.Kernel.specVar 1 BaseKit.natT) (Ix.Kernel.specVar 0 BaseKit.natT))))
      (.app (.app hMod.witness (.fvar 1 BaseKit.natT))
        (.app (.app hPow.witness (Ix.Kernel.specTwo (md := .anon))) (.fvar 0 BaseKit.natT)))
      BaseKit.natT := by
    have hf0 : OpenAt env 2 Γ2 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 2) (idx := 0) (by omega)
    have hf1 : OpenAt env 2 Γ2 (.fvar 1 BaseKit.natT) (.fvar 1 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 2) (idx := 1) (by omega)
    have h2O := OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) bvk.specTwoAt rfl
    have hpowO := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) hPow rfl).app_nondep h2O .refl rfl).app_nondep hf0 .refl rfl
    have hmodO := ((OpenAt.ofClosed hsc (d := 2) (Γ := Γ2) hMod rfl).app_nondep hf1 .refl rfl).app_nondep hpowO .refl rfl
    simpa [Ix.Kernel.specMod2Pow, Ix.Kernel.specNatOp, Ix.Kernel.specTwo, Ix.Kernel.specSucc,
      Ix.Kernel.specZero, Ix.Kernel.specC, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.cnst,
      Ix.Kernel.specVar, fvarSubst, specTwoAt] using hmodO
  have hRhsCl : ClosedAt env (Ix.Kernel.specMod2Pow (.lit (.natVal n)) (.lit (.natVal w))) BaseKit.natT :=
    (hMod.app_nondep (bvk.bk.natLitAt n) rfl).app_nondep
      ((hPow.app_nondep bvk.specTwoAt rfl).app_nondep (bvk.bk.natLitAt w) rfl) rfl
  have hEq := applyEqn2 bvk.bk hv (by decide)
    (T₀ := BaseKit.natT) (T₀w := BaseKit.natT) (T₁ := BaseKit.natT) (T₁w := BaseKit.natT)
    (Cw := BaseKit.natT)
    (lhsW := .app (.app bvk.bvToNatAt.witness (.fvar 0 BaseKit.natT))
      (.app (.app bvk.bvOfNatAt.witness (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT)))
    (rhsW := .app (.app hMod.witness (.fvar 1 BaseKit.natT))
      (.app (.app hPow.witness (Ix.Kernel.specTwo (md := .anon))) (.fvar 0 BaseKit.natT)))
    (a := .lit (.natVal w)) (b := .lit (.natVal n))
    (lhsAB := .app (.app (.const (.role .bitVecToNat) []) (.lit (.natVal w)))
      (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n))))
    (rhsAB := Ix.Kernel.specMod2Pow (.lit (.natVal n)) (.lit (.natVal w)))
    rfl rfl rfl bvk.bk.natType .refl rfl rfl
    (OpenType.ofClosed hsc bvk.bk.natType) (OpenType.ofClosed hsc bvk.bk.natType) rfl rfl
    (by decide) (by decide) (by decide) (by decide)
    hLhsO hRhsO (bvk.bk.natLitAt w) (bvk.bk.natLitAt n)
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.specVar, fvarSubst])
    (by simp [Ix.Kernel.specEqn, Ix.Kernel.specMod2Pow, Ix.Kernel.specNatOp, Ix.Kernel.specTwo,
      Ix.Kernel.specSucc, Ix.Kernel.specZero, Ix.Kernel.specC, Ix.Kernel.BasisDSL.ap2,
      Ix.Kernel.BasisDSL.cnst, Ix.Kernel.specVar, fvarSubst])
    (by
      simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.bvToNatAt.wClosed.1,
        fvarSubst_of_not_hasFvar bvk.bvOfNatAt.wClosed.1, ↓reduceIte]
      exact .app (.app bvk.bvToNatAt.defEq_witness .refl)
        (.app (.app bvk.bvOfNatAt.defEq_witness .refl) .refl))
    (by
      simp only [Ix.Kernel.specMod2Pow, Ix.Kernel.specNatOp, Ix.Kernel.specTwo, Ix.Kernel.specSucc,
        Ix.Kernel.specZero, Ix.Kernel.specC, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.cnst,
        fvarSubst, fvarSubst_of_not_hasFvar hMod.wClosed.1, fvarSubst_of_not_hasFvar hPow.wClosed.1,
        ↓reduceIte]
      exact .app (.app hMod.defEq_witness .refl) (.app (.app hPow.defEq_witness .refl) .refl))
    (bvk.bvToNatApp w n) hRhsCl
  exact hRhsCl.defEq_trans hEq (.ofRed (bvk.red_specMod2Pow n w hw))

theorem defEq_bitVecUlt (w n₁ n₂ : Nat) (hw : w ≤ 2 ^ 24) :
    DefEq env 0
      (.app (.app (.app (.const (.role .bitVecUlt) []) (.lit (.natVal w)))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₁))))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₂))))
      (.const (if n₁ % 2 ^ w < n₂ % 2 ^ w then Ix.Kernel.boolTrueName
        else Ix.Kernel.boolFalseName) []) := by
  have hsc := bvk.bk.storeClosed
  have hv := eqnValid_of bvk.hs .bitVecUlt (by decide) (by decide) (k := 0) rfl
  obtain ⟨_, _, ⟨hMod⟩⟩ := bvk.bk.natBinNatAt (r := .natMod) (by decide) (by decide) (by decide)
  obtain ⟨_, _, ⟨hPow⟩⟩ := bvk.bk.natBinNatAt (r := .natPow) (by decide) (by decide) (by decide)
  obtain ⟨_, _, ⟨hBle⟩⟩ := bvk.bk.natBinBoolAt (r := .natBle) (by decide) (Or.inr rfl)
  let Γ3 := fvarUpdate (fvarUpdate (fvarUpdate Γ₀ 0 BaseKit.natT) 1 BaseKit.natT) 2 BaseKit.natT
  have hLhsO : OpenAt env 3 Γ3
      (fvarSubst 2 (.fvar 2 BaseKit.natT) (fvarSubst 1 (.fvar 1 BaseKit.natT) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.BasisDSL.ap3 (Ix.Kernel.specC .bitVecUlt) (Ix.Kernel.specVar 0 BaseKit.natT)
          (Ix.Kernel.BasisDSL.ap2 (Ix.Kernel.specC .bitVecOfNat)
            (Ix.Kernel.specVar 0 BaseKit.natT) (Ix.Kernel.specVar 1 BaseKit.natT))
          (Ix.Kernel.BasisDSL.ap2 (Ix.Kernel.specC .bitVecOfNat)
            (Ix.Kernel.specVar 0 BaseKit.natT) (Ix.Kernel.specVar 2 BaseKit.natT))))))
      (.app (.app (.app bvk.bvUltAt.witness (.fvar 0 BaseKit.natT))
        (.app (.app bvk.bvOfNatAt.witness (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT)))
        (.app (.app bvk.bvOfNatAt.witness (.fvar 0 BaseKit.natT)) (.fvar 2 BaseKit.natT)))
      BaseKit.boolT := by
    have hf0 : OpenAt env 3 Γ3 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 0) (by omega)
    have hf1 : OpenAt env 3 Γ3 (.fvar 1 BaseKit.natT) (.fvar 1 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 1) (by omega)
    have hf2 : OpenAt env 3 Γ3 (.fvar 2 BaseKit.natT) (.fvar 2 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 2) (by omega)
    have hon1 := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) bvk.bvOfNatAt bvk.bvOfNatTy_nf).app_abs hf0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 bvk.wBV_cl.2])
    simp only [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at hon1
    have honX := hon1.app_abs hf1 .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2])
    simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1,
      (by decide : ¬ (0 : Nat) = 1), ↓reduceIte] at honX
    have honY := hon1.app_abs hf2 .refl (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2])
    simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1,
      (by decide : ¬ (0 : Nat) = 1), ↓reduceIte] at honY
    have hu1 := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) bvk.bvUltAt bvk.bvUltTy_nf).app_abs hf0 .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, lbb_abstract1_succ, lbb_of_lbb0 bvk.wBV_cl.2])
    simp only [fvarSubst, ← fvarSubst_abstract1_comm_fvar (by decide : (0 : Nat) ≠ 1),
      fvarSubst_of_not_hasFvar bvk.wBV_cl.1, ↓reduceIte] at hu1
    have hu2 := hu1.app_abs honX .refl
      (by simp [Ix.Kernel.Expr.looseBVarsBounded, bvk.wBV_cl.2])
    simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.wBV_cl.1,
      (by decide : ¬ (0 : Nat) = 1), ↓reduceIte] at hu2
    have hu3 := hu2.app_nondep honY .refl rfl
    simpa [Ix.Kernel.BasisDSL.ap3, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.specC, Ix.Kernel.BasisDSL.cnst,
      Ix.Kernel.specVar, fvarSubst] using hu3
  have hRhsO : OpenAt env 3 Γ3
      (fvarSubst 2 (.fvar 2 BaseKit.natT) (fvarSubst 1 (.fvar 1 BaseKit.natT) (fvarSubst 0 (.fvar 0 BaseKit.natT)
        (Ix.Kernel.specNatOp .natBle
          (Ix.Kernel.specSucc (Ix.Kernel.specMod2Pow (Ix.Kernel.specVar 1 BaseKit.natT) (Ix.Kernel.specVar 0 BaseKit.natT)))
          (Ix.Kernel.specMod2Pow (Ix.Kernel.specVar 2 BaseKit.natT) (Ix.Kernel.specVar 0 BaseKit.natT))))))
      (.app (.app hBle.witness
        (.app BaseKit.natSuccE
          (.app (.app hMod.witness (.fvar 1 BaseKit.natT))
            (.app (.app hPow.witness (Ix.Kernel.specTwo (md := .anon))) (.fvar 0 BaseKit.natT)))))
        (.app (.app hMod.witness (.fvar 2 BaseKit.natT))
          (.app (.app hPow.witness (Ix.Kernel.specTwo (md := .anon))) (.fvar 0 BaseKit.natT))))
      BaseKit.boolT := by
    have hf0 : OpenAt env 3 Γ3 (.fvar 0 BaseKit.natT) (.fvar 0 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 0) (by omega)
    have hf1 : OpenAt env 3 Γ3 (.fvar 1 BaseKit.natT) (.fvar 1 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 1) (by omega)
    have hf2 : OpenAt env 3 Γ3 (.fvar 2 BaseKit.natT) (.fvar 2 BaseKit.natT) BaseKit.natT :=
      OpenAt.fvar (d := 3) (idx := 2) (by omega)
    have h2O := OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) bvk.specTwoAt rfl
    have hpowO := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) hPow rfl).app_nondep h2O .refl rfl).app_nondep hf0 .refl rfl
    have hm1 := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) hMod rfl).app_nondep hf1 .refl rfl).app_nondep hpowO .refl rfl
    have hm2 := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) hMod rfl).app_nondep hf2 .refl rfl).app_nondep hpowO .refl rfl
    have hs1 := (OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) bvk.bk.natSuccAt rfl).app_nondep hm1 .refl rfl
    have hbleO := ((OpenAt.ofClosed hsc (d := 3) (Γ := Γ3) hBle rfl).app_nondep hs1 .refl rfl).app_nondep hm2 .refl rfl
    simpa [Ix.Kernel.specMod2Pow, Ix.Kernel.specNatOp, Ix.Kernel.specTwo, Ix.Kernel.specSucc,
      Ix.Kernel.specZero, Ix.Kernel.specC, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.cnst,
      Ix.Kernel.specVar, fvarSubst, specTwoAt] using hbleO
  have hMod1Cl : ClosedAt env (Ix.Kernel.specMod2Pow (.lit (.natVal n₁)) (.lit (.natVal w))) BaseKit.natT :=
    (hMod.app_nondep (bvk.bk.natLitAt n₁) rfl).app_nondep
      ((hPow.app_nondep bvk.specTwoAt rfl).app_nondep (bvk.bk.natLitAt w) rfl) rfl
  have hMod2Cl : ClosedAt env (Ix.Kernel.specMod2Pow (.lit (.natVal n₂)) (.lit (.natVal w))) BaseKit.natT :=
    (hMod.app_nondep (bvk.bk.natLitAt n₂) rfl).app_nondep
      ((hPow.app_nondep bvk.specTwoAt rfl).app_nondep (bvk.bk.natLitAt w) rfl) rfl
  have hRhsCl : ClosedAt env
      (Ix.Kernel.specNatOp .natBle
        (Ix.Kernel.specSucc (Ix.Kernel.specMod2Pow (.lit (.natVal n₁)) (.lit (.natVal w))))
        (Ix.Kernel.specMod2Pow (.lit (.natVal n₂)) (.lit (.natVal w))))
      BaseKit.boolT :=
    (hBle.app_nondep (bvk.bk.natSuccApp hMod1Cl) rfl).app_nondep hMod2Cl rfl
  have hEq := applyEqn3 bvk.bk hv (by decide)
    (T₀ := BaseKit.natT) (T₀w := BaseKit.natT)
    (T₁ := BaseKit.natT) (T₁w := BaseKit.natT)
    (T₂ := BaseKit.natT) (T₂w := BaseKit.natT)
    (Cw := BaseKit.boolT)
    (lhsW := .app (.app (.app bvk.bvUltAt.witness (.fvar 0 BaseKit.natT))
      (.app (.app bvk.bvOfNatAt.witness (.fvar 0 BaseKit.natT)) (.fvar 1 BaseKit.natT)))
      (.app (.app bvk.bvOfNatAt.witness (.fvar 0 BaseKit.natT)) (.fvar 2 BaseKit.natT)))
    (rhsW := .app (.app hBle.witness
      (.app BaseKit.natSuccE
        (.app (.app hMod.witness (.fvar 1 BaseKit.natT))
          (.app (.app hPow.witness (Ix.Kernel.specTwo (md := .anon))) (.fvar 0 BaseKit.natT)))))
      (.app (.app hMod.witness (.fvar 2 BaseKit.natT))
        (.app (.app hPow.witness (Ix.Kernel.specTwo (md := .anon))) (.fvar 0 BaseKit.natT))))
    (a := .lit (.natVal w)) (b := .lit (.natVal n₁)) (c := .lit (.natVal n₂))
    (lhsABC := .app (.app (.app (.const (.role .bitVecUlt) []) (.lit (.natVal w)))
      (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₁))))
      (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₂))))
    (rhsABC := Ix.Kernel.specNatOp .natBle
      (Ix.Kernel.specSucc (Ix.Kernel.specMod2Pow (.lit (.natVal n₁)) (.lit (.natVal w))))
      (Ix.Kernel.specMod2Pow (.lit (.natVal n₂)) (.lit (.natVal w))))
    rfl rfl rfl bvk.bk.boolType .refl rfl rfl
    (OpenType.ofClosed hsc bvk.bk.natType) (OpenType.ofClosed hsc bvk.bk.natType)
    (OpenType.ofClosed hsc bvk.bk.natType) rfl rfl rfl rfl
    (by decide) (by decide)
    hLhsO hRhsO (bvk.bk.natLitAt w) (bvk.bk.natLitAt n₁) (bvk.bk.natLitAt n₂)
    (by
      simp only [fvarSubst, fvarSubst_of_not_hasFvar bvk.bvUltAt.wClosed.1,
        fvarSubst_of_not_hasFvar bvk.bvOfNatAt.wClosed.1, ↓reduceIte]
      exact .app (.app (.app bvk.bvUltAt.defEq_witness .refl)
        (.app (.app bvk.bvOfNatAt.defEq_witness .refl) .refl))
        (.app (.app bvk.bvOfNatAt.defEq_witness .refl) .refl))
    (by
      simp only [Ix.Kernel.specMod2Pow, Ix.Kernel.specNatOp, Ix.Kernel.specTwo, Ix.Kernel.specSucc,
        Ix.Kernel.specZero, Ix.Kernel.specC, Ix.Kernel.BasisDSL.ap2, Ix.Kernel.BasisDSL.cnst,
        fvarSubst, fvarSubst_of_not_hasFvar hBle.wClosed.1, fvarSubst_of_not_hasFvar hMod.wClosed.1,
        fvarSubst_of_not_hasFvar hPow.wClosed.1, ↓reduceIte]
      exact .app (.app hBle.defEq_witness
        (.app .refl (.app (.app hMod.defEq_witness .refl) (.app (.app hPow.defEq_witness .refl) .refl))))
        (.app (.app hMod.defEq_witness .refl) (.app (.app hPow.defEq_witness .refl) .refl)))
    (bvk.bvUltApp w n₁ n₂) hRhsCl
  have hRedRhs : Red env 0
      (Ix.Kernel.specNatOp .natBle
        (Ix.Kernel.specSucc (Ix.Kernel.specMod2Pow (.lit (.natVal n₁)) (.lit (.natVal w))))
        (Ix.Kernel.specMod2Pow (.lit (.natVal n₂)) (.lit (.natVal w))))
      (.const (if n₁ % 2 ^ w < n₂ % 2 ^ w then Ix.Kernel.boolTrueName
        else Ix.Kernel.boolFalseName) []) := by
    have hs1 : Red env 0
        (Ix.Kernel.specSucc (Ix.Kernel.specMod2Pow (.lit (.natVal n₁)) (.lit (.natVal w))))
        (.lit (.natVal (n₁ % 2 ^ w + 1))) :=
      .trans (.appArg (bvk.red_specMod2Pow n₁ w hw)) (bvk.bk.red_natSucc_lit (n₁ % 2 ^ w))
    have hbleRes : Ix.Kernel.natOpResult (md := .anon) (.role .natBle) (n₁ % 2 ^ w + 1) (n₂ % 2 ^ w) =
        some (.const (if n₁ % 2 ^ w < n₂ % 2 ^ w then Ix.Kernel.boolTrueName
          else Ix.Kernel.boolFalseName) []) := by
      have hiff : (n₁ % 2 ^ w + 1 ≤ n₂ % 2 ^ w) ↔ (n₁ % 2 ^ w < n₂ % 2 ^ w) := by omega
      simp [Ix.Kernel.natOpResult, Ix.Kernel.natBleName, hiff]
    exact .trans (.appFn (.appArg hs1))
      (.trans (.appArg (bvk.red_specMod2Pow n₂ w hw))
        (bvk.bk.red_natOp (r := .natBle) (by decide) hbleRes))
  exact hRhsCl.defEq_trans hEq (.ofRed hRedRhs)

end BitVecKit

end BitVecKitSec

/-! ## Assembling `Core.PrimEqnEnv` from `BaseKit`, `strLitSupported`, and `Shapes (· < 77)` -/

theorem primEqnEnv_of_shapes {env : Ix.Kernel.Env .anon}
    (bk : BaseKit env) (hsup : Ix.Kernel.strLitSupported env = true)
    (hs : Shapes (· < 77) env) : Core.PrimEqnEnv env := by
  have hInt := intPrimEqns_of_shapes bk hs
  have hStr := strPrimEqns_of_shapes bk hsup hs
  obtain ⟨wBV, ⟨bvk⟩⟩ := bitVecKit_exists bk hs
  have hBVOpS : ∀ r : Role, r ∈ [.bitVecToNat, .bitVecUlt] →
      ∃ ci, env.find? (.role r) = some ci := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨ci, _, hf, -⟩ := roleExact_eqns hs .bitVecToNat (by decide) (by decide)
      exact ⟨ci, hf⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · obtain ⟨ci, _, hf, -⟩ := roleExact_eqns hs .bitVecUlt (by decide) (by decide)
        exact ⟨ci, hf⟩
      · cases hr
  have hBVOfNatS : ∃ ci, env.find? (.role .bitVecOfNat) = some ci := by
    obtain ⟨ci, _, hf, -⟩ := roleExact_anchor_of hs .bitVecToNat .bitVecOfNat
      (by decide) (by decide) (by decide)
    exact ⟨ci, hf⟩
  exact {
    intOfNatStored := hInt.intOfNatStored
    intNegSuccStored := hInt.intNegSuccStored
    intOpStored := hInt.intOpStored
    intNeg := hInt.intNeg
    intNatAbs := hInt.intNatAbs
    intAdd := hInt.intAdd
    intSub := hInt.intSub
    intMul := hInt.intMul
    intEdiv := hInt.intEdiv
    intEmod := hInt.intEmod
    intPow := hInt.intPow
    intBmod := hInt.intBmod
    intBdiv := hInt.intBdiv
    strOpStored := hStr.strOpStored
    charOfNatStored := hStr.charOfNatStored
    byteArrayEmptyStored := hStr.byteArrayEmptyStored
    stringStored := hStr.stringStored
    eqStored := hStr.eqStored
    eqReflStored := hStr.eqReflStored
    decidableIsTrueStored := hStr.decidableIsTrueStored
    charUtf8Size := hStr.charUtf8Size
    strUtf8ByteSize := hStr.strUtf8ByteSize
    strBack := hStr.strBack
    strToByteArrayEmpty := hStr.strToByteArrayEmpty
    strDecEqRefl := hStr.strDecEqRefl
    strAppend := hStr.strAppend
    bitVecOpStored := hBVOpS
    bitVecOfNatStored := hBVOfNatS
    bitVecToNat := fun d w n hw =>
      ClosedAt.red_of_defEq rfl (bvk.bvToNatApp w n) (bk.natLitAt (n % 2 ^ w))
        (bvk.defEq_bitVecToNat w n hw) d
    bitVecUlt := fun d w n₁ n₂ hw => by
      have hBoolRes : ClosedAt env
          (.const (if n₁ % 2 ^ w < n₂ % 2 ^ w then Ix.Kernel.boolTrueName
            else Ix.Kernel.boolFalseName) []) BaseKit.boolT := by
        split_ifs
        · exact bk.boolTrueAt
        · exact bk.boolFalseAt
      exact ClosedAt.red_of_defEq rfl (bvk.bvUltApp w n₁ n₂) hBoolRes
        (bvk.defEq_bitVecUlt w n₁ n₂ hw) d }

section FoldTailPrim

universe u

open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

/-- **Certified `PrimEqnEnv` at group 76 of the binding fold**, combining `Int`, `String`/`Char`,
and `BitVec` equations from the invariant below group 76 and the validated equation shapes below
group 77. -/
theorem primEqnEnv_of_bndOver {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hall : AllBound t) (hb : BndOver.{u} L t (· < 76) R env)
    (hshapes : Shapes (· < 77) env) : Core.PrimEqnEnv env :=
  primEqnEnv_of_shapes (baseKit_of_bndOver hall hb) (strLitSupported_of_bndOver hall hb) hshapes

end FoldTailPrim

end IxVM.Refinement.Binding
