import IxVMRefinement.Decl.NativeCommon
import IxVMRefinement.Decl.NativeRunMap

/-! # Semantic no-recursor runs from checked native stages

The former and constructor pass already exposes the actual capability record and normalized
signatures. Its checked stages, index sorts, field check, and projection table supply the
no-recursor semantic relation directly.
-/

universe u

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics

/-- A settled former/constructor pass and its checked table form a semantic no-recursor run. -/
theorem nativeNoRecRunJ_of_pass {md : Mode} {mode : CheckMode} {fuel : Nat}
    {env env₂ : Env md} {p₀ : NativeParts md} {isRec : Bool} {q : NativePass md (Env md)}
    {tfvs : List (Expr md)} {trest : Expr md} {isorts : List Level}
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hpass : checkNativePass (m := CheckM md) (fueledOps mode fuel) env p₀ isRec = .ok (q, true))
    (hopen : openPisAtFvars (q.p.nP + q.p.nIdx) q.cvTa.type 0 = some (tfvs, trest))
    (hsorts : checkStructFieldSortsI (m := CheckM md) (fueledOps mode fuel) q.env₁ true false
      q.p.resSort q.p.nP (tfvs.drop q.p.nP) [] q.p.nIdx = .ok isorts)
    (hfields : nativeFieldsOk env q.p.cvT.name q.p.cvT.levelParams q.p.nP q.p.nIdx q.ctorsA
      q.p.kinds = true)
    (htable : checkNativeTable (m := CheckM md) q.p q.ctorsA q.sortss
      (consSumCtors q.p.nP q.ctorsA q.env₁) = .ok env₂) :
    DeclNativeNoRecRunJ (runJ mode fuel) env p₀ env₂ := by
  obtain ⟨p₁, kinds, hInd, hCtors, hK, hp, hb⟩ := checkNativePass_inv hpass
  have hcaps : nativeCaps q.p = nativeCapsAt p₁ isRec := beq_iff_eq.mp hb.symm
  have hformer : FormerReadJ q.env₁ q.p q.cvTa q.ctorsA := by
    obtain ⟨cvT, s, -, -, -, hp₁, henv₁, -⟩ := checkSumInd_shape hInd
    have hname : q.cvTa.name = q.p.cvT.name := by
      rw [hp, hp₁]
      exact (sumIndRunJ_of_run hInd).former.1
    refine Or.inl ?_
    rw [henv₁, ← hname]
    exact ⟨_, Env.find?_cons_self _ _⟩
  refine ⟨hnd, isRec, q.env₁, q.cvTa, p₁, q.p, q.ctorsA, q.sortss, kinds, tfvs, trest,
    isorts, sumIndRunJ_of_run hInd, hp, ?_, ?_, hcaps, hopen,
    fieldSortsJ_of_run hsorts, hfields, htable, hformer⟩
  · apply sumCtorsRunJ_of_run
    rw [hp]
    exact hCtors
  · rw [hp]
    exact hK

/-- No-recursor semantic runs preserve the reference model without a global eta-table
companion invariant. -/
theorem nativeNoRec_model_step {V : Type u} [SetTheory V]
    {env env₂ : Env .anon} {block : List (ConstantInfo .anon)} {nP : Nat}
    {p₀ : NativeParts .anon}
    (hpin : basisPinHit block = none) (hparts : nativePartsNoRec? nP block = some p₀)
    (hrun : DeclNativeNoRecRunJ Model.rulesJ env p₀ env₂)
    (hmodel : Model.EnvModelT V .verified env) : Model.EnvModelT V .verified env₂ :=
  Model.foldRulesRoutes (.cons (declRunJ_of_nativeNoRec hpin hparts hrun) .nil) hmodel

end IxVM.Refinement.Decl
