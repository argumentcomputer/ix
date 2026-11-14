import IxVMRefinement.Decl.ModeledSoundPlain
import IxC.Kernel.Model.IndNestedParam
import IxC.Kernel.Model.IndPinRow
import IxC.Kernel.Model.Rules.IotaSoundKit
import IxC.Kernel.Semantics.IndRecsCore
import IxC.Kernel.Model.IndRecs
import IxC.Kernel.Model.IndEtaLaw
import IxC.Kernel.Model.IndUnitLaw
import IxC.Kernel.Model.Swap
import IxC.Kernel.Model.IndMembers
import IxC.Kernel.Model.Capstone

/-!
# Soundness of Nested Modeled-Inductive `iota` Rules and Full `DeclIndVmRunJ` Steps

Completes the semantic soundness bridge for VM-checked modeled inductive blocks:
* `indBottomNested_vm` and `iotaRuleNested_vm` (nested branch over `LamTeleWalkJ`);
* `iotaRule_vm`, `iotaRules_vm`, `indRecsFold_vm`, `indRecs_vm`;
* `declIndJ_vm`, `declIndStepJ_vm`, `DeclInv.step_modeled_vm`, and `decls_step_of_modeled_vm`.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  LevelParam SwapShList openPisAtFvars eqName eqA auxKey nestedRuleShape recRuleBits isEqHead
  fvarLeaves_getAppArgs fvarLeaves_instSpine hasFvar_renameConsts instPisAt_WScoped
  instSpine_WScoped instSpine_closed nestedRuleShape_inv openPisAtFvars_WScoped
  openPisAtFvars_index recFireComparands_nested swapSh_find?_corr)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe w

set_option maxHeartbeats 25600000 in
/-- Nested modeled-iota bottom over `LamTeleWalkJ` (`indBottomNested` adapted to VM `defeq_lam_tele`). -/
theorem indBottomNested_vm {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {env : Env .anon}
    (mp : EnvModelM V μ env) {J : Judgements .anon}
    (hdeq : ∀ ψ : LevelParam → Nat, DefEqClaimJ J mp.base2 ψ)
    (hinf : ∀ ψ : LevelParam → Nat, InferClaimJ J mp.base2 ψ)
    (hreadsP : ∀ ψ : LevelParam → Nat, InferReadsJ J mp.base2 ψ)
    (hframe : ∀ ψ : LevelParam → Nat, InferFrameJ J mp.base2 ψ)
    {f : Key .anon → Key .anon} (hroT : RenameOk mp.base2.acval env f)
    (heqfE : env.find? eqName = some eqA)
    {Rn : Key .anon} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (htyOk : ∀ (ψ : LevelParam → Nat) (ta : AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 tyA = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta)
    {ciRm : ConstantInfo .anon}
    (hfRnE : env.find? (f Rn) = some ciRm)
    (hRmlps : ciRm.toConstantVal.levelParams = lps)
    {ctor : Key .anon} {cvj : ConstantVal .anon} {cnP cnF : Nat}
    (hctorE : env.find? ctor = some (.ctorInfo cvj cnP cnF))
    {ciCm : ConstantInfo .anon}
    (hfCmE : env.find? (f ctor) = some ciCm)
    (hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hClp : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hrPmI : rP ≤ mI)
    {lvls : List Level} {pins : List KExpr}
    (hlvlsLen : lvls.length = cvj.levelParams.length)
    (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    {rhsA : KExpr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hrhsKey : ∀ ψ : LevelParam → Nat, ∃ Ra ta,
      denoteMeta mp.base2.acval env ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Ra ∧
        interp V ρ Ra ∈ˢ interp V ρ ta)
    {stmtTy : KExpr} (hSw : stmtTy.hasFvar = false)
    (hSb : stmtTy.looseBVarsBounded 0 = true)
    (hthm : ∀ ψ : LevelParam → Nat, ∃ ta,
      denoteMeta mp.base2.acval env ψ 0 stmtTy = some ta ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ ta) ∧
        WellDenotedV V ρ ta)
    {fvs : List KExpr} {tbody : KExpr} {ℓA : Level} {αS lhsS rhsS : KExpr}
    (hopen : openPisAtFvars (rP + cnF) stmtTy 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)))
    (hCstripsHead : ∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = Expr.const Dc usc)
    {cdoms : List KExpr} {cres : KExpr}
    (hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    {rdoms : List KExpr} {rrest : KExpr}
    (hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
      = some (rdoms, rrest))
    {fvsP : List KExpr} {restP : KExpr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List KExpr} {crestP : KExpr}
    (hcinstP : Expr.instPisAt
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      = some (cdomsP, crestP))
    {xFvsP : List KExpr} {ldoms : KExpr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (hwalk : LamTeleWalkJ J env rP cnF tyA
      (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      (fun pre => pins.map (fun p => Expr.instSpine pre (rP - 1) p)) rhsA)
    (hTypedP : TypedListJ J env (rP + cnF)
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) cdomsP)
    (hdeIdx : DefEqListJ J env (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hdePre : DefEqListJ J env (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListJ J env (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hdeRhs : J.defeq env (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs))
    (hsideL : ∃ tl, J.infer env (rP + cnF) lhsS tl ∧
      J.defeq env (rP + cnF) tl αS)
    (hsideR : ∃ tr, J.infer env (rP + cnF) rhsS tr ∧
      J.defeq env (rP + cnF) tr αS) :
    ∀ (φ : LevelParam → Nat) (us : List Level), us.length = lps.length →
      ∃ Ra : AnnotTerm,
        denoteMeta mp.base2.acval env φ 0
          (rhsA.instantiateLevelParams lps us) = some Ra ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
          (TVa TVja restR restC : AnnotTerm),
          xs.length = mI →
          ys.length = cnP + cnF →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (lvls.map (Level.subst lps us)) →
          (∀ i, i < cnP → ∀ vpa : AnnotTerm,
            denoteMeta mp.base2.acval env φ rP
              (openRev 0 rP
                ((pins.getD i default).instantiateLevelParams lps us))
              = some vpa →
            interp V ρ (ys.getD i default)
              = interp V ρ
                  (AnnotTerm.instRevChain (xs.take rP) vpa)) →
          IotaIndexPin (V := V) ρ restC cnP mI rP xs →
          denoteMeta mp.base2.acval env φ 0
            (tyA.instantiateLevelParams lps us) = some TVa →
          denoteMeta mp.base2.acval env φ 0
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            = some TVja →
          TeleFitPA V ρ TVa
            (xs ++ [AnnotTerm.mkAppN
              (mp.base2.acval ctor
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
          TeleFitPA V ρ TVja ys restC →
          interp V ρ
              (AnnotTerm.mkAppN
                (mp.base2.acval Rn (Level.substFn φ lps us))
                (xs ++ [AnnotTerm.mkAppN
                  (mp.base2.acval ctor
                    (Level.substFn φ cvj.levelParams usj)) ys]))
            = interp V ρ
                (AnnotTerm.mkAppN Ra
                  (xs.take rP ++ ys.drop cnP)) ∧
          ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
            WellDenotedV V ρ
              (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop cnP))) := by
  intro φ us huslen
  obtain ⟨Ra, taR, hRaden, hRaFacts⟩ := hrhsKey (Level.substFn φ lps us)
  refine ⟨Ra, by rw [denotePInstLevels]; exact hRaden,
    fun ρ => (hRaFacts ρ).1, ?_⟩
  intro usj ρ xs ys TVa TVja restR restC hlenX hlenY husjlen hlev hparP
    hidx hTVa hTVja hfitR hfitC
  have hainst : ∀ (n : Key .anon) (ψ : LevelParam → Nat) (y : AnnotTerm) (k : Nat),
      (mp.base2.acval n ψ).inst y k = mp.base2.acval n ψ :=
    fun n ψ y k =>
      AVExprSubst.inst_eq_self_of_closed (mp.base2.acval_closed n ψ) y k
  obtain ⟨ctyL, hctyL⟩ : ∃ e : KExpr,
      e = cvj.type.instantiateLevelParams cvj.levelParams lvls := ⟨_, rfl⟩
  obtain ⟨psP, hpsP⟩ : ∃ l : List KExpr,
      l = pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)) := ⟨_, rfl⟩
  obtain ⟨psR, hpsR⟩ : ∃ l : List KExpr,
      l = pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) := ⟨_, rfl⟩
  rw [← hpsR] at hmaj hcinst
  rw [← hctyL] at hcinst hcinstP hwalk
  rw [← hpsP] at hcinstP hTypedP
  -- ===== the statement, opened =====
  obtain ⟨Tst, hTstden, hTstFacts⟩ := hthm (Level.substFn φ lps us)
  obtain ⟨Γs, Rbody, htowerS, hRbodyDenA, hdomsS0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (rP + cnF) hopen hTstden
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hfvslen : fvs.length = rP + cnF := Ix.Kernel.Model.openPisAtFvars_length _ hopen
  have hshapeS : ∀ (i : Nat) (x : KExpr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopen i x hx
    exact ⟨ty, by simpa using hx'⟩
  have hwsS := openPisAtFvars_WScoped (rP + cnF) stmtTy 0 hopen
    (Expr.WScoped.of_not_hasFvar hSw)
  have hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x := by
    intro x hx
    have h := hwsS.1 x hx
    rwa [Nat.zero_add] at h
  have hbFvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := hshapeS q x hq
    rfl
  have hlbFvs : ∀ (i : Nat) (ty : KExpr),
      Expr.fvar i ty ∈ fvs → ty.looseBVarsBounded 0 = true :=
    fun i ty hmem =>
      (openPisAtFvars_bounded (rP + cnF) hopen hSb).2 _ hmem
  have hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvs := by
    intro l ⟨x, hx, hl⟩
    rcases openPisAtFvars_leaves _ hopen l (Or.inr ⟨x, hx, hl⟩) with
      h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hSw] at h0
      exact nomatch h0
    · exact h0
  have hleafBody : ∀ l ∈ tbody.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rcases openPisAtFvars_leaves _ hopen l (Or.inl hl) with h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hSw] at h0
      exact nomatch h0
    · exact h0
  have hfvsLt : ∀ l : Nat × KExpr,
      Expr.fvar l.1 l.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1, ← hfvslen]
    exact hql
  have hdomsS0 : ∀ (i : Nat) (x : KExpr), fvs[i]? = some x →
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) i
          (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i x hx
    have h := hdomsS0A i x hx
    rwa [Nat.zero_add] at h
  have hRbodyDen : denoteMeta mp.base2.acval env
      (Level.substFn φ lps us) (rP + cnF) tbody = some Rbody := by
    have h := hRbodyDenA
    rwa [Nat.zero_add] at h
  have hΔaent : ∀ i, i < rP + cnF →
      Γs[rP + cnF - 1 - i]?
        = some (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i hi
    rw [List.getD]
    rcases hg : Γs[rP + cnF - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  have hokTst : ∀ σ : Nat → V, WellDenotedV V σ Tst :=
    fun σ => (hTstFacts σ).2
  have hpadLen : ∀ N, N ≤ rP + cnF →
      (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
        ++ Γs.drop (rP + cnF - N)).length = rP + cnF := by
    intro N hN
    rw [List.length_append, List.length_replicate, List.length_drop,
      hΓslen]
    omega
  have hpadEnt : ∀ N, N ≤ rP + cnF → ∀ i, i < N →
      (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
        ++ Γs.drop (rP + cnF - N))[rP + cnF - 1 - i]?
        = some (Γs.getD (rP + cnF - 1 - i) default) := by
    intro N hN i hi
    rw [List.getElem?_append_right
        (by simp only [List.length_replicate]; omega),
      List.length_replicate, List.getElem?_drop,
      show rP + cnF - N + (rP + cnF - 1 - i - (rP + cnF - N))
        = rP + cnF - 1 - i from by omega, List.getD]
    rcases hg : Γs[rP + cnF - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  -- ===== the public (recursor) tower =====
  have hTV0 : denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 tyA
      = some TVa := by
    rw [← denotePInstLevels]
    exact hTVa
  obtain ⟨ΓP, RP, htowerP, hRPden, hdomsP0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) rP hopenP hTV0
  have hfvsPlen : fvsP.length = rP := Ix.Kernel.Model.openPisAtFvars_length _ hopenP
  have hshapeP : ∀ (i : Nat) (x : KExpr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
    exact ⟨ty, by simpa using hx'⟩
  have hdomsP0 : ∀ (i : Nat) (x : KExpr), fvsP[i]? = some x →
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) i
          (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i x hx
    have h := hdomsP0A i x hx
    rwa [Nat.zero_add] at h
  have hwsP := openPisAtFvars_WScoped rP tyA 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyw)
  have hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x := by
    intro x hx
    have h := hwsP.1 x hx
    rwa [Nat.zero_add] at h
  have hlbFvsP : ∀ (i : Nat) (ty : KExpr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true :=
    fun i ty hmem =>
      (openPisAtFvars_bounded rP hopenP htyb).2 _ hmem
  have hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP := by
    intro l ⟨x, hx, hl⟩
    rcases openPisAtFvars_leaves _ hopenP l (Or.inr ⟨x, hx, hl⟩) with
      h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
      exact nomatch h0
    · exact h0
  have hokTV : ∀ σ : Nat → V, WellDenotedV V σ TVa := htyOk _ TVa hTV0
  -- ===== the constructor's assignment, at the stored levels =====
  have hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p
        = Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls p := by
    intro p hp
    rw [hlev]
    exact Level.substFn_map_subst hlvlsLen hp
  have hTVj0 : denoteMeta mp.base2.acval env
      (Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls) 0
      cvj.type = some TVja := by
    have h := hTVja
    rw [denotePInstLevels,
      denoteMeta_params_ext mp.base2 hagree 0 cvj.type hClp] at h
    exact h
  have hTVjcl : ∀ k : Nat, TVja.liftN 1 k = TVja := fun k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hCw hCb hTVj0 1 k
  have hokTVj : ∀ σ : Nat → V, WellDenotedV V σ TVja :=
    mp.type_wellDenotedV _ (Ix.Kernel.Semantics.Env.find?_mem hctorE) _ TVja hTVj0
  have hCvLw : ctyL.hasFvar = false := by
    rw [hctyL, Expr.hasFvar_instantiateLevelParams]
    exact hCw
  have hCvLb : ctyL.looseBVarsBounded 0 = true := by
    rw [hctyL, Expr.looseBVarsBounded_instantiateLevelParams]
    exact hCb
  have hCwR : (ctyL.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hCvLw
  have hCbR : (ctyL.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact hCvLb
  have hCvL0 : ∀ d : Nat, denoteMeta mp.base2.acval env
      (Level.substFn φ lps us) d ctyL = some TVja := by
    intro d
    refine denoteMeta_depth_of_closed mp.base2.acval_closed hCvLw hTVjcl ?_ d
    rw [hctyL, denotePInstLevels]
    exact hTVj0
  have hTVjK : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (ctyL.renameConsts f) = some TVja := by
    rw [denoteMeta_renameConsts hroT]
    exact hCvL0 (rP + cnF)
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  -- ===== `Rj`'s decomposition and its arity =====
  obtain ⟨bsC0, cbody0, Dc, usc, hstripRaw, hheadRaw⟩ := hCstripsHead
  obtain ⟨Γj, Rj, htowerJ, hΓjlen0, hRjdenA, hdomsJ⟩ :=
    stripPis_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls)
      (cnP + cnF) hstripRaw hTVj0
  have hcbApp : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
      cbody0
      = Expr.mkAppN
          (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
            cbody0.getAppFn)
          (cbody0.getAppArgs.map
            (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
              ·)) := by
    have hcb : cbody0 = Expr.mkAppN cbody0.getAppFn cbody0.getAppArgs :=
      (Expr.mkAppN_getApp cbody0).symm
    have h1 : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
        cbody0
        = Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
          (Expr.mkAppN cbody0.getAppFn cbody0.getAppArgs) := by
      conv => lhs; rw [hcb]
    rw [h1, Expr.instSeq_mkAppN]
  have hRjdenA' := hRjdenA
  rw [Nat.zero_add, hcbApp] at hRjdenA'
  obtain ⟨vHC, vArgsC, hvHCden, hcspJ, hRjdec⟩ :=
    denoteMeta_mkAppN_inv hRjdenA'
  have hsplen : (psR ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, hpsR, List.length_map, List.length_drop,
      hpinsLen, hfvslen]
    omega
  obtain ⟨⟨bsC, bodyC0⟩, hstripC⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams lvls
      (cnP + cnF) (by rw [hstripRaw]; rfl))
  obtain ⟨hbodyL, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams lvls (cnP + cnF) hstripRaw hstripC
  rw [← hctyL] at hstripC
  have hheadLR : (bodyC0.renameConsts f).getAppFn
      = .const (f Dc) (usc.map (Level.subst cvj.levelParams lvls)) := by
    rw [Expr.getAppFn_renameConsts, hbodyL,
      Ix.Kernel.Expr.getAppFn_instantiateLevelParams, hheadRaw]
    rfl
  have hstripRen : (ctyL.renameConsts f).stripPis
      (psR ++ fvs.drop rP).length
      = some (bsC.map (fun b => ((b.1).renameConsts f, b.2)),
        bodyC0.renameConsts f) := by
    rw [hsplen]
    exact stripPis_renameConsts (f := f) (cnP + cnF) hstripC
  have harity1 : cres.getAppArgs.length = bodyC0.getAppArgs.length := by
    have h1 := instPisAt_residual_arity_const _ hcinst hstripRen hheadLR
    rw [getAppArgs_length_renameConsts] at h1
    exact h1
  have hcbodyArity : cbody0.getAppArgs.length = cnP + (mI - rP) := by
    have h2 : bodyC0.getAppArgs.length = cbody0.getAppArgs.length := by
      rw [hbodyL, Expr.getAppArgs_length_instantiateLevelParams]
    rw [← h2, ← harity1, hclen]
  have hArgsClen : vArgsC.length = cnP + (mI - rP) := by
    rw [← hcspJ.length, List.length_map, hcbodyArity]
  -- ===== the fitting prefix =====
  have htakexs : (xs ++ [AnnotTerm.mkAppN
      (mp.base2.acval ctor (Level.substFn φ cvj.levelParams usj))
      ys]).take rP = xs.take rP := by
    rw [List.take_append_of_le_length (by rw [hlenX]; omega)]
  obtain ⟨restRpre, hfitRpre⟩ := hfitR.take rP
  rw [htakexs] at hfitRpre
  have hPpreRun : Expr.instPisAt fvsP tyA
      = some (fvsP.map Expr.fvarTypeD, restP) :=
    openPisAtFvars_instPisAt _ hopenP
  have hrdomslen : rdoms.length = rP := by
    have h := instPisAt_length hrinst
    rw [List.length_take, hfvslen] at h
    omega
  have hrenP : ∀ n, n < rP →
      RenEqT f ((fvsP.map Expr.fvarTypeD).getD n default)
        (rdoms.getD n default) := by
    intro n hn
    have hrenD := instPisAt_renEq fvsP (fvs.take rP) hPpreRun hrinst
      (show Expr.ErasedEq (tyA.renameConsts f) (tyA.renameConsts f) from
        Expr.ErasedEq.rfl _)
      (fun i0 a a' ha ha' => by
        have hi0 : i0 < rP := by
          have := (List.getElem?_eq_some_iff.mp ha).1
          rw [hfvsPlen] at this
          exact this
        obtain ⟨ty, rfl⟩ := hshapeP i0 a ha
        rw [List.getElem?_take_of_lt hi0] at ha'
        obtain ⟨ty', rfl⟩ := hshapeS i0 a' ha'
        exact RenEqT.fvar)
      (by rw [hfvsPlen, List.length_take, hfvslen]; omega)
    rcases hp : fvsP[n]? with _ | px
    · rw [List.getElem?_eq_none_iff, hfvsPlen] at hp
      omega
    rcases hr : rdoms[n]? with _ | rx
    · rw [List.getElem?_eq_none_iff, hrdomslen] at hr
      omega
    rw [List.getD, List.getD, List.getElem?_map, hp, hr]
    exact hrenD.1 n _ _ (by rw [List.getElem?_map, hp]; rfl) hr
  -- ===== the fired spine's syntactic data =====
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  have hzstake : (xs.take rP ++ ys.drop cnP).take rP = xs.take rP := by
    rw [List.take_append_of_le_length (by rw [hxtlen])]
    exact List.take_of_length_le (by rw [hxtlen])
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right (by rw [hxtlen]; omega),
      hxtlen, List.getElem?_drop, show rP + j - rP = j from by omega]
    rfl
  have htkSlen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvslen]
    omega
  have htkPlen : (fvsP.take rP).length = rP := by
    rw [List.length_take, hfvsPlen]
    omega
  have hpgetd : ∀ q, q < cnP →
      pins[q]? = some (pins.getD q default) := by
    intro q hq
    rw [List.getD]
    rcases hp : pins[q]? with _ | p
    · rw [List.getElem?_eq_none_iff, hpinsLen] at hp
      omega
    · rfl
  have hpmemd : ∀ q, q < cnP → pins.getD q default ∈ pins :=
    fun q hq => List.mem_of_getElem? (hpgetd q hq)
  have hpwd : ∀ q, q < cnP → (pins.getD q default).hasFvar = false ∧
      (pins.getD q default).looseBVarsBounded rP = true :=
    fun q hq => hpinsWf _ (hpmemd q hq)
  have hpwdR : ∀ q, q < cnP →
      ((pins.getD q default).renameConsts f).hasFvar = false ∧
      ((pins.getD q default).renameConsts f).looseBVarsBounded rP
        = true := by
    intro q hq
    exact ⟨by rw [hasFvar_renameConsts]; exact (hpwd q hq).1,
      by rw [looseBVarsBounded_renameConsts]; exact (hpwd q hq).2⟩
  have hpinsRlen : psR.length = cnP := by
    rw [hpsR, List.length_map, hpinsLen]
  have hpinsRget : ∀ q, q < cnP →
      psR[q]?
      = some (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)) := by
    intro q hq
    rw [hpsR, List.getElem?_map, hpgetd q hq]
    rfl
  have hspPar : ∀ q, q < cnP →
      (psR ++ fvs.drop rP)[q]?
      = some (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)) := by
    intro q hq
    rw [List.getElem?_append_left (by rw [hpinsRlen]; omega),
      hpinsRget q hq]
  have hspFld : ∀ j, j < cnF →
      (psR ++ fvs.drop rP)[cnP + j]? = fvs[rP + j]? := by
    intro j hj
    rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
      hpinsRlen, List.getElem?_drop,
      show cnP + j - cnP = j from by omega]
  have hopenerLeaf : ∀ (q0 : Nat) (a : KExpr), (fvs.take rP)[q0]? = some a →
      ∀ l ∈ a.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP := by
    intro q0 a ha l hl
    have hq0lt : q0 < rP := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [htkSlen] at this
      exact this
    rw [List.getElem?_take_of_lt hq0lt] at ha
    obtain ⟨ty, rfl⟩ := hshapeS q0 a ha
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨List.mem_of_getElem? ha, hq0lt⟩
    · have hwsty : Expr.WScoped q0 ty := by
        have h' := hwsFvs _ (List.mem_of_getElem? ha)
        simp only [Expr.WScoped] at h'
        exact h'.2
      have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty l hl'
      refine ⟨hleafClosed l ⟨_, List.mem_of_getElem? ha, ?_⟩, by omega⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hspLeaf : ∀ (q : Nat) (x : KExpr),
      (psR ++ fvs.drop rP)[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP) := by
    intro q x hx l hl
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · rw [hspPar q hqc] at hx
      obtain rfl : x = Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f) :=
        (Option.some.inj hx).symm
      rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨a, ha, hla⟩
      · exfalso
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpwdR q hqc).1] at hl'
        exact nomatch hl'
      · obtain ⟨q0, hq0⟩ := List.getElem?_of_mem ha
        obtain ⟨hmem, hlt⟩ := hopenerLeaf q0 a hq0 l hla
        exact ⟨hmem, by omega⟩
    · rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx
      obtain ⟨ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨List.mem_of_getElem? hx, by omega⟩
      · have hwsty : Expr.WScoped (rP + (q - cnP)) ty := by
          have h' := hwsFvs _ (List.mem_of_getElem? hx)
          simp only [Expr.WScoped] at h'
          exact h'.2
        have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty l hl'
        refine ⟨hleafClosed l ⟨_, List.mem_of_getElem? hx, ?_⟩, by omega⟩
        rw [Expr.fvarLeaves]
        exact List.mem_cons_of_mem _ hl'
  have hspScope : ∀ (q : Nat) (x : KExpr),
      (psR ++ fvs.drop rP)[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · rw [hspPar q hqc] at hx
      obtain rfl : x = Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f) :=
        (Option.some.inj hx).symm
      refine ⟨?_, ?_⟩
      · exact instSpine_WScoped (rP - 1)
          (Expr.WScoped.of_not_hasFvar (hpwdR q hqc).1)
          (fun a ha => hwsFvs a (List.mem_of_mem_take ha))
      · have h := instSpine_closed (args := fvs.take rP)
          (e := (pins.getD q default).renameConsts f)
          (fun a ha => hbFvs a (List.mem_of_mem_take ha))
          (by rw [htkSlen]; exact (hpwdR q hqc).2)
        rwa [htkSlen] at h
    · rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx
      obtain ⟨ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      exact ⟨hwsFvs _ (List.mem_of_getElem? hx),
        hbFvs _ (List.mem_of_getElem? hx)⟩
  -- ===== the statement body, decomposed and graded =====
  have htbody : tbody
      = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS] := by
    have h := (Expr.mkAppN_getApp tbody).symm
    rw [hheadEq, hargs3] at h
    exact h
  have hwsBody : Expr.WScoped (rP + cnF) tbody := by
    have h := hwsS.2
    rwa [Nat.zero_add] at h
  have hbBody : tbody.looseBVarsBounded 0 = true :=
    (openPisAtFvars_bounded (rP + cnF) hopen hSb).1
  have hargLeaf : ∀ e : KExpr, e ∈ tbody.getAppArgs →
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) ∧
      (∀ l ∈ e.fvarLeaves, l.1 < rP + cnF) := by
    intro e hmem
    have h1 : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs :=
      fun l hl => hleafBody l (fvarLeaves_getAppArgs hmem l hl)
    exact ⟨h1, fun l hl => hfvsLt l (h1 l hl)⟩
  have hmemα : αS ∈ tbody.getAppArgs := by
    rw [hargs3]; exact List.mem_cons_self
  have hmemL : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hmemR : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨hleafα, hltα⟩ := hargLeaf αS hmemα
  obtain ⟨hleafL, hltL⟩ := hargLeaf lhsS hmemL
  obtain ⟨hleafR, hltR⟩ := hargLeaf rhsS hmemR
  have hwsα : Expr.WScoped (rP + cnF) αS := hwsBody.getAppArgs αS hmemα
  have hwsL : Expr.WScoped (rP + cnF) lhsS := hwsBody.getAppArgs lhsS hmemL
  have hwsR : Expr.WScoped (rP + cnF) rhsS := hwsBody.getAppArgs rhsS hmemR
  have hbα : αS.looseBVarsBounded 0 = true :=
    Ix.Kernel.looseBVarsBounded_getAppArgs hbBody αS hmemα
  have hbL : lhsS.looseBVarsBounded 0 = true :=
    Ix.Kernel.looseBVarsBounded_getAppArgs hbBody lhsS hmemL
  have hbR : rhsS.looseBVarsBounded 0 = true :=
    Ix.Kernel.looseBVarsBounded_getAppArgs hbBody rhsS hmemR
  have hLα : Expr.LeavesBounded αS := fun l hl =>
    hlbFvs l.1 l.2 (hleafα l hl)
  have hLL : Expr.LeavesBounded lhsS := fun l hl =>
    hlbFvs l.1 l.2 (hleafL l hl)
  have hLR : Expr.LeavesBounded rhsS := fun l hl =>
    hlbFvs l.1 l.2 (hleafR l hl)
  have hokA : ∀ i, i < rP + cnF → ∀ σ : Nat → V, Sat V Γs σ →
      WellDenotedV V (fun j => σ (j + (rP + cnF - 1 - i) + 1))
        (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i hi σ hσ
    refine hokA_padded htowerS hokTst (Nat.le_refl _) i hi σ ?_
    rw [show rP + cnF - (rP + cnF) = 0 from by omega,
      List.replicate_zero, List.nil_append, List.drop_zero]
    exact hσ
  have hctxOf : ∀ e : KExpr,
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) →
      (∀ l ∈ e.fvarLeaves, l.1 < rP + cnF) →
      CtxOk mp.base2 (Level.substFn φ lps us) (rP + cnF) Γs e :=
    fun e hleafE hltE =>
      ctxOk_of_openers mp.base2.acval_closed hΓslen hshapeS hwsFvs
        hdomsS0 hleafE hltE hΔaent hokA
  have hRbody3 : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS])
      = some Rbody := by
    rw [← htbody]; exact hRbodyDen
  obtain ⟨vEq0, vs30, hvEq0, hsp30, hRbodyEq⟩ :=
    denoteMeta_mkAppN_inv hRbody3
  obtain ⟨va0, vl0, vr0, rfl, hva0, hvl0, hvr0⟩ : ∃ va0 vl0 vr0,
      vs30 = [va0, vl0, vr0] ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (rP + cnF) αS
        = some va0 ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (rP + cnF) lhsS
        = some vl0 ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (rP + cnF) rhsS
        = some vr0 := by
    cases hsp30 with
    | cons hα htail =>
      cases htail with
      | cons hL htail2 =>
        cases htail2 with
        | cons hR htail3 =>
          cases htail3 with
          | nil => exact ⟨_, _, _, rfl, hα, hL, hR⟩
  have hokVα : ∀ σ : Nat → V, Sat V Γs σ → WellDenotedV V σ va0 := by
    intro σ hσ
    have h : WellDenotedV V σ (AnnotTerm.mkAppN vEq0 [va0, vl0, vr0]) := by
      rw [← hRbodyEq]
      exact wellDenotedV_tower_body_sat htowerS (hokTst _) hσ
    have hshow : AnnotTerm.mkAppN vEq0 [va0, vl0, vr0]
        = .app (.app (.app vEq0 va0) vl0) vr0 := rfl
    refine ⟨?_, ?_⟩
    · have h1 := h.1
      rw [hshow, WellDenoted_app] at h1
      have hA := h1.1
      rw [WellDenoted_app] at hA
      have hB := hA.1
      rw [WellDenoted_app] at hB
      exact hB.2.1
    · have h1 := h.2
      rw [hshow, AnnotValid_app] at h1
      have hA := h1.1
      rw [AnnotValid_app] at hA
      have hB := hA.1
      rw [AnnotValid_app] at hB
      exact hB.2
  -- ===== the pins' readings, off the statement's own major =====
  have hvl0' : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (Expr.mkAppN lhsS.getAppFn lhsS.getAppArgs)
      = some vl0 := by
    rw [Expr.mkAppN_getApp lhsS]; exact hvl0
  obtain ⟨vlh, vlargs, hvlh, hcspL, -⟩ := denoteMeta_mkAppN_inv hvl0'
  have hmajIdx : lhsS.getAppArgs[mI]?
      = some (lhsS.getAppArgs.getLastD (.bvar 0)) := by
    rcases hx : lhsS.getAppArgs[mI]? with _ | y
    · rw [List.getElem?_eq_none_iff, hlarity] at hx
      omega
    · rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlarity,
        Nat.add_sub_cancel, hx, Option.getD_some]
  obtain ⟨vmaj, -, hvmaj⟩ := denoteMetaSpine_getElem?' hcspL mI _ hmajIdx
  rw [denoteMeta_erasedEq hmaj (rP + cnF)] at hvmaj
  obtain ⟨vch, vmargs, hvch, hcspSp, -⟩ := denoteMeta_mkAppN_inv hvmaj
  have hmargsLen : vmargs.length = cnP + cnF := by
    rw [← hcspSp.length, hsplen]
  -- ===== the pins' canonical readings and the crossing datum =====
  have hspPre : DenoteMetaSpine mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (fvs.take rP)
      ((List.range rP).map (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))) := by
    refine DenoteMetaSpine.of_getD _ _
      (by rw [htkSlen, List.length_map, List.length_range]) ?_
    intro q hq
    rw [htkSlen] at hq
    rcases hx : fvs[q]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx; omega
    obtain ⟨ty, rfl⟩ := hshapeS q x hx
    rw [show (fvs.take rP).getD q default = Expr.fvar q ty from by
        rw [List.getD, List.getElem?_take_of_lt hq, hx]; rfl,
      show ((List.range rP).map
          (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))).getD q default
        = AnnotTerm.bvar (rP + cnF - 1 - q) from by
        rw [List.getD, List.getElem?_map, List.getElem?_range hq]; rfl]
    exact denoteMeta_fvar mp.base2.acval (rP + cnF) q ty
  have hpinRead : ∀ q, q < cnP → ∃ w,
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (rP + cnF)
        (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)) = some w := by
    intro q hq
    obtain ⟨w, -, hw⟩ := denoteMetaSpine_getElem?' hcspSp q _ (hspPar q hq)
    exact ⟨w, hw⟩
  have hpinOpen : ∀ q, q < cnP → ∃ vpa,
      denoteMeta mp.base2.acval env φ rP
        (openRev 0 rP
          ((pins.getD q default).instantiateLevelParams lps us))
        = some vpa := by
    intro q hq
    obtain ⟨w, hw⟩ := hpinRead q hq
    have hkey := Rules.denoteMeta_openRev (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) mp.base2.acval_closed hainst
      (fvs.take rP) (e := (pins.getD q default).renameConsts f)
      (d := rP + cnF)
      (fun a ha => ⟨hwsFvs a (List.mem_of_mem_take ha),
        hbFvs a (List.mem_of_mem_take ha)⟩)
      (Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpwdR q hq).1] at hl
        exact nomatch hl))
      (by rw [htkSlen]; exact (hpwdR q hq).2) hspPre
    rw [htkSlen, ← Expr.instSpine_eq_instSeq, hw] at hkey
    rcases hin : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
        (rP + cnF + rP)
        (openRev (rP + cnF) rP ((pins.getD q default).renameConsts f))
      with _ | W
    · rw [hin] at hkey
      exact nomatch hkey
    · refine ⟨W, ?_⟩
      rw [openRev_instantiateLevelParams lps us 0 rP, denotePInstLevels,
        ← denoteMeta_renameConsts hroT, ← openRev_renameConsts,
        ← Rules.denoteMeta_openRev_base (acval := mp.base2.acval)
          (cval := mp.base2.cvalE) (env := env)
          (φ := Level.substFn φ lps us) mp.base2.acval_closed
          mp.base2.acval_erase mp.base2.cval_closed
          (hpwdR q hq).1 (hpwdR q hq).2 (rP + cnF)]
      exact hin
  have hpinCross : ∀ q, q < cnP → ∃ vpa w0,
      denoteMeta mp.base2.acval env φ rP
        (openRev 0 rP
          ((pins.getD q default).instantiateLevelParams lps us))
        = some vpa ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (rP + cnF)
        (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)) = some w0 ∧
      AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w0
        = AnnotTerm.instRevChain (xs.take rP) vpa := by
    intro q hq
    obtain ⟨vpa, hvpa⟩ := hpinOpen q hq
    have hvpa' : denoteMeta mp.base2.acval env (Level.substFn φ lps us) rP
        (openRev 0 rP ((pins.getD q default).renameConsts f))
        = some vpa := by
      rw [openRev_renameConsts, denoteMeta_renameConsts hroT,
        ← denotePInstLevels, ← openRev_instantiateLevelParams lps us 0 rP]
      exact hvpa
    obtain ⟨w0, hw0, hcross⟩ := pinCross (acval := mp.base2.acval)
      (cval := mp.base2.cvalE) (env := env)
      (φ := Level.substFn φ lps us) (cnF := cnF)
      mp.base2.acval_closed hainst mp.base2.acval_erase
      mp.base2.cval_closed (AnnotTerm.sort 0) htkSlen
      (fun i x hx => by
        have hilt : i < rP := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          rw [htkSlen] at this
          exact this
        rw [List.getElem?_take_of_lt hilt] at hx
        exact hshapeS i x hx)
      (fun a ha => hwsFvs a (List.mem_of_mem_take ha))
      (fun a ha => hbFvs a (List.mem_of_mem_take ha))
      (hpwdR q hq).1 (hpwdR q hq).2 hvpa' hxtlen
      (vals := xs.take rP ++ ys.drop cnP) (n := rP + cnF)
      hzslen (by omega) (Nat.le_refl _) hzstake
    rw [show rP + cnF - (rP + cnF) = 0 from by omega, List.replicate_zero,
      List.append_nil] at hcross
    exact ⟨vpa, w0, hvpa, hw0, hcross⟩
  -- ===== the mixed value spine =====
  have hmixlen : ((vmargs.take cnP).map (AnnotTerm.instSeq
      (xs.take rP ++ ys.drop cnP) (rP + cnF - 1))
      ++ ys.drop cnP).length = cnP + cnF := by
    rw [List.length_append, List.length_map, List.length_take,
      List.length_drop, hmargsLen, hlenY]
    omega
  have hmixTakeLen : (vmargs.take cnP).length = cnP := by
    rw [List.length_take, hmargsLen]
    omega
  have hmixsp : ∀ (q : Nat) (x : KExpr),
      (psR ++ fvs.drop rP)[q]? = some x →
      ∃ w0, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF) x = some w0 ∧
        ((vmargs.take cnP).map (AnnotTerm.instSeq
          (xs.take rP ++ ys.drop cnP) (rP + cnF - 1))
          ++ ys.drop cnP)[q]?
          = some (AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP)
            (rP + cnF - 1) w0) := by
    intro q x hx
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · obtain ⟨w, hwq, hdw⟩ := denoteMetaSpine_getElem?' hcspSp q x hx
      refine ⟨w, hdw, ?_⟩
      rw [List.getElem?_append_left
          (by rw [List.length_map, hmixTakeLen]; omega),
        List.getElem?_map, List.getElem?_take_of_lt hqc, hwq]
      rfl
    · rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx
      have hqf : q < cnP + cnF := by
        have hlt := (List.getElem?_eq_some_iff.mp hx).1
        rw [hfvslen] at hlt
        omega
      obtain ⟨ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      refine ⟨.bvar (rP + cnF - 1 - (rP + (q - cnP))),
        denoteMeta_fvar mp.base2.acval (rP + cnF) _ ty, ?_⟩
      rw [instSeqAV_bvar_full (by omega) hzslen,
        List.getElem?_append_right
          (by rw [List.length_map, hmixTakeLen]; omega),
        List.length_map, hmixTakeLen, List.getElem?_drop,
        show cnP + (q - cnP) = q from by omega,
        hzsFld (q - cnP) (by omega),
        show cnP + (q - cnP) = q from by omega, List.getD]
      rcases hy : ys[q]? with _ | v
      · rw [List.getElem?_eq_none_iff, hlenY] at hy
        omega
      · rfl
  have hmixFldEq : ∀ j, j < cnF →
      ((vmargs.take cnP).map (AnnotTerm.instSeq
        (xs.take rP ++ ys.drop cnP) (rP + cnF - 1))
        ++ ys.drop cnP).getD (cnP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right
      (by rw [List.length_map, hmixTakeLen]; omega),
      List.length_map, hmixTakeLen, List.getElem?_drop,
      show cnP + j - cnP = j from by omega]
    rfl
  have hmixPar : ∀ q, q < cnP →
      interp V ρ (((vmargs.take cnP).map (AnnotTerm.instSeq
        (xs.take rP ++ ys.drop cnP) (rP + cnF - 1))
        ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    obtain ⟨vpa, w0, hvpa, hw0, hcross⟩ := hpinCross q hq
    obtain ⟨w, hwq, hdw⟩ := denoteMetaSpine_getElem?' hcspSp q _
      (hspPar q hq)
    obtain rfl : w = w0 := Option.some.inj (hdw.symm.trans hw0)
    have hget : ((vmargs.take cnP).map (AnnotTerm.instSeq
        (xs.take rP ++ ys.drop cnP) (rP + cnF - 1))
        ++ ys.drop cnP).getD q default
        = AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w := by
      rw [List.getD, List.getElem?_append_left
        (by rw [List.length_map, hmixTakeLen]; omega),
        List.getElem?_map, List.getElem?_take_of_lt hq, hwq]
      rfl
    rw [hget, hcross]
    exact (hparP q hq vpa hvpa).symm
  have hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ (((vmargs.take cnP).map (AnnotTerm.instSeq
        (xs.take rP ++ ys.drop cnP) (rP + cnF - 1))
        ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · exact hmixPar q hqc
    · rw [show q = cnP + (q - cnP) from by omega]
      exact congrArg _ (hmixFldEq (q - cnP) (by omega))
  -- ===== the ladders, and the zipper =====
  have hparZ : ∀ N, rP ≤ N → N ≤ rP + cnF → ∀ q, q < cnP →
      ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      ∃ w, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF)
            ((psR ++ fvs.drop rP).getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF) (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw := by
    intro N hrPN hN
    refine nestedParamSupply (m := mp.base2) (hdeq _) (hinf _)
      (hreadsP _) (hframe _) hroT hrPN hfvslen hΓslen hfvsPlen hshapeP hwsFvsP
      hleafClosedP hlbFvsP htowerP hokTV hdomsP0 (hpadLen N hN)
      (hpadEnt N hN)
      (prefixGradeFire (hdeq _) hfvslen hshapeS hwsFvs hleafClosed
        hlbFvs htowerS hokTst hdomsS0 hfvsPlen hshapeP htowerP hokTV
        hdomsP0 hroT htyRw htyRb hrinst hrenP hdePre hN)
      hpinsLen hpinsWf hCvLw hCvLb (hCvL0 (rP + cnF)) hokTVj hpsP
      hcinstP hTypedP hsplen hspPar hcinst
      (show RenEqT f ctyL
          (ctyL.renameConsts f) from Expr.ErasedEq.rfl _)
      ?_ ?_
    · intro q hq
      show Expr.ErasedEq _ _
      rw [Expr.instSpine_eq_instSeq, Expr.instSpine_eq_instSeq]
      refine Expr.ErasedEq.trans
        (Expr.instSeq_renameConsts (f := f) (fvsP.take rP) (rP - 1) ?_) ?_
      · intro x hx
        obtain ⟨q0, hq0⟩ := List.getElem?_of_mem hx
        have hq0lt : q0 < rP := by
          have := (List.getElem?_eq_some_iff.mp hq0).1
          rw [htkPlen] at this
          exact this
        rw [List.getElem?_take_of_lt hq0lt] at hq0
        obtain ⟨ty, rfl⟩ := hshapeP q0 _ hq0
        exact rfl
      · refine Expr.instSeq_erasedEq_args (fvsP.take rP) (fvs.take rP)
          (rP - 1) (Expr.ErasedEq.rfl _) ?_ (by rw [htkPlen, htkSlen])
        intro k b₁ b₂ hb₁ hb₂
        have hklt : k < rP := by
          rcases Nat.lt_or_ge k rP with h' | h'
          · exact h'
          · rw [List.getElem?_eq_none (by rw [htkPlen]; omega)] at hb₁
            exact nomatch hb₁
        rw [List.getElem?_take_of_lt hklt] at hb₁
        rw [List.getElem?_take_of_lt hklt] at hb₂
        obtain ⟨ty, rfl⟩ := hshapeP k _ hb₁
        obtain ⟨ty', rfl⟩ := hshapeS k _ hb₂
        exact rfl
    · intro q hq
      obtain ⟨w, hw⟩ := hpinRead q hq
      refine ⟨w, ?_⟩
      rw [List.getD, hspPar q hq]
      exact hw
  obtain ⟨hsat, hfitS⟩ := zipper (hdeq _) hroT hrPmI hlenX hlenY
    hfvslen hshapeS hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0
    hfvsPlen hshapeP htowerP hokTV hdomsP0 htyRw htyRb hrinst hrenP
    hCwR hCbR hTVjK hokTVj hTVjcl htowerJ hsplen hspLeaf hspScope
    hspFld hcinst hmixlen hmixsp hmixFldEq hmixPar hfitRpre hfitC
    hdePre hdeFld hparZ
  -- ===== the sides' memberships and gradings =====
  obtain ⟨tl, hInfL, hDeqL⟩ := hsideL
  obtain ⟨tr, hInfR, hDeqR⟩ := hsideR
  obtain ⟨hwsTl, hbTl, hsubTl⟩ := hframe (Level.substFn φ lps us) hInfL hwsL hbL
    hLL (hctxOf lhsS hleafL hltL) hvl0
  obtain ⟨hwsTr, hbTr, hsubTr⟩ := hframe (Level.substFn φ lps us) hInfR hwsR hbR
    hLR (hctxOf rhsS hleafR hltR) hvr0
  have hleafTl : ∀ l ∈ tl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs :=
    fun l hl => hleafL l (hsubTl l hl)
  have hleafTr : ∀ l ∈ tr.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs :=
    fun l hl => hleafR l (hsubTr l hl)
  have hltTl : ∀ l ∈ tl.fvarLeaves, l.1 < rP + cnF :=
    fun l hl => hfvsLt l (hleafTl l hl)
  have hltTr : ∀ l ∈ tr.fvarLeaves, l.1 < rP + cnF :=
    fun l hl => hfvsLt l (hleafTr l hl)
  have hLTl : Expr.LeavesBounded tl := fun l hl =>
    hlbFvs l.1 l.2 (hleafTl l hl)
  have hLTr : Expr.LeavesBounded tr := fun l hl =>
    hlbFvs l.1 l.2 (hleafTr l hl)
  obtain ⟨tla, htla⟩ := hreadsP (Level.substFn φ lps us) hInfL hwsL hbL
    hLL (hctxOf lhsS hleafL hltL) hvl0
  obtain ⟨tra, htra⟩ := hreadsP (Level.substFn φ lps us) hInfR hwsR hbR
    hLR (hctxOf rhsS hleafR hltR) hvr0
  obtain ⟨hokVL, hokVR, hmemLR⟩ := sidesMem (hinf _) (hdeq _)
    (hctxOf αS hleafα hltα) (hctxOf lhsS hleafL hltL)
    (hctxOf rhsS hleafR hltR) hwsα hbα hLα hwsL hbL hLL hwsR hbR hLR
    hva0 hvl0 hvr0 hokVα hInfL hDeqL hInfR hDeqR htla htra
    (hctxOf tl hleafTl hltTl) (hctxOf tr hleafTr hltTr)
    hwsTl hbTl hLTl hwsTr hbTr hLTr
  -- ===== the transport's frame data =====
  have hCfb : Expr.fvarsBelow rP ctyL :=
    Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCvLw] at hl
      exact nomatch hl)
  have hpsPlen : psP.length = cnP := by
    rw [hpsP, List.length_map, hpinsLen]
  have hpsPget : ∀ q, q < cnP →
      psP[q]?
        = some (Expr.instSpine (fvsP.take rP) (rP - 1)
            (pins.getD q default)) := by
    intro q hq
    rw [hpsP, List.getElem?_map, hpgetd q hq]
    rfl
  have hpsRen : ∀ (i : Nat) (a a' : KExpr),
      psP[i]? = some a →
      psR[i]? = some a' → RenEqT f a a' := by
    intro i a a' ha ha'
    have hi : i < cnP := by
      rcases Nat.lt_or_ge i cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hpsPlen]; omega)] at ha
        exact nomatch ha
    rw [hpsPget i hi] at ha
    rw [hpinsRget i hi] at ha'
    obtain rfl : a = Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD i default) := (Option.some.inj ha).symm
    obtain rfl : a' = Expr.instSpine (fvs.take rP) (rP - 1)
        ((pins.getD i default).renameConsts f) := (Option.some.inj ha').symm
    show Expr.ErasedEq _ _
    rw [Expr.instSpine_eq_instSeq, Expr.instSpine_eq_instSeq]
    refine Expr.ErasedEq.trans
      (Expr.instSeq_renameConsts (f := f) (fvsP.take rP) (rP - 1) ?_) ?_
    · intro x hx
      obtain ⟨q0, hq0⟩ := List.getElem?_of_mem hx
      have hq0lt : q0 < rP := by
        have := (List.getElem?_eq_some_iff.mp hq0).1
        rw [htkPlen] at this
        exact this
      rw [List.getElem?_take_of_lt hq0lt] at hq0
      obtain ⟨ty, rfl⟩ := hshapeP q0 _ hq0
      exact rfl
    · refine Expr.instSeq_erasedEq_args (fvsP.take rP) (fvs.take rP)
        (rP - 1) (Expr.ErasedEq.rfl _) ?_ (by rw [htkPlen, htkSlen])
      intro k b₁ b₂ hb₁ hb₂
      have hklt : k < rP := by
        rcases Nat.lt_or_ge k rP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by rw [htkPlen]; omega)] at hb₁
          exact nomatch hb₁
      rw [List.getElem?_take_of_lt hklt] at hb₁
      rw [List.getElem?_take_of_lt hklt] at hb₂
      obtain ⟨ty, rfl⟩ := hshapeP k _ hb₁
      obtain ⟨ty', rfl⟩ := hshapeS k _ hb₂
      exact rfl
  have hpsPfacts : ∀ (j : Nat) (x : KExpr),
      psP[j]? = some x →
      (∃ w, denoteMeta mp.base2.acval env (Level.substFn φ lps us) rP x
        = some w) ∧ Expr.WScoped rP x ∧ x.looseBVarsBounded 0 = true := by
    intro j x hx
    have hj : j < cnP := by
      rcases Nat.lt_or_ge j cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hpsPlen]; omega)] at hx
        exact nomatch hx
    rw [hpsPget j hj] at hx
    obtain rfl : x = Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD j default) := (Option.some.inj hx).symm
    have hwsx : Expr.WScoped rP (Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD j default)) :=
      instSpine_WScoped (rP - 1)
        (Expr.WScoped.of_not_hasFvar (hpwd j hj).1)
        (fun a ha => hwsFvsP a (List.mem_of_mem_take ha))
    have hbx : (Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD j default)).looseBVarsBounded 0 = true := by
      have hbFvsP : ∀ a ∈ fvsP, a.looseBVarsBounded 0 = true := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
        obtain ⟨ty, rfl⟩ := hshapeP q a hq
        rfl
      have h := instSpine_closed (args := fvsP.take rP)
        (e := pins.getD j default)
        (fun a ha => hbFvsP a (List.mem_of_mem_take ha))
        (by rw [htkPlen]; exact (hpwd j hj).2)
      rwa [htkPlen] at h
    refine ⟨?_, hwsx, hbx⟩
    obtain ⟨w, hw⟩ := hpinRead j hj
    have hsame : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
        (rP + cnF) (Expr.instSpine (fvsP.take rP) (rP - 1)
          (pins.getD j default))
        = some w := by
      rw [← RenEqT.denoteMeta (φ := Level.substFn φ lps us) hroT
        (hpsRen j _ _ (hpsPget j hj) (hpinsRget j hj)) (rP + cnF)]
      exact hw
    rw [denoteMeta_lift mp.base2.acval_closed hwsx (rP + cnF) (by omega)] at hsame
    rcases hd : denoteMeta mp.base2.acval env (Level.substFn φ lps us) rP
        (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD j default))
      with _ | v
    · rw [hd] at hsame
      exact nomatch hsame
    · exact ⟨v, rfl⟩
  obtain ⟨Xcrest, hXcrest⟩ := instPisAt_denoteMeta_defined
    mp.base2.acval_closed hainst
    psP hcinstP hpsPfacts
    hCfb hCvLb (hCvL0 rP)
  obtain ⟨Γx, Rx, htowerX, hRxden, hdomsX0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) cnF hopenXP hXcrest
  have hpsPws : ∀ a ∈ psP, Expr.WScoped rP a := by
    intro a ha
    rw [hpsP] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact instSpine_WScoped (rP - 1)
      (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1)
      (fun x hx => hwsFvsP x (List.mem_of_mem_take hx))
  have hwsCrestP : Expr.WScoped rP crestP :=
    (instPisAt_WScoped (d := rP) psP ctyL hcinstP
      (Expr.WScoped.of_not_hasFvar hCvLw) hpsPws).2
  have hwsX : ∀ x ∈ xFvsP, Expr.WScoped (rP + cnF) x :=
    (openPisAtFvars_WScoped cnF crestP rP hopenXP hwsCrestP).1
  have hsatId : ∀ ρ' : Nat → V, Sat V Γs ρ' →
      Sat V (List.replicate (rP + cnF - (rP + cnF)) (AnnotTerm.sort 0)
        ++ Γs.drop (rP + cnF - (rP + cnF))) ρ' := by
    intro ρ' h
    rw [show rP + cnF - (rP + cnF) = 0 from by omega,
      List.replicate_zero, List.nil_append, List.drop_zero]
    exact h
  have hpreK := prefixGradeFire (hdeq (Level.substFn φ lps us)) hfvslen
    hshapeS hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0 hfvsPlen
    hshapeP htowerP hokTV hdomsP0 hroT htyRw htyRb hrinst hrenP hdePre
    (Nat.le_refl (rP + cnF))
  have hzipAll := fun j (hj : j < cnF) =>
    zipFieldTermEq mp.base2.acval_closed hainst hCwR hCbR hTVjK hTVjcl
      htowerJ hsplen hspLeaf hspScope hcinst hzslen hmixlen hmixsp hj
  have hfldK := fieldGradeFire (hdeq (Level.substFn φ lps us)) hfvslen
    hshapeS hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0 hCwR hCbR
    hTVjK hokTVj hsplen hspScope hspFld hcinst
    (fun j hj => (hzipAll j hj).1) (fun j hj => (hzipAll j hj).2.1)
    hdeFld (Nat.le_refl (rP + cnF))
    (hparZ (rP + cnF) (by omega) (Nat.le_refl _))
  have hIdent := annotPFrameEq (m := mp.base2) hroT hopenP hdomsP0
    (show RenEqT f ctyL
        (ctyL.renameConsts f) from Expr.ErasedEq.rfl _)
    hpsPlen hpinsRlen hpsRen hcinstP hopenXP hwsX hwsFvsP hdomsX0A
    hfvslen hcinst hshapeS
    (fun n hn ρ' hρ' => hpreK n (by omega) hn ρ' (hsatId ρ' hρ'))
    (fun n hn1 hn2 ρ' hρ' dw hdw =>
      hfldK n (by omega) hn1 hn2 ρ' (hsatId ρ' hρ') dw hdw)
  -- ===== the applied reduct's grading at the frame's own openers =====
  have hcinstP' : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p)) ctyL
      = some (cdomsP, crestP) := by
    rw [← hpsP]
    exact hcinstP
  have hokApp := annotOpeners_lamWalk (m := mp.base2)
    (hdeq (Level.substFn φ lps us)) hroT hfvslen hshapeS hwsFvs hlbFvs
    hΓslen hdomsS0 hΔaent (pinsWalkOk_nested hpinsLen hpinsWf)
    htyw htyb hCvLw hCvLb hopenP hcinstP' hopenXP hIdent
    hrhsw hrhsb hRaden (fun τ => (hRaFacts τ).1) hwalk
  -- ===== the right side is the rule's own application =====
  have heqR := reduct (hdeq (Level.substFn φ lps us)) hroT hfvslen
    hshapeS hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0 hΓslen
    hΔaent hrhsw hrhsb hRaden hvr0 hwsR hbR hleafR hltR hokVR hdeRhs
    hokApp hzslen hsat
  -- ===== fire the checked equation =====
  obtain ⟨vα1, vL1, vR1, hvα1, hvL1, hvR1, heqLR⟩ :=
    fire (m := mp.base2) (eqFormerKey mp heqfE) mp.eq_law heqfE
      htowerS hokTst (fun σ => (hTstFacts σ).1) hRbodyDen htbody
      (fun a b c h1 h2 h3 => by
        obtain rfl : a = va0 := Option.some.inj (h1.symm.trans hva0)
        obtain rfl : b = vl0 := Option.some.inj (h2.symm.trans hvl0)
        obtain rfl : c = vr0 := Option.some.inj (h3.symm.trans hvr0)
        exact hmemLR (chain V ρ (xs.take rP ++ ys.drop cnP)) hsat)
      hzslen hsat hfitS
  obtain rfl : vL1 = vl0 := Option.some.inj (hvL1.symm.trans hvl0)
  obtain rfl : vR1 = vr0 := Option.some.inj (hvR1.symm.trans hvr0)
  -- ===== the left side is the fired redex =====
  have hctorHead : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (.const (f ctor) lvls)
      = some (mp.base2.acval ctor
        (Level.substFn φ cvj.levelParams usj)) := by
    have hctorLev : mp.base2.acval ctor
          (Level.substFn φ cvj.levelParams usj)
        = mp.base2.acval ctor
          (Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls) :=
      mp.base2.acval_params ctor _ hctorE _ _ (fun p hp => hagree p hp)
    rw [denoteMeta_const hfCmE (by rw [hCmlps]; exact hlvlsLen), hCmlps,
      hroT.2.2, hctorLev]
  have hspMem : ∀ σ : Nat → V, Sat V Γs σ →
      ∀ (q : Nat) (x : KExpr),
        (psR ++ fvs.drop rP)[q]? = some x →
        ∃ w, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
              (rP + cnF) x = some w ∧ WellDenotedV V σ w ∧
          ∀ dw, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
              (rP + cnF) (cdoms.getD q default) = some dw →
            interp V σ w ∈ˢ interp V σ dw := by
    intro σ hσ q x hx
    have hgq : (psR ++ fvs.drop rP).getD q default = x := by
      rw [List.getD, hx]
      rfl
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · have h := hparZ (rP + cnF) (by omega) (Nat.le_refl _) q hqc σ
        (hsatId σ hσ)
      rw [hgq] at h
      exact h
    · have hq : q < cnP + cnF := by
        rcases Nat.lt_or_ge q (cnP + cnF) with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by rw [hsplen]; omega)] at hx
          exact nomatch hx
      have hx' := hx
      rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx'
      obtain ⟨ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx'
      refine ⟨.bvar (rP + cnF - 1 - (rP + (q - cnP))),
        denoteMeta_fvar mp.base2.acval (env := env)
          (φ := Level.substFn φ lps us) (rP + cnF) (rP + (q - cnP)) ty,
        ⟨by simp, by simp⟩, ?_⟩
      intro dw hdw
      have hfld := hfldK (rP + (q - cnP)) (by grind) (by grind)
        (by grind) σ (hsatId σ hσ) dw (by
          rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel' hqc]
          exact hdw)
      have hslot := hσ (rP + cnF - 1 - (rP + (q - cnP)))
        (Γs.getD (rP + cnF - 1 - (rP + (q - cnP))) default)
        (hΔaent (rP + (q - cnP)) (by omega))
      rw [show (fun j => σ (j + (rP + cnF - 1 - (rP + (q - cnP))) + 1))
          = (fun j => σ (j + (rP + cnF - (rP + (q - cnP))))) from by
        funext j; congr 1; grind] at hslot
      rw [hfld.2] at hslot
      rw [interp_bvar]
      exact hslot
  have heqL := point (hdeq (Level.substFn φ lps us)) hroT
    (zs := xs.take rP ++ ys.drop cnP) rfl hrPmI hlenX hlenY hfRnE
    hRmlps hfvslen hshapeS hwsFvs hlbFvs htowerS hokTst hdomsS0 hΓslen
    hΔaent hsat hvl0 hwsL hbL hokVL hlhead hlarity hlpre hmaj
    hctorHead hleafL hltL hCwR hCbR hTVjK hokTVj hTVjcl htowerJ
    hsplen hspLeaf hspScope hcinst hclen hspMem hRjdec hArgsClen
    hdeIdx hmixlen hmixsp hmixVal hfitC hidx
  refine ⟨heqL.symm.trans (heqLR.trans heqR), ?_⟩
  -- ===== the truthfulness transport =====
  intro hxsA hysA
  have hzsAnnot : ∀ w ∈ xs.take rP ++ ys.drop cnP, WellDenotedV V ρ w := by
    intro w hw
    rcases List.mem_append.mp hw with hw' | hw'
    · exact hxsA w (List.mem_of_mem_take hw')
    · exact hysA w (List.mem_of_mem_drop hw')
  exact annotTransport_lamWalk (hdeq (Level.substFn φ lps us))
    (pinsWalkOk_nested hpinsLen hpinsWf) htyw htyb hCvLw hCvLb
    hopenP hcinstP' hopenXP hΓslen hΔaent hIdent hrhsw hrhsb hRaden
    (fun τ => (hRaFacts τ).1) hwalk hzslen hsat
    (teleFitPA_to_chain (rP + cnF) htowerS hzslen hfitS) hzsAnnot

set_option maxHeartbeats 12800000 in
/-- One checked `.nested` rule's `RecRuleLaw` from `IotaRuleVmRunJ` at arbitrary `RenameOk` renaming `f`. -/
theorem iotaRuleNested_vmF {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {J : Judgements .anon} {env₂ envSelf : Env .anon}
    (mp : EnvModelM V μ envSelf)
    (hJ : JudgeSound J mp.base2)
    {f : Key .anon → Key .anon}
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hup : ∀ (n : Key .anon) (ci : ConstantInfo .anon), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal .anon} {mI rP j : Nat} {r r' : RecRule .anon}
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleNVmRunJ J env₂ envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    {lvls : List Level} {pins : List KExpr}
    (hfireN : RecRule.fire r' = .nested lvls pins) (φ : LevelParam → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' := by
  have hdeq := hJ.defeq
  have hinf := hJ.infer
  have hreadsP := hJ.reads
  have hframe := hJ.frame
  obtain ⟨cvjK, cnPK, cnFK, rhsA, lvls0, pins0, hfcK, hnfK, hrb, hrf, hann, hrlp,
    hrres, hstripRhs, hrun0, hr'eq, hthm0⟩ := hkit
  have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]; rfl
  have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]; rfl
  have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]; rfl
  have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq, hnfK]; rfl
  have hr'fire : RecRule.fire r' = .nested lvls0 pins0 := by rw [hr'eq]; rfl
  obtain ⟨htyw0, -, -, htyb0, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hself)
  have htyw : cvA.type.hasFvar = false := htyw0
  have htyb : cvA.type.looseBVarsBounded 0 = true := htyb0
  have hfcS : envSelf.find? (RecRule.ctor r)
      = some (.ctorInfo cvjK cnPK cnFK) := by
    rcases hup _ _ hfcK with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hCw, hClp, -, hCb, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hfcS)
  obtain ⟨ciRm, hfRnE, hRmlps⟩ := hroT.1 cvA.name _ hself
  obtain ⟨ciCm, hfCmE, hCmlps⟩ := hroT.1 (RecRule.ctor r) _ hfcS
  have heqfS : envSelf.find? eqName = some eqA := by
    rcases hup _ _ heqfind with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hrhsAw, hrhsAb⟩ := hJ.annot_syntax hann hrf hrb
  have htyOk : ∀ (ψ : LevelParam → Nat) (ta : AnnotTerm),
      denoteMeta mp.base2.acval envSelf ψ 0 cvA.type = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta :=
    mp.type_wellDenotedV _ (Env.find?_mem hself)
  have hrhsLeafNil : ∀ l ∈ rhsA.fvarLeaves, False := by
    intro l hl
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsAw] at hl
    exact nomatch hl
  have hrhsWs : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrhsAw
  have hrhsLb : Expr.LeavesBounded rhsA :=
    fun l hl => absurd hl (fun h => hrhsLeafNil l h)
  obtain ⟨t', hrun⟩ := hrun0
  have hrhsKey : ∀ ψ : LevelParam → Nat, ∃ Ra ta,
      denoteMeta mp.base2.acval envSelf ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Ra ∧
        interp V ρ Ra ∈ˢ interp V ρ ta := by
    intro ψ
    obtain ⟨Ra, hRa⟩ :=
      hJ.accepted ψ hrun hrhsWs hrhsAb hrhsLb
    have hctx : CtxOk mp.base2 ψ 0 [] rhsA :=
      ⟨rfl, fun l hl => absurd hl (fun h => hrhsLeafNil l h)⟩
    obtain ⟨ta, hta⟩ := hreadsP ψ hrun hrhsWs hrhsAb hrhsLb
      hctx hRa
    obtain ⟨hokRa, -, hmemRa⟩ :=
      hinf ψ hrun hrhsWs hrhsAb hrhsLb hctx hRa hta
    exact ⟨Ra, ta, hRa, fun ρ =>
      ⟨hokRa ρ (Sat_nil V ρ), hmemRa ρ (Sat_nil V ρ)⟩⟩
  have hctorId : ∀ {cvj' : ConstantVal .anon} {cnP' cnF' : Nat},
      envSelf.find? (RecRule.ctor r')
        = some (.ctorInfo cvj' cnP' cnF') →
      cvj' = cvjK ∧ cnP' = cnPK ∧ cnF' = cnFK := by
    intro cvj' cnP' cnF' hf'
    rw [hr'ctor, hfcS] at hf'
    injection hf' with h1
    injection h1 with e1 e2 e3
    exact ⟨e1.symm, e2.symm, e3.symm⟩
  -- ===== the nested branch =====
  obtain ⟨rfl, rfl⟩ : lvls = lvls0 ∧ pins = pins0 :=
    Ix.Kernel.RecRuleFire.nested.inj (hfireN.symm.trans hr'fire)
  obtain ⟨hshape, hthmN⟩ := hthm0
  obtain ⟨hrPmI, -, hpinsWf0, -⟩ := nestedRuleShape_inv hshape
  obtain ⟨-, -, -, pre, domD, bodyD, bmD, D,
    -, -, -, hpinsLen⟩ := nestedRuleShape_inv hshape
  have hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true :=
    fun p hp => ⟨(hpinsWf0 p hp).1, (hpinsWf0 p hp).2.2.2⟩
  refine ⟨hrPmI, ?_⟩
  intro us huslen
  obtain ⟨cvt, fvs, tbody, hcvtE, hcvtlps, hopen, hEqH,
    hlen3, hlhead0, hlarity0, hlpre0, hmaj0, hCstripsHead,
    cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP, xFvsP,
    ldoms, hcinst, hclen, hrinst, hopenP,
    ⟨hcinstP, hopenXP, hldomsAr⟩,
    hwalk, hTypedP, hruns⟩ := hthmN
  obtain ⟨ciT, hciTS, hciTcv⟩ : ∃ ciT, envSelf.find?
      (auxKey (auxKey cvA.name .model) (.iota j)) = some ciT ∧
      ciT.toConstantVal = cvt := by
    unfold Env.findCV? at hcvtE
    rcases h : env₂.find? (auxKey (auxKey cvA.name .model) (.iota j))
      with _ | ci₂
    · rw [h] at hcvtE; exact nomatch hcvtE
    · rw [h] at hcvtE
      have hcv₂ : ci₂.toConstantVal = cvt := Option.some.inj hcvtE
      rcases hup _ _ h with h' |
        ⟨cv, mI', rP', rules, rules', heq, h'⟩
      · exact ⟨ci₂, h', hcv₂⟩
      · exact ⟨.recInfo cv mI' rP' rules', h',
        by rw [← hcv₂, heq]; rfl⟩
  obtain ⟨hSw0, -, -, hSb0, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hciTS)
  rw [hciTcv] at hSw0 hSb0
  have hSw : cvt.type.hasFvar = false := hSw0
  have hSb : cvt.type.looseBVarsBounded 0 = true := hSb0
  have hthm : ∀ ψ : LevelParam → Nat, ∃ ta,
      denoteMeta mp.base2.acval envSelf ψ 0 cvt.type = some ta ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ ta) ∧
        WellDenotedV V ρ ta := by
    intro ψ
    obtain ⟨ta, hta0⟩ := mp.type_reads ciT (Env.find?_mem hciTS) ψ
    have hta : denoteMeta mp.base2.acval envSelf ψ 0 cvt.type = some ta := by
      rwa [hciTcv] at hta0
    exact ⟨ta, hta, fun ρ =>
      ⟨⟨_, mp.mem_type ciT (Env.find?_mem hciTS) ψ ta hta0 ρ⟩,
        mp.type_wellDenotedV ciT (Env.find?_mem hciTS) ψ ta hta0 ρ⟩⟩
  obtain ⟨ℓA, hheadEq⟩ : ∃ ℓA,
      tbody.getAppFn = .const eqName [ℓA] := by
    unfold isEqHead at hEqH
    split at hEqH
    · next c ℓ heq =>
      exact ⟨ℓ, by rw [heq, eq_of_beq hEqH]⟩
    · exact nomatch hEqH
  obtain ⟨αS, lhsS, rhsS, hargs3⟩ : ∃ αS lhsS rhsS,
      tbody.getAppArgs = [αS, lhsS, rhsS] := by
    rcases h : tbody.getAppArgs with _ | ⟨a, l1⟩
    · rw [h] at hlen3; exact nomatch hlen3
    rcases l1 with _ | ⟨b, l2⟩
    · rw [h] at hlen3; exact nomatch hlen3
    rcases l2 with _ | ⟨c, l3⟩
    · rw [h] at hlen3; exact nomatch hlen3
    rcases l3 with _ | ⟨d, l4⟩
    · exact ⟨a, b, c, rfl⟩
    · rw [h] at hlen3; exact nomatch hlen3
  have hα : tbody.getAppArgs.getD 0 (.bvar 0) = αS := by
    rw [hargs3]; rfl
  have hL : tbody.getAppArgs.getD 1 (.bvar 0) = lhsS := by
    rw [hargs3]; rfl
  have hR : tbody.getAppArgs.getD 2 (.bvar 0) = rhsS := by
    rw [hargs3]; rfl
  simp only [hL] at hlhead0 hlarity0 hlpre0 hmaj0
  simp only [hα, hL, hR] at hruns
  obtain ⟨hdeIdx, hdeFld, hdePre, hdeRhs, hsideL, hsideR⟩ := hruns
  have hCstrips' := hCstripsHead
  obtain ⟨Tst0, hTst0, -⟩ := hthm φ
  have hlvlsLen : lvls.length = cvjK.levelParams.length := by
    have hCmlps' : _ = cvjK.levelParams := hCmlps
    rw [← hCmlps']
    exact nestedLvlsLength
      (denoteMeta_erase mp.base2.acval_erase 0 _ hTst0)
      hopen hheadEq hargs3 (eq_of_beq hlhead0) hlarity0 hmaj0 hfCmE
  -- ===== the public frame, at the instantiated valuation =====
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LevelParam → Nat,
      ψ = Level.substFn φ cvA.levelParams us := ⟨_, rfl⟩
  obtain ⟨TV, hTV0R⟩ := mp.type_reads _ (Env.find?_mem hself) ψ
  have hTV0 : denoteMeta mp.base2.acval envSelf ψ 0 cvA.type = some TV :=
    hTV0R
  obtain ⟨ΓP, RP, htowerP, hRPden, hdomsP0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval)
      (env := envSelf) (φ := ψ) rP hopenP hTV0
  have hfvsPlen : fvsP.length = rP := Ix.Kernel.Model.openPisAtFvars_length _ hopenP
  have hshapeP : ∀ (i : Nat) (x : KExpr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
    exact ⟨ty, by simpa using hx'⟩
  have hdomsP0 : ∀ (i : Nat) (x : KExpr), fvsP[i]? = some x →
      denoteMeta mp.base2.acval envSelf ψ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i x hx
    have h := hdomsP0A i x hx
    rwa [Nat.zero_add] at h
  have hwsP := openPisAtFvars_WScoped rP cvA.type 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyw)
  have hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x := by
    intro x hx
    have h := hwsP.1 x hx
    rwa [Nat.zero_add] at h
  have hlbFvsP : ∀ (i : Nat) (ty : KExpr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true :=
    fun i ty hmem =>
      (openPisAtFvars_bounded rP hopenP htyb).2 _ hmem
  have hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP := by
    intro l ⟨x, hx, hl⟩
    rcases openPisAtFvars_leaves _ hopenP l (Or.inr ⟨x, hx, hl⟩) with
      h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
      exact nomatch h0
    · exact h0
  have hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV := htyOk ψ TV hTV0
  have hctyPw : (cvjK.type.instantiateLevelParams cvjK.levelParams
      lvls).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact hCw
  have hctyPb : (cvjK.type.instantiateLevelParams cvjK.levelParams
      lvls).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hCb
  obtain ⟨TVjP, hTVjP0R⟩ := mp.type_reads _ (Env.find?_mem hfcS)
    (Level.substFn ψ cvjK.levelParams lvls)
  have hTVjP00 : denoteMeta mp.base2.acval envSelf
      (Level.substFn ψ cvjK.levelParams lvls) 0 cvjK.type
      = some TVjP := hTVjP0R
  have hTVjP0 : denoteMeta mp.base2.acval envSelf ψ 0
      (cvjK.type.instantiateLevelParams cvjK.levelParams lvls)
      = some TVjP := by
    rw [denotePInstLevels]
    exact hTVjP00
  have hTVjPcl : ∀ k : Nat, TVjP.liftN 1 k = TVjP := fun k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hctyPw hctyPb hTVjP0 1 k
  have hTVjP : denoteMeta mp.base2.acval envSelf ψ (rP + cnFK)
      (cvjK.type.instantiateLevelParams cvjK.levelParams lvls)
      = some TVjP :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hctyPw hTVjPcl
      hTVjP0 (rP + cnFK)
  have hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP :=
    mp.type_wellDenotedV _ (Env.find?_mem hfcS) _ TVjP hTVjP0R
  have htkPlen : (fvsP.take rP).length = rP := by
    rw [List.length_take, hfvsPlen]
    omega
  have hbFvsP : ∀ x ∈ fvsP, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := hshapeP q x hq
    rfl
  have hopenerLeafP : ∀ (q0 : Nat) (a : KExpr),
      (fvsP.take rP)[q0]? = some a → ∀ l ∈ a.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvsP := by
    intro q0 a ha l hl
    have hq0lt : q0 < rP := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [htkPlen] at this
      exact this
    rw [List.getElem?_take_of_lt hq0lt] at ha
    obtain ⟨ty, rfl⟩ := hshapeP q0 a ha
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact List.mem_of_getElem? ha
    · refine hleafClosedP l ⟨_, List.mem_of_getElem? ha, ?_⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hpinSyn : ∀ x ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      Expr.WScoped (rP + cnFK) x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine ⟨(instSpine_WScoped (rP - 1)
        (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1)
        (fun x hx => hwsFvsP x (List.mem_of_mem_take hx))).mono
      (by omega), ?_, ?_⟩
    · have h := instSpine_closed (args := fvsP.take rP) (e := p)
        (fun x hx => hbFvsP x (List.mem_of_mem_take hx))
        (by rw [htkPlen]; exact (hpinsWf p hp).2)
      rwa [htkPlen] at h
    · intro l hl
      rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨x, hx, hlx⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinsWf p hp).1] at hl'
        exact nomatch hl'
      · obtain ⟨q0, hq0⟩ := List.getElem?_of_mem hx
        exact hlbFvsP _ _ (hopenerLeafP q0 x hq0 l hlx)
  have hpinsGetD : ∀ q, q < cnPK →
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).getD q default
        = Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default) := by
    intro q hq
    rw [List.getD, List.getElem?_map, List.getD]
    rcases hp : pins[q]? with _ | p
    · rw [List.getElem?_eq_none_iff, hpinsLen] at hp; omega
    · rfl
  have hpinMem : ∀ q, q < cnPK →
      Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default)
        ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)) := by
    intro q hq
    have hp : pins[q]? = some (pins.getD q default) := by
      rw [List.getD]
      rcases hp : pins[q]? with _ | p
      · rw [List.getElem?_eq_none_iff, hpinsLen] at hp; omega
      · rfl
    exact List.mem_map.mpr ⟨_, List.mem_of_getElem? hp, rfl⟩
  have hpinRead : ∀ q, q < cnPK →
      ∃ w, denoteMeta mp.base2.acval envSelf ψ (rP + cnFK)
        (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default))
        = some w := by
    intro q hq
    obtain ⟨ty, hi, -⟩ := typedListOk_getD hTypedP q
      (by rw [List.length_map, hpinsLen]; exact hq)
    rw [hpinsGetD q hq] at hi
    exact hJ.accepted ψ hi
      (hpinSyn _ (hpinMem q hq)).1 (hpinSyn _ (hpinMem q hq)).2.1
      (hpinSyn _ (hpinMem q hq)).2.2
  -- ===== the pin conjunct's row =====
  have hrow := nestedPinRow (m := mp.base2) (φ := ψ)
    (hdeq ψ) (hinf ψ) (hreadsP ψ) (hframe ψ) hfvsPlen hshapeP hwsFvsP
    hleafClosedP hlbFvsP htowerP hokTV hdomsP0 hpinsLen hpinsWf
    hctyPw hctyPb hTVjP hokTVjP hcinstP hTypedP hpinRead
  -- ===== fire the nested bottom =====
  obtain ⟨Ra, hRaden, hokRa, hRalaw⟩ := indBottomNested_vm (V := V) mp
    hdeq hinf hreadsP hframe hroT heqfS htyw htyb htyOk hfRnE hRmlps hfcS
    hfCmE hCmlps hCw hCb hClp hrPmI hlvlsLen hpinsLen hpinsWf
    hrhsAw hrhsAb hrhsKey hSw hSb hthm hopen hheadEq hargs3
    (eq_of_beq hlhead0) hlarity0 (eq_of_beq hlpre0) hmaj0 hCstrips'
    hcinst hclen hrinst hopenP hcinstP hopenXP hwalk
    hTypedP hdeIdx hdePre hdeFld hdeRhs hsideL hsideR
    φ us huslen
  refine ⟨Ra, by rw [hr'rhs]; exact hRaden, hokRa, ?_, ?_⟩
  · intro lvls' pins' hn i hi
    obtain ⟨rfl, rfl⟩ : lvls' = lvls ∧ pins' = pins := by
      rw [hfireN] at hn
      injection hn with a b
      exact ⟨a.symm, b.symm⟩
    obtain ⟨vpa, hvp, hgr⟩ := hrow i (by rw [← hr'cp]; exact hi)
    refine ⟨vpa, ?_, ?_⟩
    · rw [openRev_instantiateLevelParams, denotePInstLevels, ← hψ]
      exact hvp
    · intro ρ zs TVa restR hzslen hzsOk hTVa hfit
      obtain rfl : TVa = TV := by
        rw [denotePInstLevels, ← hψ, hTV0] at hTVa
        exact (Option.some.inj hTVa).symm
      exact hgr ρ zs restR hzslen hzsOk hfit
  intro cvj cnP cnF hfcv usj ρ xs ys TVa TVja restR restC hlenX hlenY
    husjlen hlev hplain hnested hidx hTVa hTVja hfitR hfitC
  obtain ⟨rfl, rfl, rfl⟩ := hctorId hfcv
  rw [hr'cp, hr'nf] at hlenY
  rw [hr'cp] at hidx hnested ⊢
  rw [hr'ctor] at hfitR ⊢
  refine hRalaw usj ρ xs ys TVa TVja restR restC hlenX hlenY husjlen
    ?_ ?_ hidx hTVa hTVja hfitR hfitC
  · dsimp only [ConstantInfo.toConstantVal]
    rw [hlev, recFireComparands_nested hfireN]
  · exact hnested lvls pins hfireN

theorem iotaRuleNested_vm {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {J : Judgements .anon} {env₂ envSelf : Env .anon}
    (mp : EnvModelM V μ envSelf)
    (hJ : JudgeSound J mp.base2)
    {blockNames : List KKey} {f : Key .anon → Key .anon}
    (_hf : f = fun n => if blockNames.contains n then auxKey n .model else n)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (_hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hup : ∀ (n : Key .anon) (ci : ConstantInfo .anon), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal .anon} {mI rP j : Nat} {r r' : RecRule .anon}
    (_hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleVmRunJ J env₂ envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    {lvls : List Level} {pins : List KExpr}
    (hfireN : RecRule.fire r' = .nested lvls pins) (φ : LevelParam → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' :=
  iotaRuleNested_vmF mp hJ hroT hup hself heqfind (hkit.toNVm hfireN) hfireN φ

/-- Per-rule soundness bridge over `IotaRuleVmRunJ` (`iotaRule` adapted). -/
theorem iotaRule_vm {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {J : Judgements .anon} {env₂ envSelf : Env .anon}
    (mp : EnvModelM V μ envSelf)
    (hJ : JudgeSound J mp.base2)
    {blockNames : List KKey} {f : Key .anon → Key .anon}
    (hf : f = fun n =>
      if blockNames.contains n then auxKey n .model else n)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hup : ∀ (n : Key .anon) (ci : ConstantInfo .anon), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal .anon} {mI rP j : Nat} {r r' : RecRule .anon}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleVmRunJ J env₂ envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    (hfire : RecRule.fire r' ≠ .inert) (φ : LevelParam → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' := by
  cases hfm : RecRule.fire r' with
  | inert => exact absurd hfm hfire
  | plain =>
    exact iotaRulePlain_vm mp hJ hf hroT hIS hup hbnA hself heqfind hkit hfm φ
  | nested lvls pins =>
    exact iotaRuleNested_vm mp hJ hf hroT hIS hup hbnA hself heqfind hkit hfm φ

/-- Rule-list soundness fold over `IotaRulesVmRunJ` (`iotaRules` adapted). -/
theorem iotaRules_vm {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {J : Judgements .anon} {env₂ envSelf : Env .anon}
    (mp : EnvModelM V μ envSelf)
    (hJ : JudgeSound J mp.base2)
    {blockNames : List KKey} {f : Key .anon → Key .anon}
    (hf : f = fun n =>
      if blockNames.contains n then auxKey n .model else n)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hup : FoldUpS env₂ envSelf)
    {cvA : ConstantVal .anon} {mI rP : Nat}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA) :
    ∀ (j : Nat) (rules rules' : List (RecRule .anon)),
      IotaRulesVmRunJ J env₂ envSelf f cvA.name
        cvA.levelParams cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RecRule.fire rl ≠ .inert → ∀ φ : LevelParam → Nat,
        RecRuleLaw mp.base2 φ cvA.name cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' h rl hrl
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · intro hfire φ
      rw [heqrl] at hfire ⊢
      exact iotaRule_vm mp hJ hf hroT hIS hup hbnA hself heqfind hkit hfire φ
    · exact ih (j + 1) rest' hrec rl hrl'

set_option maxHeartbeats 1600000 in
/-- Provisioning and install fold over `IndRecsFoldVmRunJ` (`indRecsFold` adapted). -/
theorem indRecsFold_vm {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {J : Judgements .anon} {blockNames : List KKey} {envSelf envBase : Env .anon}
    (mp : EnvModelM V μ envSelf) (hJ : JudgeSound J mp.base2)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hroT : RenameOk mp.base2.acval envSelf (fun n =>
      if blockNames.contains n then auxKey n .model else n))
    (hupB : FoldUpS envBase envSelf)
    (heqfB : envBase.find? eqName = some eqA) :
    ∀ (recs : List (ConstantInfo .anon)) {envP envF env₃ : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      (∀ (n : Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAt mp.base2 cv mI rP rules) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsRunJ J blockNames envP recs envSelf checked →
      IndRecsFoldVmRunJ J blockNames envBase envSelf envF checked env₃ →
      ∀ (n : Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAt mp.base2 cv mI rP rules := by
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ checked hentF hbn hprov hfold
    obtain ⟨rfl, rfl⟩ := hprov
    subst hfold
    exact hentF
  | cons ci₀ rest ih =>
    intro envP envF env₃ checked hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', hcv, hcvAdef, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvAdef]
    have hselfA : envSelf.find? cvA.name = some (.recInfo cvA mI rP []) :=
      provisionRecsRunS_mono rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    have hfacts : RecLawsAt mp.base2 cvA mI rP rules' :=
      fun rl hrl hfire φ =>
        iotaRules_vm mp hJ rfl hroT hIS hupB hbnA hselfA heqfB 0 rules rules' hiot rl hrl hfire φ
    refine ih ?_ (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci)) hprov' hfold'
    intro n cv mI₀ rP₀ rules₀ hfx
    rw [Env.find?_cons] at hfx
    split at hfx
    · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj hfx)
      exact Or.inr hfacts
    · exact hentF n cv mI₀ rP₀ rules₀ hfx

set_option maxHeartbeats 1600000 in
/-- Recursor-group phase over `IndRecsVmRunJ` (`indRecs` adapted, reusing syntactic swap facts
via `.toTrivDefEq`). -/
theorem indRecs_vm {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    (hetaP : (MemberEtaLaw (md := .anon)) V) (hunitP : (MemberUnitLaw (md := .anon)) V)
    {J : Judgements .anon} (hfr : ∀ e : Env .anon, JudgeFrames J e)
    (hJ : ∀ {e : Env .anon} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {blockNames : List KKey} {env₂ env₃ : Env .anon}
    {recs : List (ConstantInfo .anon)}
    (mp : EnvModelM V μ env₂)
    (hI : BlockInstalledTT blockNames env₂ mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env₂ mp.base2.acval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hEC : Ix.Kernel.EtaFamiliesClosedO blockNames env₂)
    (hBP : Ix.Kernel.BlockEtaPinned μ blockNames env₂)
    (h : IndRecsVmRunJ J blockNames env₂ recs env₃) :
    ∃ mp₃ : EnvModelM V μ env₃,
      BlockInstalledTT blockNames env₃ mp₃.base2.cvalE ∧
      BlockAcvalInstalled blockNames env₃ mp₃.base2.acval ∧
      ModelExt mp mp₃ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, heqf, envSelf, checked, hprov, hfold⟩
  · exact ⟨mp, hI, hIA, .refl⟩
  obtain ⟨mS, hIS, hIAS, hECS, hBPS, hextS⟩ :=
    provisionRecsPM hetaP hunitP hfr recs mp hbn hprov hI hIA hEC hBP
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, rfl⟩
    · rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hfound; exact nomatch hfound
      · rw [provisionRecsRunS_mono recs hprov n ci hf]; rfl
    · exact provisionRecsRunS_stored recs hprov ci hci
  have hroP := blockRenameOk hIS hIAS hnames
  have hprovT := ProvisionRecsRunJ.toTrivDefEq hprov
  have hdenS : ∀ e : KExpr, e.hasFvar = false →
      e.looseBVarsBounded 0 = true →
      (∃ t', (trivDefEqOf J).infer envSelf 0 e t') →
      ∀ φ : LevelParam → Nat,
        ∃ Rv, denoteClosed mS.base2.cvalE envSelf φ e = some Rv := by
    intro e hef heb hrun φ
    obtain ⟨t', hrun'⟩ := hrun
    obtain ⟨ea, hea⟩ :=
      (hJ mS).accepted φ hrun'
        (Expr.WScoped.of_not_hasFvar hef) heb
        (fun l hl => absurd hl (fun h' => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hef] at h'
          exact nomatch h'))
    exact ⟨ea.erase, denoteMeta_erase mS.base2.acval_erase 0 e hea⟩
  obtain ⟨hswR, hnresR, hentR, hentFR⟩ :=
    indRecsFoldFactsRun (RuleFacts envSelf mS.base2.cvalE)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesFactsRun
          (fun n ci hf =>
            Or.inl (provisionRecsRunS_mono recs hprovT n ci hf))
          hdenS (JudgeFrames.toTrivDefEq (hfr envSelf)).annot_syntax 0 rules rules' hiot)
      recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf =>
        Or.inl (provisionRecsRunS_mono recs hprovT n ci hf))
      (provisionRecsRunS_mono recs hprovT) heqf
      (fun c hc => Or.inl (provisionRecsRunS_mem recs hprovT c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsRunS_mono recs hprovT n _ hf))
      hbn hprovT hfold.toTrivDefEq
  have hcg : Ix.Kernel.SwapCongr envSelf env₃ := SwapShList.congr hswR
  have hentF := indRecsFold_vm (V := V) mS (hJ mS) hIS hroP
    (fun n ci hf => Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
    heqf recs
    (fun n cv mI rP rules hf =>
      Or.inl (provisionRecsRunS_mono recs hprov n _ hf))
    hbn hprov hfold
  have hrecP : ∀ m₃ : EnvModel V env₃, m₃.acval = mS.base2.acval →
      ∀ φ : LevelParam → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases hentF n cv mI rP rules hf with hfS | hlaws
    · exact RecRuleLaw.swapP hcg hac
        (mS.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · rw [← Env.find?_name hf]
      exact RecRuleLaw.swapP hcg hac (hlaws rl hrl hfire φ)
  obtain ⟨hwf₃, hctors₃, hbp₃, hproj₃⟩ :=
    swapEnvFacts mS.base2.wf mS.base2.rec_ctors mS.base2.basis_pinned
      mS.base2.proj_ok hswR hnresR hentR hentFR
  obtain ⟨mp₃, hacc, hcval₃⟩ :=
    EnvModelM.swapP mS hswR hwf₃ hctors₃ hbp₃ hproj₃ hrecP
  have hext₃ : ModelExt mp mp₃ :=
    ModelExt.swap hextS (fun n hn => by rw [← hcg.isSomeEq n]; exact hn)
      (fun cv v hmem => by
        rcases hentR _ hmem with h | ⟨_, _, _, _, heq, -⟩
        · exact h
        · exact nomatch heq)
      (fun ψ d e => denoteMeta_swap hcg ψ d e) hacc
  refine ⟨mp₃, ?_, by rw [hacc]; exact blockAcvalInstalled_swap hcg hIAS, hext₃⟩
  rw [hcval₃]
  intro n hn ci₃ hf₃
  rcases swapSh_find?_corr hswR n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)),
      hlps, hren, hv⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn _ h₀
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)),
      hlps, hren, hv⟩

set_option maxHeartbeats 1600000 in
/-- Modeled block extends the model over `DeclIndVmRunJ` (`declIndJ` adapted). -/
theorem declIndJ_vm {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {J : Judgements .anon}
    (hfr : ∀ e : Env .anon, JudgeFrames J e)
    (hJ : ∀ {e : Env .anon} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env .anon} {block : List (ConstantInfo .anon)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndVmRunJ J env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hbnNon : ∀ ci ∈ block.filter isNonRecInfo,
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hbnRec : ∀ ci ∈ block.filter isRecInfo,
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hEC0 : Ix.Kernel.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  have hnostore : ∀ n, (block.map (·.name)).contains n = true →
      ∀ ci : ConstantInfo .anon, env.find? n = some ci → False := by
    intro n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [indMembersRun_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := indMembersRun_mono _ hmem _ _ hf
      rw [indRecsRun_fresh hrecs.toTrivDefEq ci₀ hci₀] at hup
      exact nomatch hup
  have hI0 : BlockInstalledTT (block.map (·.name)) env mp.base2.cvalE :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hIA0 : BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hBP0 : Ix.Kernel.BlockEtaPinned μ (block.map (·.name)) env :=
    fun n cvS capsS hnb hf _ => absurd (hnostore n hnb _ hf) (fun h => h)
  have hall : ∀ n, (block.map (·.name)).contains n = true →
      (envM.find? n).isSome = true ∨
      ∃ ci ∈ block.filter isRecInfo, ci.name = n := by
    intro n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (indMembersRun_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁, hext₁⟩ :=
    indMembersPM memberEtaLaw memberUnitLaw hfr _ mp hbnNon
      (fun cv caps₂ _ => ⟨etaPins_empty,
        ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩)
      hmem hI0 hIA0 hEC0 hBP0
  obtain ⟨mp₂, -, -, hext₂⟩ :=
    indRecs_vm memberEtaLaw memberUnitLaw hfr hJ mp₁ hI₁ hIA₁ hbnRec hall hEC₁ hBP₁ hrecs
  exact ⟨mp₂, hext₁.trans hext₂⟩

/-- Modeled block preserves `EtaFamiliesClosed` and extends `EnvModelM` over `DeclIndVmRunJ`. -/
theorem declIndStepJ_vm {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {J : Judgements .anon}
    (hfr : ∀ e : Env .anon, JudgeFrames J e)
    (hJ : ∀ {e : Env .anon} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env .anon} {block : List (ConstantInfo .anon)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndVmRunJ J env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  ⟨declIndEtaClosedRunJ hE h.toTrivDefEq, declIndJ_vm hfr hJ mp hE h⟩

/-- **Full `DeclInv` preservation** across a modeled inductive block checked at `DeclIndVmRunJ posRulesJ`. -/
theorem DeclInv.step_modeled_vm {V : Type w} [Ix.Kernel.SetTheory V]
    {env env₂ : Env .anon} {block : List (ConstantInfo .anon)}
    (hrun : DeclIndVmRunJ posRulesJ env block env₂)
    (h : DeclInv V env) : DeclInv V env₂ := by
  obtain ⟨⟨⟨mp, hT⟩, hE⟩, hS⟩ := h
  obtain ⟨hE₂, mp₂, hext⟩ :=
    declIndStepJ_vm judgeFrames_posRulesJ (fun m => judgeSound_posRulesJ_of m) mp hE hrun
  exact ⟨⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩, hS.declInd_vm hrun⟩

/-- Lift a `DeclStoreInv`-conditioned `DeclIndVmRunJ posRulesJ` witness to the full `Decls` step
obligation (`∃ env₂, InstallStep env (.indDecl block nP) env₂ ∧ ∀ V, DeclInv V env → DeclInv V env₂`). -/
theorem decls_step_of_modeled_vm {calls : List (Call F)} {env : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hnodup : ((IxVM.Consistency.installs (.indDecl block nP)).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci₀.name = none)
    (hstep : DeclStoreInv env → ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      DeclIndVmRunJ posRulesJ env block env₂) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type w) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨env₂, hinst, hrun⟩ := hstep hS
    exact ⟨env₂, hinst, fun _ _ hInv => hInv.step_modeled_vm hrun⟩
  · obtain ⟨env₂, hinst⟩ := installStep_of_checked_fresh hchk hnodup hfresh
    exact ⟨env₂, hinst, fun _ _ hInv => absurd hInv.store hS⟩

/-! ## `f`-parametric soundness bridge (`declIndJ_vmF`) -/

/-- Per-rule soundness bridge over `IotaRuleNVmRunJ` at arbitrary `RenameOk` renaming `f`. -/
theorem iotaRule_vmF {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {J : Judgements .anon} {env₂ envSelf : Env .anon}
    (mp : EnvModelM V μ envSelf)
    (hJ : JudgeSound J mp.base2)
    {f : Key .anon → Key .anon}
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hup : ∀ (n : Key .anon) (ci : ConstantInfo .anon), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal .anon} {mI rP j : Nat} {r r' : RecRule .anon}
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleNVmRunJ J env₂ envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    (φ : LevelParam → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' := by
  have ⟨_, _, _, _, lvls₀, pins₀, _, _, _, _, _, _, _, _, _, hr'eq, _⟩ := hkit
  have hfm : RecRule.fire r' = .nested lvls₀ pins₀ := by rw [hr'eq]; rfl
  exact iotaRuleNested_vmF mp hJ hroT hup hself heqfind hkit hfm φ

/-- Rule-list soundness fold over `IotaRulesNVmRunJ` at arbitrary `RenameOk` renaming `f`. -/
theorem iotaRules_vmF {V : Type w} [Ix.Kernel.SetTheory V]
    {μ : CheckMode} {J : Judgements .anon} {env₂ envSelf : Env .anon}
    (mp : EnvModelM V μ envSelf)
    (hJ : JudgeSound J mp.base2)
    {f : Key .anon → Key .anon}
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hup : FoldUpS env₂ envSelf)
    {cvA : ConstantVal .anon} {mI rP : Nat}
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP [])) :
    ∀ (j : Nat) (rules rules' : List (RecRule .anon)),
      (rules ≠ [] → env₂.find? eqName = some eqA) →
      IotaRulesNVmRunJ J env₂ envSelf f cvA.name
        cvA.levelParams cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RecRule.fire rl ≠ .inert → ∀ φ : LevelParam → Nat,
        RecRuleLaw mp.base2 φ cvA.name cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' _ h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' heqfind h rl hrl
    have heq₀ : env₂.find? eqName = some eqA := heqfind (fun hnil => nomatch hnil)
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · intro _ φ
      rw [heqrl]
      exact iotaRule_vmF mp hJ hroT hup hself heq₀ hkit φ
    · exact ih (j + 1) rest' (fun _ => heq₀) hrec rl hrl'

set_option maxHeartbeats 1600000 in
/-- Provisioning and install fold over `IndRecsFoldNVmRunJF`. -/
theorem indRecsFold_vmF {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {J : Judgements .anon} {blockNames : List KKey} {f : KKey → KKey} {envSelf envBase : Env .anon}
    (mp : EnvModelM V μ envSelf) (hJ : JudgeSound J mp.base2)
    (hroT : RenameOk mp.base2.acval envSelf f)
    (hupB : FoldUpS envBase envSelf) :
    ∀ (recs : List (ConstantInfo .anon)) {envP envF env₃ : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ((∃ c ∈ checked, c.2.2.2 ≠ []) → envBase.find? eqName = some eqA) →
      (∀ (n : Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAt mp.base2 cv mI rP rules) →
      ProvisionRecsRunJ J blockNames envP recs envSelf checked →
      IndRecsFoldNVmRunJF J f envBase envSelf envF checked env₃ →
      ∀ (n : Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAt mp.base2 cv mI rP rules := by
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ checked _ hentF hprov hfold
    obtain ⟨rfl, rfl⟩ := hprov
    subst hfold
    exact hentF
  | cons ci₀ rest ih =>
    intro envP envF env₃ checked heqfB hentF hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', _, _, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    have hselfA : envSelf.find? cvA.name = some (.recInfo cvA mI rP []) :=
      provisionRecsRunS_mono rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hfacts : RecLawsAt mp.base2 cvA mI rP rules' :=
      fun rl hrl hfire φ =>
        iotaRules_vmF mp hJ hroT hupB hselfA 0 rules rules'
          (fun hne => heqfB ⟨(cvA, mI, rP, rules), List.mem_cons_self, hne⟩)
          hiot rl hrl hfire φ
    refine ih (fun ⟨c, hc, hne⟩ => heqfB ⟨c, List.mem_cons_of_mem _ hc, hne⟩) ?_ hprov' hfold'
    intro n cv mI₀ rP₀ rules₀ hfx
    rw [Env.find?_cons] at hfx
    split at hfx
    · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj hfx)
      exact Or.inr hfacts
    · exact hentF n cv mI₀ rP₀ rules₀ hfx

set_option maxHeartbeats 1600000 in
/-- Recursor-group phase over `IndRecsNVmRunJF`. -/
theorem indRecs_vmF {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    (hetaP : (MemberEtaLaw (md := .anon)) V) (hunitP : (MemberUnitLaw (md := .anon)) V)
    {J : Judgements .anon} (hfr : ∀ e : Env .anon, JudgeFrames J e)
    (hJ : ∀ {e : Env .anon} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {blockNames : List KKey} {f : KKey → KKey} {env₀ env₂ env₃ : Env .anon}
    {recs : List (ConstantInfo .anon)}
    {mp₀ : EnvModelM V μ env₀} (mp : EnvModelM V μ env₂)
    (hAlias : ModelAliasOk blockNames env₀ mp₀.base2.acval f)
    (hext₀ : ModelExt mp₀ mp)
    (hmono₀ : ∀ n ci, env₀.find? n = some ci → env₂.find? n = some ci)
    (hI : BlockInstalledTT blockNames env₂ mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env₂ mp.base2.acval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hEC : Ix.Kernel.EtaFamiliesClosedO blockNames env₂)
    (hBP : Ix.Kernel.BlockEtaPinned μ blockNames env₂)
    (h : IndRecsNVmRunJF J blockNames f env₂ recs env₃) :
    ∃ mp₃ : EnvModelM V μ env₃,
      BlockInstalledTT blockNames env₃ mp₃.base2.cvalE ∧
      BlockAcvalInstalled blockNames env₃ mp₃.base2.acval ∧
      ModelExt mp mp₃ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, envSelf, checked, heqf, hprov, hfold⟩
  · exact ⟨mp, hI, hIA, .refl⟩
  obtain ⟨mS, hIS, hIAS, hECS, hBPS, hextS⟩ :=
    provisionRecsPM hetaP hunitP hfr recs mp hbn hprov hI hIA hEC hBP
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, rfl⟩
    · rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hfound; exact nomatch hfound
      · rw [provisionRecsRunS_mono recs hprov n ci hf]; rfl
    · exact provisionRecsRunS_stored recs hprov ci hci
  have hroP := modelRenameOk_of_alias hAlias (hext₀.trans hextS)
    (fun n ci hf => provisionRecsRunS_mono recs hprov n ci (hmono₀ n ci hf))
    hIS hIAS hnames
  have hdenS : ∀ e : KExpr, e.hasFvar = false →
      e.looseBVarsBounded 0 = true →
      (∃ t', J.infer envSelf 0 e t') →
      ∀ φ : LevelParam → Nat,
        ∃ Rv, denoteClosed mS.base2.cvalE envSelf φ e = some Rv := by
    intro e hef heb hrun φ
    obtain ⟨t', hrun'⟩ := hrun
    obtain ⟨ea, hea⟩ :=
      (hJ mS).accepted φ hrun'
        (Expr.WScoped.of_not_hasFvar hef) heb
        (fun l hl => absurd hl (fun h' => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hef] at h'
          exact nomatch h'))
    exact ⟨ea.erase, denoteMeta_erase mS.base2.acval_erase 0 e hea⟩
  obtain ⟨hswR, hnresR, hentR, hentFR⟩ :=
    indRecsFoldNVmFactsRunF (RuleFacts envSelf mS.base2.cvalE)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesNVmFactsRun
          (fun n ci hf =>
            Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
          hdenS (hfr envSelf).annot_syntax 0 rules rules' hiot)
      recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf =>
        Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
      (provisionRecsRunS_mono recs hprov)
      (fun c hc => Or.inl (provisionRecsRunS_mem recs hprov c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsRunS_mono recs hprov n _ hf))
      hbn hprov hfold
  have hcg : Ix.Kernel.SwapCongr envSelf env₃ := SwapShList.congr hswR
  have hentF := indRecsFold_vmF (V := V) mS (hJ mS) hroP
    (fun n ci hf => Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
    recs heqf
    (fun n cv mI rP rules hf =>
      Or.inl (provisionRecsRunS_mono recs hprov n _ hf))
    hprov hfold
  have hrecP : ∀ m₃ : EnvModel V env₃, m₃.acval = mS.base2.acval →
      ∀ φ : LevelParam → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases hentF n cv mI rP rules hf with hfS | hlaws
    · exact RecRuleLaw.swapP hcg hac
        (mS.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · rw [← Env.find?_name hf]
      exact RecRuleLaw.swapP hcg hac (hlaws rl hrl hfire φ)
  obtain ⟨hwf₃, hctors₃, hbp₃, hproj₃⟩ :=
    swapEnvFacts mS.base2.wf mS.base2.rec_ctors mS.base2.basis_pinned
      mS.base2.proj_ok hswR hnresR hentR hentFR
  obtain ⟨mp₃, hacc, hcval₃⟩ :=
    EnvModelM.swapP mS hswR hwf₃ hctors₃ hbp₃ hproj₃ hrecP
  have hext₃ : ModelExt mp mp₃ :=
    ModelExt.swap hextS (fun n hn => by rw [← hcg.isSomeEq n]; exact hn)
      (fun cv v hmem => by
        rcases hentR _ hmem with h | ⟨_, _, _, _, heq, -⟩
        · exact h
        · exact nomatch heq)
      (fun ψ d e => denoteMeta_swap hcg ψ d e) hacc
  refine ⟨mp₃, ?_, by rw [hacc]; exact blockAcvalInstalled_swap hcg hIAS, hext₃⟩
  rw [hcval₃]
  intro n hn ci₃ hf₃
  rcases swapSh_find?_corr hswR n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)),
      hlps, hren, hv⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn _ h₀
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)),
      hlps, hren, hv⟩

set_option maxHeartbeats 1600000 in
/-- Modeled block extends `EnvModelM` over `DeclIndNVmRunJF` with advice renaming `f`. -/
theorem declIndJ_vmF {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {J : Judgements .anon}
    (hfr : ∀ e : Env .anon, JudgeFrames J e)
    (hJ : ∀ {e : Env .anon} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {f : KKey → KKey} {env env₂ : Env .anon} {block : List (ConstantInfo .anon)}
    (mp : EnvModelM V μ env)
    (hAlias : ModelAliasOk (block.map (·.name)) env mp.base2.acval f)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndNVmRunJF J f env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hbnNon : ∀ ci ∈ block.filter isNonRecInfo,
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hbnRec : ∀ ci ∈ block.filter isRecInfo,
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hEC0 : Ix.Kernel.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  have hrecs_fresh : ∀ ci₀ ∈ block.filter isRecInfo, envM.find? ci₀.name = none := by
    rcases hrecs with ⟨href, _⟩ | ⟨_, _, _, _, hprov, _⟩
    · intro ci₀ hci₀; rw [href] at hci₀; exact nomatch hci₀
    · exact provisionRecsRunS_fresh _ hprov
  have hnostore : ∀ n, (block.map (·.name)).contains n = true →
      ∀ ci : ConstantInfo .anon, env.find? n = some ci → False := by
    intro n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [indMembersRun_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := indMembersRun_mono _ hmem _ _ hf
      rw [hrecs_fresh ci₀ hci₀] at hup
      exact nomatch hup
  have hI0 : BlockInstalledTT (block.map (·.name)) env mp.base2.cvalE :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hIA0 : BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hBP0 : Ix.Kernel.BlockEtaPinned μ (block.map (·.name)) env :=
    fun n cvS capsS hnb hf _ => absurd (hnostore n hnb _ hf) (fun h => h)
  have hall : ∀ n, (block.map (·.name)).contains n = true →
      (envM.find? n).isSome = true ∨
      ∃ ci ∈ block.filter isRecInfo, ci.name = n := by
    intro n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (indMembersRun_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁, hext₁⟩ :=
    indMembersPM memberEtaLaw memberUnitLaw hfr _ mp hbnNon
      (fun cv caps₂ _ => ⟨etaPins_empty,
        ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩)
      hmem hI0 hIA0 hEC0 hBP0
  obtain ⟨mp₂, -, -, hext₂⟩ :=
    indRecs_vmF memberEtaLaw memberUnitLaw hfr hJ mp₁ hAlias hext₁
      (indMembersRun_mono _ hmem) hI₁ hIA₁ hbnRec hall hEC₁ hBP₁ hrecs
  exact ⟨mp₂, hext₁.trans hext₂⟩

end IxVM.Refinement.Decl
