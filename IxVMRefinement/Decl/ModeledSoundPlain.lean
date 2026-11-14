import IxVMRefinement.Decl.ModeledSoundKit
import IxC.Kernel.Model.IndPinGrade
import IxC.Kernel.Model.IndBottomProj
import IxC.Kernel.Model.JudgeSound
import IxC.Kernel.Model.Tiers
import IxC.Kernel.Model.Annot.Bit
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Verify.Denote.OpenRevDenote
import IxC.Kernel.Semantics.IndBlockRun

/-!
# Soundness of Canonical (`.plain`) Modeled-Inductive `iota` Rules for the VM

Adapts `Ix.Kernel.Model.indBottomPlain` and `Ix.Kernel.Model.iotaRulePlain` from
`instLamsAt (fvsP ++ xFvsP) rhsA` to `LamTeleWalkJ` (`defeq_lam_tele`), using
`annotOpeners_lamWalk` and `annotTransport_lamWalk` from `ModeledSoundKit`.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule
  LevelParam openPisAtFvars eqName eqA auxKey recRuleBits isEqHead)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe w

set_option maxHeartbeats 25600000 in
/-- Plain modeled-iota bottom over `LamTeleWalkJ` (`indBottomPlain` adapted to VM `defeq_lam_tele`). -/
theorem indBottomPlain_vm {V : Type w} [Ix.Kernel.SetTheory V]
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
    (hrPmI : rP ≤ mI) (hplainLe : cnP ≤ rP)
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
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (hCstrips : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    {cdoms : List KExpr} {cres : KExpr}
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    {rdoms : List KExpr} {rrest : KExpr}
    (hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
      = some (rdoms, rrest))
    {fvsP : List KExpr} {restP : KExpr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List KExpr} {crestP : KExpr}
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type
      = some (cdomsP, crestP))
    {xFvsP : List KExpr} {ldoms : KExpr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (hwalk : LamTeleWalkJ J env rP cnF tyA cvj.type (fun pre => pre.take cnP) rhsA)
    (hdeIdx : DefEqListJ J env (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hdePre : DefEqListJ J env (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListJ J env (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hdePars : DefEqListJ J env (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
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
                (cvj.levelParams.map fun p =>
                  Level.subst lps us (.param p)) →
          (∀ i, i < cnP → i < mI →
            interp V ρ (ys.getD i default)
              = interp V ρ (xs.getD i default)) →
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
  -- ===== the statement, opened =====
  obtain ⟨Tst, hTstden, hTstFacts⟩ := hthm (Level.substFn φ lps us)
  obtain ⟨Γs, Rbody, htowerS, hRbodyDenA, hdomsS0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (rP + cnF) hopen hTstden
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hfvslen : fvs.length = rP + cnF := openPisAtFvars_length _ hopen
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
  -- ===== the public (recursor) tower =====
  have hTV0 : denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 tyA
      = some TVa := by
    rw [← denotePInstLevels]
    exact hTVa
  obtain ⟨ΓP, RP, htowerP, hRPden, hdomsP0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) rP hopenP hTV0
  have hfvsPlen : fvsP.length = rP := openPisAtFvars_length _ hopenP
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
  -- ===== the constructor's assignment and tower =====
  have hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p
        = Level.substFn φ lps us p := by
    intro p hp
    have hmm : (cvj.levelParams.map fun q => Level.subst lps us (.param q))
        = (cvj.levelParams.map Level.param).map (Level.subst lps us) := by
      rw [List.map_map]
      rfl
    calc Level.substFn φ cvj.levelParams usj p
        = Level.substFn φ cvj.levelParams
            ((cvj.levelParams.map Level.param).map (Level.subst lps us))
            p := by rw [hlev, hmm]
      _ = Level.substFn (Level.substFn φ lps us) cvj.levelParams
            (cvj.levelParams.map Level.param) p :=
          Level.substFn_map_subst (by rw [List.length_map]) hp
      _ = Level.substFn φ lps us p := Level.substFn_map_param
  have hTVj0 : denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0
      cvj.type = some TVja := by
    have h := hTVja
    rw [denotePInstLevels,
      denoteMeta_params_ext mp.base2 hagree 0 cvj.type hClp] at h
    exact h
  have hTVjcl : ∀ k : Nat, TVja.liftN 1 k = TVja := fun k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hCw hCb hTVj0 1 k
  have hCwR : (cvj.type.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hCw
  have hCbR : (cvj.type.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact hCb
  have hTVjK : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (cvj.type.renameConsts f) = some TVja := by
    refine denoteMeta_depth_of_closed mp.base2.acval_closed hCwR hTVjcl
      ?_ (rP + cnF)
    rw [denoteMeta_renameConsts hroT]
    exact hTVj0
  have hokTVj : ∀ σ : Nat → V, WellDenotedV V σ TVja :=
    mp.type_wellDenotedV _ (Ix.Kernel.Semantics.Env.find?_mem hctorE)
      (Level.substFn φ lps us) TVja hTVj0
  obtain ⟨⟨bsC, cbody⟩, hstripC⟩ := Option.isSome_iff_exists.mp hCstrips
  obtain ⟨Γj, Rj, htowerJ, hΓjlen0, hRjdenA, hdomsJ⟩ :=
    stripPis_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (cnP + cnF) hstripC hTVj0
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  -- ===== `Rj`'s decomposition and its arity =====
  have hcbApp : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
      cbody
      = Expr.mkAppN
          (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
            cbody.getAppFn)
          (cbody.getAppArgs.map
            (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
              ·)) := by
    have hcb : cbody = Expr.mkAppN cbody.getAppFn cbody.getAppArgs :=
      (Expr.mkAppN_getApp cbody).symm
    have h1 : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
        cbody
        = Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
          (Expr.mkAppN cbody.getAppFn cbody.getAppArgs) := by
      conv => lhs; rw [hcb]
    rw [h1, Expr.instSeq_mkAppN]
  have hRjdenA' := hRjdenA
  rw [Nat.zero_add, hcbApp] at hRjdenA'
  obtain ⟨vHC, vArgsC, hvHCden, hcspJ, hRjdec⟩ :=
    denoteMeta_mkAppN_inv hRjdenA'
  have hcbodyArity : cbody.getAppArgs.length = cnP + (mI - rP) := by
    have hstripR := stripPis_renameConsts (f := f) (cnP + cnF) hstripC
    have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
      rw [List.length_append, List.length_take, List.length_drop,
        hfvslen]
      omega
    have h1 := instPisAt_fvar_residual_arity
      (fvs.take cnP ++ fvs.drop rP) hcinst
      (fun x hx => by
        rcases List.mem_append.mp hx with hx' | hx'
        · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
          have hq' : fvs[q]? = some x := by
            have hql : q < cnP := by
              have := (List.getElem?_eq_some_iff.mp hq).1
              rw [List.length_take] at this
              omega
            rw [← List.getElem?_take_of_lt hql]
            exact hq
          obtain ⟨ty, rfl⟩ := hshapeS q x hq'
          exact ⟨q, ty, rfl⟩
        · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
          rw [List.getElem?_drop] at hq
          obtain ⟨ty, rfl⟩ := hshapeS (rP + q) x hq
          exact ⟨rP + q, ty, rfl⟩)
      (bs := bsC.map (fun b => (b.1.renameConsts f, b.2)))
      (body := cbody.renameConsts f)
      (by rw [hsplen]; exact hstripR)
    rw [getAppArgs_length_renameConsts] at h1
    rw [← h1, hclen]
  have hArgsClen : vArgsC.length = cnP + (mI - rP) := by
    rw [← hcspJ.length, List.length_map, hcbodyArity]
  -- ===== the fitting prefix and parameter equalities =====
  have htakexs : (xs ++ [AnnotTerm.mkAppN
      (mp.base2.acval ctor (Level.substFn φ cvj.levelParams usj))
      ys]).take rP = xs.take rP := by
    rw [List.take_append_of_le_length (by rw [hlenX]; omega)]
  obtain ⟨restRpre, hfitRpre⟩ := hfitR.take rP
  rw [htakexs] at hfitRpre
  have hpar : ∀ i, i < cnP →
      interp V ρ (ys.getD i default)
        = interp V ρ (xs.getD i default) :=
    fun i hi => hparP i hi (by omega)
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
  -- ===== the plain fire's spine, and the fired chain =====
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]; omega
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hfvslen]
    omega
  have hspIdx : ∀ (q : Nat) (x : KExpr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ ty, x = Expr.fvar
          (if q < cnP then q else rP + (q - cnP)) ty ∧
        x ∈ fvs ∧ (if q < cnP then q else rP + (q - cnP))
          < rP + (q + 1 - cnP) := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hx
        exact nomatch hx
    by_cases hqc : q < cnP
    · rw [List.getElem?_append_left
        (by rw [List.length_take, hfvslen]; omega),
        List.getElem?_take_of_lt hqc] at hx
      obtain ⟨ty, rfl⟩ := hshapeS q x hx
      exact ⟨ty, by simp only [hqc, ↓reduceIte], List.mem_of_getElem? hx,
        by simp only [hqc, ↓reduceIte]; omega⟩
    · rw [List.getElem?_append_right
        (by rw [List.length_take, hfvslen]; omega),
        List.length_take, hfvslen,
        show min cnP (rP + cnF) = cnP from by omega,
        List.getElem?_drop] at hx
      obtain ⟨ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      exact ⟨ty, by simp only [hqc, ↓reduceIte], List.mem_of_getElem? hx,
        by simp only [hqc, ↓reduceIte]; omega⟩
  have hspLeaf : ∀ (q : Nat) (x : KExpr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP) := by
    intro q x hx l hl
    obtain ⟨ty, rfl, hmem, hidx0⟩ := hspIdx q x hx
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨hmem, hidx0⟩
    · have hwsty := hwsFvs _ hmem
      have hwsty' : Expr.WScoped
          (if q < cnP then q else rP + (q - cnP)) ty := by
        have h' := hwsty
        simp only [Expr.WScoped] at h'
        exact h'.2
      have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty' l hl'
      refine ⟨hleafClosed l ⟨_, hmem, ?_⟩, by omega⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hspScope : ∀ (q : Nat) (x : KExpr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨ty, rfl, hmem, -⟩ := hspIdx q x hx
    exact ⟨hwsFvs _ hmem, hbFvs _ hmem⟩
  have hspPar : ∀ q, q < cnP →
      (fvs.take cnP ++ fvs.drop rP)[q]? = fvs[q]? := by
    intro q hq
    rw [List.getElem?_append_left
      (by rw [List.length_take, hfvslen]; omega),
      List.getElem?_take_of_lt hq]
  have hspFld : ∀ j, j < cnF →
      (fvs.take cnP ++ fvs.drop rP)[cnP + j]? = fvs[rP + j]? := by
    intro j hj
    rw [List.getElem?_append_right
      (by rw [List.length_take, hfvslen]; omega),
      List.length_take, hfvslen,
      show min cnP (rP + cnF) = cnP from by omega,
      List.getElem?_drop, show cnP + j - cnP = j from by omega]
  have hmixlen : (xs.take cnP ++ ys.drop cnP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hlenX,
      hlenY]
    omega
  have hzsPre : ∀ n, n < rP →
      (xs.take rP ++ ys.drop cnP).getD n default
        = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getElem?_append_left
      (by rw [List.length_take, hlenX]; omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right
      (by rw [List.length_take, hlenX]; omega),
      List.length_take, hlenX, show min rP mI = rP from by omega,
      List.getElem?_drop, show rP + j - rP = j from by omega]
    rfl
  have hmixsp : ∀ (q : Nat) (x : KExpr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ w0, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF) x = some w0 ∧
        (xs.take cnP ++ ys.drop cnP)[q]?
          = some (AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP)
              (rP + cnF - 1) w0) := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hx
        exact nomatch hx
    obtain ⟨ty, rfl, hmem, -⟩ := hspIdx q x hx
    have hidxK : (if q < cnP then q else rP + (q - cnP)) < rP + cnF := by
      by_cases hqc : q < cnP
      · simp only [hqc, ↓reduceIte]; omega
      · simp only [hqc, ↓reduceIte]; omega
    refine ⟨.bvar (rP + cnF - 1
        - (if q < cnP then q else rP + (q - cnP))),
      denoteMeta_fvar mp.base2.acval (rP + cnF) _ ty, ?_⟩
    rw [instSeqAV_bvar_full hidxK hzslen]
    by_cases hqc : q < cnP
    · simp only [hqc, ↓reduceIte]
      rw [List.getElem?_append_left
        (by rw [List.length_take, hlenX]; omega),
        List.getElem?_take_of_lt hqc, hzsPre q (by omega), List.getD]
      rcases hx0 : xs[q]? with _ | v
      · rw [List.getElem?_eq_none_iff, hlenX] at hx0
        omega
      · rfl
    · simp only [hqc, ↓reduceIte]
      rw [List.getElem?_append_right
        (by rw [List.length_take, hlenX]; omega),
        List.length_take, hlenX, show min cnP mI = cnP from by omega,
        List.getElem?_drop, show cnP + (q - cnP) = q from by omega,
        hzsFld (q - cnP) (by omega),
        show cnP + (q - cnP) = q from by omega, List.getD]
      rcases hy0 : ys[q]? with _ | v
      · rw [List.getElem?_eq_none_iff, hlenY] at hy0
        omega
      · rfl
  have hmixFldEq : ∀ j, j < cnF →
      (xs.take cnP ++ ys.drop cnP).getD (cnP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right
      (by rw [List.length_take, hlenX]; omega),
      List.length_take, hlenX, show min cnP mI = cnP from by omega,
      List.getElem?_drop, show cnP + j - cnP = j from by omega]
    rfl
  have hmixPar : ∀ q, q < cnP →
      interp V ρ ((xs.take cnP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    have h0 : (xs.take cnP ++ ys.drop cnP).getD q default
        = xs.getD q default := by
      rw [List.getD, List.getD, List.getElem?_append_left
        (by rw [List.length_take, hlenX]; omega),
        List.getElem?_take_of_lt hq]
    rw [h0]
    exact (hpar q hq).symm
  -- ===== the four ladders, and the zipper =====
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
  have hTVjPd : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) cvj.type = some TVja :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hCw hTVjcl hTVj0
      (rP + cnF)
  have hparZ : ∀ N, rP ≤ N → N ≤ rP + cnF → ∀ q, q < cnP →
      ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      ∃ w, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF) ((fvs.take cnP ++ fvs.drop rP).getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF) (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw := by
    intro N hrPN hN
    exact plainParamSupply (hdeq _) hplainLe hrPN hfvslen hshapeS
      hΓslen hfvsPlen hshapeP hwsFvsP hleafClosedP hlbFvsP htowerP
      hokTV hdomsP0 (hpadLen N hN) (hpadEnt N hN)
      (prefixGradeFire (hdeq _) hfvslen hshapeS hwsFvs hleafClosed
        hlbFvs htowerS hokTst hdomsS0 hfvsPlen hshapeP htowerP hokTV
        hdomsP0 hroT htyRw htyRb hrinst hrenP hdePre hN)
      hCw hCb hTVjPd hokTVj hcinstP hdePars hsplen hspPar hcinst hroT
      (Expr.ErasedEq.rfl _)
  obtain ⟨hsat, hfitS⟩ := zipper (hdeq _) hroT hrPmI hlenX hlenY
    hfvslen hshapeS hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0
    hfvsPlen hshapeP htowerP hokTV hdomsP0 htyRw htyRb hrinst hrenP
    hCwR hCbR hTVjK hokTVj hTVjcl htowerJ hsplen hspLeaf hspScope
    hspFld hcinst hmixlen hmixsp hmixFldEq hmixPar hfitRpre hfitC
    hdePre hdeFld hparZ
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
  have hainst : ∀ (n : Key .anon) (ψ : LevelParam → Nat) (y : AnnotTerm) (k : Nat),
      (mp.base2.acval n ψ).inst y k = mp.base2.acval n ψ :=
    fun n ψ y k =>
      AVExprSubst.inst_eq_self_of_closed (mp.base2.acval_closed n ψ) y k
  have hCfb : Expr.fvarsBelow rP cvj.type :=
    Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl
      exact nomatch hl)
  have hTVjrP : denoteMeta mp.base2.acval env (Level.substFn φ lps us) rP
      cvj.type = some TVja :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hCw hTVjcl hTVj0 rP
  have hpsPlen : (fvsP.take cnP).length = cnP := by
    rw [List.length_take, hfvsPlen]; omega
  have hpsRlen : (fvs.take cnP).length = cnP := by
    rw [List.length_take, hfvslen]; omega
  have hpsRen : ∀ (i : Nat) (a a' : KExpr), (fvsP.take cnP)[i]? = some a →
      (fvs.take cnP)[i]? = some a' → RenEqT f a a' := by
    intro i a a' ha ha'
    have hi : i < cnP := by
      rcases Nat.lt_or_ge i cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hpsPlen]; omega)] at ha
        exact nomatch ha
    rw [List.getElem?_take_of_lt hi] at ha
    rw [List.getElem?_take_of_lt hi] at ha'
    obtain ⟨ty, rfl⟩ := hshapeP i a ha
    obtain ⟨ty', rfl⟩ := hshapeS i a' ha'
    exact RenEqT.fvar
  have hpsPfacts : ∀ (j : Nat) (x : KExpr), (fvsP.take cnP)[j]? = some x →
      (∃ w, denoteMeta mp.base2.acval env (Level.substFn φ lps us) rP x
        = some w) ∧ Expr.WScoped rP x ∧ x.looseBVarsBounded 0 = true := by
    intro j x hx
    have hj : j < cnP := by
      rcases Nat.lt_or_ge j cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hpsPlen]; omega)] at hx
        exact nomatch hx
    have hx' : fvsP[j]? = some x := by
      rw [← List.getElem?_take_of_lt hj]; exact hx
    obtain ⟨ty, rfl⟩ := hshapeP j x hx'
    exact ⟨⟨_, denoteMeta_fvar mp.base2.acval rP j ty⟩,
      hwsFvsP _ (List.mem_of_getElem? hx'), rfl⟩
  obtain ⟨Xcrest, hXcrest⟩ := instPisAt_denoteMeta_defined
    mp.base2.acval_closed hainst (fvsP.take cnP) hcinstP hpsPfacts
    hCfb hCb hTVjrP
  obtain ⟨Γx, Rx, htowerX, hRxden, hdomsX0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) cnF hopenXP hXcrest
  have hwsCrestP : Expr.WScoped rP crestP :=
    (instPisAt_WScoped (d := rP) (fvsP.take cnP) cvj.type hcinstP
      (Expr.WScoped.of_not_hasFvar hCw)
      (fun a ha => hwsFvsP a (List.mem_of_mem_take ha))).2
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
    (show RenEqT f cvj.type (cvj.type.renameConsts f) from
      Expr.ErasedEq.rfl _)
    hpsPlen hpsRlen hpsRen hcinstP hopenXP hwsX hwsFvsP hdomsX0A
    hfvslen hcinst hshapeS
    (fun n hn ρ' hρ' => hpreK n (by omega) hn ρ' (hsatId ρ' hρ'))
    (fun n hn1 hn2 ρ' hρ' dw hdw =>
      hfldK n (by omega) hn1 hn2 ρ' (hsatId ρ' hρ') dw hdw)
  -- ===== the applied reduct's grading at the frame's own openers =====
  have hcinstP' : Expr.instPisAt ((fvsP.take rP).take cnP) cvj.type
      = some (cdomsP, crestP) := by
    rw [List.take_take, Nat.min_eq_left hplainLe]
    exact hcinstP
  have hokApp := annotOpeners_lamWalk (m := mp.base2)
    (hdeq (Level.substFn φ lps us)) hroT hfvslen hshapeS hwsFvs hlbFvs
    hΓslen hdomsS0 hΔaent (pinsWalkOk_plain hplainLe) htyw htyb hCw hCb
    hopenP hcinstP' hopenXP hIdent
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
  have hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ ((xs.take cnP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · exact hmixPar q hqc
    · rw [show q = cnP + (q - cnP) from by omega]
      exact congrArg _ (hmixFldEq (q - cnP) (by omega))
  have hconstDenC : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (.const (f ctor) (cvj.levelParams.map .param))
      = some (mp.base2.acval ctor
        (Level.substFn φ cvj.levelParams usj)) := by
    have hctorLev : mp.base2.acval ctor
          (Level.substFn φ cvj.levelParams usj)
        = mp.base2.acval ctor (Level.substFn φ lps us) :=
      mp.base2.acval_params ctor _ hctorE _ _ (fun p hp => hagree p hp)
    rw [denoteMeta_const hfCmE (by rw [hCmlps, List.length_map]), hCmlps,
      show Level.substFn (Level.substFn φ lps us) cvj.levelParams
          (cvj.levelParams.map .param)
        = Level.substFn φ lps us from
        funext fun _ => Level.substFn_map_param, hroT.2.2, hctorLev]
  have hspMem : ∀ σ : Nat → V, Sat V Γs σ →
      ∀ (q : Nat) (x : KExpr),
        (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
        ∃ w, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
              (rP + cnF) x = some w ∧ WellDenotedV V σ w ∧
          ∀ dw, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
              (rP + cnF) (cdoms.getD q default) = some dw →
            interp V σ w ∈ˢ interp V σ dw := by
    intro σ hσ q x hx
    have hgq : (fvs.take cnP ++ fvs.drop rP).getD q default = x := by
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
      obtain ⟨ty, rfl, hmem, -⟩ := hspIdx q x hx
      have hqc' : ¬ q < cnP := by omega
      simp only [hqc', ↓reduceIte] at hx ⊢
      refine ⟨.bvar (rP + cnF - 1 - (rP + (q - cnP))), ?_,
        ⟨by simp, by simp⟩, ?_⟩
      · exact denoteMeta_fvar mp.base2.acval (env := env)
          (φ := Level.substFn φ lps us) (rP + cnF) (rP + (q - cnP)) ty
      · intro dw hdw
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
    hΔaent hsat hvl0 hwsL hbL hokVL hlhead hlarity hlpre
    (show Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
        (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (fvs.take cnP ++ fvs.drop rP)) from by
      rw [hmaj]
      exact Expr.ErasedEq.rfl _)
    hconstDenC hleafL hltL hCwR hCbR hTVjK hokTVj hTVjcl htowerJ
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
    (pinsWalkOk_plain hplainLe) htyw htyb hCw hCb hopenP hcinstP' hopenXP
    hΓslen hΔaent hIdent hrhsw hrhsb hRaden
    (fun τ => (hRaFacts τ).1) hwalk hzslen hsat
    (teleFitPA_to_chain (rP + cnF) htowerS hzslen hfitS) hzsAnnot

set_option maxHeartbeats 12800000 in
/-- One checked `.plain` rule's `RecRuleLaw` from `IotaRuleVmRunJ` (`iotaRulePlain` adapted). -/
theorem iotaRulePlain_vm {V : Type w} [Ix.Kernel.SetTheory V]
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
    (hfireP : RecRule.fire r' = .plain) (φ : LevelParam → Nat) :
    RecRuleLaw mp.base2 φ cvA.name cvA mI rP r' := by
  have hdeq := hJ.defeq
  have hinf := hJ.infer
  have hreadsP := hJ.reads
  have hframe := hJ.frame
  obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
    hrres, hstripRhs, hrun0, fire, hr'eq, hbranch⟩ := hkit
  have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]; rfl
  have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]; rfl
  have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]; rfl
  have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq, hnfK]; rfl
  have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]; rfl
  have hr'pb : RecRule.paramsBlind r' = false := by rw [hr'eq]; rfl
  obtain ⟨htyw, -, -, htyb, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hself)
  have hfcS : envSelf.find? (RecRule.ctor r)
      = some (.ctorInfo cvjK cnPK cnFK) := by
    rcases hup _ _ hfcK with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hCw, hClp, -, hCb, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hfcS)
  obtain ⟨cvm, mval, hm, hfm, hlpsm, -, -⟩ :=
    hIS cvA.name hbnA _ hself
  have hfRnE : envSelf.find? (f cvA.name)
      = some (.defnInfo cvm mval hm) := by
    rw [hf]
    dsimp only
    simp only [hbnA, ↓reduceIte]
    exact hfm
  obtain ⟨ciCm, hfCmE, hCmlps⟩ : ∃ ciCm,
      envSelf.find? (f (RecRule.ctor r)) = some ciCm ∧
      ciCm.toConstantVal.levelParams = cvjK.levelParams := by
    by_cases hbc : blockNames.contains (RecRule.ctor r) = true
    · obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC, -, -⟩ := hIS _ hbc _ hfcS
      refine ⟨.defnInfo cvmC mvalC hmC, ?_, hlpsC⟩
      rw [hf]
      dsimp only
      simp only [hbc, ↓reduceIte]
      exact hfmC
    · refine ⟨.ctorInfo cvjK cnPK cnFK, ?_, rfl⟩
      rw [hf]
      dsimp only
      simp only [hbc, ↓reduceIte]
      exact hfcS
  have heqfS : envSelf.find? eqName = some eqA := by
    rcases hup _ _ heqfind with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hrhsAw, hrhsAb⟩ := hJ.annot_syntax hann hrf hrb
  have hRmlps : (ConstantInfo.defnInfo cvm mval
      hm).toConstantVal.levelParams = cvA.levelParams := hlpsm
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
  -- ===== the canonical branch =====
  obtain ⟨hpl, hfireP0, hthmR⟩ :
      Expr.recRulePlain cvA.type mI rP cnPK cvjK.levelParams = true ∧ fire = .plain ∧
        IotaThmVmRunJ J env₂ envSelf f cvA.name
          cvA.levelParams cvA.type mI rP j r cvjK cnPK cnFK rhsA := by
    rcases hbranch with h | ⟨hnpl, hrest⟩
    · exact h
    · exfalso
      obtain ⟨lvls, pins, hfireN, -⟩ := hrest
      rw [hr'fire, hfireN] at hfireP; exact nomatch hfireP
  refine ⟨recRulePlain_le_mIT hpl, ?_⟩
  intro us huslen
  obtain ⟨cvt, fvs, tbody, hcvtE, hcvtlps, hopen, hEqH, hlen3,
    hlhead0, hlarity0, hlpre0, hmaj0, hCstrips,
    cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, crest2, ldoms,
    lrest, hcinst, hclen, hrinst, hopenP, hcinstP, hopenXP,
    hwalk, hdeParsRun, hruns⟩ := hthmR
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
  obtain ⟨Ra, hRaden, hokRa, hRalaw⟩ := indBottomPlain_vm (V := V) mp
    hdeq hinf hreadsP hframe hroT heqfS htyw htyb htyOk hfRnE hRmlps hfcS
    hfCmE hCmlps hCw hCb hClp
    (recRulePlain_le_mIT hpl) (recRulePlain_leT hpl) hrhsAw hrhsAb
    hrhsKey hSw hSb hthm hopen hheadEq hargs3
    (eq_of_beq hlhead0) hlarity0 (eq_of_beq hlpre0) (eq_of_beq hmaj0)
    (Ix.Kernel.Expr.ctorTeleOk_isSome hCstrips) hcinst hclen hrinst hopenP hcinstP hopenXP
    hwalk
    hdeIdx hdePre hdeFld hdeParsRun hdeRhs hsideL hsideR
    φ us huslen
  refine ⟨Ra, by rw [hr'rhs]; exact hRaden, hokRa, ?_, ?_⟩
  · intro lvls pins hn
    rw [hfireP] at hn
    exact nomatch hn
  intro cvj cnP cnF hfcv usj ρ xs ys TVa TVja restR restC hlenX hlenY
    husjlen hlev hplain hnested hidx hTVa hTVja hfitR hfitC
  obtain ⟨rfl, rfl, rfl⟩ := hctorId hfcv
  rw [hr'cp, hr'nf] at hlenY
  rw [hr'cp] at hidx ⊢
  rw [hr'ctor] at hfitR ⊢
  refine hRalaw usj ρ xs ys TVa TVja restR restC hlenX hlenY husjlen
    ?_ ?_ hidx hTVa hTVja hfitR hfitC
  · rw [hlev, recFireComparands_plain hfireP]
  · intro i hi him
    exact hplain hr'pb hfireP i (by rw [hr'cp]; exact hi) him

end IxVM.Refinement.Decl
