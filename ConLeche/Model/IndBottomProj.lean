module

import ConLeche.Model.IndProjKit
public import ConLeche.Model.IndBottomPlain
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitRename
public section

/-!
# The projection bottom, at the reading (task #161, IND TIER part 9)

`Install/IndBottomProjS.lean` transposed to `denoteMeta`/`interp`: the
checked `proj_i.iota` theorem of a stored *degenerate* projection
recursor, fired at an arbitrary fitting spine, yields the stored rule's
`RecRuleLaw` law.

The projection install runs **different checks** from the iota install,
and the two deltas v1 records survive the transposition unchanged:

* **the zipper is syntactic.**  `checkProjIota`'s `domsMatchAux` pins
  the statement's telescope domains to the constructor's renamed ones,
  so the two *read* contexts are equal (`towerCtxEqDAV` + `PiTeleAV.det`)
  and the statement's `Sat` is the constructor fit read at the fired
  spine — no ladder, no strong induction, no `DefEqListOk` row;
* **the reduct is a β-contraction.**  `checkProjRule` pins the rule to
  the constructor telescope's λ-tower returning the field's bound
  variable, so the tower's context is again the statement's
  (`towerCtxEqAV`) and `lamTowerStep` delivers the equality *and* the
  truthfulness transport in one descent (`projBodyValueAV` names the
  contractum).

**The P tier's own delta is where `point`'s `hspMem` comes from.**  The
plain and nested bottoms read the fire spine's memberships off a
position ladder; the projection records no walks, so there is no ladder
to read.  It comes from the syntactic identification instead: with
`cnP = rP` the fire spine **is** the statement frame's openers, so the
constructor run's `q`-th domain reads at depth `q` to the tower slot
`Γs.getD (K - 1 - q)` and the membership is the frame's own `Sat`
slot, lifted (`projSpineMem`, `Interp/IndProjKitP.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta isDefEqCore inferTypeCore DefEqListOk)

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 25600000 in
/-- **The projection bottom, at the reading** (`indBottomProjS`). -/
theorem indBottomProj {μ : CheckMode} {env : Env}
    (mp : EnvModelM V μ env) {F : Nat}
    (hdeq : ∀ ψ : Name → Nat, DefEqClaim μ mp.base2 ψ F)
    (hinf : ∀ ψ : Name → Nat, InferClaim μ mp.base2 ψ F)
    -- the totality residue (routed: `inferReads_of` at the caller)
    (hreadsP : ∀ ψ : Name → Nat, InferReads mp.base2 μ ψ F)
    {f : Name → Name} (hroT : RenameOk mp.base2.acval env f)
    (heqfE : env.find? eqName = some eqA)
    {Rn : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    {ciRm : ConstantInfo}
    (hfRnE : env.find? (f Rn) = some ciRm)
    (hRmlps : ciRm.toConstantVal.levelParams = lps)
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (hctorE : env.find? ctor = some (.ctorInfo cvj cnP cnF))
    {ciCm : ConstantInfo}
    (hfCmE : env.find? (f ctor) = some ciCm)
    (hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hClp : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    -- the degenerate recursor's shape
    {i : Nat} (hmIrP : mI = rP) (hcnPrP : cnP = rP) (hilt : i < cnF)
    -- `checkProjShape`: the constructor's telescope and residual
    {cbinders : List (Expr × BinderMeta)} {cbody : Expr}
    (hCstrip : cvj.type.stripPis (cnP + cnF) = some (cbinders, cbody))
    (hcbodyArity : cbody.getAppArgs.length = cnP)
    -- `checkProjRule`: the rule is the constructor telescope's λ-tower
    -- returning the field, with the constructor's domains
    -- (the rule's closedness is a statement premise the projection
    -- reduct does not consume: `lamTowerStep` descends the read tower
    -- itself, so no depth transport is needed)
    {rhsA : Expr} (_hrhsw : rhsA.hasFvar = false)
    (_hrhsb : rhsA.looseBVarsBounded 0 = true)
    {rbinders : List (Expr × BinderMeta)}
    (hrhsAstrip : rhsA.stripLams (cnP + cnF)
      = some (rbinders, .bvar (cnF - 1 - i)))
    (hrdomsEq : ∀ (i0 : Nat) (b b' : Expr × BinderMeta),
      i0 < cnP + cnF → rbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.1 = b'.1)
    -- the rule rhs's front door, at the reading (`ProjFnR`'s recorded
    -- run row, graded through `InferClaim` at the caller)
    (hrhsKey : ∀ ψ : Name → Nat, ∃ Ra ta,
      denoteMeta mp.base2.acval env ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Ra ∧
        interp V ρ Ra ∈ˢ interp V ρ ta)
    -- the checked statement's front doors and opened kit
    {stmtTy : Expr} (hSw : stmtTy.hasFvar = false)
    (hSb : stmtTy.looseBVarsBounded 0 = true)
    (hthm : ∀ ψ : Name → Nat, ∃ ta,
      denoteMeta mp.base2.acval env ψ 0 stmtTy = some ta ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ ta) ∧
        WellDenotedV V ρ ta)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (hopen : openPisAtFvars (rP + cnF) stmtTy 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (hrhsSpin : rhsS = fvs.getD (rP + i) default)
    -- `checkProjIota`: the statement's domains are the constructor's,
    -- renamed to the model side
    {sbinders : List (Expr × BinderMeta)} {sbody : Expr}
    (hSstrip : stmtTy.stripPis (cnP + cnF) = some (sbinders, sbody))
    (hdomsSC : ∀ (i0 : Nat) (b b' : Expr × BinderMeta),
      i0 < cnP + cnF → sbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.1 = b'.1.renameConsts f)
    -- the sides pack's two recorded runs
    (hsideL : ∃ tl, inferTypeCore μ env F (rP + cnF) lhsS = .ok tl ∧
      isDefEqCore μ env F (rP + cnF) tl αS = .ok true)
    (hsideR : ∃ tr, inferTypeCore μ env F (rP + cnF) rhsS = .ok tr ∧
      isDefEqCore μ env F (rP + cnF) tr αS = .ok true) :
    ∀ (φ : Name → Nat) (us : List Level), us.length = lps.length →
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
  have hrPmI : rP ≤ mI := by omega
  have hKeq : cnP + cnF = rP + cnF := by omega
  -- the fire spine **is** the frame's openers (`cnP = rP`)
  have hspEq : fvs.take cnP ++ fvs.drop rP = fvs := by
    rw [hcnPrP]
    exact List.take_append_drop rP fvs
  rw [hspEq] at hmaj
  -- ===== the statement, opened =====
  obtain ⟨Tst, hTstden, hTstFacts⟩ := hthm (Level.substFn φ lps us)
  obtain ⟨Γs, Rbody, htowerS, hRbodyDenA, hdomsS0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (rP + cnF) hopen hTstden
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hfvslen : fvs.length = rP + cnF := openPisAtFvars_length _ hopen
  have hshapeS : ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
      ∃ ty, x = Expr.fvar q ty := by
    intro q x hx
    obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopen q x hx
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
  have hlbFvs : ∀ (q : Nat) (ty : Expr),
      Expr.fvar q ty ∈ fvs → ty.looseBVarsBounded 0 = true :=
    fun q ty hmem =>
      (openPisAtFvars_bounded (rP + cnF) hopen hSb).2 _ hmem
  have hwsTy : ∀ (q : Nat) (ty : Expr),
      Expr.fvar q ty ∈ fvs → Expr.WScoped q ty := by
    intro q ty hmem
    have h := hwsFvs _ hmem
    simp only [Expr.WScoped] at h
    exact h.2
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
  have hfvsLt : ∀ l : Nat × Expr,
      Expr.fvar l.1 l.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1, ← hfvslen]
    exact hql
  have hdomsS0 : ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) q
          (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - q) default) := by
    intro q x hx
    have h := hdomsS0A q x hx
    rwa [Nat.zero_add] at h
  have hRbodyDen : denoteMeta mp.base2.acval env
      (Level.substFn φ lps us) (rP + cnF) tbody = some Rbody := by
    have h := hRbodyDenA
    rwa [Nat.zero_add] at h
  have hΔaent : ∀ q, q < rP + cnF →
      Γs[rP + cnF - 1 - q]?
        = some (Γs.getD (rP + cnF - 1 - q) default) := by
    intro q hq
    rw [List.getD]
    rcases hg : Γs[rP + cnF - 1 - q]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  have hokTst : ∀ σ : Nat → V, WellDenotedV V σ Tst :=
    fun σ => (hTstFacts σ).2
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
  have hTVjR0 : denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0
      (cvj.type.renameConsts f) = some TVja := by
    rw [denoteMeta_renameConsts hroT]
    exact hTVj0
  have hTVjK : denoteMeta mp.base2.acval env (Level.substFn φ lps us)
      (rP + cnF) (cvj.type.renameConsts f) = some TVja :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hCwR hTVjcl hTVjR0
      (rP + cnF)
  have hokTVj : ∀ σ : Nat → V, WellDenotedV V σ TVja :=
    mp.type_wellDenotedV _ (ConLeche.Semantics.Env.find?_mem hctorE)
      (Level.substFn φ lps us) TVja hTVj0
  obtain ⟨Γj, Rj, htowerJ, hΓjlen0, hRjdenA, hdomsJ⟩ :=
    stripPis_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (cnP + cnF) hCstrip hTVj0
  -- ===== the statement's read context IS the constructor's =====
  obtain ⟨Γs2, Rbody2, htowerS2, hΓs2len, hRbody2den, hdomsS2⟩ :=
    stripPis_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (cnP + cnF) hSstrip hTstden
  have hΓs2 : Γs2 = Γs := by
    have h := htowerS2
    rw [hKeq] at h
    exact (PiTeleAV.det htowerS h).1.symm
  have hΓsJ : Γs = Γj := by
    refine (hΓs2 ▸ towerCtxEqDAV (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us)
      (Expr.stripPis_length _ hSstrip) (Expr.stripPis_length _ hCstrip)
      (by rw [hΓs2len]) hΓjlen0 hdomsS2 hdomsJ ?_)
    intro i0 b b' hi0 hb hb'
    have hdom := hdomsSC i0 b b' hi0 hb hb'
    have hopeners : ∀ a ∈ openFvars 0 i0,
        Expr.ErasedEq (a.renameConsts f) a := by
      intro a ha
      obtain ⟨q0, hq0⟩ := List.getElem?_of_mem ha
      have hq0lt : q0 < i0 := by
        have := (List.getElem?_eq_some_iff.mp hq0).1
        rwa [openFvars_length] at this
      rw [openFvars_getElem? (d := 0) hq0lt] at hq0
      obtain rfl : a = Expr.fvar (0 + q0) (.sort .zero) :=
        (Option.some.inj hq0).symm
      exact rfl
    have hee := Expr.instSeq_renameConsts (f := f) (openFvars 0 i0)
      (i0 - 1) (X := b'.1) hopeners
    rw [hdom, ← denoteMeta_erasedEq hee (0 + i0),
      denoteMeta_renameConsts hroT]
  -- ===== the fired spine =====
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  have hzsPre : ∀ n, n < rP →
      (xs.take rP ++ ys.drop cnP).getD n default
        = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getElem?_append_left (by rw [hxtlen]; omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right (by rw [hxtlen]; omega),
      hxtlen, List.getElem?_drop, show rP + j - rP = j from by omega]
    rfl
  have hpar : ∀ q, q < cnP →
      interp V ρ (ys.getD q default)
        = interp V ρ (xs.getD q default) :=
    fun q hq => hparP q hq (by omega)
  have hzsVal : ∀ q, q < rP + cnF →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q rP with hqc | hqc
    · rw [hzsPre q hqc]
      exact (hpar q (by omega)).symm
    · have hz := hzsFld (q - rP) (by omega)
      rw [show rP + (q - rP) = q from by omega,
        show cnP + (q - rP) = q from by omega] at hz
      rw [hz]
  -- ===== the zipper: the constructor fit, read at the fired spine ==
  have hchainC := teleFitPA_to_chain (cnP + cnF) htowerJ hlenY hfitC
  have hchainEq : ∀ q, q ≤ rP + cnF →
      chain V ρ ((xs.take rP ++ ys.drop cnP).take q)
        = chain V ρ (ys.take q) := by
    intro q hq
    funext q0
    have htq : ((xs.take rP ++ ys.drop cnP).take q).length = q := by
      rw [List.length_take, hzslen]
      omega
    have htq' : (ys.take q).length = q := by
      rw [List.length_take, hlenY]
      omega
    by_cases hiq : q0 < q
    · rw [chain_lt (by omega), chain_lt (by omega), htq, htq']
      have hlt : q - 1 - q0 < q := by omega
      rw [show ((xs.take rP ++ ys.drop cnP).take q).getD (q - 1 - q0)
            default
          = (xs.take rP ++ ys.drop cnP).getD (q - 1 - q0) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt],
        show (ys.take q).getD (q - 1 - q0) default
          = ys.getD (q - 1 - q0) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt]]
      exact hzsVal _ (by omega)
    · rw [chain_ge (by omega), chain_ge (by omega), htq, htq']
  have hallK : ∀ m, m < rP + cnF →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD m default)
        ∈ˢ interp V (chain V ρ ((xs.take rP ++ ys.drop cnP).take m))
          (Γs.getD (rP + cnF - 1 - m) default) := by
    intro m hm
    have h1 := hchainC m (by omega)
    rw [hchainEq m (by omega), hzsVal m hm, hΓsJ,
      show rP + cnF - 1 - m = cnP + cnF - 1 - m from by omega]
    exact h1
  have hsat : Sat V Γs (chain V ρ (xs.take rP ++ ys.drop cnP)) :=
    sat_of_tower htowerS hzslen hallK
  have hfitS : TeleFitPA V ρ Tst (xs.take rP ++ ys.drop cnP)
      (AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        Rbody) :=
    teleFitPA_of_tower (rP + cnF) htowerS hzslen hallK
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
  have hargLeaf : ∀ e : Expr, e ∈ tbody.getAppArgs →
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) ∧
      (∀ l ∈ e.fvarLeaves, l.1 < rP + cnF) := by
    intro e hmem
    have h1 : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs :=
      fun l hl => hleafBody l (fvarLeaves_getAppArgs hmem l hl)
    exact ⟨h1, fun l hl => hfvsLt l (h1 l hl)⟩
  have hmemα : αS ∈ tbody.getAppArgs := by
    rw [hargs3]; exact List.mem_cons_self ..
  have hmemL : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hmemR : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))
  obtain ⟨hleafα, hltα⟩ := hargLeaf αS hmemα
  obtain ⟨hleafL, hltL⟩ := hargLeaf lhsS hmemL
  obtain ⟨hleafR, hltR⟩ := hargLeaf rhsS hmemR
  have hwsα : Expr.WScoped (rP + cnF) αS := hwsBody.getAppArgs αS hmemα
  have hwsL : Expr.WScoped (rP + cnF) lhsS := hwsBody.getAppArgs lhsS hmemL
  have hwsR : Expr.WScoped (rP + cnF) rhsS := hwsBody.getAppArgs rhsS hmemR
  have hbα : αS.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_getAppArgs hbBody αS hmemα
  have hbL : lhsS.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_getAppArgs hbBody lhsS hmemL
  have hbR : rhsS.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_getAppArgs hbBody rhsS hmemR
  have hLα : Expr.LeavesBounded αS := fun l hl =>
    hlbFvs l.1 l.2 (hleafα l hl)
  have hLL : Expr.LeavesBounded lhsS := fun l hl =>
    hlbFvs l.1 l.2 (hleafL l hl)
  have hLR : Expr.LeavesBounded rhsS := fun l hl =>
    hlbFvs l.1 l.2 (hleafR l hl)
  have hokA : ∀ q, q < rP + cnF → ∀ σ : Nat → V, Sat V Γs σ →
      WellDenotedV V (fun j => σ (j + (rP + cnF - 1 - q) + 1))
        (Γs.getD (rP + cnF - 1 - q) default) := by
    intro q hq σ hσ
    refine hokA_padded htowerS hokTst (Nat.le_refl _) q hq σ ?_
    rw [show rP + cnF - (rP + cnF) = 0 from by omega,
      List.replicate_zero, List.nil_append, List.drop_zero]
    exact hσ
  have hctxOf : ∀ e : Expr,
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
  have hwsTl : Expr.WScoped (rP + cnF) tl :=
    inferTypeCore_WScoped mp.base2.wf F hInfL hwsL
  have hwsTr : Expr.WScoped (rP + cnF) tr :=
    inferTypeCore_WScoped mp.base2.wf F hInfR hwsR
  have hleafTl : ∀ l ∈ tl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs :=
    fun l hl => hleafL l
      (inferTypeCore_fvarLeaves mp.base2.wf F hInfL hwsL l hl)
  have hleafTr : ∀ l ∈ tr.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs :=
    fun l hl => hleafR l
      (inferTypeCore_fvarLeaves mp.base2.wf F hInfR hwsR l hl)
  have hltTl : ∀ l ∈ tl.fvarLeaves, l.1 < rP + cnF :=
    fun l hl => hfvsLt l (hleafTl l hl)
  have hltTr : ∀ l ∈ tr.fvarLeaves, l.1 < rP + cnF :=
    fun l hl => hfvsLt l (hleafTr l hl)
  have hbTl : tl.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars mp.base2.wf F hInfL hwsL hbL hLL
  have hbTr : tr.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars mp.base2.wf F hInfR hwsR hbR hLR
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
  -- ===== the fire spine's data (the spine is the frame's openers) ==
  have hCstripR := stripPis_renameConsts (f := f) (cnP + cnF) hCstrip
  obtain ⟨⟨cdoms, cres⟩, hcinst⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (e := cvj.type.renameConsts f)
      fvs (by rw [hfvslen, ← hKeq, hCstripR]; rfl))
  have hspLeaf : ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP) := by
    intro q x hx l hl
    obtain ⟨ty, rfl⟩ := hshapeS q x hx
    have hmem := List.mem_of_getElem? hx
    have hqlt : q < rP + cnF := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rwa [hfvslen] at this
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨hmem, by omega⟩
    · have hlt := Expr.fvarLeaves_lt_of_wscoped (hwsTy q ty hmem) l hl'
      refine ⟨hleafClosed l ⟨_, hmem, ?_⟩, by omega⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hspScope : ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    exact ⟨hwsFvs _ (List.mem_of_getElem? hx),
      hbFvs _ (List.mem_of_getElem? hx)⟩
  have hmixsp : ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
      ∃ w0, denoteMeta mp.base2.acval env (Level.substFn φ lps us)
            (rP + cnF) x = some w0 ∧
        (xs.take rP ++ ys.drop cnP)[q]?
          = some (AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP)
              (rP + cnF - 1) w0) := by
    intro q x hx
    have hqlt : q < rP + cnF := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rwa [hfvslen] at this
    obtain ⟨ty, rfl⟩ := hshapeS q x hx
    refine ⟨.bvar (rP + cnF - 1 - q),
      denoteMeta_fvar mp.base2.acval (rP + cnF) q ty, ?_⟩
    rw [instSeqAV_bvar_full hqlt hzslen, List.getD]
    rcases hz : (xs.take rP ++ ys.drop cnP)[q]? with _ | v
    · rw [List.getElem?_eq_none_iff, hzslen] at hz
      omega
    · rfl
  -- the run's `q`-th domain reads at depth `q` to the tower's slot
  have hdomsLow : ∀ q, q < rP + cnF →
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) q
          (cdoms.getD q default)
        = some (Γs.getD (rP + cnF - 1 - q) default) := by
    intro q hq
    have h := instPisAt_openerDoms (acval := mp.base2.acval)
      (env := env) (φ := Level.substFn φ lps us) fvs hcinst
      (j := 0) (fun q0 x hx => by
        obtain ⟨ty, hsh⟩ := hshapeS q0 x hx
        exact ⟨ty, by rw [hsh, Nat.zero_add]⟩)
      hTVjR0 (Γ := Γj) (R := Rj) (by rw [hfvslen, ← hKeq]; exact htowerJ)
      q (by rw [hfvslen]; exact hq)
    rw [Nat.zero_add, hfvslen] at h
    rw [h, hΓsJ]
  have hspMem := projSpineMem (acval := mp.base2.acval) (env := env)
    (φ := Level.substFn φ lps us) (V := V) mp.base2.acval_closed
    hfvslen hshapeS hwsTy hCwR hcinst hΓslen hdomsLow
  -- ===== the left side is the fired redex =====
  have hclen : cres.getAppArgs.length = cnP + (mI - rP) := by
    have h1 := instPisAt_fvar_residual_arity fvs hcinst
      (fun x hx => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
        obtain ⟨ty, hsh⟩ := hshapeS q x hq
        exact ⟨q, ty, hsh⟩)
      (bs := cbinders.map (fun b => (b.1.renameConsts f, b.2)))
      (body := cbody.renameConsts f)
      (by rw [hfvslen, ← hKeq]; exact hCstripR)
    rw [getAppArgs_length_renameConsts] at h1
    rw [h1, hcbodyArity]
    omega
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
  have hArgsClen : vArgsC.length = cnP + (mI - rP) := by
    rw [← hcspJ.length, List.length_map, hcbodyArity]
    omega
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
  have hdeIdxNil : DefEqListOk μ F env (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP) := by
    rw [show mI - rP = 0 from by omega, List.take_zero,
      List.drop_eq_nil_of_le (by rw [hclen]; omega)]
    trivial
  have heqL := point (hdeq (Level.substFn φ lps us)) hroT
    (zs := xs.take rP ++ ys.drop cnP) rfl hrPmI hlenX hlenY hfRnE
    hRmlps hfvslen hshapeS hwsFvs hlbFvs htowerS hokTst hdomsS0 hΓslen
    hΔaent hsat hvl0 hwsL hbL hokVL hlhead hlarity hlpre
    (show Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
        (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          fvs) from by
      rw [hmaj]
      exact Expr.ErasedEq.rfl _)
    hconstDenC hleafL hltL hCwR hCbR hTVjK hokTVj hTVjcl htowerJ
    (by rw [hfvslen, hKeq]) hspLeaf hspScope hcinst hclen hspMem hRjdec
    hArgsClen hdeIdxNil
    (show (xs.take rP ++ ys.drop cnP).length = cnP + cnF from by
      rw [hzslen]; omega)
    hmixsp (fun q hq => hzsVal q (by omega)) hfitC hidx
  -- ===== the reduct: the rule λ-tower's β-contractum =====
  obtain ⟨Γlam, C, htowerLam, hΓlamlen, hCden, hdomsLam⟩ :=
    stripLams_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (cnP + cnF) hrhsAstrip hRaden
  have hΓlamJ : Γlam = Γj :=
    towerCtxEqAV (Expr.stripLams_length _ hrhsAstrip)
      (Expr.stripPis_length _ hCstrip) hΓlamlen hΓjlen0 hdomsLam hdomsJ
      hrdomsEq
  have hCval : C = .bvar (cnP + cnF - 1 - (cnP + i)) :=
    projBodyValueAV hilt hCden
  have hmemLam : ∀ k, k < cnP + cnF →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD k default)
        ∈ˢ interp V (chain V ρ ((xs.take rP ++ ys.drop cnP).take k))
          (Γlam.getD (cnP + cnF - 1 - k) default) := by
    intro k hk
    rw [hΓlamJ, ← hΓsJ, show cnP + cnF - 1 - k = rP + cnF - 1 - k from
      -- task #77: `rw [hcnPrP]`, not `by omega` (seconds in this context)
      by rw [hcnPrP]]
    exact hallK k (by omega)
  obtain ⟨L', htele', hval', hokL', hokApp'⟩ :=
    lamTowerStep (V := V) (C := C) (cnP + cnF) (Nat.le_refl _)
      htowerLam (by rw [hzslen]; omega) hmemLam (hRaFacts ρ).1
  obtain rfl : L' = C := by
    rw [Nat.sub_self] at htele'
    cases htele'
    rfl
  have htkFull : (xs.take rP ++ ys.drop cnP).take (cnP + cnF)
      = xs.take rP ++ ys.drop cnP :=
    List.take_of_length_le (by rw [hzslen]; omega)
  rw [htkFull] at hval' hokApp'
  -- the statement's right side is the contractum
  have hvRval : vR1 = .bvar (rP + cnF - 1 - (rP + i)) := by
    refine projRhsValueAV (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) hshapeS hfvslen hilt ?_
    rw [← hrhsSpin]
    exact hvr0
  refine ⟨heqL.symm.trans (heqLR.trans ?_), ?_⟩
  · rw [hval', hvRval, hCval,
      show cnP + cnF - 1 - (cnP + i) = rP + cnF - 1 - (rP + i) from
        -- task #77: `rw [hcnPrP]`, not `by omega` (seconds in this context)
        by rw [hcnPrP]]
  · -- the truthfulness transport, from the same descent
    intro hxsA hysA
    refine hokApp' (fun w hw => ?_)
    rcases List.mem_append.mp hw with hw' | hw'
    · exact hxsA w (List.mem_of_mem_take hw')
    · exact hysA w (List.mem_of_mem_drop hw')

end ConLeche.Model
