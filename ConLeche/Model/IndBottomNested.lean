module

import ConLeche.Model.IndNestedParam
public import ConLeche.Model.IndOpenerGrade
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Denote.OpenRevDenote
public section

/-!
# The nested bottom, at the reading (task #161, IND TIER part 8)

`Install/IndBottomNestedS.lean` transposed to `denoteMeta`/`interp`:
the checked nested-auxiliary `iota_j` theorem, fired at an arbitrary
fitting spine, yields the stored `.nested` rule's `RecRuleLaw` law.

It is `indBottomPlain` at the **pin** parameter spine, with the same
stage composition (`zipper` → `fire` → `reduct` → `point`, then
`annotPFrameEq` → `annotMem` → `annotTransport`) and v1's own
deltas: no `cnP ≤ rP`, the constructor walks at the level-instantiated
renamed type, the major pinned only up to `ErasedEq`, and the
parameter positions supplied by `nestedParamSupply` instead of
`plainParamSupply`.

**The one delta that is the P tier's alone is where the pins' readings
come from.**  v1 reads them off the `TypedListW` walk — a derivation
pack, which carries denotations.  The P tier's row is a *run*, and a
run carries neither reading nor grading (part 4's lesson), so the
readings are taken from the only other place the checked statement
mentions the pins: its own **major argument**, which `IotaThmNR` pins
to the pin application up to `ErasedEq`.  `denoteMeta_erasedEq` crosses
the pin, `denoteMeta_mkAppN_inv` decomposes it, and the spine's readings
fall out — after which `Rules.denoteMeta_openRev` and
`Rules.denoteMeta_openRev_base` read each pin back to its canonical `openRev` form and `pinCross` (part 7,
generalized here to an unpadded fired spine) supplies the crossing
datum `RecRuleLaw`'s parameter premise is quantified over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta isDefEqCore inferTypeCore DefEqListOk TypedListOk)

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 25600000 in
/-- **The nested bottom, at the reading** (`indBottomNestedS`). -/
theorem indBottomNested {μ : CheckMode} {env : Env}
    (mp : EnvModelM V μ env) {F : Nat}
    (hdeq : ∀ ψ : Name → Nat, DefEqClaim μ mp.base2 ψ F)
    (hinf : ∀ ψ : Name → Nat, InferClaim μ mp.base2 ψ F)
    -- the totality residue (routed: `inferReads_of` at the caller)
    (hreadsP : ∀ ψ : Name → Nat, InferReads mp.base2 μ ψ F)
    {f : Name → Name} (hroT : RenameOk mp.base2.acval env f)
    (heqfE : env.find? eqName = some eqA)
    {Rn : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 tyA = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta)
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
    (hrPmI : rP ≤ mI)
    -- the stored nested-fire data
    {lvls : List Level} {pins : List Expr}
    (hlvlsLen : lvls.length = cvj.levelParams.length)
    (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hrhsKey : ∀ ψ : Name → Nat, ∃ Ra ta,
      denoteMeta mp.base2.acval env ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Ra ∧
        interp V ρ Ra ∈ˢ interp V ρ ta)
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
    -- the major, up to `ErasedEq`, at the pin spine
    (hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)))
    (hCstripsHead : ∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = Expr.const Dc usc)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
      = some (rdoms, rrest))
    {fvsP : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    {ldomsL : List Expr} {lrest2 : Expr}
    (hinstLam : Expr.instLamsAt (fvsP ++ xFvsP) rhsA
      = some (ldomsL, lrest2))
    -- the recorded runs (`IotaRuns`, plus the second widening's rows)
    (hTypedP : TypedListOk μ F env (rP + cnF)
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) cdomsP)
    (hdeIdx : DefEqListOk μ F env (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hdePre : DefEqListOk μ F env (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk μ F env (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hdeLam : DefEqListOk μ F env (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL)
    (hdeRhs : isDefEqCore μ env F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
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
  -- the acval's substitution facts, named once
  have hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (mp.base2.acval n ψ).inst y k = mp.base2.acval n ψ :=
    fun n ψ y k =>
      AVExprSubst.inst_eq_self_of_closed (mp.base2.acval_closed n ψ) y k
  -- **The nested fire's three big syntactic objects, named once.**  The
  -- two pin spines and the level-instantiated constructor type occur in
  -- (almost) every downstream type, and every stage takes them
  -- abstractly; naming them keeps this proof's terms the plain bottom's
  -- SIZE, which is what keeps its elaboration the plain bottom's COST
  -- (part 8 finding — with the spines inlined the tail is ~30× slower
  -- and runs the elaborator out of memory).
  obtain ⟨ctyL, hctyL⟩ : ∃ e : Expr,
      e = cvj.type.instantiateLevelParams cvj.levelParams lvls := ⟨_, rfl⟩
  obtain ⟨psP, hpsP⟩ : ∃ l : List Expr,
      l = pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)) := ⟨_, rfl⟩
  obtain ⟨psR, hpsR⟩ : ∃ l : List Expr,
      l = pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) := ⟨_, rfl⟩
  rw [← hpsR] at hmaj hcinst
  rw [← hctyL] at hcinst hcinstP
  rw [← hpsP] at hcinstP hTypedP
  -- ===== the statement, opened =====
  obtain ⟨Tst, hTstden, hTstFacts⟩ := hthm (Level.substFn φ lps us)
  obtain ⟨Γs, Rbody, htowerS, hRbodyDenA, hdomsS0A⟩ :=
    openPisAtFvars_denotePTele (acval := mp.base2.acval) (env := env)
      (φ := Level.substFn φ lps us) (rP + cnF) hopen hTstden
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hfvslen : fvs.length = rP + cnF := openPisAtFvars_length _ hopen
  have hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
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
  have hlbFvs : ∀ (i : Nat) (ty : Expr),
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
  have hfvsLt : ∀ l : Nat × Expr,
      Expr.fvar l.1 l.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1, ← hfvslen]
    exact hql
  have hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
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
  have hfvsPlen : fvsP.length = rP := openPisAtFvars_length _ hopenP
  have hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
    exact ⟨ty, by simpa using hx'⟩
  have hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
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
  have hlbFvsP : ∀ (i : Nat) (ty : Expr),
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
    mp.type_wellDenotedV _ (ConLeche.Semantics.Env.find?_mem hctorE) _ TVja hTVj0
  -- the level-instantiated (and renamed) constructor type
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
      (Level.substFn φ lps us) d
      ctyL
      = some TVja := by
    intro d
    refine denoteMeta_depth_of_closed mp.base2.acval_closed hCvLw hTVjcl
      ?_ d
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
  -- the fired spine's length, and the pin instantiations
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
      Expr.getAppFn_instantiateLevelParams, hheadRaw]
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
    have h := instPisAt_length _ hrinst
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
    rw [List.take_append_of_le_length (by rw [hxtlen]; omega)]
    exact List.take_of_length_le (by rw [hxtlen]; omega)
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
  -- the pins, pointwise
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
  have hopenerLeaf : ∀ (q0 : Nat) (a : Expr), (fvs.take rP)[q0]? = some a →
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
  have hspLeaf : ∀ (q : Nat) (x : Expr),
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
  have hspScope : ∀ (q : Nat) (x : Expr),
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
  have hokA : ∀ i, i < rP + cnF → ∀ σ : Nat → V, Sat V Γs σ →
      WellDenotedV V (fun j => σ (j + (rP + cnF - 1 - i) + 1))
        (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i hi σ hσ
    refine hokA_padded htowerS hokTst (Nat.le_refl _) i hi σ ?_
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
  have hmixsp : ∀ (q : Nat) (x : Expr),
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
      (hreadsP _) hroT hrPN hfvslen hΓslen hfvsPlen hshapeP hwsFvsP
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
  -- ===== the transport's frame data =====
  have hCfb : Expr.fvarsBelow rP
      ctyL :=
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
  have hpsRen : ∀ (i : Nat) (a a' : Expr),
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
  have hpsPfacts : ∀ (j : Nat) (x : Expr),
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
    -- the reading: the statement frame's, across the renaming, at depth `rP`
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
  have hbFvsP : ∀ x ∈ fvsP, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := hshapeP q x hq
    rfl
  have hpsPws : ∀ a ∈ psP,
      Expr.WScoped rP a := by
    intro a ha
    rw [hpsP] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact instSpine_WScoped (rP - 1)
      (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1)
      (fun x hx => hwsFvsP x (List.mem_of_mem_take hx))
  have hwsCrestP : Expr.WScoped rP crestP :=
    (instPisAt_WScoped (d := rP)
      psP
      ctyL hcinstP
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
  -- ===== the public λ-frame's own facts =====
  have hxlen : xFvsP.length = cnF := openPisAtFvars_length _ hopenXP
  have hPlen : (fvsP ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPlen, hxlen]
  have hPshape : ∀ (i : Nat) (x : Expr), (fvsP ++ xFvsP)[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    rcases Nat.lt_or_ge i rP with hi | hi
    · rw [List.getElem?_append_left (by rw [hfvsPlen]; exact hi)] at hx
      exact hshapeP i x hx
    · rw [List.getElem?_append_right (by rw [hfvsPlen]; exact hi),
        hfvsPlen] at hx
      obtain ⟨ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenXP (i - rP) x hx
      -- task #77: `Nat.add_sub_cancel' hi`, not `by omega` — the ambient
      -- context made this one arithmetic step cost 9.7 s.
      exact ⟨ty, by rw [hx', Nat.add_sub_cancel' hi]⟩
  have hPws : ∀ x ∈ fvsP ++ xFvsP, Expr.WScoped (rP + cnF) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact (hwsFvsP x hx').mono (by omega)
    · exact hwsX x hx'
  have hbCrestP : crestP.looseBVarsBounded 0 = true :=
    (instPisAt_bounded psP
      hcinstP hCvLb
      (fun a ha => by
        rw [hpsP] at ha
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        have h := instSpine_closed (args := fvsP.take rP) (e := p)
          (fun x hx => hbFvsP x (List.mem_of_mem_take hx))
          (by rw [htkPlen]; exact (hpinsWf p hp).2)
        rwa [htkPlen] at h)).2
  have hlbP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvsP ++ xFvsP →
        ty.looseBVarsBounded 0 = true := by
    intro i ty hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact hlbFvsP i ty h'
    · exact (openPisAtFvars_bounded cnF hopenXP hbCrestP).2 _ h'
  have hPleafClosed : ∀ l, (∃ x ∈ fvsP ++ xFvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP ++ xFvsP := by
    intro l ⟨x, hx, hl⟩
    rcases List.mem_append.mp hx with hx' | hx'
    · exact List.mem_append.mpr (Or.inl (hleafClosedP l ⟨x, hx', hl⟩))
    · rcases openPisAtFvars_leaves cnF hopenXP l (Or.inr ⟨x, hx', hl⟩) with
        h0 | h0
      · rcases instPisAt_leaves
          psP
          hcinstP l (Or.inr h0) with h1 | ⟨a, ha, hla⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCvLw] at h1
          exact nomatch h1
        · rw [hpsP] at ha
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
          rcases fvarLeaves_instSpine (rP - 1) hla with hl' | ⟨y, hy, hly⟩
          · exfalso
            rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
              (hpinsWf p hp).1] at hl'
            exact nomatch hl'
          · exact List.mem_append.mpr (Or.inl
              (hleafClosedP l ⟨y, List.mem_of_mem_take hy, hly⟩))
      · exact List.mem_append.mpr (Or.inr h0)
  -- ===== the applied reduct's grading at the frame's own openers =====
  -- (`reduct`'s third exposure: the transport fired at the frame's own
  -- openers.  Part 8 extracted it to `annotOpeners` — inline, its
  -- arithmetic side conditions are what make this proof's `omega`s
  -- exponential; see that file's docstring.)
  have hokApp := annotOpeners (m := mp.base2)
    (hdeq (Level.substFn φ lps us)) hroT hfvslen hshapeS hwsFvs hlbFvs
    hΓslen hdomsS0 hΔaent hPlen hPshape hPws hPleafClosed hlbP hIdent
    hrhsw hrhsb hRaden (fun τ => (hRaFacts τ).1) hinstLam hdeLam
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
      ∀ (q : Nat) (x : Expr),
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
      -- task #77: `grind`, not `omega`, on the three position side
      -- conditions — 5.2 s of `omega` in this ~100-hypothesis context.
      have hfld := hfldK (rP + (q - cnP)) (by grind) (by grind)
        (by grind) σ (hsatId σ hσ) dw (by
          -- task #77: the two cancellations by name (4.0 s as one `omega`).
          rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel' hqc]
          exact hdw)
      have hslot := hσ (rP + cnF - 1 - (rP + (q - cnP)))
        (Γs.getD (rP + cnF - 1 - (rP + (q - cnP))) default)
        (hΔaent (rP + (q - cnP)) (by omega))
      -- task #77: `grind`, not `omega`.  Under this proof's ~100-hypothesis
      -- context the nested truncated subtractions made `omega`'s case
      -- split exponential in the AMBIENT facts: this one step cost 39 s.
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
  exact annotTransport (hdeq (Level.substFn φ lps us)) hPlen hPshape
    hPws hPleafClosed hlbP hΓslen hΔaent hIdent hrhsw hrhsb hRaden
    (fun τ => (hRaFacts τ).1) hinstLam hdeLam hzslen hsat
    (teleFitPA_to_chain (rP + cnF) htowerS hzslen hfitS) hzsAnnot

end ConLeche.Model
