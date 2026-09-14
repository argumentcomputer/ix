import Ix.Kernel.Verify.Infer.BinderScopes
import Ix.Kernel.Verify.Infer.CheapBetaPlan
import Ix.Kernel.Verify.Whnf.Beta.Meaning
import Ix.Kernel.Verify.Whnf.Structural.ApplicationCongruence

/-!
# Audited cheap beta reduction

Lambda and let inference run `cheapBetaReduce` inside the intern table.  This
module connects its pure plan to the finite `WalkerRequest.cheapBeta`
footprint and proves exact execution while preserving the complete checker
invariant.  The Theory-level beta meaning is intentionally a separate layer;
the operational theorem here cannot silently assume it.
-/

namespace Ix.Kernel

/-- Cheap beta reduction preserves the Theory meaning of a structurally
translated source.  A successful plan is discharged by WHNF's constructive
multi-beta theorem; an absent plan is reflexive. -/
theorem KExpr.cheapBetaReduceResult_meaning
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars) {Delta : KVLCtx}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source : KExpr .anon} {sourceV : Ix.Theory.Named.VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hbounds : WalkerRequest.Bounds (.cheapBeta source)) :
    WhnfMeaning trProj world uvars Delta source
      (KExpr.cheapBetaReduceResult source) := by
  cases hplan : cheapBetaPlan? source with
  | none =>
      rw [KExpr.cheapBetaReduceResult, hplan]
      exact WhnfMeaning.refl hsource
        (hsource.wf world.venvWF.ordered theory.literalWF
          theory.projections.wf hDelta)
  | some plan =>
      rw [KExpr.cheapBetaReduceResult, hplan]
      obtain ⟨head, body, args, consumed, hspine, hpeel, hcount,
        hbase, htrailing⟩ := cheapBetaPlan?_simul hplan hbounds
      have htyped := RecM.trAppSpine_of_collectSpine hsource hspine
      obtain ⟨headV, hheadTr, hsuffix⟩ := htyped.toSuffix
      have hprefixList :
          (args.extract 0 consumed).toList =
            args.toList.take consumed := by
        simp only [Array.toList_extract, List.extract_eq_take_drop,
          List.drop_zero, Nat.sub_zero]
      have htrailingList :
          (args.extract consumed args.size).toList =
            args.toList.drop consumed := by
        rw [Array.toList_extract]
        simp only [List.extract_eq_take_drop]
        have hargsLength : args.toList.length = args.size := by simp
        have hdropLength :
            (args.toList.drop consumed).length =
              args.size - consumed := by
          rw [List.length_drop, hargsLength]
        rw [← hdropLength]
        exact List.take_length
      obtain ⟨middleV, hprefix, htrailingSuffix⟩ :=
        hsuffix.splitAt consumed (by simpa using hcount)
      rw [← hprefixList] at hprefix
      rw [← htrailingList] at htrailingSuffix
      have hpeelCert := RecM.BetaPeel.of_peelLamsN head args.toList
      rw [show args.toList.length = args.size by simp, hpeel] at hpeelCert
      dsimp only at hpeelCert
      rw [← hprefixList] at hpeelCert
      have hsimBounds := hbounds.cheapBeta_simul hspine hpeel
      obtain ⟨reducedV, hreducedTr, hmiddleReduced⟩ :=
        RecM.betaPrefixMeaning trProj world theory hDelta hheadTr
          hpeelCert.1 hprefix hsimBounds
      rw [← htrailing] at htrailingSuffix
      obtain ⟨finalV, hfinalTr, hsourceFinal⟩ :=
        htrailingSuffix.rebase world.venvWF hDelta hreducedTr
          hmiddleReduced
      refine ⟨sourceV, finalV, hsource, ?_, hsourceFinal⟩
      change TrKExprS world.venv uvars world.nameOf trProj Delta
        (plan.trailing.foldl KExpr.mkApp plan.base) finalV
      rw [hbase]
      exact hfinalTr

namespace KExpr.CheapBetaReach

@[simp] theorem source (e : KExpr .anon) : CheapBetaReach e e := by
  simp [CheapBetaReach]

theorem of_plan {source : KExpr .anon} {plan : CheapBetaPlan .anon}
    (hplan : cheapBetaPlan? source = some plan) {x : KExpr .anon}
    (hx : x ∈ cheapBetaChainList plan.base plan.trailing) :
    CheapBetaReach source x := by
  simp [CheapBetaReach, hplan, hx]

end KExpr.CheapBetaReach

/-- The pure result of an application-chain plan occurs in its exact finite
candidate list. -/
theorem cheapBetaChainList_result_mem (base : KExpr .anon) :
    ∀ trailing : List (KExpr .anon),
      trailing.foldl KExpr.mkApp base ∈ cheapBetaChainList base trailing
  | [] => by simp [cheapBetaChainList]
  | arg :: trailing => by
      simp only [List.foldl_cons, cheapBetaChainList, List.mem_cons]
      exact Or.inr (cheapBetaChainList_result_mem
        (KExpr.mkApp base arg) trailing)

theorem cheapBetaChainList_base_mem (base : KExpr .anon)
    (trailing : List (KExpr .anon)) :
    base ∈ cheapBetaChainList base trailing := by
  cases trailing <;> simp [cheapBetaChainList]

namespace KExpr.CheapBetaReach

theorem result (source : KExpr .anon) :
    CheapBetaReach source (KExpr.cheapBetaReduceResult source) := by
  cases hplan : cheapBetaPlan? source with
  | none =>
      simp [KExpr.cheapBetaReduceResult, hplan, KExpr.CheapBetaReach]
  | some plan =>
      rw [KExpr.cheapBetaReduceResult, hplan]
      exact of_plan hplan
        (cheapBetaChainList_result_mem plan.base plan.trailing)

end KExpr.CheapBetaReach

/-- Execute one selected application chain exactly.  Every candidate offered
to the intern table is drawn from `cheapBetaChainList`; collision freedom
therefore returns the anonymous expression itself rather than a colliding
resident. -/
theorem internAppChain_spec
    {support : RunSupport} (hcollision : support.CollisionFree)
    {base : KExpr .anon} {trailing : List (KExpr .anon)}
    (hreach : ∀ x, x ∈ cheapBetaChainList base trailing → support x)
    (it : InternTable .anon) (hwf : it.WF)
    (hcover : support.CoversIntern it) :
    (internAppChain base trailing it).1 =
        trailing.foldl KExpr.mkApp base ∧
      (internAppChain base trailing it).2.WF ∧
      support.CoversIntern (internAppChain base trailing it).2 := by
  induction trailing generalizing base it with
  | nil =>
      exact ⟨rfl, hwf, hcover⟩
  | cons arg trailing ih =>
      let candidate := KExpr.mkApp base arg
      have hcandidate : support candidate :=
        hreach candidate (by
          simp only [cheapBetaChainList, List.mem_cons]
          exact Or.inr (cheapBetaChainList_base_mem candidate trailing))
      have hintern := TcM.internExpr_support_spec hcollision hcandidate
        it hwf hcover
      rcases hintern with ⟨hcanon, hwf', hcover'⟩
      have htail : ∀ x,
          x ∈ cheapBetaChainList candidate trailing → support x := by
        intro x hx
        exact hreach x (by
          simp only [cheapBetaChainList, List.mem_cons]
          exact Or.inr hx)
      have hrest := ih htail (it.internExpr candidate).2 hwf' hcover'
      change
        (internAppChain (it.internExpr candidate).1 trailing
          (it.internExpr candidate).2).1 =
            (arg :: trailing).foldl KExpr.mkApp base ∧
        (internAppChain (it.internExpr candidate).1 trailing
          (it.internExpr candidate).2).2.WF ∧
        support.CoversIntern
          (internAppChain (it.internExpr candidate).1 trailing
            (it.internExpr candidate).2).2
      rw [hcanon]
      simpa only [List.foldl_cons] using hrest

/-- InternM-level exactness and support preservation for the whole
peephole reducer. -/
theorem cheapBetaReduce_spec
    {support : RunSupport} (hcollision : support.CollisionFree)
    {source : KExpr .anon}
    (hreach : ∀ x, KExpr.CheapBetaReach source x → support x)
    (it : InternTable .anon) (hwf : it.WF)
    (hcover : support.CoversIntern it) :
    (cheapBetaReduce source it).1 = KExpr.cheapBetaReduceResult source ∧
      (cheapBetaReduce source it).2.WF ∧
      support.CoversIntern (cheapBetaReduce source it).2 := by
  cases hplan : cheapBetaPlan? source with
  | none =>
      rw [cheapBetaReduce, hplan]
      change source = KExpr.cheapBetaReduceResult source ∧
        it.WF ∧ support.CoversIntern it
      simpa [KExpr.cheapBetaReduceResult, hplan] using
        (show source = source ∧ it.WF ∧ support.CoversIntern it from
          ⟨rfl, hwf, hcover⟩)
  | some plan =>
      have hchain : ∀ x,
          x ∈ cheapBetaChainList plan.base plan.trailing → support x :=
        fun x hx => hreach x (KExpr.CheapBetaReach.of_plan hplan hx)
      simpa [cheapBetaReduce, KExpr.cheapBetaReduceResult, hplan,
        CheapBetaPlan.result] using
        internAppChain_spec hcollision hchain it hwf hcover

/-- Finite callback resources for cheap beta at any supported recursive
inference result.  The source quantifier ranges over a finite `RunSupport`,
so this remains a finite closure obligation. -/
structure CheapBetaResources (support : RunSupport) : Prop where
  reach : ∀ {source : KExpr .anon}, support source → ∀ x,
    KExpr.CheapBetaReach source x → support x
  bounds : ∀ {source : KExpr .anon}, support source →
    WalkerRequest.Bounds (.cheapBeta source)

namespace CheapBetaResources

/-- Request-independent execution rule used when `source` is returned by a
recursive callback and therefore is not statically named in the enclosing
execution certificate. -/
theorem whnf_wf
    {support : RunSupport} (hresources : CheapBetaResources support)
    (hcollision : support.CollisionFree)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon}
    (hsource : support source) {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (cheapBetaReduce source))
      (fun result after =>
        result = KExpr.cheapBetaReduceResult source ∧
          support result ∧ InternUpdateFrame s after) := by
  have hreach := hresources.reach hsource
  apply TcM.WF.mono
    (TcM.runIntern_whnf_wf (fun it hwf hcover =>
      cheapBetaReduce_spec hcollision hreach it hwf hcover))
  · intro result after hpost
    rcases hpost with ⟨rfl, hframe⟩
    exact ⟨rfl, hreach _ (KExpr.CheapBetaReach.result source), hframe⟩
  · intro _ _ herror
    exact herror

end CheapBetaResources

namespace RunAssumptions

/-- The audited request-list form used by inference branches. -/
theorem cheapBeta_whnf_wf
    {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon}
    (hmem : WalkerRequest.cheapBeta source ∈ requests)
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (cheapBetaReduce source))
      (fun result after =>
        result = KExpr.cheapBetaReduceResult source ∧
          support result ∧ InternUpdateFrame s after) := by
  have hreach : ∀ x, KExpr.CheapBetaReach source x → support x :=
    (h.coverage.requests _ hmem).expr
  apply TcM.WF.mono
    (TcM.runIntern_whnf_wf (fun it hwf hcover =>
      cheapBetaReduce_spec h.collisionFree hreach it hwf hcover))
  · intro result after hpost
    rcases hpost with ⟨rfl, hframe⟩
    refine ⟨rfl, ?_, hframe⟩
    exact hreach _ (KExpr.CheapBetaReach.result source)
  · intro _ _ herror
    exact herror

end RunAssumptions

end Ix.Kernel
