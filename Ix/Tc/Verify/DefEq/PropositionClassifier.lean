import Ix.Tc.Verify.DefEq.ProofIrrelevance

/-!
# Memoized proposition classification

This module verifies the production `isPropType` implementation used by
proof irrelevance.  Cache hits are interpreted through the joint K2 suffix
model.  Cache misses infer the queried expression, normalize its inferred
type with the direct K1 reducer, and install only a provenance-certified
classification.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Resources needed by the concrete proposition classifier.  Direct WHNF
is the already-closed K1 reducer; inference remains a predecessor-table edge
until K2 ties the recursive method-table knot. -/
structure PropositionClassifierContext
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport) where
  model : KernelSuffixModel trProj world
  collisionFree : support.CollisionFree
  theory : WhnfTheory trProj world model.keys.uvars
  whnf : DirectWhnf.WFAt (kernelCacheSemantics model.keys trProj) trProj
    world support model.keys.uvars
  references : forall {source : KExpr .anon} {id : KId .anon},
    support source -> source.References id -> world.trusted id

namespace PropositionClassifierContext

/-- The proposition-cache entry depends only on direct constant roots of the
queried expression, all of which are trusted by the run context. -/
private theorem cacheReferences
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (context : PropositionClassifierContext trProj world support)
    {source : KExpr .anon} {ctxAddr : Address} {answer : Bool}
    (hsource : support source) :
    (CacheEntry.isProp (source.addr, ctxAddr) answer).ReferencesAuthorized
      (CacheAuthority.stable world) support := by
  intro id href
  apply Or.inl
  obtain ⟨other, hother, haddr, hreference⟩ := href
  have hsame : other = source := by
    have herase := context.collisionFree.expr hother hsource haddr
    simpa only [KExpr.eraseMeta_anon] using herase
  subst other
  exact context.references hsource hreference

end PropositionClassifierContext

namespace RecM

/-- If direct WHNF exposes an inferred type as `Sort 0`, transport the
original typing derivation through both the quotient translation and the
reduction equality. -/
private theorem hasTypeSortZero_of_whnf
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {sourceV sortCoreV sortV : VExpr} {u : KUniv .anon}
    {info : ExprInfo .anon}
    (hsourceType : world.venv.HasType uvars Delta.toCtx sourceV sortV)
    (hsortEq : world.venv.IsDefEqU uvars Delta.toCtx sortCoreV sortV)
    (hwhnf : WhnfPost trProj world uvars Delta sortCoreV (.sort u info))
    (hzero : u.isZero = true) :
    world.venv.HasType uvars Delta.toCtx sourceV (.sort .zero) := by
  obtain ⟨reducedV, hreduced, hsortReduced⟩ := hwhnf
  cases hreduced with
  | sort hlevel =>
      have htype := hsourceType.defeqU_r world.venvWF hDelta <|
        hsortEq.symm.trans world.venvWF hDelta hsortReduced
      simpa only [KUniv.toVLevel_of_isZero hzero] using htype

/-- The uncached classifier is conservative on every failure and non-sort
result.  Its sole positive case proves that the original concrete query has
Theory type `Sort 0`. -/
private theorem classifyPropTypeUncached_wf
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (context : PropositionClassifierContext trProj world support)
    {Delta : KVLCtx} {state : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv context.model.keys.uvars world.nameOf
      trProj Delta source sourceV) :
    RecM.WF .noAccel
      (kernelCacheSemantics context.model.keys trProj) trProj world support
      context.model.keys.uvars Delta state
      (classifyPropTypeUncached source)
      (fun answer _ => IsPropMeaning trProj world context.model.keys.uvars
        Delta source answer) := by
  unfold classifyPropTypeUncached
  apply RecM.WF.bind
    (tryOptionalInferOnlyCall_wf hsourceSupport hsource)
  intro inferred afterInfer hinferred
  cases inferred with
  | none =>
      simp only
      exact RecM.WF.pure fun _ => IsPropMeaning.false
  | some sort =>
      rcases hinferred with
        ⟨hsortSupport, sortV, hsortTranslation, hsourceType⟩
      obtain ⟨sortCoreV, hsortCore, hsortEq⟩ := hsortTranslation
      simp only
      apply RecM.WF.bind
        (tryOptional_wf (RecM.WF.withInv <|
          context.whnf hsortSupport hsortCore))
      intro reduced afterWhnf hreduced
      cases reduced with
      | none =>
          simp only
          exact RecM.WF.pure fun _ => IsPropMeaning.false
      | some reduced =>
          rcases hreduced with ⟨hIWhnf, _hreducedSupport, hwhnfPost⟩
          cases reduced with
          | sort u info =>
              simp only
              cases hzero : u.isZero with
              | false =>
                  exact RecM.WF.pure fun _ => IsPropMeaning.false
              | true =>
                  exact RecM.WF.pure fun _ _ =>
                    ⟨sourceV, hsource,
                      hasTypeSortZero_of_whnf hIWhnf.2.1.wf hsourceType
                        hsortEq hwhnfPost hzero⟩
          | var | fvar | const | app | lam | all | letE | prj | nat | str =>
              simp only
              exact RecM.WF.pure fun _ => IsPropMeaning.false

/-- The production memoized proposition classifier satisfies the exact
positive-result contract consumed by proof irrelevance. -/
theorem isPropType_wf
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (context : PropositionClassifierContext trProj world support) :
    IsPropType.WFAt .noAccel
      (kernelCacheSemantics context.model.keys trProj) trProj world support
      context.model.keys.uvars := by
  intro Delta state source sourceV hsourceSupport hsource
  obtain ⟨sourceCoreV, hsourceCore, hsourceEq⟩ := hsource
  unfold isPropType
  apply RecM.WF.bind
    (RecM.WF.liftTcM <| TcM.ctxAddrForLbr_model_matches_wf context.model)
  intro ctxAddr afterKey hkey
  rcases hkey with ⟨hrepresented, _hkeyFrame⟩
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = afterKey ∧ after = afterKey)
    (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
  intro observed afterRead hread
  rcases hread with ⟨hobserved, hafterRead⟩
  subst observed
  subst afterRead
  let found := afterKey.env.isPropCache[(source.addr, ctxAddr)]?
  cases hfound : found with
  | some cached =>
      have hhit : afterKey.env.isPropCache[(source.addr, ctxAddr)]? =
          some cached := by
        simpa [found] using hfound
      simp only [hhit]
      exact RecM.WF.pure fun
          (hI : WhnfStateInv .noAccel
            (kernelCacheSemantics context.model.keys trProj) trProj world
            support context.model.keys.uvars Delta afterKey) => by
        intro htrue
        have hprovenance := hI.1.caches.hit (.isProp hhit)
        have hmeaning := hprovenance.kernelIsPropMeaning hsourceSupport rfl
          hrepresented
        have hcoreType := IsPropMeaning.of_translation context.theory
          hI.2.1.wf hsourceCore hmeaning htrue
        exact hcoreType.defeqU_l world.venvWF hI.2.1.wf hsourceEq
  | none =>
      have hmiss : afterKey.env.isPropCache[(source.addr, ctxAddr)]? =
          none := by
        simpa [found] using hfound
      simp only [hmiss, pure_bind]
      apply RecM.WF.bind
        (Q₁ := fun answer _ => IsPropMeaning trProj world
          context.model.keys.uvars Delta source answer)
        (classifyPropTypeUncached_wf context hsourceSupport hsourceCore)
      intro answer afterClassify hmeaning
      have hprovenance := context.model.isPropProvenance
        context.collisionFree hsourceSupport hrepresented hmeaning
        (context.cacheReferences hsourceSupport)
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (fun hI => IsPropCacheUpdate.whnfStateInv hI hprovenance)
          (fun _ => trivial)
      · intro _ afterWrite _
        exact RecM.WF.pure fun
            (hI : WhnfStateInv .noAccel
              (kernelCacheSemantics context.model.keys trProj) trProj world
              support context.model.keys.uvars Delta afterWrite) => by
          intro htrue
          have hcoreType := IsPropMeaning.of_translation context.theory
            hI.2.1.wf hsourceCore hmeaning htrue
          exact hcoreType.defeqU_l world.venvWF hI.2.1.wf hsourceEq

/-- Concrete proof irrelevance, with the memoized classifier discharged by
the production cache proof above. -/
theorem tryProofIrrel_classifier_wf
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (context : PropositionClassifierContext trProj world support)
    {Delta : KVLCtx} {state : TcState .anon}
    {a b : KExpr .anon} {aV bV : VExpr}
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv context.model.keys.uvars world.nameOf trProj
      Delta a aV)
    (hb : TrKExprS world.venv context.model.keys.uvars world.nameOf trProj
      Delta b bV) :
    RecM.WF .noAccel
      (kernelCacheSemantics context.model.keys trProj) trProj world support
      context.model.keys.uvars Delta state (tryProofIrrel a b)
      (fun answer _ => answer = true ->
        world.venv.IsDefEqU context.model.keys.uvars Delta.toCtx aV bV) :=
  tryProofIrrel_wf (isPropType_wf context) haSupport hbSupport ha hb

end RecM

end Ix.Tc
