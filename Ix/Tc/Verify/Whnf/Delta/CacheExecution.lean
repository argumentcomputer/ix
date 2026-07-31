import Ix.Tc.Verify.Whnf.Delta.StableCache

/-!
# Certified production unfold-cache execution

The public K1 cache contract is a WHNF overlay whose fallback owns delta
entries.  StableCache constructs the exact fallback provenance for a trusted body;
this module transports that provenance through the overlay and verifies both
physical paths of production's `unfoldConstValue`:

* a warm hit obtains its meaning from the existing certified cache entry;
* a cold hit runs the request-covered universe walker, constructs stable
  provenance from the exact declaration certificate, and only then writes the
  cache.

No arbitrary head/result write authority is used.
-/

namespace Ix.Tc

namespace CacheProvenance

/-- Install a certified delta entry underneath the public WHNF cache overlay.
For `.unfold`, `WhnfCacheValid` delegates definitionally to its fallback. -/
theorem underWhnf
    {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {key : Address} {value : KExpr .anon}
    (h : CacheProvenance
      (unfoldCacheSemantics keys.uvars trProj fallback)
      authority support (.unfold key value)) :
    CacheProvenance
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      authority support (.unfold key value) :=
  ⟨h.supported, h.references, h.valid⟩

/-- Project the delegated delta meaning from a public WHNF cache entry. -/
theorem fromWhnfUnfold
    {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {key : Address} {value : KExpr .anon}
    (h : CacheProvenance
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      authority support (.unfold key value)) :
    CacheProvenance
      (unfoldCacheSemantics keys.uvars trProj fallback)
      authority support (.unfold key value) :=
  ⟨h.supported, h.references, h.valid⟩

end CacheProvenance

namespace RecM

/-- Exact state, support, and Theory contract for production's
`unfoldConstValue` on one certified reducible constant.

The source translation supplies universe well-formedness and arity.  The run
census supplies reachability of the concrete instantiation request, while
the declaration-specific resource package supplies the level bounds omitted
by the generic request-bound relation. -/
theorem unfoldConstValue_trusted_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    (theory : StableWhnfTheory trProj world keys.uvars)
    (hreferences : TrustedReferences world support)
    {id : KId .anon} {concrete : KConst .anon}
    {ci : Lean4Lean.VDefVal} {kind : Ix.DefKind}
    {lvls : UInt64} {body : KExpr .anon}
    (trusted : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    (resources : DeltaInstantiationResources us body)
    (hheadSupport : support (.const id us info))
    (hrequest : WalkerRequest.instUniv body us ∈ requests)
    {Delta : KVLCtx} {headV : Lean4Lean.VExpr}
    (hhead : TrKExprS world.venv keys.uvars world.nameOf trProj Delta
      (.const id us info) headV)
    {s : TcState .anon} :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      trProj world support keys.uvars Delta s
      (unfoldConstValue (.const id us info) body us)
      (fun result _ =>
        support result ∧
          WhnfMeaning trProj world keys.uvars Delta
            (.const id us info) result) := by
  obtain ⟨_, hus, harity⟩ := trusted.sourceInputs hhead
  unfold unfoldConstValue
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = after)
    (RecM.WF.get fun _ => rfl)
  intro observed after hread
  subst observed
  cases hcache : after.env.unfoldCache[
      (.const id us info : KExpr .anon).addr]? with
  | some cached =>
      simp only
      apply RecM.WF.pure
      intro hI
      have hhit := hI.1.caches.hit (.unfold hcache)
      have hunfold := hhit.fromWhnfUnfold
      exact ⟨hhit.supported.2,
        hunfold.unfoldMeaning hheadSupport rfl hI.2.1.wf⟩
  | none =>
      simp only
      apply RecM.WF.bind <| RecM.WF.liftTcM <|
        TcM.instantiateUnivParams_whnf_wf hrun.collisionFree
          (hrun.coverage.instUniv hrequest)
      intro result afterInst hresult
      obtain ⟨hspec, hresultSupport⟩ := hresult
      apply RecM.WF.bind
        (Q₁ := fun _ next =>
          next =
            {afterInst with env := {afterInst.env with
              unfoldCache :=
                afterInst.env.unfoldCache.insert
                  (.const id us info : KExpr .anon).addr result}})
      · apply RecM.WF.modify
        · intro hI
          have hnew :=
            trusted.unfoldCacheProvenance (fallback := fallback)
              theory hrun.collisionFree
              hreferences hheadSupport hresultSupport hus harity hspec
              resources
          exact unfoldCacheInsert_whnfStateInv hI hnew.underWhnf
        · intro _
          rfl
      · intro _ next hnext
        subst next
        apply RecM.WF.pure
        intro hI
        exact ⟨hresultSupport,
          trusted.futureMeaning theory hus harity hspec resources
            VerifyWorld.LE.rfl hI.2.1.wf⟩

end RecM

end Ix.Tc
