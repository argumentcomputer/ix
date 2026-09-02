import Ix.Tc.Verify.Whnf.StructEta.RebuildTail
import Ix.Tc.Verify.Suffix

/-!
# Structural-core cache shell

RebuildTail closes the deepest successful struct-eta rebuild tail.  This slice
returns to the public structural driver and verifies its two cache partitions.
The existing outer-cache oracle deliberately owns only `whnfNoDelta`,
`whnfNoDeltaCheap`, and full `whnf`; structural core therefore gets a separate
collision-robust write interface for `whnfCore` and `whnfCoreCheap`.

The dispatcher theorem remains conditional on one exhaustive
`WhnfStep.WF` for `whnfCoreWithFlagsStep`.  Once that branch proof is
constructed, this file turns it into the complete public
`whnfCoreWithFlags` contract, including full/cheap hits, misses, transient
Nat bypass, and the legacy-variable prefix.
-/

namespace Ix.Tc

namespace RecM

/-- Collision-robust provenance for the two structural-core insertion sites.
An executed reduction at one source/context is not enough to justify a cache
entry: validity quantifies over every supported source sharing the expression
address and every context represented by the suffix digest. -/
structure WhnfCoreCacheWriteOracle (keys : WhnfContextKeys)
    (trProj : RawProjRel) (fallback : CacheSemantics)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  full : forall {Delta source key result s},
    support source ->
    support result ->
    keys.Matches trProj world s Delta source key ->
    WhnfMeaning trProj world keys.uvars Delta source result ->
    CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfCore key result)
  cheap : forall {Delta source key result s},
    support source ->
    support result ->
    keys.Matches trProj world s Delta source key ->
    WhnfMeaning trProj world keys.uvars Delta source result ->
    CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfCoreCheap key result)

namespace WhnfCoreCacheWriteOracle

/-- Closed expressions need no suffix transport.  Finite expression-address
collision freedom identifies every supported source at the key, while direct
reference authorization remains explicit for the generated cache entry. -/
theorem closed
    {uvars : Nat} {trProj : RawProjRel} {fallback : CacheSemantics}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    (hreferences : forall {kind key source result},
      (kind = .whnfCore \/ kind = .whnfCoreCheap) ->
      support source -> support result -> source.addr = key.1 ->
      (CacheEntry.expr kind key result).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    WhnfCoreCacheWriteOracle (WhnfContextKeys.closed uvars) trProj fallback
      world support := by
  have build : forall {kind : ExprCacheKind} {Delta source key result s},
      (kind = .whnfCore \/ kind = .whnfCoreCheap) ->
      support source ->
      support result ->
      (WhnfContextKeys.closed uvars).Matches trProj world s Delta source key ->
      WhnfMeaning trProj world uvars Delta source result ->
      CacheProvenance
        (whnfCacheSemantics (WhnfContextKeys.closed uvars) trProj fallback)
        (CacheAuthority.stable world) support (.expr kind key result) := by
    intro kind Delta source key result s hkind hsource hresult hmatch hmeaning
    have hDelta : Delta = [] := hmatch.2.1.2.2
    subst Delta
    refine ⟨⟨⟨source, hsource, hmatch.sourceAddr⟩, hresult⟩,
      hreferences hkind hsource hresult hmatch.sourceAddr, ?_⟩
    have his : kind.IsWhnf := by
      rcases hkind with hkind | hkind
      · subst kind
        exact .whnfCore
      · subst kind
        exact .whnfCoreCheap
    have htransport : forall other, support other -> other.addr = key.1 ->
        forall Delta,
          (WhnfContextKeys.closed uvars).Represents other.lbr key.2 Delta ->
          other.ContextScoped Delta ->
          WhnfMeaning trProj world uvars Delta other result := by
      intro other hother haddr Delta hrepresented _hscoped
      have heq : source = other := by
        have herase := hcollision.expr hsource hother
          (hmatch.sourceAddr.trans haddr.symm)
        simpa only [KExpr.eraseMeta_anon] using herase
      subst other
      have hDelta : Delta = [] := hrepresented.2.2
      subst Delta
      exact hmeaning
    cases his <;> exact htransport
  refine ⟨?_, ?_⟩
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inl rfl) hsource hresult hmatch hmeaning
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inr rfl) hsource hresult hmatch hmeaning

end WhnfCoreCacheWriteOracle

/-- Conditional Hoare closure for the keyed structural-core body.  The
bounded semantic loop is supplied by `WhnfCoreTrace.uncached_wf`; this theorem
discharges the actual full/cheap cache control flow, including transient Nat
bypass and provenance-certified writes. -/
theorem whnfCoreWithFlagsNonLeaf_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {flags : WhnfFlags}
    {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta id (fun cur => whnfCoreWithFlagsStep cur flags)
      stepError)
    (hwrites : WhnfCoreCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfCoreWithFlagsNonLeaf source flags)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hinner : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (whnfCoreWithFlagsUncached source flags)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => RecM.WF.mono
      (WhnfCoreTrace.uncached_wf theory hstep (s := s0) hsupport hsource)
      (fun _ _ h => h) (fun _ _ _ => trivial)
  unfold whnfCoreWithFlagsNonLeaf
  apply RecM.WF.bind
    (Q₁ := fun key _ => keys.Matches trProj world s Delta source key)
  · apply RecM.WF.liftTcM
    exact TcM.WF.mono
      (TcM.whnfKey_matches_wf
        (fun key after hctx hrun => hkeyRep s key after hctx hrun))
      (fun key _ h => h.1) (fun _ _ h => h)
  · intro key s1 hmatch
    apply RecM.WF.bind (htransient s1)
    intro transient s2 _
    cases hfull : flags.isFull with
    | true =>
        simp only [if_true]
        cases transient with
        | true =>
            simpa using hinner s2
        | false =>
            simp only [Bool.not_false, if_true]
            apply RecM.WF.bind
              (Q₁ := fun observed after => observed = s2 ∧ after = s2)
              (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
            intro observed after hread
            rcases hread with ⟨hObserved, hAfter⟩
            subst observed
            subst after
            let found := s2.env.whnfCoreCache[key]?
            cases hfound : found with
            | some cached =>
                have hcache : s2.env.whnfCoreCache[key]? = some cached := by
                  simpa [found] using hfound
                simp only [hcache]
                exact RecM.WF.pure fun hI2 => by
                  have hcached :=
                    (hI2.1.caches.hit (.whnfCore hcache)).supported.2
                  have hmeaning := hI2.1.caches.whnfHitOfMatches
                    (.whnfCore hcache) .whnfCore hsupport hmatch
                    hsource.contextScoped
                  have hstart := WhnfPost.refl hsource
                    (theory.exprWF hI2.2.1 hsource)
                  exact ⟨hcached,
                    hstart.transMeaning theory hI2.2.1.wf hmeaning⟩
            | none =>
                have hcache : s2.env.whnfCoreCache[key]? = none := by
                  simpa [found] using hfound
                simp only [hcache]
                apply RecM.WF.bind (hinner s2)
                intro result s3 hpost
                let next := {s3 with env := {s3.env with
                  whnfCoreCache := s3.env.whnfCoreCache.insert key result}}
                apply RecM.WF.bind (Q₁ := fun _ after => after = next)
                · refine RecM.WF.modify (f := fun st =>
                    {st with env := {st.env with whnfCoreCache :=
                      st.env.whnfCoreCache.insert key result}}) ?_
                    (fun _ => rfl)
                  intro hI3
                  exact WhnfCoreCacheUpdate.full_whnfStateInv hI3
                    (hwrites.full hsupport hpost.1 hmatch
                      (hpost.2.meaning hsource))
                · intro _ s4 hs4
                  subst s4
                  exact RecM.WF.pure fun _ => hpost
    | false =>
        cases transient with
        | true =>
            simpa using hinner s2
        | false =>
            simp only [Bool.not_false, if_true]
            apply RecM.WF.bind
              (Q₁ := fun observed after => observed = s2 ∧ after = s2)
              (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
            intro observed after hread
            rcases hread with ⟨hObserved, hAfter⟩
            subst observed
            subst after
            let found := s2.env.whnfCoreCheapCache[key]?
            cases hfound : found with
            | some cached =>
                have hcache : s2.env.whnfCoreCheapCache[key]? = some cached := by
                  simpa [found] using hfound
                simp only [hcache]
                exact RecM.WF.pure fun hI2 => by
                  have hcached :=
                    (hI2.1.caches.hit (.whnfCoreCheap hcache)).supported.2
                  have hmeaning := hI2.1.caches.whnfHitOfMatches
                    (.whnfCoreCheap hcache) .whnfCoreCheap hsupport hmatch
                    hsource.contextScoped
                  have hstart := WhnfPost.refl hsource
                    (theory.exprWF hI2.2.1 hsource)
                  exact ⟨hcached,
                    hstart.transMeaning theory hI2.2.1.wf hmeaning⟩
            | none =>
                have hcache : s2.env.whnfCoreCheapCache[key]? = none := by
                  simpa [found] using hfound
                simp only [hcache]
                apply RecM.WF.bind (hinner s2)
                intro result s3 hpost
                let next := {s3 with env := {s3.env with
                  whnfCoreCheapCache :=
                    s3.env.whnfCoreCheapCache.insert key result}}
                apply RecM.WF.bind (Q₁ := fun _ after => after = next)
                · refine RecM.WF.modify (f := fun st =>
                    {st with env := {st.env with whnfCoreCheapCache :=
                      st.env.whnfCoreCheapCache.insert key result}}) ?_
                    (fun _ => rfl)
                  intro hI3
                  exact WhnfCoreCacheUpdate.cheap_whnfStateInv hI3
                    (hwrites.cheap hsupport hpost.1 hmatch
                      (hpost.2.meaning hsource))
                · intro _ s4 hs4
                  subst s4
                  exact RecM.WF.pure fun _ => hpost

/-- Conditional closure of the actual public structural dispatcher for every
expression form.  Immediate leaves are reflexive; a legacy variable performs
the proved read-only let test and enters the same keyed shell only when it is
actually zeta-reducible. -/
theorem whnfCoreWithFlags_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {flags : WhnfFlags}
    {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta id (fun cur => whnfCoreWithFlagsStep cur flags)
      stepError)
    (hwrites : WhnfCoreCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfCoreWithFlags source flags)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hreflexive : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0 (pure source)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => RecM.WF.pure fun hI =>
      ⟨hsupport, WhnfPost.refl hsource (theory.exprWF hI.2.1 hsource)⟩
  have hshell : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0 (whnfCoreWithFlagsNonLeaf source flags)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => whnfCoreWithFlagsNonLeaf_wf theory hkeyRep htransient hstep
      hwrites hsupport (s := s0) hsource
  cases source with
  | sort u info =>
      simpa [whnfCoreWithFlags] using hreflexive s
  | all name bi ty body info =>
      simpa [whnfCoreWithFlags] using hreflexive s
  | lam name bi ty body info =>
      simpa [whnfCoreWithFlags] using hreflexive s
  | nat value blob info =>
      simpa [whnfCoreWithFlags] using hreflexive s
  | str value blob info =>
      simpa [whnfCoreWithFlags] using hreflexive s
  | const id us info =>
      simpa [whnfCoreWithFlags] using hreflexive s
  | fvar id name info =>
      simpa [whnfCoreWithFlags] using hshell s
  | app f arg info =>
      simpa [whnfCoreWithFlags] using hshell s
  | letE name ty value body nondep info =>
      simpa [whnfCoreWithFlags] using hshell s
  | prj id field value info =>
      simpa [whnfCoreWithFlags] using hshell s
  | var idx name info =>
      unfold whnfCoreWithFlags
      apply RecM.WF.bind
      · apply RecM.WF.liftTcM
        exact TcM.isLetVar_wf idx s
      · intro isLet s1 hs1
        subst s1
        cases isLet with
        | false =>
            simpa using hreflexive s
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false,
              pure_bind]
            exact hshell s

end RecM

namespace WhnfSuffixModel

/-- Suffix transport plus finite expression collision freedom constructs the
two structural-core write rules.  This is the open-context counterpart of
`WhnfCoreCacheWriteOracle.closed`; it relies on the same operational suffix
model already consumed by the three outer WHNF cache partitions. -/
theorem coreCacheWriteOracle
    {trProj : RawProjRel} {fallback : CacheSemantics}
    {world : VerifyWorld} {support : RunSupport}
    (model : WhnfSuffixModel trProj world)
    (hcollision : support.CollisionFree)
    (hreferences : ∀ {kind key source result},
      (kind = .whnfCore ∨ kind = .whnfCoreCheap) →
      support source → support result → source.addr = key.1 →
      (CacheEntry.expr kind key result).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    RecM.WhnfCoreCacheWriteOracle model.keys trProj fallback world support := by
  have build : ∀ {kind : ExprCacheKind} {Delta source key result s},
      (kind = .whnfCore ∨ kind = .whnfCoreCheap) →
      support source →
      support result →
      model.keys.Matches trProj world s Delta source key →
      WhnfMeaning trProj world model.keys.uvars Delta source result →
      CacheProvenance
        (whnfCacheSemantics model.keys trProj fallback)
        (CacheAuthority.stable world) support (.expr kind key result) := by
    intro kind Delta source key result s hkind hsource hresult hmatch hmeaning
    refine ⟨⟨⟨source, hsource, hmatch.sourceAddr⟩, hresult⟩,
      hreferences hkind hsource hresult hmatch.sourceAddr, ?_⟩
    have his : kind.IsWhnf := by
      rcases hkind with hkind | hkind
      · subst kind
        exact .whnfCore
      · subst kind
        exact .whnfCoreCheap
    have hvalid : ∀ other, support other → other.addr = key.1 →
        ∀ Delta', model.keys.Represents other.lbr key.2 Delta' →
          other.ContextScoped Delta' →
          WhnfMeaning trProj world model.keys.uvars Delta' other result := by
      intro other hother haddr Delta' hrepresented _hscoped
      have heq : source = other := by
        have herase := hcollision.expr hsource hother
          (hmatch.sourceAddr.trans haddr.symm)
        simpa only [KExpr.eraseMeta_anon] using herase
      subst other
      exact model.transport hmatch.2.1 hrepresented hmeaning
    cases his <;> exact hvalid
  refine ⟨?_, ?_⟩
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inl rfl) hsource hresult hmatch hmeaning
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inr rfl) hsource hresult hmatch hmeaning

end WhnfSuffixModel

end Ix.Tc
