import Ix.Tc.Verify.DefEq

/-!
# DefEq cache-policy branches

This module verifies cache exits whose state effects depend on cheap mode.
The semantic manager and guarded root-cache foundations live in
`Ix.Tc.Verify.DefEq`; the exhaustive cache shell will assemble these branches
before entering recursive comparison.
-/

namespace Ix.Tc

namespace RecM

/-- Exact positive full-cache hit while cheap mode is active.  Production
copies the validated result into the cheap partition, then joins the original
keys in the equivalence manager. -/
theorem isDefEq_fullHitCheapMode_true
    {methods : Methods .anon} {a b : KExpr .anon}
    {ctxAddr : Address} {s s1 s2 s3 s4 : TcState .anon}
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hhit : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s4 with env := {s4.env with
      defEqCheapCache := s4.env.defEqCheapCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final := by
  dsimp only
  unfold isDefEq
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}")) _ s = _
  unfold EStateM.bind
  rw [htrace]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}))
      _ s1 = _
  unfold EStateM.bind
  rw [hstats]
  simp only [haddr, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.defEqCtxKey a b) _ s2 = _
  unfold EStateM.bind
  rw [hctx]
  simp only
  change ReaderT.run
    ((liftM (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
  unfold EStateM.bind
  rw [hequiv]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hcheap]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hhit, if_true]
  rfl

/-- The cheap-mode copy of a positive full entry is justified by re-kinding
the same provenance.  Both the copied entry and final manager union preserve
the checker invariant. -/
theorem isDefEq_fullHitCheapMode_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    {ctxAddr : Address} {s s1 s2 s3 s4 : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hhit : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s4 with env := {s4.env with
      defEqCheapCache := s4.env.defEqCheapCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final ∧
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta final ∧
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb := by
  dsimp only
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1)
      htraceWf.1
  rw [hstats] at hstatsWf
  have hctxWf :=
    (TcM.defEqCtxKey_model_matches_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (support := support) model (Delta := Delta) (a := a) (b := b)
      (s := s2)) hstatsWf.1
  rw [hctx] at hctxWf
  have hrepresented := hctxWf.2.1.2.1
  have hequivWf :=
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hctxWf.1
  rw [hequiv] at hequivWf
  have hfullProvenance := hequivWf.1.1.caches.hit (.defEq hhit)
  have hmeaning := hfullProvenance.kernelDefEqMeaningCanonical
    haSupport hbSupport hrepresented
  have hsemantic := DefEqMeaning.of_translations theory hequivWf.1.2.1.wf
    ha hb hmeaning rfl
  have hcheapProvenance :
      CacheProvenance (kernelCacheSemantics model.keys trProj)
        (CacheAuthority.stable world) support
        (.defEq .cheap
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true) :=
    hfullProvenance.kernelDefEqRekind
  have hcached : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta
      {s4 with env := {s4.env with
        defEqCheapCache := s4.env.defEqCheapCache.insert
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true}} :=
    DefEqCacheUpdate.cheap_whnfStateInv hequivWf.1 hcheapProvenance
  have hrel : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ :=
    hfullProvenance.kernelDefEqEquivCanonical hcollision
      haSupport hbSupport
  have hfinal := hcached.addEquiv hrel
  exact ⟨isDefEq_fullHitCheapMode_true htrace hstats haddr hctx hequiv
    hcheap hhit, hfinal, hsemantic⟩

/-- Exact positive root/cheap-cache second-chance hit.  Both original
partitions are populated because cheap `true` is sound in full mode, then the
original keys are joined. -/
theorem isDefEq_rootCheapHit_true
    {methods : Methods .anon} {a b : KExpr .anon}
    {ctxAddr : Address} {aRoot bRoot : EqKey}
    {s s1 s2 s3 s4 s5 : TcState .anon}
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hcheapMiss : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hroots : TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em)) s4 = .ok (some aRoot, some bRoot) s5)
    (hchanged : (aRoot !=
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
      bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) = true)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hrootFullMiss : s5.env.defEqCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? = none)
    (hhit : s5.env.defEqCheapCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? =
        some true) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s5 with env := {s5.env with
      defEqCheapCache := s5.env.defEqCheapCache.insert cacheKey true
      defEqCache := s5.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final := by
  dsimp only
  unfold isDefEq
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}")) _ s = _
  unfold EStateM.bind
  rw [htrace]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}))
      _ s1 = _
  unfold EStateM.bind
  rw [hstats]
  simp only [haddr, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.defEqCtxKey a b) _ s2 = _
  unfold EStateM.bind
  rw [hctx]
  simp only
  change ReaderT.run
    ((liftM (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
  unfold EStateM.bind
  rw [hequiv]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hcheap]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hfullMiss, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hcheapMiss]
  change ReaderT.run
    ((liftM (TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em))) :
        RecM .anon (Option EqKey × Option EqKey)) >>= _)
      methods s4 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em))) _ s4 = _
  unfold EStateM.bind
  rw [hroots]
  simp only [hchanged, hscope, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s5 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s5 = .ok s5 s5 from rfl]
  simp [hrootFullMiss]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s5 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s5 = .ok s5 s5 from rfl]
  simp only [hhit, if_true]
  rfl

/-- Soundness of the guarded positive root/cheap branch.  Root paths and the
scope guard justify the hit; the copied cheap/full entries are constructed
from the resulting original-pair meaning before the manager is updated. -/
theorem isDefEq_rootCheapHit_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    {ctxAddr : Address} {aRoot bRoot : EqKey}
    {s s1 s2 s3 s4 s5 : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hcheapMiss : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hroots : TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em)) s4 = .ok (some aRoot, some bRoot) s5)
    (hchanged : (aRoot !=
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
      bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) = true)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hrootFullMiss : s5.env.defEqCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? = none)
    (hhit : s5.env.defEqCheapCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? =
        some true)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hreferences :
      (CacheEntry.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s5 with env := {s5.env with
      defEqCheapCache := s5.env.defEqCheapCache.insert cacheKey true
      defEqCache := s5.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final ∧
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta final ∧
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb := by
  dsimp only
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1)
      htraceWf.1
  rw [hstats] at hstatsWf
  have hctxWf :=
    (TcM.defEqCtxKey_model_matches_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (support := support) model (Delta := Delta) (a := a) (b := b)
      (s := s2)) hstatsWf.1
  rw [hctx] at hctxWf
  have hrepresented := hctxWf.2.1.2.1
  have hequivWf :=
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hctxWf.1
  rw [hequiv] at hequivWf
  have hrootsWf :=
    (TcM.withEquiv_findRootKeys_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s4) hequivWf.1
  rw [hroots] at hrootsWf
  have haPath := hrootsWf.2.1 aRoot rfl
  have hbPath := hrootsWf.2.2 bRoot rfl
  change DefEqKeyEquiv model.keys trProj (CacheAuthority.stable world) support
    ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ aRoot at haPath
  change DefEqKeyEquiv model.keys trProj (CacheAuthority.stable world) support
    ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ bRoot at hbPath
  have hrootProvenance := hrootsWf.1.1.caches.hit (.defEqCheap hhit)
  have hsemantic := hrootProvenance.kernelDefEqRootAcceptance
    theory hrootsWf.1.2.1.wf hcollision haPath hbPath hscope hrepresented
      haSupport hbSupport ha hb
  have horiginalMeaning :
      DefEqMeaning trProj world model.keys.uvars Delta a b true := by
    intro _
    exact ⟨va, vb, ha, hb, hsemantic⟩
  have hfullProvenance := model.defEqProvenance hcollision .full
    haSupport hbSupport hrepresented horiginalMeaning hreferences
  have hcheapProvenance :
      CacheProvenance (kernelCacheSemantics model.keys trProj)
        (CacheAuthority.stable world) support
        (.defEq .cheap
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true) :=
    hfullProvenance.kernelDefEqRekind
  have hcheapState :=
    DefEqCacheUpdate.cheap_whnfStateInv hrootsWf.1 hcheapProvenance
  have hbothStateRaw :=
    DefEqCacheUpdate.full_whnfStateInv hcheapState hfullProvenance
  have hbothState :
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta
        {s5 with env := {s5.env with
          defEqCheapCache := s5.env.defEqCheapCache.insert
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) true
          defEqCache := s5.env.defEqCache.insert
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) true}} := by
    simpa using hbothStateRaw
  have hrel : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ :=
    hfullProvenance.kernelDefEqEquivCanonical hcollision
      haSupport hbSupport
  have hfinal := hbothState.addEquiv hrel
  exact ⟨isDefEq_rootCheapHit_true htrace hstats haddr hctx hequiv hcheap
    hfullMiss hcheapMiss hroots hchanged hscope hrootFullMiss hhit,
    hfinal, hsemantic⟩

/-- Common semantic state transition for a positive guarded root hit when
cheap mode requires copying the answer into both original-key partitions. -/
theorem guardedRootHit_copyBoth
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    {kind : DefEqCacheKind} {Delta : KVLCtx}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    {ctxAddr : Address} {aRoot bRoot : EqKey} {s : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (haPath : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ aRoot)
    (hbPath : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ bRoot)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hrepresented : model.keys.Represents (max a.lbr b.lbr) ctxAddr Delta)
    (hroot : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq kind
        ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
          (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr) true))
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hreferences :
      (CacheEntry.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s with env := {s.env with
      defEqCheapCache := s.env.defEqCheapCache.insert cacheKey true
      defEqCache := s.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta final ∧
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb := by
  dsimp only
  have hsemantic := hroot.kernelDefEqRootAcceptance
    theory hI.2.1.wf hcollision haPath hbPath hscope hrepresented
      haSupport hbSupport ha hb
  have horiginalMeaning :
      DefEqMeaning trProj world model.keys.uvars Delta a b true := by
    intro _
    exact ⟨va, vb, ha, hb, hsemantic⟩
  have hfullProvenance := model.defEqProvenance hcollision .full
    haSupport hbSupport hrepresented horiginalMeaning hreferences
  have hcheapProvenance :
      CacheProvenance (kernelCacheSemantics model.keys trProj)
        (CacheAuthority.stable world) support
        (.defEq .cheap
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true) :=
    hfullProvenance.kernelDefEqRekind
  have hcheapState :=
    DefEqCacheUpdate.cheap_whnfStateInv hI hcheapProvenance
  have hbothStateRaw :=
    DefEqCacheUpdate.full_whnfStateInv hcheapState hfullProvenance
  have hbothState :
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta
        {s with env := {s.env with
          defEqCheapCache := s.env.defEqCheapCache.insert
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) true
          defEqCache := s.env.defEqCache.insert
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) true}} := by
    simpa using hbothStateRaw
  have hrel : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ :=
    hfullProvenance.kernelDefEqEquivCanonical hcollision
      haSupport hbSupport
  exact ⟨hbothState.addEquiv hrel, hsemantic⟩

/-- Exact positive root/full-cache hit observed in cheap mode.  As for a
root/cheap hit, production copies the positive answer into both original-key
partitions before joining the keys. -/
theorem isDefEq_rootFullHitCheapMode_true
    {methods : Methods .anon} {a b : KExpr .anon}
    {ctxAddr : Address} {aRoot bRoot : EqKey}
    {s s1 s2 s3 s4 s5 : TcState .anon}
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hcheapMiss : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hroots : TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em)) s4 = .ok (some aRoot, some bRoot) s5)
    (hchanged : (aRoot !=
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
      bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) = true)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hhit : s5.env.defEqCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? =
        some true) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s5 with env := {s5.env with
      defEqCheapCache := s5.env.defEqCheapCache.insert cacheKey true
      defEqCache := s5.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final := by
  dsimp only
  unfold isDefEq
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}")) _ s = _
  unfold EStateM.bind
  rw [htrace]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}))
      _ s1 = _
  unfold EStateM.bind
  rw [hstats]
  simp only [haddr, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.defEqCtxKey a b) _ s2 = _
  unfold EStateM.bind
  rw [hctx]
  simp only
  change ReaderT.run
    ((liftM (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
  unfold EStateM.bind
  rw [hequiv]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hcheap]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hfullMiss, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hcheapMiss]
  change ReaderT.run
    ((liftM (TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em))) :
        RecM .anon (Option EqKey × Option EqKey)) >>= _)
      methods s4 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em))) _ s4 = _
  unfold EStateM.bind
  rw [hroots]
  simp only [hchanged, hscope, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s5 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s5 = .ok s5 s5 from rfl]
  simp only [hhit, if_true]
  rfl

/-- Semantic acceptance of the positive root/full hit in cheap mode. -/
theorem isDefEq_rootFullHitCheapMode_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    {ctxAddr : Address} {aRoot bRoot : EqKey}
    {s s1 s2 s3 s4 s5 : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hcheapMiss : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hroots : TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em)) s4 = .ok (some aRoot, some bRoot) s5)
    (hchanged : (aRoot !=
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
      bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) = true)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hhit : s5.env.defEqCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? =
        some true)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hreferences :
      (CacheEntry.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s5 with env := {s5.env with
      defEqCheapCache := s5.env.defEqCheapCache.insert cacheKey true
      defEqCache := s5.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final ∧
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta final ∧
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb := by
  dsimp only
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1)
      htraceWf.1
  rw [hstats] at hstatsWf
  have hctxWf :=
    (TcM.defEqCtxKey_model_matches_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (support := support) model (Delta := Delta) (a := a) (b := b)
      (s := s2)) hstatsWf.1
  rw [hctx] at hctxWf
  have hrepresented := hctxWf.2.1.2.1
  have hequivWf :=
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hctxWf.1
  rw [hequiv] at hequivWf
  have hrootsWf :=
    (TcM.withEquiv_findRootKeys_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s4) hequivWf.1
  rw [hroots] at hrootsWf
  have haPath := hrootsWf.2.1 aRoot rfl
  have hbPath := hrootsWf.2.2 bRoot rfl
  change DefEqKeyEquiv model.keys trProj (CacheAuthority.stable world) support
    ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ aRoot at haPath
  change DefEqKeyEquiv model.keys trProj (CacheAuthority.stable world) support
    ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ bRoot at hbPath
  have hrootProvenance := hrootsWf.1.1.caches.hit (.defEq hhit)
  have htail := guardedRootHit_copyBoth model theory hcollision hrootsWf.1
    haPath hbPath hscope hrepresented hrootProvenance haSupport hbSupport
    ha hb hreferences
  exact ⟨isDefEq_rootFullHitCheapMode_true htrace hstats haddr hctx hequiv
    hcheap hfullMiss hcheapMiss hroots hchanged hscope hhit,
    htail.1, htail.2⟩

end RecM

end Ix.Tc
