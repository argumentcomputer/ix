import Ix.Tc.Verify.DefEq.CacheBranches

/-!
# DefEq cache shell

The production entry point exposes two exact control-flow seams.
`isDefEqAfterDirectCacheMiss` contains the guarded equivalence-root probe;
`isDefEqAfterRootCacheMiss` contains the charged recursive comparison and
final cache write. The bridge theorems below connect the entry-point prefix
to those production-owned functions.
-/

namespace Ix.Tc

namespace RecM

/-- Once the full partition misses outside cheap mode, the remaining concrete
entry-point program is exactly `isDefEqAfterDirectCacheMiss`. -/
theorem isDefEq_directMiss_noncheap
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
    (hcheap : (s4.cheapRecursionDepth > 0) = false)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none) :
    (isDefEq a b).run methods s =
      (isDefEqAfterDirectCacheMiss a b ctxAddr
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) false).run methods s4 := by
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
  simp only [hfullMiss, Bool.false_eq_true, if_false]
  rfl

/-- In cheap mode, once both direct partitions miss, the same exact root
probe remains with the captured cheap policy bit set. -/
theorem isDefEq_directMiss_cheap
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
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hcheapMiss : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none) :
    (isDefEq a b).run methods s =
      (isDefEqAfterDirectCacheMiss a b ctxAddr
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true).run methods s4 := by
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
  rfl

namespace DefEqInner

/-- Semantic contract still owed by the recursive DefEq tiers.  Separating
it from the cache shell keeps the latter independent of branch order inside
`isDefEqInner`. -/
def WF (layer : WhnfLayer) (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (model : KernelSuffixModel trProj world) : Prop :=
  ∀ {Delta s a b va vb},
    support a → support b →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb →
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s (isDefEqInner a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb)

end DefEqInner

/-- The simultaneous cheap-result write used by production is the
composition of the already-certified cheap write and, only for `true`, its
sound promotion to the full partition. -/
private theorem cheapResult_whnfStateInv
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address × Address} {answer : Bool}
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (hcheap : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support (.defEq .cheap key answer))
    (hfull : answer = true →
      CacheProvenance (kernelCacheSemantics model.keys trProj)
        (CacheAuthority.stable world) support (.defEq .full key true)) :
    WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta
      {s with env := {s.env with
        defEqCheapCache := s.env.defEqCheapCache.insert key answer
        defEqCache := if answer then s.env.defEqCache.insert key true
          else s.env.defEqCache}} := by
  cases answer with
  | false =>
      simpa using DefEqCacheUpdate.cheap_whnfStateInv hI hcheap
  | true =>
      have hcheapState := DefEqCacheUpdate.cheap_whnfStateInv hI hcheap
      have hboth := DefEqCacheUpdate.full_whnfStateInv hcheapState (hfull rfl)
      simpa using hboth

/-- A full root-cache result is always copied to the original full key and,
when the caller is already in cheap mode, to the cheap partition as well. -/
private theorem fullResult_whnfStateInv
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address × Address} {answer cheapMode : Bool}
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (hfull : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support (.defEq .full key answer)) :
    WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta
      {s with env := {s.env with
        defEqCache := s.env.defEqCache.insert key answer
        defEqCheapCache := if cheapMode then
            s.env.defEqCheapCache.insert key answer
          else s.env.defEqCheapCache}} := by
  cases cheapMode with
  | false =>
      simpa using DefEqCacheUpdate.full_whnfStateInv hI hfull
  | true =>
      have hfullState := DefEqCacheUpdate.full_whnfStateInv hI hfull
      have hcheap : CacheProvenance
          (kernelCacheSemantics model.keys trProj)
          (CacheAuthority.stable world) support (.defEq .cheap key answer) :=
        hfull.kernelDefEqRekind
      have hboth := DefEqCacheUpdate.cheap_whnfStateInv hfullState hcheap
      simpa using hboth

/-- Interpret one guarded root-cache answer at the caller's original pair.
Negative answers need only rejection-safe provenance; positive answers must
compose both manager paths with the cached root equality. -/
private theorem guardedRootResult
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    {kind : DefEqCacheKind} {answer : Bool} {Delta : KVLCtx}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    {ctxAddr : Address} {aRoot bRoot : EqKey} {s : TcState .anon}
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
    (hctx : model.keys.Represents (max a.lbr b.lbr) ctxAddr Delta)
    (hroot : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq kind
        ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
          (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr) answer))
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hreferences :
      (CacheEntry.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    CacheProvenance (kernelCacheSemantics model.keys trProj)
        (CacheAuthority.stable world) support
        (.defEq .full
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) answer) ∧
      (answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  cases answer with
  | false =>
      refine ⟨model.defEqProvenance hcollision .full haSupport hbSupport
        hctx DefEqMeaning.false hreferences, ?_⟩
      intro h
      contradiction
  | true =>
      have hsemantic := hroot.kernelDefEqRootAcceptance theory hI.2.1.wf
        hcollision haPath hbPath hscope hctx haSupport hbSupport ha hb
      have hmeaning : DefEqMeaning trProj world model.keys.uvars
          Delta a b true := by
        intro _
        exact ⟨va, vb, ha, hb, hsemantic⟩
      exact ⟨model.defEqProvenance hcollision .full haSupport hbSupport
        hctx hmeaning hreferences, fun _ => hsemantic⟩

/-- State and semantic contract for a root result sourced from the full
partition. -/
private theorem applyFullRootResult_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr} {ctxAddr : Address}
    {answer cheapMode : Bool}
    (hcollision : support.CollisionFree)
    (haSupport : support a) (hbSupport : support b)
    (hfull : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer))
    (hsemantic : answer = true →
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (do
        modify fun st => {st with env := {st.env with
          defEqCache := st.env.defEqCache.insert
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) answer
          defEqCheapCache := if cheapMode then
              st.env.defEqCheapCache.insert
                ((canonicalPair a.addr b.addr).1,
                  (canonicalPair a.addr b.addr).2, ctxAddr) answer
            else st.env.defEqCheapCache}}
        if answer then
          modify fun st => {st with
            equivManager := st.equivManager.addEquiv
              ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
              ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩}
        return answer)
      (fun result _ => result = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  cases answer with
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (fun hI => fullResult_whnfStateInv hI hfull)
          (fun _ => trivial)
      · intro _ _ _
        exact RecM.WF.pure fun _ h => by contradiction
  | true =>
      simp only [if_true]
      have hrel := hfull.kernelDefEqEquivCanonical hcollision
        haSupport hbSupport
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (fun hI => fullResult_whnfStateInv hI hfull)
          (fun _ => trivial)
      · intro _ _ _
        apply RecM.WF.bind (Q₁ := fun _ _ => True)
        · exact RecM.WF.modify
            (fun hI => hI.addEquiv hrel)
            (fun _ => trivial)
        · intro _ _ _
          exact RecM.WF.pure fun _ _ => hsemantic rfl

/-- State and semantic contract for a root result sourced from the cheap
partition. A positive cheap answer is promoted to full before union. -/
private theorem applyCheapRootResult_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr} {ctxAddr : Address}
    {answer : Bool}
    (hcollision : support.CollisionFree)
    (haSupport : support a) (hbSupport : support b)
    (hfull : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer))
    (hsemantic : answer = true →
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (do
        modify fun st => {st with env := {st.env with
          defEqCheapCache := st.env.defEqCheapCache.insert
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) answer
          defEqCache := if answer then
              st.env.defEqCache.insert
                ((canonicalPair a.addr b.addr).1,
                  (canonicalPair a.addr b.addr).2, ctxAddr) true
            else st.env.defEqCache}}
        if answer then
          modify fun st => {st with
            equivManager := st.equivManager.addEquiv
              ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
              ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩}
        return answer)
      (fun result _ => result = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  have hcheap : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq .cheap
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer) :=
    hfull.kernelDefEqRekind
  cases answer with
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (fun hI => cheapResult_whnfStateInv hI hcheap
            (fun h => by contradiction))
          (fun _ => trivial)
      · intro _ _ _
        exact RecM.WF.pure fun _ h => by contradiction
  | true =>
      simp only [if_true]
      have hrel := hfull.kernelDefEqEquivCanonical hcollision
        haSupport hbSupport
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (fun hI => cheapResult_whnfStateInv hI hcheap (fun _ => hfull))
          (fun _ => trivial)
      · intro _ _ _
        apply RecM.WF.bind (Q₁ := fun _ _ => True)
        · exact RecM.WF.modify
            (fun hI => hI.addEquiv hrel)
            (fun _ => trivial)
        · intro _ _ _
          exact RecM.WF.pure fun _ _ => hsemantic rfl

section DirectFullHit

set_option maxHeartbeats 800000

/-- A direct full-cache hit optionally copies into the cheap partition, then
joins the original keys only when the cached answer is positive. -/
private theorem applyDirectFullHit_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr} {ctxAddr : Address}
    {answer cheapMode : Bool}
    (hcollision : support.CollisionFree)
    (haSupport : support a) (hbSupport : support b)
    (hfull : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer))
    (hsemantic : answer = true →
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (do
        if cheapMode then
          modify fun st => {st with env := {st.env with
            defEqCheapCache := st.env.defEqCheapCache.insert
              ((canonicalPair a.addr b.addr).1,
                (canonicalPair a.addr b.addr).2, ctxAddr) answer}}
        if answer then
          modify fun st => {st with
            equivManager := st.equivManager.addEquiv
              ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
              ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩}
        return answer)
      (fun result _ => result = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  have hcheap : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq .cheap
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer) :=
    hfull.kernelDefEqRekind
  cases cheapMode with
  | false =>
      cases answer with
      | false =>
          simp only [Bool.false_eq_true, if_false, pure_bind]
          exact RecM.WF.pure fun _ h => by contradiction
      | true =>
          simp only [Bool.false_eq_true, if_false, if_true, pure_bind]
          have hrel := hfull.kernelDefEqEquivCanonical hcollision
            haSupport hbSupport
          apply RecM.WF.bind (Q₁ := fun _ _ => True)
          · exact RecM.WF.modify
              (Q := fun _ _ => True)
              (f := fun st : TcState .anon => {st with
                equivManager := st.equivManager.addEquiv
                  ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
                  ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩})
              (fun (hI : WhnfStateInv layer
                  (kernelCacheSemantics model.keys trProj) trProj world
                  support model.keys.uvars Delta s) =>
                hI.addEquiv hrel)
              (fun _ => trivial)
          · intro _ _ _
            exact RecM.WF.pure fun _ _ => hsemantic rfl
  | true =>
      cases answer with
      | false =>
          simp only [Bool.false_eq_true, if_false, if_true, pure_bind]
          apply RecM.WF.bind (Q₁ := fun _ _ => True)
          · exact RecM.WF.modify
              (fun hI => DefEqCacheUpdate.cheap_whnfStateInv hI hcheap)
              (fun _ => trivial)
          · intro _ _ _
            exact RecM.WF.pure fun _ h => by contradiction
      | true =>
          simp only [if_true]
          have hrel := hfull.kernelDefEqEquivCanonical hcollision
            haSupport hbSupport
          apply RecM.WF.bind (Q₁ := fun _ _ => True)
          · exact RecM.WF.modify
              (fun hI => DefEqCacheUpdate.cheap_whnfStateInv hI hcheap)
              (fun _ => trivial)
          · intro _ _ _
            apply RecM.WF.bind (Q₁ := fun _ _ => True)
            · exact RecM.WF.modify
                (f := fun st : TcState .anon => {st with
                  equivManager := st.equivManager.addEquiv
                    ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
                    ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩})
                (fun hI => hI.addEquiv hrel)
                (fun _ => trivial)
            · intro _ _ _
              exact RecM.WF.pure fun _ _ => hsemantic rfl

end DirectFullHit

/-- A direct cheap-cache hit promotes only a positive answer, combining the
full-cache write and justified union in the production record update. -/
private theorem applyDirectCheapHit_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr} {ctxAddr : Address}
    {answer : Bool}
    (hcollision : support.CollisionFree)
    (haSupport : support a) (hbSupport : support b)
    (hcheap : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq .cheap
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer))
    (hsemantic : answer = true →
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (do
        if answer then
          modify fun st => {st with
            env := {st.env with
              defEqCache := st.env.defEqCache.insert
                ((canonicalPair a.addr b.addr).1,
                  (canonicalPair a.addr b.addr).2, ctxAddr) true}
            equivManager := st.equivManager.addEquiv
              ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
              ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩}
        return answer)
      (fun result _ => result = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  cases answer with
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      exact RecM.WF.pure fun _ h => by contradiction
  | true =>
      simp only [if_true]
      have hfull : CacheProvenance
          (kernelCacheSemantics model.keys trProj)
          (CacheAuthority.stable world) support
          (.defEq .full
            ((canonicalPair a.addr b.addr).1,
              (canonicalPair a.addr b.addr).2, ctxAddr) true) :=
        hcheap.kernelDefEqRekind
      have hrel := hfull.kernelDefEqEquivCanonical hcollision
        haSupport hbSupport
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (f := fun st : TcState .anon => {st with
            env := {st.env with
              defEqCache := st.env.defEqCache.insert
                ((canonicalPair a.addr b.addr).1,
                  (canonicalPair a.addr b.addr).2, ctxAddr) true}
            equivManager := st.equivManager.addEquiv
              ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
              ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩})
          (fun (hI : WhnfStateInv layer
              (kernelCacheSemantics model.keys trProj) trProj world support
              model.keys.uvars Delta s) => by
            have hfullState :=
              DefEqCacheUpdate.full_whnfStateInv hI hfull
            have hfinal := hfullState.addEquiv hrel
            simpa using hfinal)
          (fun _ => trivial)
      · intro _ _ _
        exact RecM.WF.pure fun _ _ => hsemantic rfl

/-- Conditional closure of the charged recursive tail.  All bookkeeping
errors preserve the checker invariant; successful results are cached with
collision-robust provenance, and only a semantically justified `true` joins
the original equivalence keys. -/
theorem isDefEqAfterRootCacheMiss_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (hcollision : support.CollisionFree)
    (hinner : DefEqInner.WF layer trProj world support model)
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr} {ctxAddr : Address}
    {cheapMode : Bool}
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hctx : model.keys.Represents (max a.lbr b.lbr) ctxAddr Delta)
    (hreferences : ∀ (kind : DefEqCacheKind) (answer : Bool),
      (CacheEntry.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (isDefEqAfterRootCacheMiss a b
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) cheapMode)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  unfold isDefEqAfterRootCacheMiss
  apply RecM.WF.bind
  · apply RecM.WF.liftTcM
    exact TcM.bumpStats_whnf_wf
      (fun st => {st with deqMisses := st.deqMisses + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s
  · intro _ s₁ _
    apply RecM.WF.bind
    · apply RecM.WF.liftTcM
      exact TcM.WF.mono
        (TcM.tick.wf (fun _ hI => hI.of_semantic_fields_eq
          rfl rfl rfl rfl rfl rfl rfl rfl))
        (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · intro _ s₂ _
      apply RecM.WF.bind (Q₁ := fun _ _ => True)
      · exact RecM.WF.modify
          (fun hI => hI.of_semantic_fields_eq
            rfl rfl rfl rfl rfl rfl rfl rfl)
          (fun _ => trivial)
      · intro _ s₃ _
        apply RecM.WF.bind
          (Q₁ := fun read after => read = after)
          (RecM.WF.get fun _ => rfl)
        intro read s₄ hread
        subst read
        by_cases hdepth : s₄.defEqDepth > maxDefEqDepth
        · simp only [hdepth, if_true]
          apply RecM.WF.bind (Q₁ := fun _ _ => True)
          · exact RecM.WF.modify
              (fun hI => hI.of_semantic_fields_eq
                rfl rfl rfl rfl rfl rfl rfl rfl)
              (fun _ => trivial)
          · intro _ _ _
            exact RecM.WF.throw fun _ => trivial
        · simp only [hdepth, if_false, pure_bind]
          apply RecM.WF.bind
            (Q₁ := fun result _ => match result with
              | .ok answer => answer = true →
                  world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb
              | .error _ => True)
          · apply RecM.WF.tryCatch
            · apply RecM.WF.bind
                (hinner haSupport hbSupport ha hb)
              intro answer _ hanswer
              exact RecM.WF.pure fun _ => hanswer
            · intro _ _ _
              exact RecM.WF.pure fun _ => trivial
          · intro result s₅ hresult
            apply RecM.WF.bind (Q₁ := fun _ _ => True)
            · exact RecM.WF.modify
                (fun hI => hI.of_semantic_fields_eq
                  rfl rfl rfl rfl rfl rfl rfl rfl)
                (fun _ => trivial)
            · intro _ s₆ _
              cases result with
              | error err =>
                  exact RecM.WF.throw fun _ => trivial
              | ok answer =>
                  cases answer with
                  | false =>
                      have hmeaning : DefEqMeaning trProj world
                          model.keys.uvars Delta a b false :=
                        DefEqMeaning.false
                      cases cheapMode with
                      | false =>
                          have hfull := model.defEqProvenance hcollision .full
                            haSupport hbSupport hctx hmeaning
                            (hreferences .full false)
                          apply RecM.WF.bind (Q₁ := fun _ _ => True)
                          · exact RecM.WF.modify
                              (fun hI =>
                                DefEqCacheUpdate.full_whnfStateInv hI hfull)
                              (fun _ => trivial)
                          · intro _ _ _
                            exact RecM.WF.pure fun _ htrue => by
                              contradiction
                      | true =>
                          have hcheap := model.defEqProvenance hcollision .cheap
                            haSupport hbSupport hctx hmeaning
                            (hreferences .cheap false)
                          apply RecM.WF.bind (Q₁ := fun _ _ => True)
                          · exact RecM.WF.modify
                              (fun hI => cheapResult_whnfStateInv hI hcheap
                                (fun h => by contradiction))
                              (fun _ => trivial)
                          · intro _ _ _
                            exact RecM.WF.pure fun _ htrue => by
                              contradiction
                  | true =>
                      have hsemantic := hresult rfl
                      have hmeaning : DefEqMeaning trProj world
                          model.keys.uvars Delta a b true := by
                        intro _
                        exact ⟨va, vb, ha, hb, hsemantic⟩
                      have hfull := model.defEqProvenance hcollision .full
                        haSupport hbSupport hctx hmeaning
                        (hreferences .full true)
                      have hrel := hfull.kernelDefEqEquivCanonical hcollision
                        haSupport hbSupport
                      apply RecM.WF.bind (Q₁ := fun _ _ => True)
                      · exact RecM.WF.modify
                          (fun hI => hI.addEquiv hrel)
                          (fun _ => trivial)
                      · intro _ s₇ _
                        cases cheapMode with
                        | false =>
                            apply RecM.WF.bind (Q₁ := fun _ _ => True)
                            · exact RecM.WF.modify
                                (fun hI =>
                                  DefEqCacheUpdate.full_whnfStateInv hI hfull)
                                (fun _ => trivial)
                            · intro _ _ _
                              exact RecM.WF.pure fun _ _ => hsemantic
                        | true =>
                            have hcheap : CacheProvenance
                                (kernelCacheSemantics model.keys trProj)
                                (CacheAuthority.stable world) support
                                (.defEq .cheap
                                  ((canonicalPair a.addr b.addr).1,
                                    (canonicalPair a.addr b.addr).2,
                                    ctxAddr) true) :=
                              hfull.kernelDefEqRekind
                            apply RecM.WF.bind (Q₁ := fun _ _ => True)
                            · exact RecM.WF.modify
                                (fun hI => cheapResult_whnfStateInv hI hcheap
                                  (fun _ => hfull))
                                (fun _ => trivial)
                            · intro _ _ _
                              exact RecM.WF.pure fun _ _ => hsemantic

/-- Conditional closure of the guarded representative probe.  Every miss or
scope rejection falls through to the charged tail; every hit is interpreted
from cache provenance before its answer is copied to the caller's key. -/
theorem isDefEqAfterDirectCacheMiss_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (hinner : DefEqInner.WF layer trProj world support model)
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr} {ctxAddr : Address}
    {cheapMode : Bool}
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hctx : model.keys.Represents (max a.lbr b.lbr) ctxAddr Delta)
    (hreferences : ∀ (kind : DefEqCacheKind) (answer : Bool),
      (CacheEntry.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (isDefEqAfterDirectCacheMiss a b ctxAddr
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) cheapMode)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  unfold isDefEqAfterDirectCacheMiss
  apply RecM.WF.bind
  · apply RecM.WF.withInv
    apply RecM.WF.liftTcM
    exact TcM.withEquiv_findRootKeys_whnf_wf
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s
  · intro roots s₁ hroots
    rcases roots with ⟨aRootOpt, bRootOpt⟩
    rcases hroots with ⟨hI₁, haPaths, hbPaths⟩
    cases aRootOpt with
    | none =>
        simpa using isDefEqAfterRootCacheMiss_wf model hcollision hinner
          haSupport hbSupport ha hb hctx hreferences (s := s₁)
          (cheapMode := cheapMode)
    | some aRoot =>
        cases bRootOpt with
        | none =>
            simpa using isDefEqAfterRootCacheMiss_wf model hcollision hinner
              haSupport hbSupport ha hb hctx hreferences (s := s₁)
              (cheapMode := cheapMode)
        | some bRoot =>
            have haPath := haPaths aRoot rfl
            have hbPath := hbPaths bRoot rfl
            cases hchanged : (aRoot !=
                ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
              bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) with
            | false =>
                simp only [hchanged, Bool.false_eq_true, if_false]
                exact isDefEqAfterRootCacheMiss_wf model hcollision hinner
                  haSupport hbSupport ha hb hctx hreferences
                  (s := s₁) (cheapMode := cheapMode)
            | true =>
                simp only [hchanged, if_true]
                cases hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
                    (max a.lbr b.lbr) with
                | false =>
                    simp only [Bool.false_eq_true, if_false]
                    exact isDefEqAfterRootCacheMiss_wf model hcollision hinner
                      haSupport hbSupport ha hb hctx hreferences
                      (s := s₁) (cheapMode := cheapMode)
                | true =>
                    simp only [if_true]
                    apply RecM.WF.bind
                      (Q₁ := fun read after => read = after ∧
                        WhnfStateInv layer
                          (kernelCacheSemantics model.keys trProj) trProj
                          world support model.keys.uvars Delta after)
                      (RecM.WF.get fun hI => ⟨rfl, hI⟩)
                    intro read s₂ hread
                    rcases hread with ⟨hreadEq, hI₂⟩
                    subst read
                    cases hfullHit : (s₂.env.defEqCache[
                        ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
                          (canonicalPair aRoot.exprAddr bRoot.exprAddr).2,
                          ctxAddr)]?) with
                    | some answer =>
                        have hroot := hI₂.1.caches.hit (.defEq hfullHit)
                        have horiginal := guardedRootResult model theory
                          hcollision hI₂ haPath hbPath hscope hctx hroot
                          haSupport hbSupport ha hb (hreferences .full answer)
                        simp only [pure_bind, Bool.false_eq_true,
                          if_false]
                        exact applyFullRootResult_wf hcollision
                          haSupport hbSupport horiginal.1 horiginal.2
                          (cheapMode := cheapMode)
                    | none =>
                        cases cheapMode with
                        | false =>
                            simp only [Bool.false_eq_true, if_false,
                              pure_bind]
                            exact isDefEqAfterRootCacheMiss_wf model hcollision
                              hinner haSupport hbSupport ha hb hctx hreferences
                              (s := s₂) (cheapMode := false)
                        | true =>
                            simp only [if_true, pure_bind]
                            apply RecM.WF.bind
                              (Q₁ := fun read after => read = after ∧
                                WhnfStateInv layer
                                  (kernelCacheSemantics model.keys trProj)
                                  trProj world support model.keys.uvars Delta
                                  after)
                              (RecM.WF.get fun hI => ⟨rfl, hI⟩)
                            intro read s₃ hread
                            rcases hread with ⟨hreadEq, hI₃⟩
                            subst read
                            cases hcheapHit : (s₃.env.defEqCheapCache[
                                ((canonicalPair aRoot.exprAddr
                                      bRoot.exprAddr).1,
                                  (canonicalPair aRoot.exprAddr
                                      bRoot.exprAddr).2, ctxAddr)]?) with
                            | some answer =>
                                have hroot := hI₃.1.caches.hit
                                  (.defEqCheap hcheapHit)
                                have horiginal := guardedRootResult model theory
                                  hcollision hI₃ haPath hbPath hscope hctx
                                  hroot haSupport hbSupport ha hb
                                  (hreferences .full answer)
                                exact applyCheapRootResult_wf hcollision
                                  haSupport hbSupport horiginal.1 horiginal.2
                            | none =>
                                exact isDefEqAfterRootCacheMiss_wf model
                                  hcollision hinner haSupport hbSupport ha hb
                                  hctx hreferences (s := s₃)
                                  (cheapMode := true)

/-- Conditional semantic closure of the complete public DefEq entry point.
The only remaining assumption is the recursive tier contract; every fast
path, manager query, direct-cache branch, and guarded representative fallback
is discharged here against the concrete production program. -/
theorem isDefEq_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (hinner : DefEqInner.WF layer trProj world support model)
    {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hreferences : ∀ (ctxAddr : Address) (kind : DefEqCacheKind)
        (answer : Bool),
      (CacheEntry.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    RecM.WF layer (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s (isDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb) := by
  unfold isDefEq
  apply RecM.WF.bind
  · apply RecM.WF.liftTcM
    exact TcM.stepTrace_whnf_wf "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s
  · intro _ s₁ _
    apply RecM.WF.bind
    · apply RecM.WF.liftTcM
      exact TcM.bumpStats_whnf_wf
        (fun st => {st with deqCalls := st.deqCalls + 1})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s₁
    · intro _ s₂ _
      cases haddr : (a.addr == b.addr) with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun hI _ =>
            DefEqMeaning.of_translations theory hI.2.1.wf ha hb
              (DefEqMeaning.of_addr_beq theory hI.2.1 hcollision
                haSupport hbSupport ha haddr) rfl
      | false =>
          simp only [Bool.false_eq_true, if_false, pure_bind]
          apply RecM.WF.bind
          · apply RecM.WF.withInv
            apply RecM.WF.liftTcM
            exact TcM.defEqCtxKey_model_matches_wf
              (semantics := kernelCacheSemantics model.keys trProj)
              (support := support) model (Delta := Delta) (a := a) (b := b)
              (s := s₂)
          · intro ctxAddr s₃ hctxPost
            rcases hctxPost with ⟨hI₃, hmatches, _hframe⟩
            have hrepresented := hmatches.2.1
            apply RecM.WF.bind
            · apply RecM.WF.withInv
              apply RecM.WF.liftTcM
              exact TcM.withEquiv_isEquiv_whnf_wf
                ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
                ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s₃
            · intro isEq s₄ hequivPost
              rcases hequivPost with ⟨hI₄, hequiv⟩
              cases isEq with
              | true =>
                  simp only [if_true]
                  have hsemantic := (hequiv rfl).sound theory hI₄.2.1.wf
                    hcollision haSupport rfl hbSupport rfl hrepresented ha hb
                  exact RecM.WF.pure fun _ _ => hsemantic
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  apply RecM.WF.bind
                    (Q₁ := fun read after => read = after ∧
                      WhnfStateInv layer
                        (kernelCacheSemantics model.keys trProj) trProj world
                        support model.keys.uvars Delta after)
                    (RecM.WF.get fun hI => ⟨rfl, hI⟩)
                  intro read s₅ hread
                  rcases hread with ⟨hread, hI₅⟩
                  subst read
                  apply RecM.WF.bind
                    (Q₁ := fun read after => read = after ∧
                      WhnfStateInv layer
                        (kernelCacheSemantics model.keys trProj) trProj world
                        support model.keys.uvars Delta after)
                    (RecM.WF.get fun hI => ⟨rfl, hI⟩)
                  intro read s₆ hread
                  rcases hread with ⟨hread, hI₆⟩
                  subst read
                  cases hfullHit : (s₆.env.defEqCache[
                      ((canonicalPair a.addr b.addr).1,
                        (canonicalPair a.addr b.addr).2, ctxAddr)]?) with
                  | some answer =>
                      have hfull := hI₆.1.caches.hit (.defEq hfullHit)
                      have hmeaning := hfull.kernelDefEqMeaningCanonical
                        haSupport hbSupport hrepresented
                      have hsemantic : answer = true →
                          world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb :=
                        fun htrue => DefEqMeaning.of_translations theory
                          hI₆.2.1.wf ha hb hmeaning htrue
                      by_cases hcheapMode : s₅.cheapRecursionDepth > 0
                      · simp only [hcheapMode, if_true]
                        exact applyDirectFullHit_wf hcollision haSupport
                          hbSupport hfull hsemantic (cheapMode := true)
                      · simp only [hcheapMode, if_false]
                        exact applyDirectFullHit_wf hcollision haSupport
                          hbSupport hfull hsemantic (cheapMode := false)
                  | none =>
                      by_cases hcheapMode : s₅.cheapRecursionDepth > 0
                      · simp only [hcheapMode, if_true, decide_true]
                        apply RecM.WF.bind
                          (Q₁ := fun read after => read = after ∧
                            WhnfStateInv layer
                              (kernelCacheSemantics model.keys trProj) trProj
                              world support model.keys.uvars Delta after)
                          (RecM.WF.get fun hI => ⟨rfl, hI⟩)
                        intro read s₇ hread
                        rcases hread with ⟨hread, hI₇⟩
                        subst read
                        cases hcheapHit : (s₇.env.defEqCheapCache[
                            ((canonicalPair a.addr b.addr).1,
                              (canonicalPair a.addr b.addr).2, ctxAddr)]?) with
                        | some answer =>
                            have hcheap := hI₇.1.caches.hit
                              (.defEqCheap hcheapHit)
                            have hmeaning :=
                              hcheap.kernelDefEqMeaningCanonical
                                haSupport hbSupport hrepresented
                            have hsemantic : answer = true →
                                world.venv.IsDefEqU model.keys.uvars
                                  Delta.toCtx va vb :=
                              fun htrue => DefEqMeaning.of_translations theory
                                hI₇.2.1.wf ha hb hmeaning htrue
                            exact applyDirectCheapHit_wf hcollision haSupport
                              hbSupport hcheap hsemantic
                        | none =>
                            exact isDefEqAfterDirectCacheMiss_wf model theory
                              hcollision hinner haSupport hbSupport ha hb
                              hrepresented (hreferences ctxAddr)
                              (s := s₇) (cheapMode := true)
                      · simp only [hcheapMode, if_false, decide_false]
                        exact isDefEqAfterDirectCacheMiss_wf model theory
                          hcollision hinner haSupport hbSupport ha hb
                          hrepresented (hreferences ctxAddr)
                          (s := s₆) (cheapMode := false)

end RecM

end Ix.Tc
