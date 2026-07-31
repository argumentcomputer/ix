import Ix.Tc.Verify.DefEq

/-!
# Inference cache shell

This module verifies the policy split around the uncached inference
dispatcher.  It records the exact production executions for both cache-write
partitions and for the full/infer-only miss paths, including partial errors
before any result is cached.
-/

namespace Ix.Tc

namespace RecM

@[simp] theorem cacheInferResult_full_run
    (methods : Methods .anon) (s : TcState .anon)
    (key : Address × Address) (ty : KExpr .anon) :
    (cacheInferResult false key ty).run methods s =
      .ok () {s with env := {s.env with
        inferCache := s.env.inferCache.insert key ty}} := by
  rfl

@[simp] theorem cacheInferResult_inferOnly_run
    (methods : Methods .anon) (s : TcState .anon)
    (key : Address × Address) (ty : KExpr .anon) :
    (cacheInferResult true key ty).run methods s =
      .ok () {s with env := {s.env with
        inferOnlyCache := s.env.inferOnlyCache.insert key ty}} := by
  rfl

/-- A certified validated inference result can be installed in the full
partition without changing any other semantic state component. -/
theorem cacheInferResult_full_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .infer key ty)) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (cacheInferResult false key ty) (fun _ _ => True) := by
  intro methods _ hI
  rw [cacheInferResult_full_run]
  exact ⟨InferCacheUpdate.full_whnfStateInv hI hnew, trivial⟩

/-- Infer-only results remain confined to their policy partition. -/
theorem cacheInferResult_inferOnly_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .inferOnly key ty)) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (cacheInferResult true key ty) (fun _ _ => True) := by
  intro methods _ hI
  rw [cacheInferResult_inferOnly_run]
  exact ⟨InferCacheUpdate.inferOnly_whnfStateInv hI hnew, trivial⟩

/-- Exact successful full-mode miss: the uncached result is written only to
the validated partition. -/
theorem inferWith_fullMiss_success
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {source ty : KExpr .anon}
    {key : Address × Address} {s sKey sBody : TcState .anon}
    (hpolicy : s.inferOnly = false)
    (hkey : TcM.inferKey source s = .ok key sKey)
    (hfullMiss : sKey.env.inferCache[key]? = none)
    (hbody : (inferUncached inferRec false source).run methods sKey =
      .ok ty sBody) :
    (inferWith inferRec source).run methods s =
      .ok ty {sBody with env := {sBody.env with
        inferCache := sBody.env.inferCache.insert key ty}} := by
  unfold inferWith
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only [hpolicy]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.inferKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ sKey = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) sKey = .ok sKey sKey from rfl]
  simp only [hfullMiss, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((inferUncached inferRec false source).run methods) _ sKey = _
  unfold EStateM.bind
  rw [hbody]
  rfl

/-- An uncached full-mode error is propagated with its partial state and no
inference-cache write. -/
theorem inferWith_fullMiss_error
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {source : KExpr .anon}
    {key : Address × Address} {s sKey sBody : TcState .anon}
    {err : TcError .anon}
    (hpolicy : s.inferOnly = false)
    (hkey : TcM.inferKey source s = .ok key sKey)
    (hfullMiss : sKey.env.inferCache[key]? = none)
    (hbody : (inferUncached inferRec false source).run methods sKey =
      .error err sBody) :
    (inferWith inferRec source).run methods s = .error err sBody := by
  unfold inferWith
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only [hpolicy]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.inferKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ sKey = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) sKey = .ok sKey sKey from rfl]
  simp only [hfullMiss, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((inferUncached inferRec false source).run methods) _ sKey = _
  unfold EStateM.bind
  rw [hbody]

/-- Exact successful infer-only miss: after both partitions miss, the result
is written only to the infer-only partition. -/
theorem inferWith_inferOnlyMiss_success
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {source ty : KExpr .anon}
    {key : Address × Address} {s sKey sBody : TcState .anon}
    (hpolicy : s.inferOnly = true)
    (hkey : TcM.inferKey source s = .ok key sKey)
    (hfullMiss : sKey.env.inferCache[key]? = none)
    (hinferOnlyMiss : sKey.env.inferOnlyCache[key]? = none)
    (hbody : (inferUncached inferRec true source).run methods sKey =
      .ok ty sBody) :
    (inferWith inferRec source).run methods s =
      .ok ty {sBody with env := {sBody.env with
        inferOnlyCache := sBody.env.inferOnlyCache.insert key ty}} := by
  unfold inferWith
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only [hpolicy]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.inferKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ sKey = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) sKey = .ok sKey sKey from rfl]
  simp only [hfullMiss]
  simp only [pure_bind, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ sKey = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) sKey = .ok sKey sKey from rfl]
  simp only [hinferOnlyMiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((inferUncached inferRec true source).run methods) _ sKey = _
  unfold EStateM.bind
  rw [hbody]
  rfl

/-- Infer-only dispatcher errors likewise propagate before any cache write. -/
theorem inferWith_inferOnlyMiss_error
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {source : KExpr .anon}
    {key : Address × Address} {s sKey sBody : TcState .anon}
    {err : TcError .anon}
    (hpolicy : s.inferOnly = true)
    (hkey : TcM.inferKey source s = .ok key sKey)
    (hfullMiss : sKey.env.inferCache[key]? = none)
    (hinferOnlyMiss : sKey.env.inferOnlyCache[key]? = none)
    (hbody : (inferUncached inferRec true source).run methods sKey =
      .error err sBody) :
    (inferWith inferRec source).run methods s = .error err sBody := by
  unfold inferWith
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only [hpolicy]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.inferKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ sKey = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) sKey = .ok sKey sKey from rfl]
  simp only [hfullMiss]
  simp only [pure_bind, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ sKey = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) sKey = .ok sKey sKey from rfl]
  simp only [hinferOnlyMiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((inferUncached inferRec true source).run methods) _ sKey = _
  unfold EStateM.bind
  rw [hbody]

end RecM

end Ix.Tc
