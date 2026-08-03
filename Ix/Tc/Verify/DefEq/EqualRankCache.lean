import Ix.Tc.Verify.DefEq.SameHeadSpine

/-!
# Equal-rank same-head cache

The same-head attempt is guarded by a narrow negative cache.  Its entries
are rejection-only: they can skip work but never prove equality.  This module
proves the exact lookup/attempt/write shell and preserves provenance for the
single write made after a genuine comparison miss.
-/

namespace Ix.Tc

/-- Provenance available for every concrete failure marker this run may
insert. -/
structure DefEqFailureCacheResources (semantics : CacheSemantics)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  provenance : ∀ {left right : KExpr .anon} {ctxAddr : Address},
    support left → support right →
      CacheProvenance semantics (CacheAuthority.stable world) support
        (.defEqFailure (defEqFailureKey left right ctxAddr))

namespace CacheEntry

/-- Trusted finite expression references authorize every direct root named
by a rejection-only DefEq marker. -/
theorem defEqFailureReferencesAuthorized
    {world : VerifyWorld} {support : RunSupport}
    (htrusted : RecM.TrustedReferences world support)
    {left right : KExpr .anon} {ctxAddr : Address} :
    (CacheEntry.defEqFailure (defEqFailureKey left right ctxAddr)).ReferencesAuthorized
      (CacheAuthority.stable world) support := by
  intro id href
  change CacheEntry.SourceReferences support
      (defEqFailureKey left right ctxAddr).1 id ∨
    CacheEntry.SourceReferences support
      (defEqFailureKey left right ctxAddr).2.1 id at href
  rcases href with ⟨source, hsource, haddr, hreference⟩ |
      ⟨source, hsource, haddr, hreference⟩
  · exact .inl (htrusted hsource hreference)
  · exact .inl (htrusted hsource hreference)

end CacheEntry

namespace DefEqFailureCacheResources

/-- The joint K2 suffix model supplies failure-marker provenance without any
semantic equality premise; validity of this partition is deliberately
vacuous on acceptance. -/
theorem ofKernelSuffixModel
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    (htrusted : RecM.TrustedReferences world support) :
    DefEqFailureCacheResources (kernelCacheSemantics model.keys trProj)
      world support where
  provenance := by
    intro left right ctxAddr hleft hright
    simpa only [defEqFailureKey] using
      model.defEqFailureProvenance hleft hright
        (CacheEntry.defEqFailureReferencesAuthorized htrusted)

end DefEqFailureCacheResources

namespace RecM

/-- The regular-hint lookup preserves the full recursive invariant through
all declaration shapes and every lazy-ingress outcome. -/
theorem isRegular_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (id : KId .anon) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isRegular id) (fun _ _ => True) := by
  unfold isRegular
  apply RecM.WF.bind <| RecM.WF.liftTcM <|
    TcM.tryGetConst_wf hfault id state
  intro found afterLookup _
  cases found with
  | none => exact RecM.WF.pure fun _ => trivial
  | some decl =>
      cases decl with
      | defn name levelParams kind safety hints lvls ty value leanAll block =>
          cases hints <;> exact RecM.WF.pure fun _ => trivial
      | recr | axio | quot | indc | ctor =>
          exact RecM.WF.pure fun _ => trivial

/-- Semantic contract for the cached same-head helper. -/
def TrySameHeadSpineCached.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (trySameHeadSpineCached left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Close context-key calculation, cache lookup, the concrete same-head
attempt, and the rejection-only write on a genuine miss. -/
theorem trySameHeadSpineCached_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : Lean4Lean.VExpr}
    (hcache : DefEqFailureCacheResources semantics world support)
    (hsame : TrySameHeadSpine.WFAt layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (trySameHeadSpineCached left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold trySameHeadSpineCached
  apply RecM.WF.bind <| RecM.WF.liftTcM <|
    TcM.defEqCtxKey_wf (a := left) (b := right) (s := state)
  intro ctxAddr afterKey hframe
  apply RecM.WF.bind
    (Q₁ := fun read after => read = after)
    (RecM.WF.get fun _ => rfl)
  intro read afterRead hread
  subst read
  cases hhit : afterRead.env.defEqFailure.contains
      (defEqFailureKey left right ctxAddr) with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ => trivial
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind <|
        hsame hleftSupport hrightSupport hleft hright
      intro result afterAttempt hresult
      cases result with
      | some answer =>
          exact RecM.WF.pure fun _ => hresult
      | none =>
          apply RecM.WF.bind (Q₁ := fun _ _ => True)
          · exact RecM.WF.modify
              (fun hI => DefEqCacheUpdate.failure_whnfStateInv hI <|
                hcache.provenance hleftSupport hrightSupport)
              (fun _ => trivial)
          · intro _ afterWrite _
            exact RecM.WF.pure fun _ => trivial

namespace TrySameHeadSpineCached

/-- Package the concrete cached helper. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hcache : DefEqFailureCacheResources semantics world support)
    (hsame : TrySameHeadSpine.WFAt layer semantics trProj world support
      uvars) :
    TrySameHeadSpineCached.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact trySameHeadSpineCached_wf hcache hsame hleftSupport hrightSupport
    hleft hright

end TrySameHeadSpineCached

end RecM

end Ix.Tc
