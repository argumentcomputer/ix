import Ix.Tc.Verify.Whnf.Delta.Integration

/-!
# Semantic unfold-cache entries

`UnfoldingState` proves the operational state and support behavior of the production
unfold cache, but deliberately leaves cache provenance abstract.  This module
gives the `.unfold` family its actual fixed-universe meaning.

Unlike the WHNF expression caches, the unfold cache has no local-context key:
it stores the universe-instantiated body of a closed constant head.  Its
semantic contract must therefore hold in every mixed local context.  The
universe count is fixed, matching the `Methods.WFAt` contract used by the
recursive reducer.
-/

namespace Ix.Tc

/-- Exact fixed-universe validity for one unfold-cache entry.  Every
finite-support source sharing the stored address must reduce to the cached
body in every mixed local context.  All other cache families are delegated to
the caller-supplied fallback. -/
def UnfoldCacheValid (uvars : Nat) (trProj : RawProjRel)
    (fallback : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) : CacheEntry → Prop
  | .unfold key value =>
      ∀ later, authority ≤ later →
        ∀ source, support source → source.addr = key →
          ∀ Delta, KVLCtx.WF later.world.venv uvars Delta →
            WhnfMeaning trProj later.world uvars Delta source value
  | entry => fallback.Valid authority support entry

namespace UnfoldCacheValid

/-- A valid unfold entry remains valid as the trusted Theory world grows.
The concrete support and fixed universe count do not change. -/
theorem mono {uvars : Nat} {trProj : RawProjRel}
    {fallback : CacheSemantics} {before after : CacheAuthority}
    {support : RunSupport} {entry : CacheEntry} (hle : before ≤ after)
    (h : UnfoldCacheValid uvars trProj fallback before support entry) :
    UnfoldCacheValid uvars trProj fallback after support entry := by
  cases entry with
  | unfold key value =>
      intro later hlater source hsource haddr Delta hDelta
      exact h later (CacheAuthority.LE.trans hle hlater)
        source hsource haddr Delta hDelta
  | expr | defEq | defEqFailure | natSuccStuck | isProp | isRec |
      recursor | recMajors | blockPeer | blockResult =>
      exact fallback.mono hle h

/-- Project the concrete reduction meaning carried by one unfold entry. -/
theorem unfold {uvars : Nat} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {key : Address} {value source : KExpr .anon}
    (h : UnfoldCacheValid uvars trProj fallback authority support
      (.unfold key value))
    (hsource : support source) (haddr : source.addr = key)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF authority.world.venv uvars Delta) :
    WhnfMeaning trProj authority.world uvars Delta source value :=
  h authority CacheAuthority.LE.rfl source hsource haddr Delta hDelta

end UnfoldCacheValid

/-- Overlay semantic unfold entries on an arbitrary fallback cache contract. -/
def unfoldCacheSemantics (uvars : Nat) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := UnfoldCacheValid uvars trProj fallback
  mono := UnfoldCacheValid.mono
  blockError := by
    intro authority support block err
    exact fallback.blockError authority support block err

namespace CacheProvenance

/-- A provenance-certified unfold hit exposes its fixed-universe Theory
meaning in the caller's current mixed local context. -/
theorem unfoldMeaning {uvars : Nat} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {key : Address} {value source : KExpr .anon}
    (h : CacheProvenance (unfoldCacheSemantics uvars trProj fallback)
      authority support (.unfold key value))
    (hsource : support source) (haddr : source.addr = key)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF authority.world.venv uvars Delta) :
    WhnfMeaning trProj authority.world uvars Delta source value :=
  UnfoldCacheValid.unfold (fallback := fallback) h.valid hsource haddr hDelta

/-- Build complete stable-world provenance for one semantic unfold result.

Address collision freedom is used only to recover the exact anonymous source
from the address-only cache key.  Direct references from both possible source
witnesses and the cached value are justified independently by the run-scoped
trusted-reference boundary. -/
theorem unfoldOfMeaning {uvars : Nat} {trProj : RawProjRel}
    {fallback : CacheSemantics} {world : VerifyWorld}
    {support : RunSupport} {head value : KExpr .anon}
    (hcollision : support.CollisionFree)
    (hreferences : RecM.TrustedReferences world support)
    (hhead : support head) (hvalue : support value)
    (hmeaning : ∀ {later : VerifyWorld}, world ≤ later →
      ∀ {Delta}, KVLCtx.WF later.venv uvars Delta →
        WhnfMeaning trProj later uvars Delta head value) :
    CacheProvenance (unfoldCacheSemantics uvars trProj fallback)
      (CacheAuthority.stable world) support (.unfold head.addr value) := by
  refine ⟨⟨⟨head, hhead, rfl⟩, hvalue⟩, ?_, ?_⟩
  · intro id href
    apply Or.inl
    rcases href with href | href
    · obtain ⟨source, hsource, _, hsourceReferences⟩ := href
      exact hreferences hsource hsourceReferences
    · exact hreferences hvalue href
  · intro later hlater source hsource haddr Delta hDelta
    have hsourceEq : source = head := by
      have herase := hcollision.expr hsource hhead haddr
      simpa only [KExpr.eraseMeta_anon] using herase
    subst source
    exact hmeaning hlater.world hDelta

end CacheProvenance

end Ix.Tc
