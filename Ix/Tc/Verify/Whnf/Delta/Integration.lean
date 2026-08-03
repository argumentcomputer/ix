import Ix.Tc.Verify.Whnf.Delta.UnfoldingState

/-!
# Package delta and the fourth public WHNF field

UnfoldingState separates delta unfolding into four independently reviewable inputs:
finite execution coverage, lazy-ingress state preservation, certified
unfold-cache writes, and successful-definition reflection.  This module
packages those inputs into the exact optional-reducer field consumed by
FullStep's full-WHNF step.

The public method table also exposes `whnfCoreWithFlags`, not only the
full-flags `whnfCore` specialization already wrapped by PublicReducers.  The final
theorem below upgrades Reducer's arbitrary-flags `WhnfMeaning` result to the
`WhnfPost` shape required by `Methods.WhnfLayerWF`.
-/

namespace Ix.Tc
namespace RecM

/-- Complete run-scoped authority for production delta unfolding.  The
structure contains no opaque operational callback: UnfoldingState constructs all state
and support behavior from the finite run, leaving only successful semantic
reflection and certified cache provenance as explicit admission inputs. -/
structure DeltaUnfoldContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Type where
  run : RunAssumptions initial program requests support
  census : DeltaUnfoldRequestCensus requests world support
  lazyFault : ∀ {uvars : Nat} {Delta : KVLCtx},
    TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
  writes : UnfoldCacheWriteOracle semantics world support
  reflection : DeltaUnfoldReflection semantics trProj world support

namespace DeltaUnfoldContext

/-- Discharge FullStep's complete optional-reducer contract from the packaged
delta authorities. -/
theorem wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport}
    (context : DeltaUnfoldContext initial program requests semantics trProj
      world support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      deltaUnfoldOne :=
  deltaUnfoldOne_optional_wf_of_contexts context.run context.census
    context.lazyFault context.writes context.reflection

end DeltaUnfoldContext

namespace FullWhnfStepContext

/-- Construct FullStep's full-WHNF step context without accepting a free
`OptionalReduction.WF`: the delta field must come through UnfoldingState's audited
operational decomposition. -/
def ofDelta
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx}
    (noDelta : NoDeltaDriverContext initial program requests keys fallback
      trProj world support Delta .FULL)
    (natOffsetStuck : OptionalReduction.WFAt .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars tryNatOffsetStuck)
    (delta : DeltaUnfoldContext initial program requests
      (whnfCacheSemantics keys trProj fallback) trProj world support) :
    FullWhnfStepContext initial program requests keys fallback trProj world
      support Delta where
  noDelta := noDelta
  natOffsetStuck := natOffsetStuck
  delta := OptionalReduction.WF.atUvars delta.wf keys.uvars

end FullWhnfStepContext

namespace StructuralCoreContext

/-- The fourth WHNF method-table field: the actual public
`whnfCoreWithFlags` reducer, for an arbitrary production flag bundle, returns
the complete `WhnfPost` expected by `Methods.WF`. -/
theorem publicFlags_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx} {flags : WhnfFlags}
    (context : StructuralCoreContext initial program requests keys fallback
      trProj world support Delta flags)
    {source : KExpr .anon} (hsourceSupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta s
      (whnfCoreWithFlags source flags)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hcore :=
    context.wf (source := source) (s := s) hsourceSupport hsource
  apply RecM.WF.mono (RecM.WF.withInv hcore)
  · intro result _ hresult
    rcases hresult with ⟨hI, hresultSupport, hmeaning⟩
    refine ⟨hresultSupport, ?_⟩
    exact (WhnfPost.refl hsource
      (context.theory.exprWF hI.2.1 hsource)).transMeaning
        context.theory hI.2.1.wf hmeaning
  · intro _ _ _
    trivial

end StructuralCoreContext
end RecM
end Ix.Tc
