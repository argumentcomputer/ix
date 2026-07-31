import Ix.Tc.Verify.Whnf.NoDelta.BaseReductions

/-!
# Public no-delta reducer

Reducer constructs the structural reducer and BaseReductions constructs the five active
tail fields.  The generic no-delta driver theorem already proves reducer
ordering, bounded iteration, cache hits, transient bypass, partial errors,
and collision-robust cache writes.  This slice supplies those two concrete
components to that shell.
-/

namespace Ix.Tc
namespace RecM

/-- Complete fixed-context input for the public no-delta reducer. -/
structure NoDeltaDriverContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (keys : WhnfContextKeys)
    (fallback : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (Delta : KVLCtx) (flags : WhnfFlags) : Type where
  structural :
    StructuralCoreContext initial program requests keys fallback trProj world
      support Delta flags
  base :
    NoDeltaBaseContext initial program requests
      (whnfCacheSemantics keys trProj fallback) trProj world support flags
  cacheWrites : WhnfCacheWriteOracle keys trProj fallback world support

namespace NoDeltaDriverContext

/-- The actual public no-delta reducer satisfies its semantic Hoare contract
for either successor policy. -/
theorem wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx} {flags : WhnfFlags}
    (context : NoDeltaDriverContext initial program requests keys fallback
      trProj world support Delta flags)
    (mode : NatSuccMode) {source : KExpr .anon}
    (hsourceSupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s
      (whnfNoDeltaImpl source flags mode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  intro methods hmethods hI
  exact
    (whnfNoDeltaImpl_noAccel_wf_of_base
      context.structural.theory hI.2.1.wf
      context.structural.wf (context.base.oracle mode)
      (context.structural.keyRep source hsourceSupport)
      (TransientNatWork.preserving
        (context.structural.iotaIngress.preserves
          (uvars := keys.uvars) (Delta := Delta))
        source)
      context.cacheWrites hsourceSupport hsource)
      methods hmethods hI

end NoDeltaDriverContext
end RecM
end Ix.Tc
