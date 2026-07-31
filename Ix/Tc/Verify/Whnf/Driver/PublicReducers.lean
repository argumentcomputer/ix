import Ix.Tc.Verify.Whnf.Driver.FullStep

/-!
# Public full-WHNF reducers

FullStep constructs the exhaustive one-iteration contract for the production
full-WHNF loop.  The generic bounded-driver and cache-shell theorems in
`Verify.Whnf` already cover loop exhaustion, cycle sets, public fast paths,
instrumentation, cache hits and writes, and both Nat successor policies.
This slice supplies FullStep's concrete step to those theorems.
-/

namespace Ix.Tc
namespace RecM
namespace FullWhnfStepContext

/-- The actual public `whnfWithNatSuccMode` reducer satisfies its semantic
Hoare contract for either successor policy in the no-acceleration layer. -/
theorem publicMode_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx}
    (context : FullWhnfStepContext initial program requests keys fallback
      trProj world support Delta)
    (natSuccMode : NatSuccMode) {source : KExpr .anon}
    (hsourceSupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta s
      (whnfWithNatSuccMode source natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) :=
  whnfWithNatSuccMode_wf
    context.noDelta.structural.theory
    (context.noDelta.structural.keyRep source hsourceSupport)
    (TransientNatWork.preserving
      (context.noDelta.structural.iotaIngress.preserves
        (uvars := keys.uvars) (Delta := Delta))
      source)
    (context.wf natSuccMode)
    context.noDelta.cacheWrites hsourceSupport hsource

/-- The production `whnf` entry is the collapse-policy specialization of the
same complete public proof. -/
theorem publicWhnf_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx}
    (context : FullWhnfStepContext initial program requests keys fallback
      trProj world support Delta)
    {source : KExpr .anon} (hsourceSupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta s (whnf source)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) :=
  publicMode_wf context .collapse hsourceSupport hsource

/-- The structural `whnfCore` entry is the full-flags specialization already
contained in the same context. -/
theorem publicCore_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx}
    (context : FullWhnfStepContext initial program requests keys fallback
      trProj world support Delta)
    {source : KExpr .anon} (hsourceSupport : support source)
    {sourceV : Lean4Lean.VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta s (whnfCore source)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hcore :=
    context.noDelta.structural.wf
      (source := source) (s := s) hsourceSupport hsource
  apply RecM.WF.mono (RecM.WF.withInv hcore)
  · intro result _ hresult
    rcases hresult with ⟨hI, hresultSupport, hmeaning⟩
    refine ⟨hresultSupport, ?_⟩
    exact (WhnfPost.refl hsource
      (context.noDelta.structural.theory.exprWF hI.2.1 hsource)).transMeaning
        context.noDelta.structural.theory hI.2.1.wf hmeaning
  · intro _ _ _
    trivial

end FullWhnfStepContext
end RecM
end Ix.Tc
