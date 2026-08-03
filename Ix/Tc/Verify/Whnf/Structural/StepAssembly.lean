import Ix.Tc.Verify.Whnf.Structural.ApplicationStep

/-!
# Exhaustive structural-step assembly

All eleven raw expression constructors are dispatched here.  The theorem is
the single local `WhnfStep.WF` consumed by the already verified bounded loop
and cache shell; no syntax branch remains implicit in a classifier premise.
-/

namespace Ix.Tc
namespace RecM

/-- Exhaustive contract for one actual `whnfCoreWithFlagsStep` iteration. -/
theorem whnfCoreWithFlagsStep_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hlet : LetSubstRequestCensus requests support)
    (hbeta : BetaRequestCensus requests support)
    (hfinish : ApplicationFinishRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hfvar : FVarZetaSafety layer semantics trProj world support uvars Delta)
    (hvar : LegacyZetaRequestCensus layer semantics trProj world support
      uvars Delta requests)
    (hinputs : WhnfCoreInputSupport support)
    (hprojection : ProjectionHelper.WF layer semantics trProj world support)
    (hinductive : InductiveReductionOracle layer semantics trProj world
      support)
    (hbetaMeaning : BetaManyMeaningOracle trProj world)
    (hiota : OptionalReduction.WF layer semantics trProj world support
      (fun source => tryIotaWithFlags source flags)) :
    WhnfStep.WF layer semantics trProj world support uvars Delta id
      (fun source => whnfCoreWithFlagsStep source flags)
      (fun _ _ => True) := by
  intro source s hsource
  cases source with
  | var =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar .var) s hsource
  | fvar =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic .fvar)) s hsource
  | sort =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic (.leaf .sort))) s hsource
  | const =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic (.leaf .const))) s hsource
  | app =>
      exact whnfCoreWithFlagsStep_app_wf hrun hbeta hfinish theory hinputs
        hbetaMeaning hiota s hsource
  | lam =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic (.leaf .lam))) s hsource
  | all =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic (.leaf .all))) s hsource
  | letE =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic .letE)) s hsource
  | prj =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive .projection s hsource
  | nat =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic (.leaf .nat))) s hsource
  | str =>
      exact whnfCoreWithFlagsStep_basicVarProjection_wf hrun hlet theory
        hfvar hvar hinputs hprojection hinductive
        (.basicVar (.basic (.leaf .str))) s hsource

end RecM
end Ix.Tc
