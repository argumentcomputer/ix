import Ix.Tc.Verify.Whnf.Beta.Meaning

/-!
# Structural step without a beta oracle

`StepAssembly` assembled every raw-expression constructor but retained the historical
`BetaManyMeaningOracle` parameter.  `Meaning` constructs that contract from the
Theory and translation invariants, so the production structural step can now
be exposed with only its genuine helper and finite-run boundaries.
-/

namespace Ix.Tc
namespace RecM

/-- Exhaustive `whnfCoreWithFlagsStep` closure with general multi-beta proved
constructively. -/
theorem whnfCoreWithFlagsStep_constructive_wf
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
    (hiota : OptionalReduction.WF layer semantics trProj world support
      (fun source => tryIotaWithFlags source flags)) :
    WhnfStep.WF layer semantics trProj world support uvars Delta id
      (fun source => whnfCoreWithFlagsStep source flags)
      (fun _ _ => True) :=
  whnfCoreWithFlagsStep_wf hrun hlet hbeta hfinish theory hfvar hvar
    hinputs hprojection hinductive (betaManyMeaning trProj world) hiota

end RecM
end Ix.Tc
