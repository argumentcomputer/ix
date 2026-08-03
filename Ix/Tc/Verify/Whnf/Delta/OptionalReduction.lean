import Ix.Tc.Verify.Whnf.Delta.SpineUnfolding

/-!
# Exact delta optional-reducer closure

SpineUnfolding closes the spine-aware first half of `deltaUnfoldOne`.  Production then
retains a bare-constant fallback.  This module proves that fallback through
the same trusted declaration census and packages the complete reducer in the
fixed-universe optional contract consumed by the full-WHNF step.
-/

namespace Ix.Tc
namespace RecM

/-- Local run-equation strengthening used to connect a successful lazy
constant lookup to the exact catalog entry retained by the state invariant. -/
private theorem deltaOne_wf_with_run_eq
    {I : TcState .anon → Prop} {s : TcState .anon} {x : TcM .anon α}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x
      (fun value after => Q value after ∧ x s = .ok value after)
      (fun err after => E err after ∧ x s = .error err after) := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩

/-- Complete fixed-universe contract for production's `deltaUnfoldOne`.

The first successful result already carries SpineUnfolding's rebuilt-spine meaning.
After a first-stage miss, only the concrete bare-constant branch can perform
more work; its second lookup, body instantiation, cache hit/write, support,
and Theory meaning are discharged by the same exact certificates. -/
theorem deltaUnfoldOne_trusted_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    (operational : DeltaUnfoldRequestCensus requests world support)
    (trustedCensus : TrustedDeltaCensus trProj world support)
    (theory : StableWhnfTheory trProj world keys.uvars)
    {Delta : KVLCtx}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel
        (whnfCacheSemantics keys trProj
          (unfoldCacheSemantics keys.uvars trProj fallback))
        trProj world support keys.uvars Delta))
    (hreferences : TrustedReferences world support)
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {s : TcState .anon}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      trProj world support keys.uvars Delta s
      (deltaUnfoldOne source)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world keys.uvars Delta source reduced) := by
  unfold deltaUnfoldOne
  apply RecM.WF.bind <|
    tryDeltaUnfold_trusted_wf hrun operational trustedCensus theory hfault
      hreferences hsourceSupport hsource
  intro first afterFirst hfirst
  cases first with
  | some result =>
      simp only
      exact RecM.WF.pure fun _ => hfirst
  | none =>
      simp only [pure_bind]
      cases source with
      | const id us info =>
          apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
            TcM.WF.mono
              (deltaOne_wf_with_run_eq
                (TcM.tryGetConst_wf hfault id afterFirst))
              (fun _ _ hpost => hpost.2)
              (fun _ _ _ => trivial)
          intro entry afterLookup hlookup
          rcases hlookup with ⟨hILookup, hlookupRun⟩
          cases entry with
          | none =>
              exact RecM.WF.pure fun _ => trivial
          | some entry =>
              cases entry with
              | defn name levelParams kind safety hints lvls ty body leanAll
                  block =>
                  cases kind with
                  | opaq =>
                      exact RecM.WF.pure fun _ => trivial
                  | defn | thm =>
                      have hloaded :=
                        TcM.tryGetConst_success_loaded hlookupRun
                      have hcatalog :=
                        hILookup.1.core.loaded hloaded
                      obtain ⟨hheadSupport, hrequest, _⟩ :=
                        operational.reduce hsourceSupport rfl rfl hcatalog
                      obtain ⟨ci, htrusted, hresources⟩ :=
                        trustedCensus.resolve hheadSupport .defn hcatalog
                          (by simp)
                      apply RecM.WF.bind <|
                        unfoldConstValue_trusted_wf hrun theory hreferences
                          htrusted hresources hheadSupport hrequest hsource
                      intro result afterUnfold hresult
                      exact RecM.WF.pure fun _ => hresult
              | recr | axio | quot | indc | ctor =>
                  exact RecM.WF.pure fun _ => trivial
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact RecM.WF.pure fun _ => trivial

/-- Exact fixed-universe inputs for the trusted delta reducer. -/
structure TrustedDeltaContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (keys : WhnfContextKeys)
    (fallback : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Type where
  run : RunAssumptions initial program requests support
  operational : DeltaUnfoldRequestCensus requests world support
  trusted : TrustedDeltaCensus trProj world support
  theory : StableWhnfTheory trProj world keys.uvars
  references : TrustedReferences world support
  ingress :
    AnonLazyIngressContext .noAccel
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      trProj world support

namespace TrustedDeltaContext

/-- Construct the complete delta field required by one fixed-universe
full-WHNF context, with no broad write or success-reflection authority. -/
theorem wfAt
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : TrustedDeltaContext initial program requests keys fallback
      trProj world support) :
    OptionalReduction.WFAt .noAccel
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      trProj world support keys.uvars deltaUnfoldOne := by
  intro Delta source sourceV s hsourceSupport hsource
  exact deltaUnfoldOne_trusted_wf context.run context.operational
    context.trusted context.theory context.ingress.preserves context.references
    hsourceSupport hsource

end TrustedDeltaContext

/-- Build the production full-WHNF step context with the universe-sensitive
delta fallback installed beneath the public WHNF cache semantics. -/
def FullWhnfStepContext.ofTrustedDelta
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx}
    (noDelta : NoDeltaDriverContext initial program requests keys
      (unfoldCacheSemantics keys.uvars trProj fallback)
      trProj world support Delta .FULL)
    (natOffsetStuck : OptionalReduction.WFAt .noAccel
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      trProj world support keys.uvars tryNatOffsetStuck)
    (delta : TrustedDeltaContext initial program requests keys fallback
      trProj world support) :
    FullWhnfStepContext initial program requests keys
      (unfoldCacheSemantics keys.uvars trProj fallback)
      trProj world support Delta where
  noDelta := noDelta
  natOffsetStuck := natOffsetStuck
  delta := delta.wfAt

end RecM
end Ix.Tc
