import Ix.Tc.Verify.Whnf.Structural.BetaBoundary

/-!
# Exhaustive application-step closure

The preceding slices prove each continuation after the recursive head
callback.  This slice performs the adversarial assembly: callback errors,
lambda results, every non-lambda syntax constructor (including an application
returned by the callback), physical head changes, and address-equal heads are
all covered by one `WhnfStep.WF` contract.

The unchanged branch does not trust address equality as expression equality.
It uses the run's collision-freedom certificate over the supported callback
result and original head before rewriting the callback equation.
-/

namespace Ix.Tc
namespace RecM

/-- Every outcome of the production application branch satisfies the local
structural-step contract, conditional only on the separately named finite
request and Theory/helper boundaries. -/
theorem whnfCoreWithFlagsStep_app_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hbetaCensus : BetaRequestCensus requests support)
    (hfinishCensus : ApplicationFinishRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {f arg : KExpr .anon} {info : ExprInfo .anon}
    {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hinputs : WhnfCoreInputSupport support)
    (hbetaMeaning : BetaManyMeaningOracle trProj world)
    (hiota : OptionalReduction.WF layer semantics trProj world support
      (fun source => tryIotaWithFlags source flags)) :
    forall s,
      WhnfStep.Source trProj world support uvars Delta id
        (.app f arg info) ->
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep (.app f arg info) flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          (.app f arg info) action)
        (fun _ _ => True) := by
  intro s hsource methods hmethods hI
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  rcases hspine : (.app f arg info : KExpr .anon).collectSpine with
    ⟨head, args⟩
  obtain ⟨headV, hheadTr, hsuffix, hcallbackWF⟩ :=
    applicationHeadCallbackWithSuffix_wf (s := s) (flags := flags)
      hinputs hsourceSupport hsourceTr hspine
  have hcallbackPost := hcallbackWF methods hmethods hI
  match hheadRun : methods.whnfCoreFlags head flags s with
  | .error err s1 =>
      have hcallbackRun :
          (whnfCoreFlagsRec head flags).run methods s = .error err s1 := by
        exact hheadRun
      rw [hcallbackRun] at hcallbackPost
      rw [whnfCoreWithFlagsStep_appHeadError hspine hheadRun]
      exact ⟨hcallbackPost.1, trivial⟩
  | .ok changed s1 =>
      have hcallbackRun :
          (whnfCoreFlagsRec head flags).run methods s = .ok changed s1 := by
        exact hheadRun
      rw [hcallbackRun] at hcallbackPost
      have hI1 := hcallbackPost.1
      have hchangedSupport := hcallbackPost.2.1
      have hheadPost := hcallbackPost.2.2
      have hnonLambda
          (hnonlam : WhnfCoreNonLambda changed) :
          TcM.WF
            (WhnfStateInv layer semantics trProj world support uvars Delta) s
            ((whnfCoreWithFlagsStep (.app f arg info) flags).run methods)
            (fun action _ => WhnfStep.Meaning trProj world support uvars Delta
              id (.app f arg info) action) := by
        by_cases hdiff : (changed != head) = true
        · exact whnfCoreWithFlagsStep_appChanged_wf hrun hfinishCensus
            theory hiota hmethods hsourceSupport hsourceTr hspine hsuffix
            hchangedSupport hheadPost hnonlam hheadRun hdiff hI1
        · have hsameAddr : (changed != head) = false := by
            cases hvalue : (changed != head) with
            | false => rfl
            | true => exact False.elim (hdiff hvalue)
          have haddrEq : changed.addr = head.addr := by
            change Bool.not (changed.addr == head.addr) = false at hsameAddr
            cases heq : (changed.addr == head.addr) with
            | false => simp [heq] at hsameAddr
            | true => exact beq_iff_eq.mp heq
          have herase := hrun.collisionFree.expr hchangedSupport
            (hinputs.app hsourceSupport hspine).1 haddrEq
          have hsame : changed = head := by
            simpa only [KExpr.eraseMeta_anon] using herase
          subst changed
          exact whnfCoreWithFlagsStep_appUnchanged_wf theory hiota
            hmethods hsourceSupport hsourceTr hspine hnonlam hheadRun hI1
      cases changed with
      | lam name bi ty body lamInfo =>
          let consumedResult := consumeBetaLams
            (.lam name bi ty body lamInfo) args
          rcases hconsume : consumedResult with ⟨body0, consumed⟩
          have hconsume' :
              consumeBetaLams (.lam name bi ty body lamInfo) args =
                (body0, consumed) := by
            simpa only [consumedResult] using hconsume
          exact (whnfCoreWithFlagsStep_appBeta_wf hrun hbetaCensus theory
            hbetaMeaning hsourceSupport hsourceTr hspine hsuffix
            hchangedSupport hheadPost hheadRun hconsume' hI1) hI
      | var => exact hnonLambda .var hI
      | fvar => exact hnonLambda .fvar hI
      | sort => exact hnonLambda .sort hI
      | const => exact hnonLambda .const hI
      | app => exact hnonLambda .app hI
      | all => exact hnonLambda .all hI
      | letE => exact hnonLambda .letE hI
      | prj => exact hnonLambda .prj hI
      | nat => exact hnonLambda .nat hI
      | str => exact hnonLambda .str hI

end RecM
end Ix.Tc
