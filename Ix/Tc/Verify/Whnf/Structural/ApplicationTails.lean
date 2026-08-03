import Ix.Tc.Verify.Whnf.Structural.ApplicationRebuild

/-!
# Non-beta application tails

This slice closes both non-lambda continuations after the recursive head
callback.  The unchanged path invokes iota on the original source; the
changed path first consumes ApplicationRebuild's certified complete-spine rebuild and then
invokes iota on that rebuilt source.  In both cases the ordinary
`OptionalReduction.WF` contract accounts for iota hits, misses, and partial
error states.
-/

namespace Ix.Tc
namespace RecM

/-- Generic unchanged-head/iota-hit equation.  The older specialized theorem
fixed the spine head to a recursor constant for its semantic oracle; the
production control-flow equation only needs a non-lambda head and therefore
admits this stronger operational form. -/
theorem whnfCoreWithFlagsStep_appUnchangedIota
    {methods : Methods .anon} {s s1 s2 : TcState .anon}
    {f arg head result : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {flags : WhnfFlags}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda head)
    (hhead : methods.whnfCoreFlags head flags s = .ok head s1)
    (hself : (head != head) = false)
    (hiota : (tryIotaWithFlags (.app f arg info) flags).run methods s1 =
      .ok (some result) s2) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .ok (.next result) s2 := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  cases hnonlam <;> simp only
  all_goals
    rw [hself]
    change EStateM.bind
      (ReaderT.run (tryIotaWithFlags (.app f arg info) flags) methods) _ s1 = _
    unfold EStateM.bind
    rw [hiota]
    rfl

/-- Complete unchanged non-lambda tail.  A miss is reflexive at the original
source; a hit uses the optional iota contract directly; an error retains the
helper's partial post-state. -/
theorem whnfCoreWithFlagsStep_appUnchanged_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s1 : TcState .anon} {f arg head : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hiota : OptionalReduction.WF layer semantics trProj world support
      (fun source => tryIotaWithFlags source flags))
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hsourceSupport : support (.app f arg info))
    {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda head)
    (hhead : methods.whnfCoreFlags head flags s = .ok head s1)
    (hI1 : WhnfStateInv layer semantics trProj world support uvars Delta
      s1) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((whnfCoreWithFlagsStep (.app f arg info) flags).run methods)
      (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
        (.app f arg info) action) := by
  intro hI
  have hiotaPost := (hiota hsourceSupport hsource) methods hmethods hI1
  have hself : (head != head) = false := by
    change Bool.not (head.addr == head.addr) = false
    rw [beq_self_eq_true]
    rfl
  match hiotaRun :
      (tryIotaWithFlags (.app f arg info) flags).run methods s1 with
  | .error err s2 =>
      rw [hiotaRun] at hiotaPost
      rw [whnfCoreWithFlagsStep_appUnchangedIotaError hspine hnonlam hhead
        hself hiotaRun]
      exact ⟨hiotaPost.1, trivial⟩
  | .ok none s2 =>
      rw [hiotaRun] at hiotaPost
      rw [whnfCoreWithFlagsStep_appUnchangedDone hspine hnonlam hhead hself
        hiotaRun]
      exact ⟨hiotaPost.1, hsourceSupport,
        WhnfMeaning.refl hsource (theory.exprWF hI1.2.1 hsource)⟩
  | .ok (some result) s2 =>
      rw [hiotaRun] at hiotaPost
      rw [whnfCoreWithFlagsStep_appUnchangedIota hspine hnonlam hhead hself
        hiotaRun]
      exact ⟨hiotaPost.1, hiotaPost.2.1, hiotaPost.2.2⟩

/-- Complete changed non-lambda tail.  Head congruence justifies the rebuilt
source; an iota hit is composed transitively with that meaning, while a miss
returns the rebuilt source itself. -/
theorem whnfCoreWithFlagsStep_appChanged_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hfinishCensus : ApplicationFinishRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {s s1 : TcState .anon} {f arg head changed : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {sourceV headV : Lean4Lean.VExpr} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hiota : OptionalReduction.WF layer semantics trProj world support
      (fun source => tryIotaWithFlags source flags))
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hsourceSupport : support (.app f arg info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hsuffix : TrAppSuffix world.venv uvars world.nameOf trProj Delta headV
      args.toList sourceV)
    (hchangedSupport : support changed)
    (hheadPost : WhnfPost trProj world uvars Delta headV changed)
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s1)
    (hchanged : (changed != head) = true)
    (hI1 : WhnfStateInv layer semantics trProj world support uvars Delta
      s1) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((whnfCoreWithFlagsStep (.app f arg info) flags).run methods)
      (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
        (.app f arg info) action) := by
  intro hI
  obtain ⟨rebuilt, s2, hfinish, hfinishRun, hI2, hframe,
      hrebuiltSupport, happMeaning⟩ :=
    changedHeadFinish_acceptance hrun hfinishCensus hsourceSupport hsource
      hspine hsuffix hchangedSupport hheadPost hI1
  have happMeaningSaved := happMeaning
  obtain ⟨sourceV2, rebuiltV, hsourceTr2, hrebuiltTr, hrebuildEq⟩ :=
    happMeaning
  have hiotaPost :=
    (hiota hrebuiltSupport hrebuiltTr) methods hmethods hI2
  match hiotaRun : (tryIotaWithFlags rebuilt flags).run methods s2 with
  | .error err s3 =>
      rw [hiotaRun] at hiotaPost
      rw [whnfCoreWithFlagsStep_appChangedIotaError hspine hnonlam hhead
        hchanged hfinishRun hiotaRun]
      exact ⟨hiotaPost.1, trivial⟩
  | .ok none s3 =>
      rw [hiotaRun] at hiotaPost
      rw [whnfCoreWithFlagsStep_appChangedDone hspine hnonlam hhead hchanged
        hfinishRun hiotaRun]
      exact ⟨hiotaPost.1, hrebuiltSupport, happMeaningSaved⟩
  | .ok (some result) s3 =>
      rw [hiotaRun] at hiotaPost
      rw [whnfCoreWithFlagsStep_appChangedIota hspine hnonlam hhead hchanged
        hfinishRun hiotaRun]
      have hmeaning := theory.transMeaning hI2.2.1.wf happMeaningSaved
        hiotaPost.2.2
      exact ⟨hiotaPost.1, hiotaPost.2.1, hmeaning⟩

end RecM
end Ix.Tc
