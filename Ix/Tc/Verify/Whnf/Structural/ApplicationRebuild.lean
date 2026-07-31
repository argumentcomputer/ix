import Ix.Tc.Verify.Whnf.Structural.ApplicationCongruence

/-!
# Changed-head rebuild execution

ApplicationCongruence proves the semantic congruence theorem for a certified rebuild.  This
slice supplies those certificates uniformly for every supported application
that can enter the structural loop and every supported result returned by its
head callback.  The guard keeps the obligation finite while covering the
dynamic callback result rather than one hand-picked expression.
-/

namespace Ix.Tc
namespace RecM

/-- Finite request census for rebuilding the complete argument suffix after
a supported application head changes. -/
def ApplicationFinishRequestCensus (requests : List WalkerRequest)
    (support : RunSupport) : Prop :=
  forall {f arg head changed : KExpr .anon} {info : ExprInfo .anon}
      {args : Array (KExpr .anon)},
    support (.app f arg info) ->
    (.app f arg info : KExpr .anon).collectSpine = (head, args) ->
    support changed ->
    exists rebuilt,
      FinishAppRequests requests (args.extract 0 args.size).toList changed
        rebuilt

/-- Execute and justify one complete changed-head rebuild.  The result joins
four facts that later branch assembly needs simultaneously: the exact helper
run, invariant preservation, finite result support, and Theory meaning from
the original application to the rebuilt spine. -/
theorem changedHeadFinish_acceptance
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hcensus : ApplicationFinishRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {f arg head changed : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {sourceV headV : Lean4Lean.VExpr}
    (hsourceSupport : support (.app f arg info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hsuffix : TrAppSuffix world.venv uvars world.nameOf trProj Delta headV
      args.toList sourceV)
    (hchangedSupport : support changed)
    (hhead : WhnfPost trProj world uvars Delta headV changed)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    exists rebuilt s',
      FinishAppRequests requests (args.extract 0 args.size).toList changed
          rebuilt /\
      (finishAppResult changed args 0).run methods s = .ok rebuilt s' /\
      WhnfStateInv layer semantics trProj world support uvars Delta s' /\
      InternUpdateFrame s s' /\
      support rebuilt /\
      WhnfMeaning trProj world uvars Delta (.app f arg info) rebuilt := by
  obtain ⟨rebuilt, hfinish⟩ :=
    hcensus hsourceSupport hspine hchangedSupport
  obtain ⟨s', hfinishRun, hI', hframe⟩ := hfinish.eval hrun hI
  have hrebuiltSupport : support rebuilt :=
    hfinish.support hrun hchangedSupport
  have hmeaning := WhnfMeaning.appHeadRebuild hI.2.1.wf hsource hsuffix
    hhead hfinish
  exact ⟨rebuilt, s', hfinish, hfinishRun, hI', hframe,
    hrebuiltSupport, hmeaning⟩

end RecM
end Ix.Tc
