import Ix.Tc.Verify.Whnf.Structural.ApplicationTails

/-!
# General beta branch boundary and execution

The production beta branch peels as many lambdas as the application spine
provides, performs one simultaneous substitution with the consumed arguments
in de Bruijn order, and rebuilds only the unconsumed suffix.  This slice
closes all of that runtime behavior from the finite request census.

The one remaining semantic ingredient is named separately as
`BetaManyMeaningOracle`.  It is purely a Theory bridge from the typed original
spine, the callback's head equality, the exact `consumeBetaLams` equation, and
the substitution bounds to the final certified rebuild.  No state effect,
support fact, or production execution is hidden in that interface.
-/

namespace Ix.Tc
namespace RecM

/-- Finite request census for every dynamic multi-beta branch reachable from
a supported application and supported lambda callback result. -/
def BetaRequestCensus (requests : List WalkerRequest)
    (support : RunSupport) : Prop :=
  forall {f arg head : KExpr .anon} {info : ExprInfo .anon}
      {args : Array (KExpr .anon)}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {ty body body0 : KExpr .anon} {lamInfo : ExprInfo .anon}
      {consumed : Array (KExpr .anon)},
    support (.app f arg info) ->
    (.app f arg info : KExpr .anon).collectSpine = (head, args) ->
    support (.lam name bi ty body lamInfo) ->
    consumeBetaLams (.lam name bi ty body lamInfo) args =
      (body0, consumed) ->
    (!consumed.isEmpty) = true /\
      WalkerRequest.simulSubst body0 consumed.reverse 0 ∈ requests /\
      exists result,
        FinishAppRequests requests
          (args.extract consumed.size args.size).toList
          (KExpr.simulSubstSpec body0 consumed.reverse 0) result

/-- Theory-only semantic bridge still required for general multi-beta.  The
resource bound is the exact bound already checked for the production walker;
the rebuild certificate fixes the unconsumed suffix and its order. -/
def BetaManyMeaningOracle (trProj : RawProjRel) (world : VerifyWorld) : Prop :=
  forall {uvars : Nat}, WhnfTheory trProj world uvars ->
    forall {Delta : KVLCtx} {requests : List WalkerRequest}
      {f arg : KExpr .anon}
      {info : ExprInfo .anon} {args : Array (KExpr .anon)}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {ty body body0 : KExpr .anon} {lamInfo : ExprInfo .anon}
      {consumed : Array (KExpr .anon)} {result : KExpr .anon}
      {sourceV headV : Lean4Lean.VExpr},
    KVLCtx.WF world.venv uvars Delta ->
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV ->
    TrAppSuffix world.venv uvars world.nameOf trProj Delta headV
      args.toList sourceV ->
    WhnfPost trProj world uvars Delta headV
      (.lam name bi ty body lamInfo) ->
    consumeBetaLams (.lam name bi ty body lamInfo) args =
      (body0, consumed) ->
    (WalkerRequest.simulSubst body0 consumed.reverse 0).Bounds ->
    FinishAppRequests requests
      (args.extract consumed.size args.size).toList
      (KExpr.simulSubstSpec body0 consumed.reverse 0) result ->
    WhnfMeaning trProj world uvars Delta (.app f arg info) result

/-- Complete general beta tail for one successful lambda callback.  The
walker and suffix rebuild are both total under their finite certificates, so
the branch has one exact successful result and preserves the invariant
through the composed intern-only frame. -/
theorem whnfCoreWithFlagsStep_appBeta_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hcensus : BetaRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {s s1 : TcState .anon} {f arg head : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body body0 : KExpr .anon} {lamInfo : ExprInfo .anon}
    {consumed : Array (KExpr .anon)} {sourceV headV : Lean4Lean.VExpr}
    {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hmeaning : BetaManyMeaningOracle trProj world)
    (hsourceSupport : support (.app f arg info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hsuffix : TrAppSuffix world.venv uvars world.nameOf trProj Delta headV
      args.toList sourceV)
    (hlamSupport : support (.lam name bi ty body lamInfo))
    (hheadPost : WhnfPost trProj world uvars Delta headV
      (.lam name bi ty body lamInfo))
    (hhead : methods.whnfCoreFlags head flags s =
      .ok (.lam name bi ty body lamInfo) s1)
    (hconsume : consumeBetaLams (.lam name bi ty body lamInfo) args =
      (body0, consumed))
    (hI1 : WhnfStateInv layer semantics trProj world support uvars Delta
      s1) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((whnfCoreWithFlagsStep (.app f arg info) flags).run methods)
      (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
        (.app f arg info) action) := by
  intro hI
  obtain ⟨hnonempty, hsubstMem, result, hfinish⟩ :=
    hcensus hsourceSupport hspine hlamSupport hconsume
  obtain ⟨s2, hsubstRun, hI2, hsubstFrame⟩ :=
    hrun.simulSubst_whnf_eval hsubstMem hI1
  obtain ⟨s3, hfinishRun, hI3, hfinishFrame⟩ :=
    hfinish.eval hrun hI2
  have hsubSupport :
      support (KExpr.simulSubstSpec body0 consumed.reverse 0) :=
    hrun.coverage.simulSubst hsubstMem _
      (KExpr.SimulSubstReach.spec consumed.reverse body0 0)
  have hresultSupport : support result :=
    hfinish.support hrun hsubSupport
  have hresultMeaning := hmeaning theory hI1.2.1.wf hsource hsuffix
    hheadPost hconsume (hrun.requestBounds hsubstMem) hfinish
  rw [whnfCoreWithFlagsStep_betaMany hspine hhead hconsume hnonempty
    hsubstRun hfinishRun]
  exact ⟨hI3, hresultSupport, hresultMeaning⟩

end RecM
end Ix.Tc
