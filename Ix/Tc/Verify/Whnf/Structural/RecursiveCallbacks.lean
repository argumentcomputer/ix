import Ix.Tc.Verify.Whnf.Structural.VariableStep

/-!
# Structural recursive-callback closure

The remaining projection and application cases both recurse through the
predecessor method table before their syntax-directed helper runs.  A
structural translation already identifies the projected value and the
application-spine head, but `RunSupport` is an arbitrary finite predicate:
support for a parent expression does not silently imply support for either
child.

This slice names that finite child-coverage obligation and then instantiates
the exact full/cheap callback contracts from `Methods.WF`.  It is deliberately
only a support boundary; semantic translation of each child is derived from
the translated parent.
-/

namespace Ix.Tc
namespace RecM

/-- Finite support closure needed by one structural-WHNF iteration.  The app
field covers both the head callback and every argument later consumed by beta,
iota, or application rebuilding. -/
structure WhnfCoreInputSupport (support : RunSupport) : Prop where
  projection : forall {id : KId .anon} {field : UInt64}
      {value : KExpr .anon} {info : ExprInfo .anon},
    support (.prj id field value info) -> support value
  app : forall {f arg : KExpr .anon} {info : ExprInfo .anon}
      {head : KExpr .anon} {args : Array (KExpr .anon)},
    support (.app f arg info) ->
    (.app f arg info : KExpr .anon).collectSpine = (head, args) ->
    support head /\ forall child, child ∈ args.toList -> support child

/-- The recursive structural-WHNF callback is exactly the corresponding
field of the predecessor method table. -/
theorem whnfCoreFlagsRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {flags : WhnfFlags}
    (hsource : support source)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfCoreFlagsRec source flags)
      (fun result _ => support result /\
        WhnfPost trProj world uvars Delta sourceV result) := by
  intro methods hmethods
  simpa only [whnfCoreFlagsRec] using
    hmethods.whnfCoreFlags hsource htr

namespace TrAppSpine

/-- A typed application spine retains the translation of its raw head. -/
theorem headTr
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head : KExpr .anon}
    {args : List (KExpr .anon)} {resultV : Lean4Lean.VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head args resultV) :
    exists headV,
      TrKExprS env uvars nameOf trProj Delta head headV := by
  induction h with
  | head hhead => exact ⟨_, hhead⟩
  | app hprefix hfun harg hargTr ih => exact ih

end TrAppSpine

/-- The projection-value callback inherits either full WHNF or structural
WHNF according to the production `cheapProj` branch.  Translation of the
value is obtained by inversion of the translated projection source. -/
theorem projectionValueCallback_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {id : KId .anon} {field : UInt64} {value : KExpr .anon}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    {flags : WhnfFlags}
    (hinputs : WhnfCoreInputSupport support)
    (hsupport : support (.prj id field value info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj id field value info) sourceV) :
    exists valueV,
      TrKExprS world.venv uvars world.nameOf trProj Delta value valueV /\
      RecM.WF layer semantics trProj world support uvars Delta s
        (if flags.cheapProj then whnfCoreFlagsRec value flags
          else whnfRec value)
        (fun result _ => support result /\
          WhnfPost trProj world uvars Delta valueV result) := by
  cases hsource with
  | prj hname hvalueTr hproj =>
      refine ⟨_, hvalueTr, ?_⟩
      have hvalueSupport := hinputs.projection hsupport
      cases hcheap : flags.cheapProj with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact whnfRec_wf hvalueSupport hvalueTr
      | true =>
          simp only [if_true]
          exact whnfCoreFlagsRec_wf hvalueSupport hvalueTr

/-- The application-head callback is justified by the actual production
spine equation.  `TrAppSpine` supplies its translation and the finite input
support boundary supplies its callback admissibility. -/
theorem applicationHeadCallback_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {f arg head : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {sourceV : Lean4Lean.VExpr}
    {flags : WhnfFlags}
    (hinputs : WhnfCoreInputSupport support)
    (hsupport : support (.app f arg info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args)) :
    exists headV,
      TrKExprS world.venv uvars world.nameOf trProj Delta head headV /\
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreFlagsRec head flags)
        (fun result _ => support result /\
          WhnfPost trProj world uvars Delta headV result) := by
  have htyped := trAppSpine_of_collectSpine hsource hspine
  obtain ⟨headV, hheadTr⟩ := htyped.headTr
  have hheadSupport := (hinputs.app hsupport hspine).1
  exact ⟨headV, hheadTr,
    whnfCoreFlagsRec_wf hheadSupport hheadTr⟩

/-- Every concrete member of the production argument array is in finite run
support.  This projection of `WhnfCoreInputSupport` is the form consumed by
the walker and rebuild request censuses in the remaining app proof. -/
theorem applicationArgument_support
    {support : RunSupport} (hinputs : WhnfCoreInputSupport support)
    {f arg head child : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    (hsupport : support (.app f arg info))
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hmem : child ∈ args.toList) :
    support child :=
  (hinputs.app hsupport hspine).2 child hmem

end RecM
end Ix.Tc
