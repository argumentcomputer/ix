import Ix.Tc.Verify.Whnf.Structural.ProjectionStep

/-!
# Changed-head application congruence

The changed-head branch cannot use the callback's head-level equality as if
it were already equality of the complete application.  Every original spine
argument must be reattached with its typing derivation, in production order.

This slice converts `TrAppSpine` into the typed-suffix representation used by
the checked iota proofs, ties the recursive callback to that exact head
translation, and transports its definitional equality across the complete
suffix.  A `FinishAppRequests` certificate then identifies the semantic
left fold with the expression actually returned by `finishAppResult`.
-/

namespace Ix.Tc
namespace RecM

namespace TrAppSpine

/-- View a typed spine as a translated head followed by a typed application
suffix.  Unlike `headTr`, this keeps the chosen head translation connected to
all argument typing derivations. -/
theorem toSuffix
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head : KExpr .anon}
    {args : List (KExpr .anon)} {resultV : Lean4Lean.VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head args resultV) :
    exists headV,
      TrKExprS env uvars nameOf trProj Delta head headV /\
      TrAppSuffix env uvars nameOf trProj Delta headV args resultV := by
  induction h with
  | head hhead => exact ⟨_, hhead, .nil⟩
  | app hprefix hfun harg hargTr ih =>
      obtain ⟨headV, hheadTr, hsuffix⟩ := ih
      exact ⟨headV, hheadTr, .app hsuffix hfun harg hargTr⟩

end TrAppSpine

/-- Strong application-head callback adapter.  The callback postcondition is
indexed by the same head translation that anchors the full typed suffix. -/
theorem applicationHeadCallbackWithSuffix_wf
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
      TrAppSuffix world.venv uvars world.nameOf trProj Delta headV
        args.toList sourceV /\
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreFlagsRec head flags)
        (fun result _ => support result /\
          WhnfPost trProj world uvars Delta headV result) := by
  have htyped := trAppSpine_of_collectSpine hsource hspine
  obtain ⟨headV, hheadTr, hsuffix⟩ := htyped.toSuffix
  have hheadSupport := (hinputs.app hsupport hspine).1
  exact ⟨headV, hheadTr, hsuffix,
    whnfCoreFlagsRec_wf hheadSupport hheadTr⟩

namespace WhnfMeaning

/-- Replace the translated head of an application by a callback result and
rebuild every original argument.  The callback equality is lifted through
the typed suffix using Theory application congruence; the finite request
certificate identifies that pure rebuilt spine with production's concrete
result. -/
theorem appHeadRebuild
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source changed rebuilt : KExpr .anon}
    {args : Array (KExpr .anon)} {sourceV headV : Lean4Lean.VExpr}
    {requests : List WalkerRequest}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hsuffix : TrAppSuffix world.venv uvars world.nameOf trProj Delta headV
      args.toList sourceV)
    (hhead : WhnfPost trProj world uvars Delta headV changed)
    (hfinish : FinishAppRequests requests
      (args.extract 0 args.size).toList changed rebuilt) :
    WhnfMeaning trProj world uvars Delta source rebuilt := by
  obtain ⟨changedV, hchangedTr, hheadEq⟩ := hhead
  obtain ⟨rebuiltV, hrebuiltTr, hrebuildEq⟩ :=
    hsuffix.rebase world.venvWF hDelta hchangedTr hheadEq
  have hresult : rebuilt = args.toList.foldl KExpr.mkApp changed := by
    simpa using hfinish.result_eq_foldl
  rw [← hresult] at hrebuiltTr
  exact ⟨sourceV, rebuiltV, hsource, hrebuiltTr, hrebuildEq⟩

end WhnfMeaning

end RecM
end Ix.Tc
