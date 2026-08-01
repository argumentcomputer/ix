import Ix.Tc.Verify.Check.FullInferenceBinders
import Ix.Tc.Verify.Infer.ProjectionTypes

/-!
# Full inference for projections

The K2 projection branch starts from a typed `TrKExprS` source.  At checker
ingress K3 instead has only `PreTrKExprS`: it first establishes a typed
translation for the projected value, then delegates to the already verified
`inferProj` helper.

The helper's semantic contract is intentionally separate from its operational
policy frame.  A typing proof alone cannot show that a partial error preserved
`TcState.inferOnly`; `ProjectionInference.FullWFAt` combines those two facts
for one concrete smaller method table.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace ProjectionInference

/-- Outcome-sensitive policy frame for every invocation of `inferProj` using
one fixed recursive method table. -/
def PreservesInferOnlyAt (methods : Methods .anon) : Prop :=
  ∀ structId field val valTy,
    ((RecM.inferProj structId field val valTy).run methods).PreservesInferOnly

/-- Strong projection-helper contract needed by K3 full inference.  It is
fixed to the smaller production method table and retains full mode on both
success and error. -/
def FullWFAt (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (methods : Methods .anon) : Prop :=
  ∀ {Delta : KVLCtx} {s : TcState .anon}
      {structId : KId .anon} {field : UInt64} {val valTy : KExpr .anon}
      {valV projectedV : VExpr} {structName : Lean.Name},
    s.inferOnly = false →
    world.nameOf structId.addr = some structName →
    TrKExprS world.venv uvars world.nameOf trProj Delta val valV →
    trProj Delta.toCtx structName field.toNat valV projectedV →
    support valTy →
    InferPost trProj world uvars Delta valV valTy →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((RecM.inferProj structId field val valTy).run methods)
      (fun result after =>
        after.inferOnly = false ∧ support result ∧
          InferPost trProj world uvars Delta projectedV result)
      (fun _ after => after.inferOnly = false)

/-- Combine K2 projection soundness with the independent full-mode frame.
This is the only adapter from the ordinary, method-parametric projection
contract to K3's fixed-table contract. -/
theorem FullWFAt.of_semantic_and_policy
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {methods : Methods .anon}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hsemantic : WF semantics trProj world support uvars)
    (hpolicy : PreservesInferOnlyAt methods) :
    FullWFAt semantics trProj world support uvars methods := by
  intro Delta s structId field val valTy valV projectedV structName
    hbefore hname hval hproj hvalTySupport hvalTy
  apply TcM.WF.mono
    (TcM.PreservesInferOnly.strengthenWFValue
      (hsemantic hname hval hproj hvalTySupport hvalTy methods hmethods)
      (hpolicy structId field val valTy) hbefore)
  · intro _ _ post
    exact post
  · intro _ _ post
    exact post.1

end ProjectionInference

namespace RecM

/-- Full-mode projection inference upgrades the recursively inferred value
from pre-translation to typed translation before invoking `inferProj`. -/
theorem inferUncached_prj_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {structId : KId .anon} {field : UInt64} {val : KExpr .anon}
    {info : ExprInfo .anon} {sourceV : VExpr}
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (hinputs : ProjectionValueSupport support)
    (hprojection : ProjectionInference.FullWFAt semantics trProj world
      support uvars methods)
    (hsourceSupport : support (.prj structId field val info))
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj structId field val info) sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false (.prj structId field val info)).run
        methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.prj structId field val info) sourceV result)
      (fun _ after => after.inferOnly = false) := by
  cases hsource with
  | prj hname hvalPre hproj =>
      rename_i valV projectedV
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, inferCall]
      apply TcM.WF.bind
        (callbacks.infer hpolicy (hinputs hsourceSupport) hvalPre)
      intro valTy afterValue hvaluePost
      rcases hvaluePost with
        ⟨hpolicyValue, hvalTySupport, hvalTr, valTyV, hvalTyTr, hvalType⟩
      apply TcM.WF.mono
        (hprojection hpolicyValue hname hvalTr hproj hvalTySupport
          ⟨valTyV, hvalTyTr, hvalType⟩)
      · intro result _ hresult
        exact ⟨hresult.1, hresult.2.1,
          .prj hname hvalTr hproj, hresult.2.2⟩
      · intro _ _ herror
        exact herror

end RecM

end Ix.Tc
