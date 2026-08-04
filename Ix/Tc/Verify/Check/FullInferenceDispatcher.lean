import Ix.Tc.Verify.Check.FullInferenceProjections
import Ix.Tc.Verify.Infer.Dispatcher

/-!
# Exhaustive full-mode inference dispatcher

This module assembles the constructor-local K3 proofs for
`inferUncached inferCall false`.  Unlike the K2 dispatcher, its input is only
`PreTrKExprS`; successful execution establishes the missing typed source
translation as part of `FullInferPost`.

The context keeps semantic closure and operational policy frames separate.
In particular, neither the ordinary method-table contract nor a successful
typing postcondition says what `inferOnly` contains after a partial error.
-/

namespace Ix.Tc

namespace FullUncachedInference

/-- Resources for one full-mode layer over a fixed smaller method table.
`uncachedPolicy` covers the leaf actions reused from K2, while
`projectionPolicy` exposes the corresponding frame for the projection helper
itself.  Both are purely operational obligations to be discharged by the
concrete policy closure proof. -/
structure Context
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (methods : Methods .anon) : Type where
  base : UncachedInference.Context initial program requests semantics trProj
    world support uvars
  methodSemantics : Methods.WFAt .noAccel semantics trProj world support
    uvars methods
  callbacks : FullInferenceStepContext semantics trProj world support uvars
    methods
  uncachedPolicy : ∀ inferOnly source,
    ((RecM.inferUncached RecM.inferCall inferOnly source).run methods).PreservesInferOnly
  projectionPolicy : ProjectionInference.PreservesInferOnlyAt methods

end FullUncachedInference

namespace RecM

/-- Add the fixed full-mode policy fact to a semantic leaf proof. -/
private theorem strengthenFullLeaf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {source : KExpr .anon}
    {sourceV : Lean4Lean.VExpr} {methods : Methods .anon}
    (hsemantic : TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false source).run methods)
      (fun result _ =>
        FullInferPost trProj world support uvars Delta source sourceV result))
    (hframe :
      ((inferUncached inferCall false source).run methods).PreservesInferOnly)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false source).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support uvars Delta source sourceV result)
      (fun _ after => after.inferOnly = false) := by
  apply TcM.WF.mono
    (TcM.PreservesInferOnly.strengthenWFValue hsemantic hframe hpolicy)
  · intro _ _ post
    exact post
  · intro _ _ post
    exact post.1

/-- Exhaustive K3 correctness of `inferUncached` in full mode.  Every syntax
constructor is covered from untyped structural ingress, and both outcomes
retain `inferOnly = false`. -/
theorem inferUncached_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      semantics trProj world support uvars methods)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false source).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support uvars Delta source sourceV result)
      (fun _ after => after.inferOnly = false) := by
  cases source with
  | var idx name info =>
      intro hI
      obtain ⟨hrequest, hbound⟩ :=
        context.base.variables hI hsourceSupport
      exact (strengthenFullLeaf
        ((inferUncached_var_full_wf context.base.projection.run
          context.base.projection.theory hsource hrequest hbound)
          methods context.methodSemantics)
        (context.uncachedPolicy false (.var idx name info)) hpolicy) hI
  | fvar fv name info =>
      exact strengthenFullLeaf
        ((inferUncached_fvar_full_wf context.base.projection.theory
          (context.base.fvars Delta) hsource)
          methods context.methodSemantics)
        (context.uncachedPolicy false (.fvar fv name info)) hpolicy
  | sort u info =>
      exact strengthenFullLeaf
        ((inferUncached_sort_full_wf context.base.projection.theory
          context.base.projection.run.collisionFree
          (context.base.structural.sortResult hsourceSupport) hsource)
          methods context.methodSemantics)
        (context.uncachedPolicy false (.sort u info)) hpolicy
  | const id levels info =>
      exact strengthenFullLeaf
        ((inferUncached_const_full_wf context.base.projection.run
          context.base.projection.theory (context.base.projection.fault Delta)
          context.base.references context.base.constTypes
          context.base.constants hsourceSupport hsource)
          methods context.methodSemantics)
        (context.uncachedPolicy false (.const id levels info)) hpolicy
  | app f a info =>
      exact inferUncached_app_full_wf context.base.projection.run
        context.base.projection.theory context.callbacks
        context.methodSemantics context.base.applications hsourceSupport
        hsource hpolicy
  | lam name bi ty body info =>
      obtain ⟨hty, hbinder, hresult⟩ :=
        context.base.structural.lambda hsourceSupport
      exact inferUncached_lam_full_wf context.base.projection.run
        context.base.projection.theory context.callbacks
        context.base.cheapBeta context.base.abstraction hresult hty hbinder
        hsource hpolicy
  | all name bi ty body info =>
      obtain ⟨hty, hbinder⟩ :=
        context.base.structural.forallE hsourceSupport
      exact inferUncached_all_full_wf context.base.projection.run
        context.base.projection.theory context.callbacks
        context.base.abstraction context.base.forallResults hty hbinder
        hsource hpolicy
  | letE name ty val body nondep info =>
      obtain ⟨hty, hval, hbinder⟩ :=
        context.base.structural.letE hsourceSupport
      exact inferUncached_let_full_wf context.base.projection.theory
        context.callbacks context.base.abstraction
        context.base.projection.substitution context.base.cheapBeta hty hval
        hbinder context.base.projection.run.collisionFree hsource hpolicy
  | prj structId field val info =>
      have hprojection : ProjectionInference.FullWFAt semantics trProj world
          support uvars methods :=
        ProjectionInference.FullWFAt.of_semantic_and_policy
          context.methodSemantics context.base.projection.wf
          context.projectionPolicy
      exact inferUncached_prj_full_wf context.callbacks
        context.base.projectionValues hprojection hsourceSupport hsource
        hpolicy
  | nat n blob info =>
      exact strengthenFullLeaf
        ((inferUncached_nat_full_wf context.base.literals
          context.base.projection.theory hsource)
          methods context.methodSemantics)
        (context.uncachedPolicy false (.nat n blob info)) hpolicy
  | str value blob info =>
      exact strengthenFullLeaf
        ((inferUncached_str_full_wf context.base.literals
          context.base.projection.theory hsource)
          methods context.methodSemantics)
        (context.uncachedPolicy false (.str value blob info)) hpolicy

end RecM

end Ix.Tc
