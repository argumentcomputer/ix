import Ix.Tc.Verify.Infer.LeafCases
import Ix.Tc.Verify.RecursiveMethods.Inference
import Ix.Tc.Verify.RecursiveMethods.Public

/-!
# A positive-fuel inference schedule

This module instantiates the call-domain machinery on the smallest genuine
production inference execution: one admitted sort source at method-table
depth one.  The predecessor table admits no calls because the sort leaf only
interns its successor-sort result; it does not recurse through `Methods`.

The finite `RunSupport` still contains both source and result.  Crucially,
membership of the result does not make it another inference call, so this
contract does not demand closure under an infinite tower of successor sorts.
-/

namespace Ix.Tc

namespace InferenceCallDomainContext

/-- Build the guarded production cache shell around the method-independent
sort leaf. -/
def sort
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    (predecessor : Methods.CallDomain) :
    InferenceCallDomainContext scope model
      (.singletonInfer (.sort u info)) predecessor where
  collisionFree := hcollision
  currentWithin := Methods.CallDomain.singletonInfer_within hsourceSupport
  theory := theory
  references := references
  uncached := by
    intro Delta s inferOnly source sourceV hcall hsource
    change source = .sort u info at hcall
    subst source
    apply RecM.WFOn.ofWF_of_methodIndependent
    · intro methods
      funext state
      rfl
    · exact RecM.inferUncached_sort_wf theory hcollision hresultSupport
        hsource

end InferenceCallDomainContext

namespace Methods

/-- One production `Methods.next` layer is sound for exactly one sort
inference call when its predecessor admits no calls. -/
theorem next_sort_wfAtOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    {predecessor : Methods.CallDomain}
    (context : InferenceCallDomainContext scope model
      (.singletonInfer (.sort u info)) predecessor)
    (predecessorMethods : Methods .anon)
    (predecessorWF : Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world scope
      model.keys.uvars predecessor predecessorMethods) :
    Methods.WFAtOn .noAccel (kernelCacheSemantics model.keys trProj)
      trProj world scope model.keys.uvars
      (.singletonInfer (.sort u info)) (Methods.next predecessorMethods) where
  within := context.currentWithin
  whnf hcall := False.elim hcall
  whnfCore hcall := False.elim hcall
  whnfMode hcall := False.elim hcall
  whnfCoreFlags hcall := False.elim hcall
  infer hcall hsource :=
    context.nextInfer_wfAtOn predecessorMethods predecessorWF hcall hsource
  isDefEq hcall := False.elim hcall

namespace SortSchedule

/-- Exact call domains for the depth-one sort fixture. -/
def calls (source : KExpr .anon) : Nat → CallDomain
  | 0 => .empty
  | _ + 1 => .singletonInfer source

@[simp] theorem calls_zero (source : KExpr .anon) :
    calls source 0 = .empty := rfl

@[simp] theorem calls_succ (source : KExpr .anon) (n : Nat) :
    calls source (n + 1) = .singletonInfer source := rfl

/-- A non-circular, positive-fuel schedule for one real production method
layer. -/
theorem one
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (context : InferenceCallDomainContext scope model
      (.singletonInfer (.sort u info)) .empty) :
    CallScheduleAt .noAccel (kernelCacheSemantics model.keys trProj)
      trProj world scope model.keys.uvars (calls (.sort u info)) 1 where
  within n hn := by
    cases n with
    | zero => exact Methods.CallDomain.empty_within scope
    | succ n => exact context.currentWithin
  step n hn := by
    cases n with
    | zero => exact next_sort_wfAtOn context
    | succ n => omega

/-- The selected depth-one production table satisfies the exact singleton
sort-inference contract. -/
theorem selected
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (context : InferenceCallDomainContext scope model
      (.singletonInfer (.sort u info)) .empty) :
    Methods.WFAtOn .noAccel (kernelCacheSemantics model.keys trProj)
      trProj world scope model.keys.uvars
      (.singletonInfer (.sort u info))
      (Ix.Tc.methodsN (m := .anon) 1) := by
  simpa [calls] using (one context).selected

/-- The same finite source/result footprint supports every finite table depth:
after depth zero the admitted domain remains the singleton source, while each
sort body is method-independent.  No higher successor sort is added. -/
theorem finite
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    (depth : Nat) :
    CallScheduleAt .noAccel (kernelCacheSemantics model.keys trProj)
      trProj world scope model.keys.uvars (calls (.sort u info)) depth where
  within n hn := by
    cases n with
    | zero => exact Methods.CallDomain.empty_within scope
    | succ n =>
        exact Methods.CallDomain.singletonInfer_within hsourceSupport
  step n hn := by
    let context := InferenceCallDomainContext.sort hcollision hsourceSupport
      hresultSupport theory references (calls (.sort u info) n)
    exact next_sort_wfAtOn context

/-- In particular, recursion fuel one has two justified body layers: the
public body and its one-layer callback table. -/
theorem two
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope) :
    CallScheduleAt .noAccel (kernelCacheSemantics model.keys trProj)
      trProj world scope model.keys.uvars (calls (.sort u info)) 2 :=
  finite hcollision hsourceSupport hresultSupport theory references 2

end SortSchedule

end Methods

namespace TcM.infer

/-- A public sort-inference run at any finite recursion fuel.  The source and
its successor-sort result share one fixed finite result/collision footprint,
while the call schedule contains only the source at each positive table
depth. -/
theorem sort_wf_bounded
    {initial : TcState .anon} {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {proposition : PropositionClassifierContext trProj world scope}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (run : RunAssumptions initial (TcM.infer (.sort u info)) requests scope)
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world proposition.model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv proposition.model.keys.uvars world.nameOf
      trProj Delta (.sort u info) sourceV) :
    TcM.WF
      (WhnfStateInv .noAccel
        (kernelCacheSemantics proposition.model.keys trProj) trProj world
        scope proposition.model.keys.uvars Delta)
      initial (TcM.infer (.sort u info))
      (fun result _ => scope result ∧
        InferPost trProj world proposition.model.keys.uvars Delta sourceV
          result) := by
  let context : RecursiveMethodRunContext initial
      (TcM.infer (.sort u info)) requests trProj world scope := {
    run := run
    proposition := proposition
    calls := Methods.SortSchedule.calls (.sort u info)
    schedule := Methods.SortSchedule.finite hcollision hsourceSupport
      hresultSupport theory references (initial.recFuel.toNat + 1) }
  exact TcM.infer.wf_legacy context (by
    change (.sort u info : KExpr .anon) = .sort u info
    rfl) hsource

/-- Explicit positive-fuel specialization.  At recursion fuel one, production
uses `methodsN 1` for callbacks and the schedule certifies its outer body at
depth two. -/
theorem sort_wf_fuel_one
    {initial : TcState .anon} {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {proposition : PropositionClassifierContext trProj world scope}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hfuel : initial.recFuel.toNat = 1)
    (run : RunAssumptions initial (TcM.infer (.sort u info)) requests scope)
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world proposition.model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv proposition.model.keys.uvars world.nameOf
      trProj Delta (.sort u info) sourceV) :
    TcM.WF
      (WhnfStateInv .noAccel
        (kernelCacheSemantics proposition.model.keys trProj) trProj world
        scope proposition.model.keys.uvars Delta)
      initial (TcM.infer (.sort u info))
      (fun result _ => scope result ∧
        InferPost trProj world proposition.model.keys.uvars Delta sourceV
          result) := by
  let context : RecursiveMethodRunContext initial
      (TcM.infer (.sort u info)) requests trProj world scope := {
    run := run
    proposition := proposition
    calls := Methods.SortSchedule.calls (.sort u info)
    schedule := by
      rw [hfuel]
      exact Methods.SortSchedule.two hcollision hsourceSupport
        hresultSupport theory references }
  exact TcM.infer.wf_legacy context (by
    change (.sort u info : KExpr .anon) = .sort u info
    rfl) hsource

end TcM.infer

end Ix.Tc
