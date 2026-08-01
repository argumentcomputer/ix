import Ix.Tc.Verify.Infer.LeafCases
import Ix.Tc.Verify.RecursiveMethods.ScopedInference

/-!
# Positive-fuel inference under a run-scoped suffix model

This module closes the smallest genuine production recursion schedule without
a global suffix premise.  One sort source is admitted at every positive
method-table depth; its uncached body interns the successor sort and makes no
recursive callback.  Key memoization, interning, and cache insertion all
preserve `StateInScope` explicitly.
-/

namespace Ix.Tc

namespace ScopedInferenceCallDomainContext

/-- Build the scoped production cache shell around the method-independent
sort leaf. -/
def sort
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    (predecessor : Methods.CallDomain) :
    ScopedInferenceCallDomainContext scope model
      (.singletonInfer (.sort u info)) predecessor where
  collisionFree := hcollision
  currentWithin := Methods.CallDomain.singletonInfer_within hsourceSupport
  theory := theory
  references := references
  uncached := by
    intro Delta s inferOnly source sourceV hcall hsource
    change source = .sort u info at hcall
    subst source
    cases hsource with
    | sort hu =>
        unfold RecM.inferUncached
        apply RecM.ScopedWFOn.mono
          (RecM.ScopedWFOn.withInv <|
            RecM.ScopedWFOn.liftTcM <|
              TcM.intern_scoped_wf hcollision hresultSupport)
        · intro result after hresult
          rcases hresult with ⟨hI, rfl, _⟩
          refine ⟨hresultSupport, ?_⟩
          refine ⟨.sort (KUniv.toVLevel (KUniv.mkSucc u)), ?_, ?_⟩
          · exact (TrKExprS.sort (KUniv.toVLevel_mkSucc_wf hu)).trKExpr
              world.venvWF.ordered theory.literalWF theory.projections.wf
              hI.1.2.1.wf
          · simpa only [KUniv.toVLevel_mkSucc] using
              (Lean4Lean.VEnv.HasType.sort hu)
        · intro _ _ _
          trivial

end ScopedInferenceCallDomainContext

namespace Methods

/-- One production `Methods.next` layer is scoped-sound for exactly one sort
inference call when the predecessor satisfies its own finite call domain. -/
theorem next_sort_scopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    {predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model
      (.singletonInfer (.sort u info)) predecessor)
    (predecessorMethods : Methods .anon)
    (predecessorWF : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor
      predecessorMethods) :
    Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope
      (.singletonInfer (.sort u info)) (Methods.next predecessorMethods) where
  within := context.currentWithin
  whnf hcall := False.elim hcall
  whnfCore hcall := False.elim hcall
  whnfMode hcall := False.elim hcall
  whnfCoreFlags hcall := False.elim hcall
  infer hcall hsource :=
    context.nextInfer_scopedWFAtOn predecessorMethods predecessorWF hcall
      hsource
  isDefEq hcall := False.elim hcall

namespace ScopedSortSchedule

/-- Exact call domains for a finite sort execution. -/
def calls (source : KExpr .anon) : Nat → CallDomain
  | 0 => .empty
  | _ + 1 => .singletonInfer source

@[simp] theorem calls_zero (source : KExpr .anon) :
    calls source 0 = .empty := rfl

@[simp] theorem calls_succ (source : KExpr .anon) (n : Nat) :
    calls source (n + 1) = .singletonInfer source := rfl

/-- The same finite source/result footprint supports every finite table
depth.  The successor-sort result is a result, not another admitted call, so
no infinite successor-sort closure is required. -/
theorem finite
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    (depth : Nat) :
    ScopedCallScheduleAt model .noAccel
      (kernelCacheSemantics model.keys trProj) scope
      (calls (.sort u info)) depth where
  within n hn := by
    cases n with
    | zero => exact Methods.CallDomain.empty_within scope
    | succ n =>
        exact Methods.CallDomain.singletonInfer_within hsourceSupport
  step n hn := by
    let context := ScopedInferenceCallDomainContext.sort hcollision
      hsourceSupport hresultSupport theory references
      (calls (.sort u info) n)
    simpa [calls] using (next_sort_scopedWFAtOn context)

/-- Recursion fuel one selects a depth-one callback table and requires the
outer sort body at depth two. -/
theorem two
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope) :
    ScopedCallScheduleAt model .noAccel
      (kernelCacheSemantics model.keys trProj) scope
      (calls (.sort u info)) 2 :=
  finite hcollision hsourceSupport hresultSupport theory references 2

end ScopedSortSchedule

end Methods

namespace TcM.infer

/-- Public production sort inference at arbitrary finite fuel, proved
directly from a run-scoped suffix model. -/
theorem sort_scoped_wf_bounded
    {initial : TcState .anon}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      (.sort u info) sourceV) :
    TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) scope Delta)
      initial (TcM.infer (.sort u info))
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have schedule := Methods.ScopedSortSchedule.finite hcollision
    hsourceSupport hresultSupport theory references
    (initial.recFuel.toNat + 1)
  have hnext := schedule.nextSelected
  simpa [TcM.infer, TcM.runRec, Methods.next,
    Methods.ScopedSortSchedule.calls] using
      hnext.infer (by rfl) hsource

/-- Explicit fuel-one specialization of the scoped public sort run. -/
theorem sort_scoped_wf_fuel_one
    {initial : TcState .anon}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hfuel : initial.recFuel.toNat = 1)
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world model.keys.uvars)
    (references : RecM.TrustedReferences world scope)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      (.sort u info) sourceV) :
    TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) scope Delta)
      initial (TcM.infer (.sort u info))
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have _fuelWitness : initial.recFuel.toNat = 1 := hfuel
  exact sort_scoped_wf_bounded hcollision hsourceSupport hresultSupport
    theory references hsource

/-- The K2S construction can be consumed at the public positive-fuel entry
without first manufacturing a universally quantified suffix model. -/
theorem sort_finiteOperational_wf_fuel_one
    {initial : TcState .anon}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} (spec : ContextDigestSpec trProj world uvars)
    (digestScope : ContextDigestScope spec)
    (hdigestCollision : digestScope.CollisionFree)
    (suffixSemantics : ContextSuffixSemantics spec)
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hfuel : initial.recFuel.toNat = 1)
    (hcollision : scope.CollisionFree)
    (hsourceSupport : scope (.sort u info))
    (hresultSupport : scope (KExpr.mkSort (KUniv.mkSucc u)))
    (theory : WhnfTheory trProj world uvars)
    (references : RecM.TrustedReferences world scope)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.sort u info) sourceV) :
    let model := ScopedKernelSuffixModel.finiteOperational spec digestScope
      hdigestCollision suffixSemantics
    TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) scope Delta)
      initial (TcM.infer (.sort u info))
      (fun result _ => scope result ∧
        InferPost trProj world uvars Delta sourceV result) := by
  dsimp only
  exact sort_scoped_wf_fuel_one hfuel hcollision hsourceSupport
    hresultSupport theory references hsource

end TcM.infer

end Ix.Tc
