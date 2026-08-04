import Ix.Tc.Verify.Check.ScopedStandaloneDriver
import Ix.Tc.Verify.RecursiveMethods.Public

/-!
# Public standalone constant checking

The member and driver proofs establish K3 for a fixed method table.  This
module instantiates that table with the exact finite approximation selected
by production `TcM.runRec`, and then crosses `isolateCheckErrors`.  The latter
is transparent on success, so the certified final state is exactly the state
returned by the public checker.

Whole-block coordination remains the separately named E0 boundary.  The
theorem below therefore requires `StandaloneRoute`; axioms discharge it
definitionally, while standalone definitions may supply a finite routing
proof for their concrete block environment.
-/

namespace Ix.Tc

namespace TcM.checkConst

/-- The public wrapper returns the exact failed recursive execution after
restoring subject-sensitive caches against the entry state.  Lazy loads,
intern growth, fuel consumption, and cached block errors remain governed by
`TcState.restoreCheckCachesOnError`. -/
theorem rollback_on_error
    {before failed : TcState .anon} {id : KId .anon}
    {err : TcError .anon}
    (hbody :
      (RecM.checkConst id).run
        (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat) before =
          .error err failed) :
    TcM.checkConst id before =
      .error err (before.restoreCheckCachesOnError failed) := by
  unfold TcM.checkConst TcM.runRec
  exact TcM.isolateCheckErrors_error hbody

/-- The exact public rollback equation reassembles the stable kernel/cache
invariant from the entry caches and the failed execution's ordinary
state/intern frames.  No semantic claim about entries written by the failed
subject is assumed. -/
theorem rollback_preserves_kernel
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {before failed : TcState .anon} {id : KId .anon}
    {err : TcError .anon}
    (hbody :
      (RecM.checkConst id).run
        (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat) before =
          .error err failed)
    (hbefore : KernelStateWF semantics trProj world support before)
    (hfailedCore : TcStateWF trProj failed world)
    (hfailedIntern : support.CoversIntern failed.env.intern) :
    TcM.checkConst id before =
        .error err (before.restoreCheckCachesOnError failed) ∧
      KernelStateWF semantics trProj world support
        (before.restoreCheckCachesOnError failed) :=
  ⟨rollback_on_error hbody,
    hbefore.restoreCheckCachesOnError hfailedCore hfailedIntern⟩

/-- Successful public checking of a pending standalone declaration produces
the concrete K3 acceptance result and promotes exactly that declaration into
a trusted ghost world.  The recursive callbacks and the stronger checker
inference pipeline are both restricted to the successor-layer call domain
selected by the finite production schedule. -/
theorem wf_legacy
    {before : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext before (TcM.checkConst id)
      requests trProj world support)
    (pipelines : StandalonePipelineResources
      (kernelCacheSemantics context.proposition.model.keys trProj)
      trProj world support context.proposition.model.keys.uvars
      (context.calls (before.recFuel.toNat + 1))
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat))
    {concrete : KConst .anon} {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hpipelines : pipelines.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : context.proposition.model.keys.uvars = concrete.lvls.toNat)
    (hroute : StandaloneRoute
      (WhnfStateInv .noAccel
        (kernelCacheSemantics context.proposition.model.keys trProj) trProj
        world support context.proposition.model.keys.uvars [])
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat) concrete)
    (hI : WhnfStateInv .noAccel
      (kernelCacheSemantics context.proposition.model.keys trProj) trProj world
      support context.proposition.model.keys.uvars [] before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel
        (kernelCacheSemantics context.proposition.model.keys trProj) trProj
        world support context.proposition.model.keys.uvars []))
    {after : TcState .anon}
    (hrun : TcM.checkConst id before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics context.proposition.model.keys trProj) trProj
          world' support context.proposition.model.keys.uvars [] after ∧
        TrustedDecl trProj world' id decl := by
  let methods := Ix.Tc.methodsN (m := .anon) before.recFuel.toNat
  have hmethods : Methods.WFAtOn .noAccel
      (kernelCacheSemantics context.proposition.model.keys trProj) trProj world
      support context.proposition.model.keys.uvars
      (context.calls (before.recFuel.toNat + 1)) (Methods.next methods) := by
    simpa [methods] using context.schedule.nextSelected
  have hpolicy : (Methods.next methods).PreservesInferOnly :=
    Methods.next_preservesInferOnly methods
      (Methods.methodsN_concrete_preservesInferOnly before.recFuel.toNat)
  have hroute' : StandaloneRoute
      (WhnfStateInv .noAccel
        (kernelCacheSemantics context.proposition.model.keys trProj) trProj world
        support context.proposition.model.keys.uvars []) methods concrete := by
    simpa [methods] using hroute
  have hbody : (RecM.checkConst id).run methods before = .ok () after := by
    unfold TcM.checkConst TcM.isolateCheckErrors TcM.runRec at hrun
    cases hinner :
        (RecM.checkConst id).run
          (Ix.Tc.methodsN before.recFuel.toNat) before with
    | ok value middle =>
        simp only [hinner] at hrun
        cases hrun
        rfl
    | error err failed =>
        simp only [hinner] at hrun
        contradiction
  exact RecM.checkConst_standalone_pending_sound pipelines hmethods hpolicy
    hprojection hliterals hpending hcatalog hresources hpipelines hcollision
    huvars hroute' hI hfault hbody

/-- Successful public checking of a pending standalone declaration over one
finite suffix-state domain.  Unlike `wf_legacy`, this contract carries
`StateInScope` through every recursive callback, lazy-ingress transition,
reset, and checker stage; it has no globally quantified suffix model or
scoped-to-global conversion premise. -/
theorem wf
    {before : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext before (TcM.checkConst id)
      requests trProj world support)
    (pipelines : ScopedStandalonePipelineResources context.model support
      (context.calls (before.recFuel.toNat + 1))
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat))
    {concrete : KConst .anon} {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hpipelines : pipelines.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : context.model.keys.uvars = concrete.lvls.toNat)
    (hresetScope : context.model.ResetPreservesScope)
    (hroute : StandaloneRoute
      (ScopedWhnfStateInv context.model .noAccel
        (kernelCacheSemantics context.model.keys trProj) support [])
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat) concrete)
    (hI : ScopedWhnfStateInv context.model .noAccel
      (kernelCacheSemantics context.model.keys trProj) support [] before)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv context.model .noAccel
        (kernelCacheSemantics context.model.keys trProj) support []))
    {after : TcState .anon}
    (hrun : TcM.checkConst id before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics context.model.keys trProj) trProj world'
          support context.model.keys.uvars [] after ∧
        context.model.StateInScope after ∧
        TrustedDecl trProj world' id decl := by
  let methods := Ix.Tc.methodsN (m := .anon) before.recFuel.toNat
  have hmethods : Methods.ScopedWFAtOn context.model .noAccel
      (kernelCacheSemantics context.model.keys trProj) support
      (context.calls (before.recFuel.toNat + 1)) (Methods.next methods) := by
    simpa [methods] using context.schedule.nextSelected
  have hpolicy : (Methods.next methods).PreservesInferOnly :=
    Methods.next_preservesInferOnly methods
      (Methods.methodsN_concrete_preservesInferOnly before.recFuel.toNat)
  have hroute' : StandaloneRoute
      (ScopedWhnfStateInv context.model .noAccel
        (kernelCacheSemantics context.model.keys trProj) support []) methods
      concrete := by
    simpa [methods] using hroute
  have hbody : (RecM.checkConst id).run methods before = .ok () after := by
    unfold TcM.checkConst TcM.isolateCheckErrors TcM.runRec at hrun
    cases hinner :
        (RecM.checkConst id).run
          (Ix.Tc.methodsN before.recFuel.toNat) before with
    | ok value middle =>
        simp only [hinner] at hrun
        cases hrun
        rfl
    | error err failed =>
        simp only [hinner] at hrun
        contradiction
  exact RecM.checkConst_standalone_scoped_pending_sound pipelines hmethods
    hpolicy hprojection hliterals hpending hcatalog hresources hpipelines
    hcollision huvars hresetScope hroute' hI hfault hbody

/-- An intrinsically ill-typed pending standalone declaration cannot be
accepted by the public checker.  The contradiction uses the raw pending
translation and freshness to turn K3's successful semantic evidence into the
forbidden Theory declaration transition; no typing fact is assumed at
ingress. -/
theorem rejected_of_no_decl_wf
    {before : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext before (TcM.checkConst id)
      requests trProj world support)
    (pipelines : StandalonePipelineResources
      (kernelCacheSemantics context.proposition.model.keys trProj)
      trProj world support context.proposition.model.keys.uvars
      (context.calls (before.recFuel.toNat + 1))
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat))
    {concrete : KConst .anon} {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hpipelines : pipelines.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : context.proposition.model.keys.uvars = concrete.lvls.toNat)
    (hroute : StandaloneRoute
      (WhnfStateInv .noAccel
        (kernelCacheSemantics context.proposition.model.keys trProj) trProj
        world support context.proposition.model.keys.uvars [])
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat) concrete)
    (hI : WhnfStateInv .noAccel
      (kernelCacheSemantics context.proposition.model.keys trProj) trProj world
      support context.proposition.model.keys.uvars [] before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel
        (kernelCacheSemantics context.proposition.model.keys trProj) trProj
        world support context.proposition.model.keys.uvars []))
    (hnotWF : ¬∃ world', Lean4Lean.VDecl.WF world.venv decl world') :
    ∃ err failed,
      TcM.checkConst id before = .error err failed ∧
        PendingDecl trProj world id decl := by
  cases hrun : TcM.checkConst id before with
  | error err failed =>
      exact ⟨err, failed, rfl, hpending⟩
  | ok value after =>
      cases value
      have hresult := wf_legacy context pipelines hprojection hliterals
        hpending hcatalog hresources hpipelines hcollision huvars hroute hI
        hfault hrun
      obtain ⟨_pendingConcrete, _hpendingCatalog, hraw, _huntrusted, _hclosed,
          hfresh⟩ := hpending
      exact False.elim <| hnotWF (hraw.wfOfAccepted hfresh hresult.1.accepted)

/-- Axioms take the standalone route by definition, so their public K3
theorem has no residual block-coordination premise. -/
theorem axiom_pending_sound
    {before : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext before (TcM.checkConst id)
      requests trProj world support)
    (pipelines : StandalonePipelineResources
      (kernelCacheSemantics context.proposition.model.keys trProj)
      trProj world support context.proposition.model.keys.uvars
      (context.calls (before.recFuel.toNat + 1))
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat))
    {name : Mode.anon.F Name}
    {levelParams : Mode.anon.F (Array Name)} {isUnsafe : Bool}
    {levels : UInt64} {type : KExpr .anon} {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some
      (.axio name levelParams isUnsafe levels type))
    (hresources : StandaloneValidationResources support
      (.axio name levelParams isUnsafe levels type))
    (hpipelines : pipelines.Covers
      (.axio name levelParams isUnsafe levels type))
    (hcollision : support.CollisionFree)
    (huvars : context.proposition.model.keys.uvars = levels.toNat)
    (hI : WhnfStateInv .noAccel
      (kernelCacheSemantics context.proposition.model.keys trProj) trProj world
      support context.proposition.model.keys.uvars [] before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel
        (kernelCacheSemantics context.proposition.model.keys trProj) trProj
        world support context.proposition.model.keys.uvars []))
    {after : TcState .anon}
    (hrun : TcM.checkConst id before = .ok () after) :
    StandaloneCheckResult trProj world support id
        (.axio name levelParams isUnsafe levels type) decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics context.proposition.model.keys trProj) trProj
          world' support context.proposition.model.keys.uvars [] after ∧
        TrustedDecl trProj world' id decl := by
  apply wf_legacy context pipelines hprojection hliterals hpending
    hcatalog hresources hpipelines hcollision huvars
  · exact StandaloneRoute.axiomRoute _ _ name levelParams isUnsafe levels type
  · exact hI
  · exact hfault
  · exact hrun

end TcM.checkConst

end Ix.Tc
