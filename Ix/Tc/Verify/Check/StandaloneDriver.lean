import Ix.Tc.Verify.Check.ResetFrame

/-!
# Standalone per-constant driver

This module lifts member-level acceptance through the exact production
`checkConstMemberFresh` prefix: reset the per-check state, perform the required
lazy constant lookup, and check the value returned by that lookup.  The
catalog agreement proof prevents a successful lazy lookup from silently
changing which pending declaration is certified.
-/

namespace Ix.Tc

/-- Operational boundary separating K3 standalone checking from E0 block
coordination.  The exact production router must preserve the checker
invariant and select no coordinated block.  This condition is definitionally
inhabited for axioms; definition-family instances are discharged when their
block lookup/classification is known to select the standalone path. -/
def StandaloneRoute (I : TcState .anon → Prop) (methods : Methods .anon)
    (concrete : KConst .anon) : Prop :=
  ∀ state, TcM.WF I state ((RecM.coordinatedBlockFor concrete).run methods)
    (fun selected _ => selected = none)

namespace StandaloneRoute

/-- Axioms never enter block coordination. -/
theorem axiomRoute
    (I : TcState .anon → Prop) (methods : Methods .anon)
    (name : Mode.anon.F Name) (levelParams : Mode.anon.F (Array Name))
    (isUnsafe : Bool) (levels : UInt64) (type : KExpr .anon) :
    StandaloneRoute I methods
      (.axio name levelParams isUnsafe levels type) := by
  intro state hI
  exact ⟨hI, rfl⟩

end StandaloneRoute

namespace RecM

/-- A successful standalone fresh-member run certifies the exact pending
catalog entry returned by production lookup.  Reset establishes the empty
local context; required lookup preserves it on either eager or lazy ingress.
-/
theorem checkConstMemberFresh_pending_sound
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : StandalonePipelineResources
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls methods)
    (hmethods : Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcovers : context.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    {before after : TcState .anon}
    (hkernel : KernelStateWF
      (kernelCacheSemantics model.keys trProj) trProj world support before)
    (hlayer : WhnfLayer.noAccel.StateOK before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars []))
    (hrun : (checkConstMemberFresh id).run methods before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world' support
          model.keys.uvars [] after ∧
        TrustedDecl trProj world' id decl := by
  unfold checkConstMemberFresh at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind TcM.reset (fun _ =>
      EStateM.bind (TcM.getConst id) (fun concrete =>
        (checkConstMember id concrete).run methods)) before =
    .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hreset : TcM.reset before with
  | error err failed =>
      rw [hreset] at hrun
      contradiction
  | ok resetValue afterReset =>
      rw [hreset] at hrun
      have hresetPost :=
        TcM.reset_whnf_entry (uvars := model.keys.uvars) before hlayer hkernel
      rw [hreset] at hresetPost
      have hIReset : WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars [] afterReset :=
        ⟨hresetPost.1, hresetPost.2.2.1, hresetPost.2.2.2.1⟩
      cases hget : TcM.getConst id afterReset with
      | error err failed =>
          simp only [hget] at hrun
          contradiction
      | ok found afterLookup =>
          simp only [hget] at hrun
          have hgetPost := TcM.getConst_loaded_wf
            (hfault.withInferOnly false) id afterReset
            ⟨hIReset, hresetPost.2.1⟩
          rw [hget] at hgetPost
          have hfoundCatalog : world.catalog id = some found :=
            hgetPost.1.1.1.core.loaded hgetPost.2
          have hfound : found = concrete :=
            Option.some.inj (hfoundCatalog.symm.trans hcatalog)
          subst found
          exact checkConstMember_pending_sound context hmethods hmethodPolicy
            hprojection hliterals hpending hcatalog hresources hcovers
            hcollision huvars hgetPost.1.2 hgetPost.1.1 hfault hrun

/-- Fixed-world form of the fresh-member theorem.  This stops immediately
after constructing the actual standalone checker result and deliberately
does not perform the standalone ghost promotion.  Atomic block checking uses
this form so that the enclosing block transaction—not an individual member—
owns the semantic commit point. -/
theorem checkConstMemberFresh_pending_evidence
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : StandalonePipelineResources
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls methods)
    (hmethods : Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcovers : context.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    {before after : TcState .anon}
    (hkernel : KernelStateWF
      (kernelCacheSemantics model.keys trProj) trProj world support before)
    (hlayer : WhnfLayer.noAccel.StateOK before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars []))
    (hrun : (checkConstMemberFresh id).run methods before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      WhnfStateInv .noAccel
        (kernelCacheSemantics model.keys trProj) trProj world support
        model.keys.uvars [] after := by
  unfold checkConstMemberFresh at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind TcM.reset (fun _ =>
      EStateM.bind (TcM.getConst id) (fun concrete =>
        (checkConstMember id concrete).run methods)) before =
    .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hreset : TcM.reset before with
  | error err failed =>
      rw [hreset] at hrun
      contradiction
  | ok resetValue afterReset =>
      rw [hreset] at hrun
      have hresetPost :=
        TcM.reset_whnf_entry (uvars := model.keys.uvars) before hlayer hkernel
      rw [hreset] at hresetPost
      have hIReset : WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars [] afterReset :=
        ⟨hresetPost.1, hresetPost.2.2.1, hresetPost.2.2.2.1⟩
      cases hget : TcM.getConst id afterReset with
      | error err failed =>
          simp only [hget] at hrun
          contradiction
      | ok found afterLookup =>
          simp only [hget] at hrun
          have hgetPost := TcM.getConst_loaded_wf
            (hfault.withInferOnly false) id afterReset
            ⟨hIReset, hresetPost.2.1⟩
          rw [hget] at hgetPost
          have hfoundCatalog : world.catalog id = some found :=
            hgetPost.1.1.1.core.loaded hgetPost.2
          have hfound : found = concrete :=
            Option.some.inj (hfoundCatalog.symm.trans hcatalog)
          subst found
          obtain ⟨afterValidation, hvalidation⟩ :=
            checkConstMember_validation_success hresources hrun
          have hingress := hpending.toPre_of_validation hprojection hliterals
            hcatalog hresources hcollision hvalidation
          have hevidence := checkConstMember_sound context hmethods
            hmethodPolicy hingress hcovers hresources huvars hgetPost.1.2
            hgetPost.1.1 hfault hrun
          exact ⟨⟨hingress, hevidence.2⟩, hevidence.1⟩

/-- Lift the fresh-member theorem through the exact standalone branch of
`RecM.checkConst`.  The first required lookup and router are both executed
before the production reset; `StandaloneRoute` makes the E0 boundary
explicit and rules out silently treating block acceptance as member
acceptance. -/
theorem checkConst_standalone_pending_sound
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : StandalonePipelineResources
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls methods)
    (hmethods : Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcovers : context.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    (hroute : StandaloneRoute
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars []) methods concrete)
    {before after : TcState .anon}
    (hI : WhnfStateInv .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars [] before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars []))
    (hrun : (checkConst id).run methods before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world' support
          model.keys.uvars [] after ∧
        TrustedDecl trProj world' id decl := by
  unfold checkConst at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind (TcM.getConst id) _ before = .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hget : TcM.getConst id before with
  | error err failed =>
      rw [hget] at hrun
      contradiction
  | ok found afterLookup =>
      rw [hget] at hrun
      have hgetPost := TcM.getConst_loaded_wf hfault id before hI
      rw [hget] at hgetPost
      have hfoundCatalog : world.catalog id = some found :=
        hgetPost.1.1.core.loaded hgetPost.2
      have hfound : found = concrete :=
        Option.some.inj (hfoundCatalog.symm.trans hcatalog)
      subst found
      change EStateM.bind ((coordinatedBlockFor concrete).run methods) _
        afterLookup = .ok () after at hrun
      unfold EStateM.bind at hrun
      cases hselected : (coordinatedBlockFor concrete).run methods afterLookup with
      | error err failed =>
          rw [hselected] at hrun
          contradiction
      | ok selected afterRoute =>
          rw [hselected] at hrun
          have hroutePost := hroute afterLookup hgetPost.1
          rw [hselected] at hroutePost
          have hnone : selected = none := hroutePost.2
          subst selected
          exact checkConstMemberFresh_pending_sound context hmethods
            hmethodPolicy hprojection hliterals hpending hcatalog hresources
            hcovers hcollision huvars hroutePost.1.1 hroutePost.1.2.2 hfault
            hrun

end RecM

end Ix.Tc
