import Ix.Tc.Verify.Check.ScopedMemberEvidence
import Ix.Tc.Verify.Check.StandaloneDriver

/-!
# Run-scoped standalone per-constant driver

This module lifts the scoped member proof through the exact production
`checkConstMemberFresh` and standalone `checkConst` prefixes.  Reset is the
only transition in those prefixes that is not already covered by a generic
frame theorem.  Its effect on a suffix model's chosen state domain is
therefore exposed as a small, explicit contract.
-/

namespace Ix.Tc

namespace RecM

/-- Fixed-world form of the scoped fresh-member theorem.  Atomic block
checking uses this form so that the enclosing block transaction, rather than
an individual member, owns the semantic commit point.  Unlike the legacy
fixed-world theorem, the post-state retains the finite suffix-model domain. -/
theorem checkConstMemberFresh_scoped_pending_evidence
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
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
    (hresetScope : model.ResetPreservesScope)
    {before after : TcState .anon}
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] before)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun : (checkConstMemberFresh id).run methods before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support [] after := by
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
        TcM.reset_whnf_entry (uvars := model.keys.uvars) before hI.1.2.2
          hI.1.1
      rw [hreset] at hresetPost
      have hIResetBase : WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars [] afterReset :=
        ⟨hresetPost.1, hresetPost.2.2.1, hresetPost.2.2.2.1⟩
      have hIReset : ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support [] afterReset :=
        ⟨hIResetBase, hresetScope hI.2 hreset⟩
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
            hgetPost.1.1.1.1.core.loaded hgetPost.2
          have hfound : found = concrete :=
            Option.some.inj (hfoundCatalog.symm.trans hcatalog)
          subst found
          obtain ⟨afterValidation, hvalidation⟩ :=
            checkConstMember_validation_success hresources hrun
          have hingress := hpending.toPre_of_validation hprojection hliterals
            hcatalog hresources hcollision hvalidation
          have hevidence := checkConstMember_scoped_sound context hmethods
            hmethodPolicy hingress hcovers hresources huvars hgetPost.1.2
            hgetPost.1.1 hfault hrun
          exact ⟨⟨hingress, hevidence.2⟩, hevidence.1⟩

/-- A successful scoped fresh-member run certifies the exact pending catalog
entry returned by production lookup.  The state-domain witness is retained
through reset, eager/lazy lookup, validation, and the recursive checker
pipeline. -/
theorem checkConstMemberFresh_scoped_pending_sound
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
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
    (hresetScope : model.ResetPreservesScope)
    {before after : TcState .anon}
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] before)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun : (checkConstMemberFresh id).run methods before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world' support
          model.keys.uvars [] after ∧
        model.StateInScope after ∧
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
        TcM.reset_whnf_entry (uvars := model.keys.uvars) before hI.1.2.2
          hI.1.1
      rw [hreset] at hresetPost
      have hIResetBase : WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars [] afterReset :=
        ⟨hresetPost.1, hresetPost.2.2.1, hresetPost.2.2.2.1⟩
      have hIReset : ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support [] afterReset :=
        ⟨hIResetBase, hresetScope hI.2 hreset⟩
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
            hgetPost.1.1.1.1.core.loaded hgetPost.2
          have hfound : found = concrete :=
            Option.some.inj (hfoundCatalog.symm.trans hcatalog)
          subst found
          exact checkConstMember_scoped_pending_sound context hmethods
            hmethodPolicy hprojection hliterals hpending hcatalog hresources
            hcovers hcollision huvars hgetPost.1.2 hgetPost.1.1 hfault hrun

/-- Lift the scoped fresh-member theorem through the exact standalone branch
of `RecM.checkConst`.  The router itself is checked against the scoped
invariant, so block selection cannot discard the finite-domain witness. -/
theorem checkConst_standalone_scoped_pending_sound
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
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
    (hresetScope : model.ResetPreservesScope)
    (hroute : StandaloneRoute
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []) methods concrete)
    {before after : TcState .anon}
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] before)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun : (checkConst id).run methods before = .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world' support
          model.keys.uvars [] after ∧
        model.StateInScope after ∧
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
        hgetPost.1.1.1.core.loaded hgetPost.2
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
          exact checkConstMemberFresh_scoped_pending_sound context hmethods
            hmethodPolicy hprojection hliterals hpending hcatalog hresources
            hcovers hcollision huvars hresetScope hroutePost.1 hfault hrun

end RecM

end Ix.Tc
