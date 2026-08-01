import Ix.Tc.Verify.Check.BlockTransaction
import Ix.Tc.Verify.Check.BlockClassification
import Ix.Tc.Verify.Check.ScopedStandaloneDriver
import Ix.Tc.Verify.Check.StandaloneDriver

/-!
# Singleton definition blocks

The production definition-block branch iterates `checkConstMemberFresh` over
the complete array and then publishes the peak DefEq depth.  Lean4Lean does
not yet have an atomic mutual-definition declaration, so the constructive E0
bridge is intentionally the singleton specialization.  It extracts the
actual member run from `checkClassifiedBlock`, invokes K3 without performing
K3's standalone promotion, and packages that evidence for the enclosing
atomic block transaction.
-/

namespace Ix.Tc

namespace RecM

/-- On a singleton definition array, successful classified execution is
exactly successful execution of that member.  The final peak update is a
no-op because `max 0 peak = peak` for `UInt32`. -/
theorem checkClassifiedBlock_singleton_definition_success
    {methods : Methods .anon} {block id : KId .anon}
    {before after : TcState .anon}
    (hrun : (checkClassifiedBlock .defn block #[id]).run methods before =
      .ok () after) :
    (checkConstMemberFresh id).run methods before = .ok () after := by
  unfold checkClassifiedBlock at hrun
  have hneq : ((.defn : CheckBlockKind) != .defn) = false := by rfl
  rw [hneq] at hrun
  simp at hrun
  change EStateM.bind ((checkConstMemberFresh id).run methods) _ before =
    .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hmember : (checkConstMemberFresh id).run methods before with
  | error err failed =>
      rw [hmember] at hrun
      contradiction
  | ok value checked =>
      rw [hmember] at hrun
      cases value
      simp only [get, modify, ReaderT.run] at hrun
      cases hrun
      simp [UInt32.max_def]

/-- Construct the certified singleton-definition body from the actual
production trace and K3's fixed-world member theorem.  Classifier correctness
is applied to the exact observed classification equation, so no invariant for
an unexecuted branch can satisfy it.

`hblocksAfter` is the remaining representation frame for the legacy K1/K2
invariant, which tracks loaded constants and intern/cache state but predates
E0's explicit block-array agreement layer. -/
theorem certifySingletonDefinition
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : StandalonePipelineResources
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls methods)
    (hmethods : Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars calls (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {block requested id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl} {before after : TcState .anon}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcovers : context.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    (hexact : ExactCheckBlock world block #[id] .defn)
    (trace : ExactBlockBodySuccessTrace methods block requested #[id] .defn
      before after)
    (hbefore : WhnfStateInv .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars [] before)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars []))
    (hblocksAfter : LoadedBlocksAgrees world.blocks after.env) :
    CertifiedBlockBodySuccess (kernelCacheSemantics model.keys trProj) trProj
      world support methods block requested #[id] .defn before after := by
  cases trace with
  | run loaded classified hlookup hclassification hclassified =>
      have hlookupPost := TcM.tryGetBlock_wf hfault block before hbefore
      rw [hlookup] at hlookupPost
      have hloadedInv := hlookupPost.1
      have hmember :=
        checkClassifiedBlock_singleton_definition_success hclassified
      have hclassifiedInv := classifyBlock_success_exact
        (I := WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars [])
        (fun hI => hI.1.core.loaded) hfault hexact hloadedInv hclassification
      have hevidence := checkConstMemberFresh_pending_evidence context hmethods
        hmethodPolicy hprojection hliterals hpending hcatalog hresources
        hcovers hcollision huvars hclassifiedInv.1.1 hclassifiedInv.1.2.2
        hfault hmember
      exact
        { trace := .run loaded classified hlookup hclassification hclassified
          exactBlock := hexact
          activePost := ActiveBlockStateWF.ofKernel hevidence.2.1 hblocksAfter
          evidence := .singletonDefinition hpending hevidence.1 }

/-- Run-scoped singleton-definition certification for the E3-S adapter.
This is the atomic-block analogue of K3's scoped standalone theorem: the
member run produces evidence in the original world and retains the finite
suffix-model witness, while the enclosing block transaction remains the
sole semantic commit point. -/
theorem certifySingletonDefinitionScoped
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {block requested id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl} {before after : TcState .anon}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcovers : context.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    (hresetScope : model.ResetPreservesScope)
    (hexact : ExactCheckBlock world block #[id] .defn)
    (trace : ExactBlockBodySuccessTrace methods block requested #[id] .defn
      before after)
    (hbefore : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] before)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hblocksAfter : LoadedBlocksAgrees world.blocks after.env) :
    CertifiedBlockBodySuccess (kernelCacheSemantics model.keys trProj) trProj
      world support methods block requested #[id] .defn before after := by
  cases trace with
  | run loaded classified hlookup hclassification hclassified =>
      have hlookupPost := TcM.tryGetBlock_wf hfault block before hbefore
      rw [hlookup] at hlookupPost
      have hloadedInv := hlookupPost.1
      have hmember :=
        checkClassifiedBlock_singleton_definition_success hclassified
      have hclassifiedInv := classifyBlock_success_exact
        (I := ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support [])
        (fun hI => hI.1.1.core.loaded) hfault hexact hloadedInv
        hclassification
      have hevidence := checkConstMemberFresh_scoped_pending_evidence context
        hmethods hmethodPolicy hprojection hliterals hpending hcatalog
        hresources hcovers hcollision huvars hresetScope hclassifiedInv.1
        hfault hmember
      exact
        { trace := .run loaded classified hlookup hclassification hclassified
          exactBlock := hexact
          activePost :=
            ActiveBlockStateWF.ofKernel hevidence.2.1.1 hblocksAfter
          evidence := .singletonDefinition hpending hevidence.1 }

end RecM

end Ix.Tc
