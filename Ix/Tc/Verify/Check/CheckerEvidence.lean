import Ix.Tc.Verify.Check.Acceptance
import Ix.Tc.Verify.Check.FullInferenceCache

/-!
# Semantic evidence from the standalone checker pipelines

This module connects the two sequential computation fragments used by
`checkConstMember` to the declaration-local evidence consumed by acceptance.
The inference premise is K3's stronger full-mode contract: it starts from a
raw pretranslation and establishes the typed structural translation itself.

The value pipeline is parameterized by the semantic contract for the actual
`RecM.isDefEq` entry point.  This is intentionally not the smaller-table
`methods.isDefEq` callback used inside recursive inference.
-/

namespace Ix.Tc

namespace RecM

/-- A successful execution of the production type-checking fragment retains
full-inference mode and proves that the source translates to a Theory type. -/
theorem checkTypePipeline_sound
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods)
    {Delta : KVLCtx} {s after : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta source sourceV)
    (hpolicy : s.inferOnly = false)
    (hI : WhnfStateInv .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars Delta s)
    (hrun :
      ((do
        let inferred ← infer source
        let _ ← ensureSortDirect inferred).run methods) s = .ok () after) :
    WhnfStateInv .noAccel
        (kernelCacheSemantics model.keys trProj) trProj world support
        model.keys.uvars Delta after ∧
      after.inferOnly = false ∧
        TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
          source sourceV ∧
        TypeCheckEvidence trProj world support model.keys.uvars Delta
          sourceV := by
  have hinfer := infer_full_wf context hsourceSupport hsource hpolicy
  have hpipeline :
      TcM.WF
        (WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars Delta) s
        ((do
          let inferred ← infer source
          let _ ← ensureSortDirect inferred).run methods)
        (fun _ after => after.inferOnly = false ∧
          TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
            source sourceV ∧
          TypeCheckEvidence trProj world support model.keys.uvars Delta
            sourceV)
        (fun _ after => after.inferOnly = false) := by
    simp only [ReaderT.run_bind]
    apply TcM.WF.bind
      (TcM.WF.mono hinfer (fun _ _ post => post)
        (fun _ _ post => post))
    intro inferred afterInfer hinferred
    rcases hinferred with
      ⟨hpolicyAfter, hinferredSupport, hsourceTr, inferredV,
        hinferredTr, hsourceType⟩
    apply TcM.WF.bind
      (context.callbacks.ensureSort hpolicyAfter hinferredSupport hinferredTr)
    intro sort _ hsort
    rcases hsort with ⟨hpolicySort, hsort⟩
    exact TcM.WF.pure fun _ =>
      ⟨hpolicySort,
        hsourceTr,
        inferred, inferredV, hinferredTr, hsourceType, sort, hsort⟩
  have hpost := hpipeline hI
  rw [hrun] at hpost
  exact hpost

/-- A successful execution of the production value-checking fragment
preserves the checker invariant and proves that the translated value has the
declaration's advertised Theory type. -/
theorem checkValuePipeline_sound
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods)
    (hdefeq : ∀ {Delta : KVLCtx} {s : TcState .anon}
        {left right : KExpr .anon} {leftV rightV : Lean4Lean.VExpr},
      support left → support right →
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta left
        leftV →
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta right
        rightV →
      RecM.WF .noAccel (kernelCacheSemantics model.keys trProj) trProj world
        support model.keys.uvars Delta s (isDefEq left right)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU model.keys.uvars Delta.toCtx leftV rightV))
    {Delta : KVLCtx} {s after : TcState .anon}
    {value declaredType : KExpr .anon}
    {valueV declaredTypeV : Lean4Lean.VExpr}
    (hvalueSupport : support value)
    (hdeclaredSupport : support declaredType)
    (hvalue : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta value valueV)
    (hdeclared : TrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta declaredType declaredTypeV)
    (hpolicy : s.inferOnly = false)
    (hI : WhnfStateInv .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars Delta s)
    (hrun :
      ((do
        let inferredType ← infer value
        if !(← isDefEq inferredType declaredType) then
          throw TcError.declTypeMismatch).run methods) s = .ok () after) :
    WhnfStateInv .noAccel
        (kernelCacheSemantics model.keys trProj) trProj world support
        model.keys.uvars Delta after ∧
      ValueCheckEvidence world model.keys.uvars Delta valueV
        declaredTypeV := by
  have hinfer := infer_full_wf context hvalueSupport hvalue hpolicy
  have hpipeline :
      TcM.WF
        (WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world support
          model.keys.uvars Delta) s
        ((do
          let inferredType ← infer value
          if !(← isDefEq inferredType declaredType) then
            throw TcError.declTypeMismatch).run methods)
        (fun _ _ =>
          ValueCheckEvidence world model.keys.uvars Delta valueV
            declaredTypeV) := by
    simp only [ReaderT.run_bind]
    apply TcM.WF.bind
      (TcM.WF.mono hinfer (fun _ _ post => post)
        (fun _ _ _ => by trivial))
    intro inferredType _ hinferred
    rcases hinferred with
      ⟨_hpolicyAfter, hinferredSupport, _hvalueTr, inferredTypeV,
        hinferredTr, hvalueType⟩
    obtain ⟨inferredCoreV, hinferredCore, hcoreEq⟩ := hinferredTr
    apply TcM.WF.bind
      ((hdefeq hinferredSupport hdeclaredSupport hinferredCore hdeclared)
        methods context.methodSemantics)
    intro answer _ heq
    cases answer with
    | false =>
        simp only [Bool.not_false, if_true]
        exact TcM.WF.throw fun _ => trivial
    | true =>
        simp only [Bool.not_true, Bool.false_eq]
        exact TcM.WF.pure fun _ =>
          ⟨inferredCoreV,
            hvalueType.defeqU_r world.venvWF hI.2.1.wf.toCtx hcoreEq.symm,
            heq rfl⟩
  have hpost := hpipeline hI
  rw [hrun] at hpost
  exact hpost

end RecM

end Ix.Tc
