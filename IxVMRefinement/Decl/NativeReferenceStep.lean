import IxVMRefinement.Decl.ThmBodyNative
import IxVMRefinement.Decl.NativeRunMap

/-! # Native reference checks preserve the full reference model

The native check retains its actual normalized signatures and generated rules. This result
establishes the checking model; reader-shape correspondence is a separate obligation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- The actual native declaration branch replays under opaque theorem-body agreement. -/
theorem checkedDecl_native_referenceModelStep {source target referenceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel nP : Nat} {ev : Evidences .anon}
    {block : List (ConstantInfo .anon)} {parts : NativeParts .anon}
    (notPinned : basisPinHit block = none) (native : nativeParts? nP block = some parts)
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source (.indDecl block nP)
      = .ok referenceOut) :
    ∃ targetOut, ThmBodyView.Agrees referenceOut targetOut ∧
      DeclNativeRun .verified fuel target parts targetOut ∧
      DeclNativeRunJ rulesJ target parts targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  simp only [checkDecl, notPinned, native] at checked
  have rest := (checkIndShape_bind_ok checked).2
  split at rest
  · obtain ⟨targetOut, outAgreement, run⟩ := agreement.nativeRun (declNativeRun_of rest)
    have rules := (verifiedRunMap fuel).native (declNativeRun_runJ run)
    refine ⟨targetOut, outAgreement, run, rules, ?_⟩
    intro V _ inv
    have routed : DeclRunJ rulesJ (IndRoutesJ rulesJ target) target (.indDecl block nP) targetOut := by
      simp only [DeclRunJ, notPinned]
      exact Or.inl ⟨parts, native, rules⟩
    exact foldRulesRoutes (.cons routed .nil) inv
  · cases rest

end IxVM.Refinement.Decl
