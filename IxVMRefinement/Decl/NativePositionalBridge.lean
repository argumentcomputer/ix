import IxVMRefinement.Decl.NativePositionalStep
import IxVMRefinement.Decl.NativeBridge

/-! # Positional native certificates in the shared declaration fold -/

universe u

namespace IxVM.Refinement.Decl

open Aiur.Generic.SourceSemantics (Call)
open Ix.Kernel Ix.Kernel.Semantics
open Core (S₀)

private theorem native_pos_declRunJ {env after : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {parts : NativeParts .anon}
    (hpin : basisPinHit block = none) (hparts : nativeParts? nP block = some parts)
    (run : DeclNativeRunJ nativePosRulesJ env parts after) :
    DeclRunJ nativePosRulesJ (IndRoutesJ nativePosRulesJ env) env (.indDecl block nP) after := by
  simp only [DeclRunJ, hpin]
  exact Or.inl ⟨parts, hparts, run⟩

/-- Positional native installs preserve auxiliary ownership and old projection lookups. -/
theorem cleanInstallStep_of_nativePos {env after : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {parts : NativeParts .anon}
    (hpin : basisPinHit block = none) (hparts : nativeParts? nP block = some parts)
    (hna : DeclNonAux (.indDecl block nP))
    (installed : IxVM.Consistency.InstallStep env (.indDecl block nP) after)
    (run : DeclNativeRunJ nativePosRulesJ env parts after) :
    CleanInstallStep env (.indDecl block nP) after where
  step := installed
  auxSynced haux := auxRootSynced_step_declRunJ_generic haux hna (native_pos_declRunJ hpin hparts run)
  noNewProj := noNewProj_declNativeRunJ run
  monoSome _ hk := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
    rw [(declNativeRunJ_envExt run).find hci]
    rfl

/-- The positional native result preserves all properties used by the final reader fold. -/
theorem fullDeclInv_step_nativePos {env after : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {parts : NativeParts .anon}
    (hpin : basisPinHit block = none) (hparts : nativeParts? nP block = some parts)
    (hna : DeclNonAux (.indDecl block nP))
    (installed : IxVM.Consistency.InstallStep env (.indDecl block nP) after)
    (run : DeclNativeRunJ nativePosRulesJ env parts after) :
    ∀ (V : Type u) [SetTheory V], FullDeclInv V env → FullDeclInv V after := by
  intro V _ h
  have routed := native_pos_declRunJ hpin hparts run
  have inv := h.declInvM.inv.step_nativePos hparts run
  have clean := cleanInstallStep_of_nativePos hpin hparts hna installed run
  have eta := etaShape_declRunJ_generic judgeFrames_nativePosRulesJ
    h.declInvM.inv.store.store h.etaCtorStored h.etaShape routed
  refine ⟨⟨inv, clean.auxSynced h.declInvM.auxSynced⟩,
    strongEnvProps_declRunJ_generic h.strongProps inv.store.tableBodies ?_ routed, eta.1, eta.2⟩
  intro block' nP' heq _ ci hci
  cases heq
  have hmem : ci ∈ IxVM.Consistency.installs (.indDecl block nP) := by
    simpa only [IxVM.Consistency.installs, hpin] using hci
  exact (hna.1 ci hmem).1

/-- The native fold seam consumes the positional certificate without a separate sort-lifting
premise. The retained raw witness and constructor-use evidence are explicit. -/
theorem nativeIndStep_of_nativeWithRec_pos
    (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call IxVM.F)} {env : Env .anon} {block : List (ConstantInfo .anon)}
    {nP : Nat} {parts : NativeParts .anon}
    (hchk : Core.S0.Checked calls env (.indDecl block nP))
    (hna : DeclNonAux (.indDecl block nP))
    (hfresh : ∀ ci ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci.name = none)
    (hpin : basisPinHit block = none) (hparts : nativeParts? nP block = some parts)
    (data : NativeWithRecData calls env block parts) : NativeIndStep.{u} calls env block nP := by
  by_cases store : DeclStoreInv env
  · obtain ⟨after, installed, run⟩ := nativeWithRec_step_pos hLevels hCore hpin hparts store data
    have clean := cleanInstallStep_of_nativePos hpin hparts hna installed run
    exact ⟨after, clean, fun _ _ h =>
      ⟨h.inv.step_nativePos hparts run, clean.auxSynced h.auxSynced⟩⟩
  · obtain ⟨after, clean⟩ := cleanInstallStep_of_checked_fresh hchk hna.2 hfresh
    exact ⟨after, clean, fun _ _ h => absurd h.inv.store store⟩

/-- Actual native evidence yields a clean install preserving the full shared invariant. -/
theorem nativeWithRec_full_step_pos
    (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call IxVM.F)} {env : Env .anon} {block : List (ConstantInfo .anon)}
    {nP : Nat} {parts : NativeParts .anon}
    (hna : DeclNonAux (.indDecl block nP))
    (hpin : basisPinHit block = none) (hparts : nativeParts? nP block = some parts)
    (store : DeclStoreInv env) (data : NativeWithRecData calls env block parts) :
    ∃ after, CleanInstallStep env (.indDecl block nP) after ∧
      ∀ (V : Type u) [SetTheory V], FullDeclInv V env → FullDeclInv V after := by
  obtain ⟨after, installed, run⟩ := nativeWithRec_step_pos hLevels hCore hpin hparts store data
  exact ⟨after, cleanInstallStep_of_nativePos hpin hparts hna installed run,
    fullDeclInv_step_nativePos hpin hparts hna installed run⟩

end IxVM.Refinement.Decl
