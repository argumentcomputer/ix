import IxVMRefinement.Decl.ThmBodyRole
import IxVMRefinement.Decl.ModeledRoleInstall
import IxVMRefinement.Decl.NativeReferenceStep
import IxC.Kernel.Verify.Cached.Reference

/-! # The complete accepted reference fold with checked theorem values

Every declaration kind advances a model in the actual reference order. The checking view
keeps normalized native signatures and all non-theorem data exact, while theorem bodies
are the checked annotations needed by the rules-tier model invariant.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

private theorem reference_rules_step {env out : Env .anon} {d : Declaration .anon}
    (run : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d out) :
    ∀ (V : Type u) [SetTheory V], EnvModelT V .verified env → EnvModelT V .verified out :=
  fun _ _ inv => foldRulesRoutes (.cons run .nil) inv

private theorem reference_basis_step {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {kind : BasisKind}
    (checked : checkBasisDecl (m := CheckM .anon) source kind = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨targetOut, agree, run⟩ := agreement.declBasisRun (declBasisRunOf checked)
  exact ⟨targetOut, agree, reference_rules_step (d := .basisDecl kind) run⟩

/-- Every actual accepted declaration advances the annotated reference model. -/
theorem checkedDecl_referenceModelStep {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel : Nat} {ev : Evidences .anon}
    {d : Declaration .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨out, agree, _, run, _⟩ := agreement.checkedDefn_step checked
    exact ⟨out, agree, reference_rules_step (d := .defnDecl cv value hint) run⟩
  | thmDecl cv value =>
    obtain ⟨out, agree, _, run, _⟩ := agreement.checkedThm_step checked
    exact ⟨out, agree, reference_rules_step (d := .thmDecl cv value) run⟩
  | opaqueDecl cv value =>
    obtain ⟨out, agree, _, run, _⟩ := agreement.checkedOpaque_step checked
    exact ⟨out, agree, reference_rules_step (d := .opaqueDecl cv value) run⟩
  | axiomDecl cv =>
    obtain ⟨out, agree, _, run, _⟩ := agreement.checkedAxiom_step checked
    exact ⟨out, agree, reference_rules_step (d := .axiomDecl cv) run⟩
  | basisDecl kind => exact reference_basis_step agreement checked
  | indDecl block nP =>
    cases pinned : basisPinHit block with
    | some kind =>
      simp only [checkDecl, pinned] at checked
      exact reference_basis_step agreement (checkIndShape_bind_ok checked).2
    | none =>
      cases native : nativeParts? nP block with
      | some parts =>
        obtain ⟨out, agree, _, _, preserved⟩ :=
          checkedDecl_native_referenceModelStep agreement pinned native checked
        exact ⟨out, agree, preserved⟩
      | none =>
        obtain ⟨out, agree, _, preserved⟩ :=
          checkedDecl_modeled_referenceStep agreement pinned native checked
        exact ⟨out, agree, preserved⟩
  | quotDecl kind cv =>
    simp only [checkDecl] at checked
    split at checked
    · cases kind with
      | type => exact reference_basis_step agreement checked
      | ctor | lift | ind | sound =>
        have same : source = sourceOut := Except.ok.inj checked
        subst sourceOut
        exact ⟨target, agreement, fun _ _ inv => inv⟩
    · cases checked

/-- The real checker fold, in its reference order, preserves the annotated reference model. -/
theorem checkedDecls_referenceModelStep {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  induction declarations generalizing source target with
  | nil =>
    have same : source = sourceOut := Except.ok.inj checked
    subst sourceOut
    exact ⟨target, agreement, fun _ _ inv => inv⟩
  | cons d rest ih =>
    simp only [List.foldlM_cons] at checked
    obtain ⟨sourceNext, head, tail⟩ := exceptBind_ok checked
    obtain ⟨targetNext, nextAgreement, nextModel⟩ := checkedDecl_referenceModelStep agreement head
    obtain ⟨targetOut, outAgreement, restModel⟩ := ih nextAgreement tail
    exact ⟨targetOut, outAgreement, fun V _ inv => restModel V (nextModel V inv)⟩

/-- Reference acceptance constructs a model with actual checked theorem values. -/
theorem acceptsRef_referenceModel {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ target, ThmBodyView.Agrees reference target ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target := by
  obtain ⟨fuel, checked⟩ := Cached.AcceptsRef.iff.mp accepted
  have emptyAgreement : ThmBodyView.Agrees (Env.empty : Env .anon) Env.empty := fun _ => .same _
  obtain ⟨target, agree, preserved⟩ := checkedDecls_referenceModelStep emptyAgreement checked
  exact ⟨target, agree, fun V _ => preserved V EnvModelT.empty⟩

end IxVM.Refinement.Decl
