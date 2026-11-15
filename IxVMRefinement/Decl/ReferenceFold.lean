import IxVMRefinement.Decl.ReferenceStorage
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
      IxVM.Consistency.InstallStep target (.basisDecl kind) targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨targetOut, agree, run⟩ := agreement.declBasisRun (declBasisRunOf checked)
  exact ⟨targetOut, agree, installStep_glue_basis run,
    reference_rules_step (d := .basisDecl kind) run⟩

/-- Every accepted declaration retains its actual storage evidence alongside model preservation. -/
theorem checkedDecl_referenceTraceStep {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel : Nat} {ev : Evidences .anon}
    {d : Declaration .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ReferenceStep fuel target d targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedDefn_step.{u} agreement checked
    exact ⟨out, agree, .stored installed, reference_rules_step (d := .defnDecl cv value hint) run⟩
  | thmDecl cv value =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedThm_step.{u} agreement checked
    exact ⟨out, agree, .stored installed, reference_rules_step (d := .thmDecl cv value) run⟩
  | opaqueDecl cv value =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedOpaque_step.{u} agreement checked
    exact ⟨out, agree, .stored installed, reference_rules_step (d := .opaqueDecl cv value) run⟩
  | axiomDecl cv =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedAxiom_step.{u} agreement checked
    exact ⟨out, agree, .stored installed, reference_rules_step (d := .axiomDecl cv) run⟩
  | basisDecl kind =>
    obtain ⟨out, agree, installed, preserved⟩ := reference_basis_step agreement checked
    exact ⟨out, agree, .stored installed, preserved⟩
  | indDecl block nP =>
    cases pinned : basisPinHit block with
    | some kind =>
      simp only [checkDecl, pinned] at checked
      obtain ⟨out, agree, installed, preserved⟩ :=
        reference_basis_step agreement (checkIndShape_bind_ok checked).2
      refine ⟨out, agree, .stored ?_, preserved⟩
      simpa only [IxVM.Consistency.InstallStep, IxVM.Consistency.installs, pinned] using installed
    | none =>
      cases native : nativeParts? nP block with
      | some parts =>
        obtain ⟨out, agree, run, _, preserved⟩ :=
          checkedDecl_native_referenceModelStep agreement pinned native checked
        exact ⟨out, agree, .native pinned native run, preserved⟩
      | none =>
        obtain ⟨out, agree, installed, preserved⟩ :=
          checkedDecl_modeled_referenceStep agreement pinned native checked
        exact ⟨out, agree, .stored installed, preserved⟩
  | quotDecl kind cv =>
    simp only [checkDecl] at checked
    split at checked
    · cases kind with
      | type =>
        obtain ⟨out, agree, installed, preserved⟩ := reference_basis_step agreement checked
        exact ⟨out, agree, .stored installed, preserved⟩
      | ctor | lift | ind | sound =>
        have same : source = sourceOut := Except.ok.inj checked
        subst sourceOut
        exact ⟨target, agreement, .stored (installStep_glue_empty target rfl), fun _ _ inv => inv⟩
    · cases checked

/-- Every actual accepted declaration advances the annotated reference model. -/
theorem checkedDecl_referenceModelStep {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel : Nat} {ev : Evidences .anon}
    {d : Declaration .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨out, agree, _, preserved⟩ := checkedDecl_referenceTraceStep agreement checked
  exact ⟨out, agree, preserved⟩

/-- The real checker fold retains all intermediate storage steps in reference order. -/
theorem checkedDecls_referenceTrace {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ReferenceTrace fuel target declarations targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  induction declarations generalizing source target with
  | nil =>
    have same : source = sourceOut := Except.ok.inj checked
    subst sourceOut
    exact ⟨target, agreement, .nil target, fun _ _ inv => inv⟩
  | cons d rest ih =>
    simp only [List.foldlM_cons] at checked
    obtain ⟨sourceNext, head, tail⟩ := exceptBind_ok checked
    obtain ⟨targetNext, nextAgreement, step, nextModel⟩ := checkedDecl_referenceTraceStep agreement head
    obtain ⟨targetOut, outAgreement, trace, restModel⟩ := ih nextAgreement tail
    exact ⟨targetOut, outAgreement, .cons step trace, fun V _ inv => restModel V (nextModel V inv)⟩

/-- The real checker fold, in its reference order, preserves the annotated reference model. -/
theorem checkedDecls_referenceModelStep {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨out, agree, _, preserved⟩ := checkedDecls_referenceTrace agreement checked
  exact ⟨out, agree, preserved⟩

/-- Reference acceptance constructs both the typed model and the complete storage trace. -/
theorem acceptsRef_referenceTrace {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ fuel target, ThmBodyView.Agrees reference target ∧
      ReferenceTrace fuel Env.empty declarations target ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target := by
  obtain ⟨fuel, checked⟩ := Cached.AcceptsRef.iff.mp accepted
  have emptyAgreement : ThmBodyView.Agrees (Env.empty : Env .anon) Env.empty := fun _ => .same _
  obtain ⟨target, agree, trace, preserved⟩ := checkedDecls_referenceTrace emptyAgreement checked
  exact ⟨fuel, target, agree, trace, fun V _ => preserved V EnvModelT.empty⟩

/-- Reference acceptance constructs a model with actual checked theorem values. -/
theorem acceptsRef_referenceModel {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ target, ThmBodyView.Agrees reference target ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target := by
  obtain ⟨_, target, agree, _, model⟩ := acceptsRef_referenceTrace accepted
  exact ⟨target, agree, model⟩

end IxVM.Refinement.Decl
