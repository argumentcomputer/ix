import IxVMRefinement.Decl.ReferenceReplay
import IxC.Kernel.Verify.Cached.Reference

/-! # The complete accepted reference fold with checked theorem values

Every declaration kind retains its actual checking certificate in reference order. The
checking view keeps normalized native signatures and all non-theorem data exact, while
theorem bodies are the checked annotations needed by the model and typed theorem rows.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

private theorem reference_basis_checked {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {kind : BasisKind}
    (checked : checkBasisDecl (m := CheckM .anon) source kind = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧ DeclBasisRun target kind targetOut :=
  agreement.declBasisRun (declBasisRunOf checked)

/-- Every accepted declaration retains the typing or complete inductive run actually checked. -/
theorem checkedDecl_referenceCheck {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel : Nat} {ev : Evidences .anon}
    {d : Declaration .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      CheckedReferenceStep fuel target d targetOut := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨out, agree, installed, run⟩ := agreement.checkedDefn_runStep checked
    exact ⟨out, agree, .derived run (declDefnRun_rulesJ run) installed⟩
  | thmDecl cv value =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedThm_step.{0} agreement checked
    exact ⟨out, agree, .derived trivial run installed⟩
  | opaqueDecl cv value =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedOpaque_step.{0} agreement checked
    exact ⟨out, agree, .derived trivial run installed⟩
  | axiomDecl cv =>
    obtain ⟨out, agree, installed, run, _⟩ := ThmBodyView.Agrees.checkedAxiom_step.{0} agreement checked
    exact ⟨out, agree, .derived trivial run installed⟩
  | basisDecl kind =>
    obtain ⟨out, agree, run⟩ := reference_basis_checked agreement checked
    exact ⟨out, agree, .derived trivial run (installStep_glue_basis run)⟩
  | indDecl block nP =>
    cases pinned : basisPinHit block with
    | some kind =>
      simp only [checkDecl, pinned] at checked
      obtain ⟨out, agree, run⟩ :=
        reference_basis_checked agreement (checkIndShape_bind_ok checked).2
      refine ⟨out, agree, .derived trivial ?_ (installStep_glue_pinnedInd pinned run)⟩
      simpa only [DeclRunJ, pinned] using run
    | none =>
      cases native : nativeParts? nP block with
      | some parts =>
        obtain ⟨out, agree, run, _, _⟩ :=
          checkedDecl_native_referenceModelStep.{0} agreement pinned native checked
        exact ⟨out, agree, .native pinned native run⟩
      | none =>
        simp only [checkDecl, pinned, native] at checked
        have rest := (checkIndShape_bind_ok checked).2
        split at rest
        · obtain ⟨out, agree, run, _⟩ := ThmBodyView.Agrees.checkedModeled_modelStep.{0} agreement rest
          exact ⟨out, agree, .modeled pinned run⟩
        · cases rest
  | quotDecl kind cv =>
    simp only [checkDecl] at checked
    split at checked
    · cases kind with
      | type =>
        obtain ⟨out, agree, run⟩ := reference_basis_checked agreement checked
        exact ⟨out, agree, .derived trivial run (installStep_glue_quot run)⟩
      | ctor | lift | ind | sound =>
        have same : source = sourceOut := Except.ok.inj checked
        subst sourceOut
        exact ⟨target, agreement, .derived trivial rfl (installStep_glue_empty target rfl)⟩
    · cases checked

/-- Every accepted declaration retains its actual storage evidence alongside model preservation. -/
theorem checkedDecl_referenceTraceStep {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel : Nat} {ev : Evidences .anon}
    {d : Declaration .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ReferenceStep fuel target d targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨out, agree, step⟩ := checkedDecl_referenceCheck agreement checked
  refine ⟨out, agree, step.storage, fun V _ inv => ?_⟩
  exact (CheckedReferenceTrace.cons step (.nil out)).envModelT inv

/-- Every actual accepted declaration advances the annotated reference model. -/
theorem checkedDecl_referenceModelStep {source target sourceOut : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {fuel : Nat} {ev : Evidences .anon}
    {d : Declaration .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨out, agree, _, preserved⟩ := checkedDecl_referenceTraceStep agreement checked
  exact ⟨out, agree, preserved⟩

/-- The actual source calls and annotated target steps remain paired throughout the fold. -/
theorem checkedDecls_referenceReplay {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ReferenceReplay fuel ev source target declarations sourceOut targetOut := by
  induction declarations generalizing source target with
  | nil =>
    have same : source = sourceOut := Except.ok.inj checked
    subst sourceOut
    exact ⟨target, .nil agreement⟩
  | cons d rest ih =>
    simp only [List.foldlM_cons] at checked
    obtain ⟨sourceNext, head, tail⟩ := exceptBind_ok checked
    obtain ⟨targetNext, nextAgreement, step⟩ := checkedDecl_referenceCheck agreement head
    obtain ⟨targetOut, replay⟩ := ih nextAgreement tail
    exact ⟨targetOut, .cons agreement head step replay⟩

/-- The real checker fold retains its actual intermediate certificates and environments. -/
theorem checkedDecls_referenceChecks {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      CheckedReferenceTrace fuel target declarations targetOut := by
  obtain ⟨out, replay⟩ := checkedDecls_referenceReplay agreement checked
  exact ⟨out, replay.endAgreement, replay.checked⟩

/-- The real checker fold retains all intermediate storage steps in reference order. -/
theorem checkedDecls_referenceTrace {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ReferenceTrace fuel target declarations targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨out, agree, trace⟩ := checkedDecls_referenceChecks agreement checked
  exact ⟨out, agree, trace.storage, fun _ _ inv => trace.envModelT inv⟩

/-- The real checker fold, in its reference order, preserves the annotated reference model. -/
theorem checkedDecls_referenceModelStep {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut : Env .anon} (agreement : ThmBodyView.Agrees source target)
    {declarations : List (Declaration .anon)}
    (checked : declarations.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut) :
    ∃ targetOut, ThmBodyView.Agrees sourceOut targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨out, agree, _, preserved⟩ := checkedDecls_referenceTrace agreement checked
  exact ⟨out, agree, preserved⟩

/-- Reference acceptance constructs the paired source and annotated checking replay. -/
theorem acceptsRef_referenceReplay {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ fuel target, ReferenceReplay fuel ev Env.empty Env.empty declarations reference target := by
  obtain ⟨fuel, checked⟩ := Cached.AcceptsRef.iff.mp accepted
  have emptyAgreement : ThmBodyView.Agrees (Env.empty : Env .anon) Env.empty := fun _ => .same _
  obtain ⟨target, replay⟩ := checkedDecls_referenceReplay emptyAgreement checked
  exact ⟨fuel, target, replay⟩

/-- Reference acceptance constructs a complete trace of actual checking certificates. -/
theorem acceptsRef_referenceChecks {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ fuel target, ThmBodyView.Agrees reference target ∧
      CheckedReferenceTrace fuel Env.empty declarations target := by
  obtain ⟨fuel, target, replay⟩ := acceptsRef_referenceReplay accepted
  exact ⟨fuel, target, replay.endAgreement, replay.checked⟩

/-- The accepted checking store has actual typed theorem rows and a model at every set theory. -/
theorem acceptsRef_referenceTyped {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ fuel target, ThmBodyView.Agrees reference target ∧
      CheckedReferenceTrace fuel Env.empty declarations target ∧ ThmTyped target ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target := by
  obtain ⟨fuel, target, agree, trace⟩ := acceptsRef_referenceChecks accepted
  exact ⟨fuel, target, agree, trace, trace.thmTyped ThmTyped.empty,
    fun _ _ => trace.envModelT EnvModelT.empty⟩

/-- Reference acceptance constructs both the typed model and the complete storage trace. -/
theorem acceptsRef_referenceTrace {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ fuel target, ThmBodyView.Agrees reference target ∧
      ReferenceTrace fuel Env.empty declarations target ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target := by
  obtain ⟨fuel, target, agree, trace, _, model⟩ := acceptsRef_referenceTyped accepted
  exact ⟨fuel, target, agree, trace.storage, model⟩

/-- Reference acceptance constructs a model with actual checked theorem values. -/
theorem acceptsRef_referenceModel {ev : Evidences .anon} {declarations : List (Declaration .anon)}
    {reference : Env .anon} (accepted : Cached.AcceptsRef .verified ev declarations reference) :
    ∃ target, ThmBodyView.Agrees reference target ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target := by
  obtain ⟨_, target, agree, _, model⟩ := acceptsRef_referenceTrace accepted
  exact ⟨target, agree, model⟩

end IxVM.Refinement.Decl
