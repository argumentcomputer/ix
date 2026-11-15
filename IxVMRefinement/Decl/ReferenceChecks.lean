import IxVMRefinement.Decl.ReferenceStorage
import IxVMRefinement.Decl.ModeledRunStructure

/-! # Actual checking certificates in reference order

This companion retains the typing derivations of value declarations and the complete
modeled/native runs. It projects to the storage trace while preserving the typed theorem
rows and the model extensions needed by later declaration proofs.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Consistency (InstallStep)

universe u

/-- Definitions retain the exact executable value and type fronts. -/
def ReferenceDefinitionRun (fuel : Nat) (env : Env .anon) (d : Declaration .anon)
    (out : Env .anon) : Prop :=
  match d with
  | .defnDecl cv value hint => DeclDefnRun .verified fuel env cv value hint out
  | _ => True

/-- The actual checked step, with the ordinary typing derivation or complete inductive run. -/
inductive CheckedReferenceStep (fuel : Nat) (env : Env .anon) : Declaration .anon → Env .anon → Prop
  | derived {d out} (front : ReferenceDefinitionRun fuel env d out) (run : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d out)
      (installed : InstallStep env d out) : CheckedReferenceStep fuel env d out
  | modeled {block nP out} (notPinned : basisPinHit block = none)
      (run : DeclIndRun .verified fuel env block out) :
      CheckedReferenceStep fuel env (.indDecl block nP) out
  | native {block nP parts out} (notPinned : basisPinHit block = none)
      (recognized : nativeParts? nP block = some parts)
      (run : DeclNativeRun .verified fuel env parts out) :
      CheckedReferenceStep fuel env (.indDecl block nP) out

theorem CheckedReferenceStep.storage {fuel : Nat} {env out : Env .anon} {d : Declaration .anon}
    (step : CheckedReferenceStep fuel env d out) : ReferenceStep fuel env d out := by
  cases step with
  | derived _ _ installed => exact .stored installed
  | modeled notPinned run => exact .stored (modeledRun_installStep notPinned run)
  | native notPinned recognized run => exact .native notPinned recognized run

theorem CheckedReferenceStep.envExt {fuel : Nat} {env out : Env .anon} {d : Declaration .anon}
    (step : CheckedReferenceStep fuel env d out) : EnvExt env out := by
  cases step with
  | derived _ run _ => exact declRunJ_envExt_routes run
  | modeled _ run => exact (modeledRun_structure run).1
  | native _ _ run =>
    exact declNativeRunJ_envExt ((verifiedRunMap _).native (declNativeRun_runJ run))

theorem CheckedReferenceStep.thmTyped {fuel : Nat} {env out : Env .anon} {d : Declaration .anon}
    (step : CheckedReferenceStep fuel env d out) (typed : ThmTyped env) : ThmTyped out := by
  cases step with
  | derived _ run _ => exact thmTyped_declRunJ typed run
  | modeled _ run => exact modeledRun_thmTyped run typed
  | @native block nP parts out notPinned recognized run =>
    apply thmTyped_declRunJ typed (d := .indDecl block nP)
    simp only [DeclRunJ, notPinned]
    exact .inl ⟨parts, recognized, (verifiedRunMap _).native (declNativeRun_runJ run)⟩

private theorem routed_modelExt {V : Type u} [SetTheory V] {env out : Env .anon}
    {d : Declaration .anon} (run : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d out)
    (model : EnvModelM V .verified env) (theorems : ThmValOk model) (eta : EtaFamiliesClosed env) :
    EtaFamiliesClosed out ∧ ∃ modelOut : EnvModelM V .verified out, ModelExt model modelOut :=
  declStep_preservesJ rulesJ_thmValue model (judgeSound_rulesJ_of model) (axiomBits_rulesJ env) eta
    (by
      intro _ _ _ routes
      rcases routes with ⟨_, recognized, native⟩ | modeled | ⟨_, recognized, native⟩ | twin
      · exact nativeStep_rulesJ model theorems eta recognized native
      · exact modeledStep_rulesJ model eta modeled
      · exact nativeNoRecStep_rulesJ model theorems eta recognized native
      · exact twinStep_rulesJ model eta twin) run

/-- Each actual checking step retains its model extension, model preservation. -/
theorem CheckedReferenceStep.modelExt {V : Type u} [SetTheory V]
    {fuel : Nat} {env out : Env .anon} {d : Declaration .anon}
    (step : CheckedReferenceStep fuel env d out)
    (model : EnvModelM V .verified env) (theorems : ThmValOk model) (eta : EtaFamiliesClosed env) :
    EtaFamiliesClosed out ∧ ∃ modelOut : EnvModelM V .verified out, ModelExt model modelOut := by
  cases step with
  | derived _ run _ => exact routed_modelExt run model theorems eta
  | modeled _ run => exact ⟨declIndEtaClosedRun eta run, Ix.Kernel.Model.declIndExt rfl model eta run⟩
  | native _ recognized run =>
    exact nativeStep_rulesJ model theorems eta recognized
      ((verifiedRunMap _).native (declNativeRun_runJ run))

/-- An actual value declaration exposes its checked type and value fronts at the real prefix. -/
theorem CheckedReferenceStep.definition {fuel : Nat} {env out : Env .anon}
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint}
    (step : CheckedReferenceStep fuel env (.defnDecl cv value hint) out) :
    DeclDefnRun .verified fuel env cv value hint out := by
  cases step with
  | derived front _ _ => exact front

/-- A checked trace retains all intermediate environments and the certificates checked there. -/
inductive CheckedReferenceTrace (fuel : Nat) : Env .anon → List (Declaration .anon) → Env .anon → Prop
  | nil (env) : CheckedReferenceTrace fuel env [] env
  | cons {env middle out d ds} (step : CheckedReferenceStep fuel env d middle)
      (tail : CheckedReferenceTrace fuel middle ds out) :
      CheckedReferenceTrace fuel env (d :: ds) out

theorem CheckedReferenceTrace.storage {fuel : Nat} {env out : Env .anon}
    {ds : List (Declaration .anon)} (trace : CheckedReferenceTrace fuel env ds out) :
    ReferenceTrace fuel env ds out := by
  induction trace with
  | nil env => exact .nil env
  | cons step _ ih => exact .cons step.storage ih

theorem CheckedReferenceTrace.envExt {fuel : Nat} {env out : Env .anon}
    {ds : List (Declaration .anon)} (trace : CheckedReferenceTrace fuel env ds out) :
    EnvExt env out := by
  induction trace with
  | nil env => exact EnvExt.refl env
  | cons step _ ih => exact step.envExt.trans ih

theorem CheckedReferenceTrace.thmTyped {fuel : Nat} {env out : Env .anon}
    {ds : List (Declaration .anon)} (trace : CheckedReferenceTrace fuel env ds out) :
    ThmTyped env → ThmTyped out := by
  induction trace with
  | nil => exact id
  | cons step _ ih => exact fun typed => ih (step.thmTyped typed)

/-- The full checked trace preserves the same old constant readings through model extension. -/
theorem CheckedReferenceTrace.modelExt {V : Type u} [SetTheory V] {fuel : Nat}
    {env out : Env .anon} {ds : List (Declaration .anon)}
    (trace : CheckedReferenceTrace fuel env ds out) :
    ∀ model : EnvModelM V .verified env, ThmValOk model → EtaFamiliesClosed env →
      EtaFamiliesClosed out ∧ ∃ modelOut : EnvModelM V .verified out, ModelExt model modelOut := by
  induction trace with
  | nil => intro model _ eta; exact ⟨eta, model, .refl⟩
  | cons step _ ih =>
    intro model theorems eta
    obtain ⟨etaMiddle, middle, first⟩ := step.modelExt model theorems eta
    obtain ⟨etaOut, outModel, rest⟩ := ih middle (theorems.of_ext first) etaMiddle
    exact ⟨etaOut, outModel, first.trans rest⟩

theorem CheckedReferenceTrace.envModelT {V : Type u} [SetTheory V] {fuel : Nat}
    {env out : Env .anon} {ds : List (Declaration .anon)}
    (trace : CheckedReferenceTrace fuel env ds out) (inv : EnvModelT V .verified env) :
    EnvModelT V .verified out := by
  obtain ⟨⟨model, theorems⟩, eta⟩ := inv
  obtain ⟨etaOut, outModel, extension⟩ := trace.modelExt model theorems eta
  exact ⟨⟨outModel, theorems.of_ext extension⟩, etaOut⟩

/-- Recover the actual checking certificate at any declaration in the accepted order. -/
theorem CheckedReferenceTrace.declarationStep {fuel : Nat} {env out : Env .anon}
    {ds : List (Declaration .anon)} (trace : CheckedReferenceTrace fuel env ds out)
    {d : Declaration .anon} (member : d ∈ ds) :
    ∃ before after start finish,
      ds = before ++ d :: after ∧ CheckedReferenceTrace fuel env before start ∧
        CheckedReferenceStep fuel start d finish ∧ CheckedReferenceTrace fuel finish after out := by
  induction trace with
  | nil => cases member
  | @cons env middle out head rest step tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨[], rest, env, middle, rfl, .nil env, step, tail⟩
    · obtain ⟨before, after, start, finish, split, prefixRun, selected, suffixRun⟩ := ih later
      refine ⟨head :: before, after, start, finish, ?_, .cons step prefixRun, selected, suffixRun⟩
      rw [split]
      rfl

end IxVM.Refinement.Decl
