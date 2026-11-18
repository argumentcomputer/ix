import IxVMRefinement.FamilyGraph.Skeleton
import IxVMRefinement.TwinFamily.Keeps

/-! # The family skeleton carrying the family recursors' companions

A twin's step needs its block's family record installed: each of its recursors stored with a
model companion (`TwinFamily.FamilyInstalled`). The fold hands a twin only that the record's
constant addresses are stored, so the companions are carried as a clause beside the fold's own
`X`: `X ∧ FamilyRecsModeled` (a stored constant at a constant address of a claimed family record
is a recursor with a companion). `typing_skeleton_core_family_modeled` is
`typing_skeleton_core_family` at that clause, with

* the plain steps (top-walked units and units checked inside a family check) taken at `X`: a
  unit is claimed by no block, so its step keeps the clause
  (`TwinFamily.unitStep_keepsFamilyRecsModeled`);
* the family step and the twin step taken at `X ∧ FamilyRecsModeled`: the family step stores the
  recursors of its record with their companions, and the twin's step reads the clause;
* the clause at the witness's environment from the graph (`famFresh`:
  `TwinFamily.familyRecsModeled_start`).

No clause file is edited: the fold's clause stays `X`, and the conjunct lives in this wrapper. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open TwinFamily (FamilyRecsModeled)

set_option linter.unusedVariables false

section Skeleton

variable {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon}
  {seeds : List _root_.Address} {calls : List (Call F)}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- **The typing conclusion over the family graph, with the family recursors' companions
carried beside the clause `X`** (module docstring). The inputs are `typing_skeleton_core_family`'s,
with the top-walked and the inner units' steps at `X` and the family and twin steps at
`X ∧ FamilyRecsModeled`. -/
theorem typing_skeleton_core_family_modeled {V : View} {extra : List ByteArray}
    {X : Ixon.Env → Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hinvL : ∀ E, RecordsFor R E → Decl.PrefixInv.{u} E t lim envT)
    (hwholeL : ∀ E, RecordsFor R E →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb →
        cb.info = .muts ms → BlockStored t envT B ms)
    (hX : ∀ E, RecordsFor R E → X E envT)
    (ht : t.check = .ok ())
    (hb : Bounded calls) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) (hS : LoadedReads.RunStore calls E₀)
    (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hstepTop : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → Unclaimed fam A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (X E) t envT E₀ E lim A c)
    (hstepInner : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (X E) t envT E₀ E lim A c)
    (hstepFam : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c rb crb rs, Top A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = some rb →
      FamRecRecord E₀ rb crb rs →
      UnitStepFamily.{u} (fun env => X E env ∧ FamilyRecsModeled t E₀ fam env) t envT E₀ E lim
        A c rb crb (adv A))
    (hstepTwin : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B rb crb, Walked Top Inner A →
      recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = some rb →
      recordOf E₀ rb = some crb →
      UnitStepTwin.{u} (fun env => X E env ∧ FamilyRecsModeled t E₀ fam env) t envT E₀ E lim
        A c rb crb) :
    ConsistentReadOver.{u} calls t R envT seeds := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  exact typing_skeleton_core_family
    (X := fun E env => X E env ∧ FamilyRecsModeled t E₀ fam env)
    hshape hinvL hwholeL (fun E hE => ⟨hX E hE, TwinFamily.familyRecsModeled_start hF⟩) ht hb
    hextra hnc hS hG hF
    (fun E hctx A c hT hU hc hlog hk hfa htw =>
      TwinFamily.unitStep_keepsFamilyRecsModeled hG hF hroles (Or.inl hT) hU hc
        (hstepTop E hctx A c hT hU hc hlog hk hfa htw))
    (fun E hctx A c hI hU hc hlog hk hfa htw =>
      TwinFamily.unitStep_keepsFamilyRecsModeled hG hF hroles (Or.inr hI) hU hc
        (hstepInner E hctx A c hI hU hc hlog hk hfa htw))
    hstepFam hstepTwin

end Skeleton

end IxVM.Refinement.Typing
