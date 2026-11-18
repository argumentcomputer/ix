import IxVMRefinement.TwinFamily.StoredTwin

/-! # The twin row restated with its stored case at the witness's selected family record

`FamilyTwinRow`'s stored disjunct accepts any stored pair `rb crb` (review H1: the empty record
satisfies it and supplies no canonical member). Restated, the stored case names the witness's
selected record of the twin's block (`StoredTwinCanon`), and the row takes the selected records'
form (`Binding.StoredFamiliesRForm`) with the witness's map:

* `FamilyTwinRowFam RFormS L`: the row with the restated stored case;
* `familyTwinRowFam_of`: the row from the graph case's seam and form choice (as
  `familyTwinRow_of`) and the stored case's seam and positional identity
  (`storedTwinStepFam_of`);
* `storedTwinStepFam_of_row`: the stored case is the row's second disjunct, so the composition's
  stored conjunct (`storedTwinSteps_of`) follows from the row;
* `storedFamiliesRForm_none`: the graph case asks no selected record, so the row is used there at
  the empty map. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Binding (StoredFamiliesRForm StoredFormPred)
open Ix.Kernel.Semantics (NativeFam)

set_option linter.unusedVariables false

/-- **The twin row, with its stored case at the witness's selected family record**: the step of
a second family record `A` of a block `B`, handed the block's family record: the graph's
(`fam B = some rb`), or, for a block with no family record in the graph, the record the witness
selects for it (`StoredTwinCanon`), with every selected record in the form `RFormS`. -/
def FamilyTwinRowFam (RFormS : StoredFormPred)
    (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ famOf : _root_.Address → Option _root_.Address, StoredFamiliesRForm RFormS t R famOf →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (B rb : _root_.Address) (crb : Ixon.Constant),
        Walked Top Inner A → recordOf E₀ A = some c → InLogic c → twin A = some B →
        ((fam B = some rb ∧ recordOf E₀ rb = some crb) ∨
          (fam B = none ∧ StoredTwinCanon t R envT famOf B rb crb)) →
        UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb

/-- **The restated twin row** from the graph case's seam at `RForm` and the graph's form choice
at every run (as `familyTwinRow_of`), and the stored case's seam at `RFormS` and the positional
identity of the two records (`storedTwinStepFam_of`). -/
theorem familyTwinRowFam_of {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {RForm : RecordFormPred} (hseam : TwinSeam.{u} RForm)
    (hform : ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
      (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
      (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ (envT : Ix.Kernel.Env .anon) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
        TwinFormAt RForm calls t E₀ lim fam twin adv Inner)
    {RFormS : StoredFormPred} (hseamS : TwinSeamStored.{u} RFormS)
    (hpos : TwinOnStoredFlat.{u}) :
    FamilyTwinRowFam.{u} RFormS L := by
  intro calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx famOf hRF A c B
    rb crb hW hc hlog htw hcase
  rcases hcase with ⟨hfam, hcrb⟩ | ⟨hnone, hcanon⟩
  · exact familyTwinStep_graph hL hseam hWalk hFR
      (hform calls t seeds E₀ lim Top rank hWalk envT fam twin adv Inner hFR) hctx hW hc htw hfam
      hcrb
  · exact storedTwinStepFam_of hL hseamS hpos calls t seeds E₀ lim Top rank hWalk R envT E fam
      twin adv Inner hFR hctx famOf hRF A c B rb crb hW hc hlog htw hnone hcanon

/-- **The stored case is the row's second disjunct.** -/
theorem storedTwinStepFam_of_row {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred} (h : FamilyTwinRowFam.{u} RFormS L) :
    StoredTwinStepFam.{u} RFormS L :=
  fun calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx famOf hRF A c B
    rb crb hW hc hlog htw hnone hcanon =>
    h calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx famOf hRF A c B rb
      crb hW hc hlog htw (Or.inr ⟨hnone, hcanon⟩)

/-- **The empty map selects no record**, so every selected record is in any form. -/
theorem storedFamiliesRForm_none (RFormS : StoredFormPred) {t : Ix.Kernel.RoleTable}
    {R : Ixon.Env} : StoredFamiliesRForm RFormS t R (fun _ => none) :=
  fun _ _ h => nomatch h

/-- **The graph case of the restated row**, at the empty map (the composition's twin conjunct
with the graph's family record). -/
theorem familyTwinStep_graph_of_row {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred} (h : FamilyTwinRowFam.{u} RFormS L)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    {E₀ : Ixon.Env} {lim : Option Nat} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A : _root_.Address} {c : Ixon.Constant} {B rb : _root_.Address} {crb : Ixon.Constant}
    (hW : Walked Top Inner A) (hc : recordOf E₀ A = some c) (hlog : InLogic c)
    (htw : twin A = some B) (hfam : fam B = some rb) (hcrb : recordOf E₀ rb = some crb) :
    UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb :=
  h calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx (fun _ => none)
    (storedFamiliesRForm_none RFormS) A c B rb crb hW hc hlog htw (Or.inl ⟨hfam, hcrb⟩)

end IxVM.Refinement.Typing.TwinFamily
