import IxVMRefinement.TwinFamily.StepOfFacts
import IxVMRefinement.FamilyGraph.Composition

/-! # The twin row from the twin's step

`FamilyTwinRow` steps a second family record `A` of a block `B` (`twin A = some B`), handed the
block's family record: the graph's (`fam B = some rb`), or one the witness's environment stores.
This module gives the graph case from the twin's step `unitStepTwin_of_facts_fam`, at the row's
own hypotheses, and the row from it and the stored case.

The run gives the step what it reads: the block is a block of inductive types
(`FamilyRun.famInd`), whose member and constructor projections the walk holds; the family checks
of the block with its family record and with the twin are at one binding
(`FamilyRun.famRecAt`, `FamilyChecksAt.twinCall`). What the run does not yet give is the graph's
choice of the family record in the form `RForm` wherever the twin is in it, at that binding
(`TwinFormAt`): a field of the run's checks once `RForm` is fixed.

* `familyTwinStep_graph`: the twin's step at the graph's family record;
* `familyTwinRow_of`: `FamilyTwinRow`, from the seam, the form choice at every run, and the step
  of a twin of a block the witness's environment stores. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel.Semantics (NativeFam)

set_option linter.unusedVariables false

/-- **The graph's form choice at the run's checks**: at the binding of the run's family checks,
a block's family record is in the form `RForm` wherever a twin of the block is. -/
def TwinFormAt (RForm : RecordFormPred) (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (lim : Option Nat) (fam twin : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop) : Prop :=
  ∀ bAddr, FamilyChecksAt calls bAddr t E₀ lim fam twin adv Inner →
    ∀ rb' B rb, twin rb' = some B → fam B = some rb →
      RForm calls bAddr t E₀ B rb' lim → RForm calls bAddr t E₀ B rb lim

/-- **The twin's step at the graph's family record**: at the row's hypotheses with
`fam B = some rb`, from the seam and the form choice. -/
theorem familyTwinStep_graph {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {RForm : RecordFormPred} (hseam : TwinSeam.{u} RForm)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    {E₀ : Ixon.Env} {lim : Option Nat} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hform : TwinFormAt RForm calls t E₀ lim fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A : _root_.Address} {c : Ixon.Constant} {B rb : _root_.Address} {crb : Ixon.Constant}
    (hW : Walked Top Inner A) (hc : recordOf E₀ A = some c) (htw : twin A = some B)
    (hfam : fam B = some rb) (hcrb : recordOf E₀ rb = some crb) :
    UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb := by
  obtain ⟨bAddrW, hWc, hG⟩ := hWalk
  have ht : t.check = .ok () := hWc.check_ok
  -- the block's record
  obtain ⟨-, cb₀, hcb₀, hlogB, -⟩ := hFR.graph.famUnit B rb hfam
  obtain ⟨cb, ms, hcb, hms, hind⟩ := hFR.famInd B rb hfam
  have ecb : cb = cb₀ := Option.some.inj (hcb.symm.trans hcb₀)
  have hlog : InLogic cb := by
    rw [ecb]
    exact hlogB
  have hTB : Top B := hFR.graph.famBlock B rb hfam
  have hB : FamBlockRecord E₀ B cb ms :=
    { record := hcb
      muts := hms
      indcs := hind
      logic := hlog
      members := fun i m hm => (hG.members B cb ms hTB hcb hms i m hm).1
      ctors := fun i ind j hm hj =>
        (hG.members B cb ms hTB hcb hms i (.indc ind) hm).2 ind j rfl hj }
  -- the family checks of the block, with its family record and with the twin, at one binding
  obtain ⟨bAddr, hC, hrec⟩ := hFR.famRecAt
  have hrbB : FamRecOfBlock calls bAddr t E₀ B rb crb lim := hrec B rb crb hfam hcrb
  obtain ⟨cs', hcallA⟩ := hC.twinCall A B htw
  have hpref := hform bAddr hC A B rb htw hfam
  have hroute : ModeledRouteAt calls B := (hC.famCall B rb hfam).1
  -- the twin's record
  obtain ⟨c₀, rs', hA₀, hsz⟩ := hFR.graph.twinRecord A B htw
  have hA : FamRecRecord E₀ A c rs' := by
    have e : c₀ = c := Option.some.inj (hA₀.record.symm.trans hc)
    rw [← e]
    exact hA₀
  have hne : A ≠ rb := by
    rcases hFR.graph.twinBlock A B htw with ⟨rb₀, hrb₀, hne, -⟩ | hnone
    · have e : rb₀ = rb := Option.some.inj (hrb₀.symm.trans hfam)
      rw [← e]
      exact hne
    · rw [hfam] at hnone
      cases hnone
  -- a step is asked only at an environment that extends the witness's and stores none of the
  -- twin's constant addresses, so none of them is the witness's
  intro env hext hnd hinv hX href hrbS hfresh
  have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
    intro x hx hst
    obtain ⟨ci, hci, hname⟩ := hst
    have hs : (env.find? (keyOf t x)).isSome = true :=
      find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
    rw [hfresh x hx] at hs
    simp at hs
  exact unitStepTwin_of_facts_fam hL hseam ht hWc.runStore hctx.toStepStore hB hrbB hfam hA hsz
    hne hcallA hpref hroute (fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx))
    env hext hnd hinv hX href hrbS hfresh

/-- **The twin's step at a family record the witness's environment stores** (the stored case of
`FamilyTwinRow`; open: to be restated against one block-indexed stored family). -/
def StoredTwinStep (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (B rb : _root_.Address) (crb : Ixon.Constant),
        Walked Top Inner A → recordOf E₀ A = some c → InLogic c → twin A = some B →
        fam B = none → (∀ x, ConstAddrOf rb crb x → StoredAt t envT x) →
        FamilyInstalled t envT rb crb →
        UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb

/-- **The twin row** from the seam at a record form `RForm`, the graph's form choice at every
run (`TwinFormAt`, a field of the run's checks once `RForm` is fixed), and the stored case. -/
theorem familyTwinRow_of {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {RForm : RecordFormPred} (hseam : TwinSeam.{u} RForm)
    (hform : ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
      (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
      (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ (envT : Ix.Kernel.Env .anon) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
        TwinFormAt RForm calls t E₀ lim fam twin adv Inner)
    (hstored : StoredTwinStep.{u} L) :
    FamilyTwinRow.{u} L := by
  intro calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c B rb crb
    hW hc hlog htw hcase
  rcases hcase with ⟨hfam, hcrb⟩ | ⟨hnone, hst, hinst⟩
  · exact familyTwinStep_graph hL hseam hWalk hFR
      (hform calls t seeds E₀ lim Top rank hWalk envT fam twin adv Inner hFR) hctx hW hc htw hfam
      hcrb
  · exact hstored calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c B
      rb crb hW hc hlog htw hnone hst hinst

end IxVM.Refinement.Typing.TwinFamily
