import IxVMRefinement.FamilyGraph.ProducersInner
import IxVMRefinement.TwinFamily.StoredTwin
import IxVMRefinement.TwinFamily.StoredTwinRow
import IxVMRefinement.FamilyAlias.ClosureFamilyStep
import IxVMRefinement.Binding.BasisWalked

/-! # The typing half at the witness with its stored families, and the stored twins from them

The binding half gives the table's witness with one selected family map (`OverWFam L`: the
internal part `OverW L` and `∃ famOf, StoredFamilies t R env famOf`). The typing half over the
family graph is stated at `OverW L` and weakened (`typingSpecOn_mono`), so the graph row cannot
read the map, and the stored twins' field (`StoredTwinField`, `FamilyRun.storedTwin`) is a
premise of its own. This module states the typing half at `OverWFam L` and produces that field
from the map:

* `FamilyStepsFam`: `FamilySteps` with the witness's map, the agreement of the run's store
  with the witness's on the records both hold (the no-collision branch gives it:
  `records_agree`) and a step store of the run for the witness (`StepCtx`; the same branch gives
  the merged store) as premises;
* `typing_skeleton_over_familyFam`: the typing half at `OverWFam L` from `FamilyStepsFam`;
  `composed_skeleton_over_familyWFam`: the composed statement with no weakening;
* `FamilyGraphRowInnerFam`, `familyStepsFam_of_graphInner`: the graph row with the inner records
  (`FamilyGraphRowInner`) reading the map and the agreement, and the typing half's premise from
  it and the other rows;
* `storedTwinField_of_block`: the stored twins' field from the map, given that the block of each
  stored twin is a stored modeled block of the witness's store (`TwinFamily.StoredTwinBlock`);
* `FamRunCtx.twinBlock_stored`, `FamRunCtx.twin_routed`, `StoredTwinReads`,
  `storedTwinBlock_of_reads`: that block fact from the selector (a twin's block with no family
  record has its constant addresses stored), the run's facts (every twin's block routed as
  modeled and in Lean's logic: `BatchGives.routed`, `BatchGives.inLogic`), the agreement, and two
  reads of the witness (`StoredTwinReads`: its store holds the block and routes it as modeled);
* `recordsFor_basisStore`, `storedTwinReads_of_walk`: those two reads at a walk with a step
  store, whose route the run's dispatch answers and which holds the run's records, the
  witness's and the basis rows;
* `FamilyGraphInnerOwedFam`, `familyGraphRowInnerFam_of_owed`: what the graph row and the inner
  records are owed at the witness with its map and a step store: neither `StoredTwinField` nor
  `StoredTwinReads`;
* `circuitComposed_of_partsFamInnerW`: the public statement with the typing half at
  `OverWFam L`;
* `FamilyGraphRowInnerFamT Pref`, `familyGraphRowInnerFamT_of_owed`: the graph row at the
  witness with its stored families, exporting at the run's one binding its family checks
  (`FamilyChecksAt`), the block of every stored twin a stored modeled block of the witness's store
  (`StoredTwinBlock`), and, at a block with a family record and a twin, the record non-empty and
  in the preferred form when the twin is (`FamRunCtx.twin_canonical`);
* `StoredFormAt RFormS`: the selected records of every witness in the form `RFormS`;
  `storedFormAt_recon`: it at the reconstruction's form `FamilyRecon.RFormS`, from the stored
  families (`StoredFamilies.form`);
* `familyStepsFam_of_graphInnerT`, `circuitComposed_of_partsFamInnerWT`: the typing half's premise
  and the public statement with the twin row's stored case at the witness's selected record
  (`TwinFamily.FamilyTwinRowFam`): the graph case from the row at the graph's record, the stored
  case from the row at the selected record (`TwinFamily.storedTwinSteps_of`) with the selected
  records' flattened families (`StoredFamilies.flat`) and form. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Binding
open IxVM.Refinement.Endpoint
open TwinFamily (FamilyRecsModeled FamilyInstalled StoredTwinBlock)
open FamilyAlias (FamilyCallAtLim)

set_option linter.unusedVariables false

/-! ## The typing half at the witness with its stored families -/

/-- **The agreement of the run's store with the witness's**: a record both hold at one address
is the same record. On the branch where the run hashed no collision with the witness's store it
holds (`records_agree`). -/
def RecordsAgree (E₀ R : Ixon.Env) : Prop :=
  ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c'

/-- **The typing half's premise over the family graph, reading the witness's stored families**:
`FamilySteps` with the witness's selected family map (`StoredFamilies`), the agreement of the
run's store with the witness's (`RecordsAgree`) and a step store of the run for the witness
(`StepCtx`) as premises. -/
def FamilyStepsFam (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (calls : List (Call F))
    (Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop) : Prop :=
  ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∀ famOf, StoredFamilies t R envT famOf → RecordsAgree E₀ R →
      (∃ E, StepCtx.{u} calls t R envT E₀ E) →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        Walk t seeds E₀ lim Top rank' ∧
        FamilyGraph t envT E₀ Top rank' fam twin adv Inner ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c rb crb rs, Top A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = some rb →
          FamRecRecord E₀ rb crb rs →
          UnitStepFamily.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c rb crb (adv A)) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B rb crb, Walked Top Inner A →
          recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = some rb →
          recordOf E₀ rb = some crb →
          UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c rb crb) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B, Walked Top Inner A →
          recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = none →
          UnitStep.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c)

/-- `FamilySteps` gives `FamilyStepsFam`: the new premises are not read. -/
theorem familyStepsFam_of_steps {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    (h : FamilySteps.{u} L calls Walk) : FamilyStepsFam.{u} L calls Walk :=
  fun t seeds E₀ lim Top rank hW R envT hshape _ _ _ _ =>
    h t seeds E₀ lim Top rank hW R envT hshape

/-- **The typing half over the fold's clause and the family graph, at the witness with its
stored families**: `typing_skeleton_over_family` at `OverWFam L`, handing the graph the
witness's map and, on the branch where the run hashed no collision, the agreement of the two
stores and the merged store as a step store (`Merged.recordsFor`, `Merged.run_record`,
`Merged.good`). -/
theorem typing_skeleton_over_familyFam {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hsteps : FamilyStepsFam.{u} L calls Walk) :
    TypingSpecOn.{u} (OverWFam.{u} L) calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  by_cases hnc : CollisionWith V (bytes :: tb :: committedFootprint) R calls
  · exact Or.inl hnc
  · refine Or.inr ?_
    have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ bytes :: tb :: committedFootprint :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
    rcases hclaim bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm with
      hcol | ⟨E₀, lim, Top, rank, hS, hWalk⟩
    · exact (hnc (Or.inl hcol)).elim
    · have hF : BoundaryFacts t (fun _ => True) R envT := hW.facts.1.1
      obtain ⟨Reg, hR⟩ := hW.facts.1.2
      obtain ⟨famOf, hSF⟩ := hW.facts.2
      have hc : Carried lim := carried_of_typingLim (hlim t seeds E₀ lim Top rank hWalk)
      have hctx : ∃ E, StepCtx.{u} calls t R envT E₀ E := by
        obtain ⟨E, hM⟩ := merged_exists E₀ R
        exact ⟨E, hW.shape,
          hM.recordsFor hS.loaded hS.decoded hW.shape.committed hextra hnc,
          fun a c h => hM.run_record hS.loaded hS.decoded hextra hnc h,
          fun a b h => hM.run_blob hS.loaded hnc h,
          fun env lim => hM.good hS.loaded hW.shape.zeroFree hextra hnc hb env t lim⟩
      obtain ⟨rank', fam, twin, adv, Inner, hWalk', hFG, hTop, hInner, hFam, hTwin,
        hTwinStored⟩ := hsteps t seeds E₀ lim Top rank hWalk R envT hW.shape famOf hSF
          (records_agree hS.loaded hnc) hctx
      exact typing_skeleton_core_family_modeled (X := fun E => FoldExtra.{u} L t E) hW.shape
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).prefixInv) hF.whole
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).extra) ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank' hWalk') hFG hTop hInner hFam hTwin hTwinStored

/-- **The composed statement with the binding half's family form and the typing half reading
it**: `composed_skeleton_over_familyW` with the typing half at `OverWFam L` itself
(`typing_skeleton_over_familyFam`), no weakening. -/
theorem composed_skeleton_over_familyWFam {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (bindingClaimExport : BindingClaimExportObs Run callsB dB)
    (basisGroups : BasisOverW.{u} L Run)
    (groupAdmissions : AdmitsChain Run) (groupAdmissionReads : AdmitsReadsChain Run)
    (groupFamilies : FamiliesChain Run Fam)
    (groupClosure : AtGroups Run fun ρ t g => ClosureStepOverFamilyW.{u} L ρ t g (Fam ρ t g))
    (groupWithoutRoleUnit : AtGroups Run (RoleFreeShapes.{u} L))
    (operationRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepsA : FamilyStepsFam.{u} L callsA Walk) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_overW bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
      groupFamilies groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit)
    (typing_skeleton_over_familyFam hb hclaimA hlim hgraph hstepsA)

/-! ## The graph row reading the witness's stored families -/

/-- **Row `familyGraph` with the inner records, at the witness with its stored families**:
`FamilyGraphRowInner` with the witness's map, the agreement of the two stores and a step store
of the run for the witness as premises. -/
def FamilyGraphRowInnerFam : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∀ famOf, StoredFamilies t R envT famOf → RecordsAgree E₀ R →
      (∃ E, StepCtx.{u} calls t R envT E₀ E) →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        Claim.TopWalk calls t seeds E₀ lim Top rank' ∧
        FamilyRun calls t envT E₀ lim Top rank' fam twin adv Inner ∧
        ∃ bAddr, InnerChecked calls bAddr t envT E₀ lim Top rank' fam twin Inner

/-- `FamilyGraphRowInner` gives `FamilyGraphRowInnerFam`: the new premises are not read. -/
theorem familyGraphRowInnerFam_of_row (h : FamilyGraphRowInner.{u}) :
    FamilyGraphRowInnerFam.{u} :=
  fun calls t seeds E₀ lim Top rank hW R envT hshape _ _ _ _ =>
    h calls t seeds E₀ lim Top rank hW R envT hshape

/-- **The typing half's premise at the witness with its stored families, from the rows**:
`familySteps_of_graphInner` with the graph row reading the map. -/
theorem familyStepsFam_of_graphInner {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (familyGraph : FamilyGraphRowInnerFam.{u}) (innerSteps : InnerStepsChecked.{u} L)
    (familyBlock : FamilyBlockRow.{u} L) (familyTwin : FamilyTwinRow.{u} L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (calls : List (Call F)) :
    FamilyStepsFam.{u} L calls (Claim.TopWalk calls) := by
  intro t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore
  obtain ⟨rank, fam, twin, adv, Inner, hWalk, hFR, bAddr, hIC⟩ :=
    familyGraph calls t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore
  exact ⟨rank, fam, twin, adv, Inner, hWalk, hFR.graph,
    topUnitSteps_family standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
      definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope hWalk hFR,
    innerSteps calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner bAddr hFR hIC,
    fun E => familyBlock calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR,
    fun E hctx A c B rb crb hW hc hlog htw hrb hcrb =>
      familyTwin calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c B
        rb crb hW hc hlog htw (Or.inl ⟨hrb, hcrb⟩),
    fun E hctx A c B hW hc hlog htw hnone => by
      obtain ⟨rb, crb, hst, hinst⟩ := hFR.storedTwin A B htw hnone
      exact unitStep_of_twin_stored hst
        (familyTwin calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c
          B rb crb hW hc hlog htw (Or.inr ⟨hnone, hst, hinst⟩))⟩

/-! ## The stored twins from the witness's map -/

/-- **The stored twins' field from the witness's map**: the block of each stored twin is a
stored modeled block of the witness's store, so the map selects its family record, stored whole
with its companions (`storedFamily_of_clause`). -/
theorem storedTwinField_of_block {K : FamRunCtx} {R : Ixon.Env}
    {famOf : _root_.Address → Option _root_.Address} (hSF : StoredFamilies K.t R K.envT famOf)
    (hblock : StoredTwinBlock K.t R K.envT K.fam K.twin) : StoredTwinField K := by
  intro rb' B htw hnone
  obtain ⟨cb, hB, hroute, hst⟩ := hblock rb' B htw hnone
  obtain ⟨rb, ms, crb, rs, flat, -, -, hstored, hinst⟩ := storedFamily_of_clause hSF hB hroute hst
  exact ⟨rb, crb, hstored, hinst⟩

/-- **A twin's block with no family record has its constant addresses stored**, when it is in
Lean's logic and the run routes it as modeled: it is a top-walked non-empty block of inductive
types with a family check, so an unstored constant address would make it a block the selector
gives a family record (`FamRunCtx.fam_of`). -/
theorem FamRunCtx.twinBlock_stored {K : FamRunCtx} {rb' B : _root_.Address}
    (h : K.twin rb' = some B) (hnone : K.fam B = none) (hroute : ModeledRouteAt K.calls B)
    (hlog : ∀ cb, recordOf K.E₀ B = some cb → InLogic cb) :
    ∀ cb x, recordOf K.E₀ B = some cb → ConstAddrOf B cb x → StoredAt K.t K.envT x := by
  intro cb x hcb hx
  refine Classical.byContradiction fun hns => ?_
  have hTB : K.Top B ∧ IndBlock K.E₀ B := by
    rcases FamRunCtx.twin_some h with ⟨-, -, -, -, -, hT, -, hI⟩ | ⟨-, hT, hI, -⟩
    · exact ⟨hT, hI⟩
    · exact ⟨hT, hI⟩
  have hFB : K.FamBlock B := ⟨hTB.1, hroute, hTB.2, ⟨cb, x, hcb, hx, hns⟩, hlog⟩
  obtain ⟨rb, hrb⟩ := FamRunCtx.fam_of hFB (FamRunCtx.twin_facts h).2.2.2
  rw [hnone] at hrb
  cases hrb

/-- **A top-walked twin's block is routed as modeled** (`FamRunCtx.TwinOf`). -/
theorem FamRunCtx.twinOf_route {K : FamRunCtx} {rb' B : _root_.Address} (h : K.TwinOf rb' B) :
    ModeledRouteAt K.calls B :=
  h.2.2.2.2.2.2.1

/-- **Every twin's block is routed as modeled**: a top-walked twin's by `FamRunCtx.TwinOf`, a
nested twin's by `check_const`'s `Rec` arm (`BatchGives.routed`). -/
theorem FamRunCtx.twin_routed {K : FamRunCtx} (hB : BatchGives K) {rb' B : _root_.Address}
    (h : K.twin rb' = some B) : ModeledRouteAt K.calls B := by
  rcases FamRunCtx.twin_some h with ht | hn
  · exact FamRunCtx.twinOf_route ht
  · exact hB.routed rb' B hn

/-- **What the selector gives a twin of a block with a family record**: the block's family record
is non-empty, and in the preferred form when the twin is (the selector takes a complete record
first, then one in the preferred form; a twin is a complete record of a family check of the
block). -/
theorem FamRunCtx.twin_canonical {K : FamRunCtx} {B rb rb' : _root_.Address}
    (hf : K.fam B = some rb) (ht : K.twin rb' = some B) :
    RecBlock K.E₀ rb ∧ (K.Pref B rb' → K.Pref B rb) := by
  obtain ⟨-, -, hrec, hpref⟩ := FamRunCtx.fam_some hf
  obtain ⟨hRB, -, -, hFC⟩ := FamRunCtx.twin_facts ht
  exact ⟨hrec ⟨rb', hFC, hRB⟩, fun hp => hpref ⟨rb', hFC, hRB, hp⟩⟩

/-- **What the stored twins' block fact reads of the witness**, of the block of a twin with no
family record. Proved at a walk with a step store (`storedTwinReads_of_walk`). That the run
routes the block as modeled and that it is in Lean's logic are the run's
(`FamRunCtx.twin_routed`, `BatchGives.inLogic`). -/
structure StoredTwinReads (K : FamRunCtx) (R : Ixon.Env) : Prop where
  /-- The witness's store holds the block: the address of the block's first member is stored by
  the witness's environment (`FamRunCtx.twinBlock_stored`), whose constant there is no pin and
  so a reading of the store's record at it (`TableShape.reading.provenance`); that record is the
  run's projection record, and the store is closed under a projection's block
  (`TableShape.usedClosed`). -/
  record : ∀ rb' B, K.twin rb' = some B → K.fam B = none → ∃ cb, recordOf R B = some cb
  /-- The witness's store routes the block as modeled: the run routes it as modeled
  (`FamRunCtx.twin_routed`), its dispatch on the block's first member answers the route of a
  step's store (`FamilyAlias.blockRoute_of_modeledRoute`), which is the route of the witness's
  store, used-closed and holding the block (`FamilyAlias.blockRoute_recordsFor`). -/
  route : ∀ rb' B, K.twin rb' = some B → K.fam B = none → Route.blockRoute R B = some true

/-- **The block of every stored twin is a stored modeled block of the witness's store**, from
the run's facts, the reads and the agreement of the two stores: the witness's record of the
block is the run's, whose constant addresses are stored (`FamRunCtx.twinBlock_stored`). -/
theorem storedTwinBlock_of_reads {K : FamRunCtx} {R : Ixon.Env} (hB : BatchGives K)
    (hagree : RecordsAgree K.E₀ R)
    (hr : StoredTwinReads K R) : StoredTwinBlock K.t R K.envT K.fam K.twin := by
  intro rb' B htw hnone
  obtain ⟨cb, hcb⟩ := hr.record rb' B htw hnone
  have hTB : IndBlock K.E₀ B := by
    rcases FamRunCtx.twin_some htw with ⟨-, -, -, -, -, -, -, hI⟩ | ⟨-, -, hI, -⟩
    · exact hI
    · exact hI
  obtain ⟨cb₀, ms, hcb₀, -, -, -⟩ := hTB
  have e : cb₀ = cb := hagree B cb₀ cb hcb₀ hcb
  rw [← e] at hcb
  exact ⟨cb₀, hcb, hr.route rb' B htw hnone,
    fun x hx => FamRunCtx.twinBlock_stored htw hnone (FamRunCtx.twin_routed hB htw)
      (hB.inLogic rb' B htw) cb₀ x hcb₀ hx⟩

/-! ## The reads of the stored twins' blocks, at a step store -/

set_option maxRecDepth 100000 in
/-- The names of the pinned basis constants are keys of basis roles. -/
private theorem pinned_names_basisRole (kind : Ix.Kernel.BasisKind) :
    ∀ n ∈ (kind.declsA (md := .anon)).map (·.name),
      n ∈ TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := by
  cases kind <;> decide +kernel

/-- **A record store for a witness's store is one for the basis store**: it decodes its records
and holds every committed prelude row, the basis store's records among them; the basis store
holds no blob. -/
theorem recordsFor_basisStore {R E : Ixon.Env} (h : RecordsFor R E) :
    RecordsFor StoreInhabit.basisStore E := by
  refine ⟨h.1, fun a c hc => ?_, fun x b hb => ?_, h.2.2.2⟩
  · obtain ⟨hrow, hd⟩ := ClosedFacts.committedPrelude_rows (a, c)
      (StoreInhabit.basisRows_sub _ (StoreInhabit.store_record_inv hc))
    obtain ⟨lc, hlc, hraw⟩ := h.2.2.2 _ hrow
    obtain ⟨c0, hget, hd0⟩ := h.1 a lc hlc
    rw [hraw, hd] at hd0
    have e : c = c0 := Except.ok.inj hd0
    rw [e]
    exact recordAt_of_get hlc hget
  · exact absurd hb (by simp [StoreInhabit.basisStore])

/-- **The witness's reads of the stored twins' blocks**, at a walk with a step store `E` (a
record store for the witness's store that holds the run's records and that the run is good for,
`StepCtx`). At the block `B` of a twin with no family record:

* the step store routes `B` as modeled: the walk checked the first member of the top-walked
  block, the check observed the dispatch on it, which answers the step store's route, and the
  run routes the block as modeled (`FamilyAlias.blockRoute_of_modeledRoute`);
* the witness's store holds `B`. Its environment stores the address of the block's first member
  (`FamRunCtx.twinBlock_stored`), where the run holds a projection record of `B`. The constant
  stored there is no pin: a pin's key is a basis role's, bound to a row of the basis store, which
  would then hold the projection record and its block `B`; the step store, holding the basis
  rows, would route `B` as the basis store does, and no block of the basis store routes as
  modeled (`Binding.blockRoute_basisStore_ne_true`). So the constant is a reading of the witness's
  record at the address (`TableShape.reading.provenance`), which is the run's projection record
  (`RecordsAgree`), and the witness's store is closed under a projection's block;
* the witness's store routes `B` as the step store does: it is used-closed and holds `B`
  (`FamilyAlias.blockRoute_recordsFor`). -/
theorem storedTwinReads_of_walk {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    (hagree : RecordsAgree K.E₀ R) (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E) :
    StoredTwinReads K R := by
  have hshape := hctx.shape
  have hcheck : K.t.check = .ok () := hW.check_ok
  have htwf : K.t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [hcheck]
    rfl
  have hroles : (K.t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup hcheck).1
  have hdecE : L1.EnvDecoded E := hctx.recordsFor.1
  have hrunE : ∀ a c, recordOf K.E₀ a = some c → recordOf E a = some c := fun a c h =>
    (recordOf_eq_recordAt_of_decoded hdecE a).trans (hctx.runRecord a c h)
  have hEb : RecordsFor StoreInhabit.basisStore E := recordsFor_basisStore hctx.recordsFor
  have key : ∀ rb' B, K.twin rb' = some B → K.fam B = none →
      Route.blockRoute E B = some true ∧ ∃ cb, recordOf R B = some cb := by
    intro rb' B htw hnone
    have hTB : K.Top B ∧ IndBlock K.E₀ B := by
      rcases FamRunCtx.twin_some htw with ⟨-, -, -, -, -, hT, -, hI⟩ | ⟨-, hT, hI, -⟩
      · exact ⟨hT, hI⟩
      · exact ⟨hT, hI⟩
    obtain ⟨hT, cb, ms, hcb, hms, hpos, hall⟩ := hTB
    have hroute : ModeledRouteAt K.calls B := FamRunCtx.twin_routed hB htw
    have hchk : (∃ ms, cb.info = .muts ms ∧
          ∀ k, k < ms.size → Claim.MemberCheckedLimAt K.calls K.bAddr K.t B ms k K.lim) ∨
        Claim.CheckedLimAt K.calls K.bAddr K.t B K.lim := by
      obtain ⟨c', hc', h⟩ := hW.checked B hT
      have e3 : c' = cb := Option.some.inj (hc'.symm.trans hcb)
      rw [e3] at h
      exact h
    have hm0 : Claim.MemberCheckedLimAt K.calls K.bAddr K.t B ms 0 K.lim :=
      Claim.membersChecked_of_block hW.runStore hcb hms hchk 0 hpos
    have hcanon₀ : L1.CanonicalHashCoverage K.E₀ K.calls := by
      intro bytes value hashed size exactRead
      obtain ⟨entry, stored, bytesEq, cached⟩ := hW.hashedStored bytes value hashed size
        (L1.deConstant_of_deConstantExact exactRead) exactRead
      refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
      rw [bytesEq]
      exact exactRead
    have hcanon : L1.CanonicalHashCoverage E K.calls :=
      Assembly.canonicalHashCoverage_frame hcanon₀ hdecE
        (fun a v h => hctx.runRecord a v ((hW.runStore.recordOf_eq_recordAt a).trans h))
    have hRE : Route.blockRoute E B = some true :=
      FamilyAlias.blockRoute_of_modeledRoute hW.runStore hctx.toStepStore hcanon hall hm0 hroute
    refine ⟨hRE, ?_⟩
    have hx : ConstAddrOf B cb (memberAddr B 0 ms[0]) := constAddr_member0 hms hpos
    obtain ⟨P, hP, -, hPo⟩ :=
      hG.block_record hT hcb hms (Array.getElem?_eq_getElem hpos) (Or.inl rfl)
    have hst : StoredAt K.t K.envT (memberAddr B 0 ms[0]) :=
      FamRunCtx.twinBlock_stored htw hnone hroute (hB.inLogic rb' B htw) cb _ hcb hx
    obtain ⟨ci, hfind⟩ := Option.isSome_iff_exists.mp (find_isSome_of_storedAt hst)
    have hname : ci.name = keyOf K.t (memberAddr B 0 ms[0]) :=
      Ix.Kernel.Semantics.Env.find?_name hfind
    obtain ⟨hclaimed, hna⟩ := seed_claimed hfind
    rcases hshape.reading.provenance ci hclaimed with ⟨tbl, htbl⟩ | ⟨kind, hci⟩ | ⟨a, hk⟩
    · rw [htbl] at hna
      exact absurd rfl (hna tbl.structName .projTable)
    · exfalso
      obtain ⟨r, hr, hrk⟩ : ∃ r ∈ TableInhabit.basisRoleOrder, ci.name = .role r := by
        obtain ⟨r, hr, he⟩ := List.mem_map.mp
          (pinned_names_basisRole kind ci.name (List.mem_map.mpr ⟨ci, hci, rfl⟩))
        exact ⟨r, hr, he.symm⟩
      have had : K.t.addressOf? r = some (memberAddr B 0 ms[0]) :=
        Core.addressOf_of_keyOf htwf (by rw [LoadedReads.keyOf_eq]; exact hname.symm.trans hrk)
      have hxb : (recordOf StoreInhabit.basisStore (memberAddr B 0 ms[0])).isSome = true := by
        have hrows := List.all_eq_true.mp basisRoles_rows r hr
        simp only [← Binding.addressOf_basis hshape.prelude hr, had] at hrows
        exact StoreInhabit.isSome_of_hasKey hrows
      obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp hxb
      have e : cx = P := Option.some.inj
        (((recordOf_eq_recordAt_of_decoded hdecE _).trans (hEb.2.1 _ cx hcx)).symm.trans
          (hrunE _ P hP))
      have hown := (StoreInhabit.store_usedClosed.1 _ cx hcx).1
      rw [e, hPo] at hown
      obtain ⟨cB, hcB⟩ := Option.isSome_iff_exists.mp hown
      rw [FamilyAlias.blockRoute_recordsFor StoreInhabit.store_usedClosed hEb hcB] at hRE
      exact Binding.blockRoute_basisStore_ne_true B hRE
    · have haa : a = memberAddr B 0 ms[0] :=
        keyOf_inj hroles ((keptIn_name hk).symm.trans hname)
      rw [haa] at hk
      obtain ⟨-, ci₀, hr, -⟩ := hk
      obtain ⟨c₀, hc₀, -⟩ := hr
      have e : P = c₀ := hagree _ P c₀ hP hc₀
      have hown := (hshape.usedClosed.1 _ c₀ hc₀).1
      rw [← e, hPo] at hown
      exact Option.isSome_iff_exists.mp hown
  refine ⟨fun rb' B htw hnone => (key rb' B htw hnone).2, fun rb' B htw hnone => ?_⟩
  obtain ⟨hRE, cb, hcb⟩ := key rb' B htw hnone
  rw [← FamilyAlias.blockRoute_recordsFor hshape.usedClosed hctx.recordsFor hcb]
  exact hRE

/-! ## What the graph row is owed at the witness with its stored families -/

/-- **A premise at every walk and every witness with its stored families**: `P` of the run's
choices, the witness's store and map, where the two stores agree and the run has a step store
for the witness (`StepCtx`; the typing half has one on the branch where the run hashed no
collision, `typing_skeleton_over_familyFam`). -/
def AtWalkFam (Pref : RunPref)
    (P : FamRunCtx → Ixon.Env → (_root_.Address → Option _root_.Address) →
      (_root_.Address → Nat) → Prop) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (seeds : List _root_.Address) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
    Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank → TopGraph t E₀ seeds Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∀ famOf, StoredFamilies t R envT famOf → RecordsAgree E₀ R →
      (∃ E, StepCtx.{u} calls t R envT E₀ E) →
      P ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ R famOf rank

/-- **What the graph row and the inner records are owed at the witness with its stored
families**, at the twin preference `Pref`: only the run's facts the graph reads (`BatchGives`).
Both `InnerOwed` (`innerOwed_of_walk`) and the stored twins' field (`storedTwinField_of_block` via
`storedTwinReads_of_walk`) are proved unconditionally at the walk. -/
def FamilyGraphInnerOwedFam (Pref : RunPref) : Prop :=
  AtWalkFam.{u} Pref fun K _ _ _ => BatchGives K

/-- **The graph row with the inner records at the witness with its stored families, from what
they are owed**: as `familyGraphRowInner_of_owed`, the stored twins' field from the map. -/
theorem familyGraphRowInnerFam_of_owed {Pref : RunPref} (h : FamilyGraphInnerOwedFam.{u} Pref) :
    FamilyGraphRowInnerFam.{u} := by
  intro calls t seeds E₀ lim Top rank hWalk R envT hshape famOf hSF hagree hstore
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  have hB :=
    h calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape famOf hSF hagree hstore
  obtain ⟨E, hctx⟩ := hstore
  have hreads : StoredTwinReads
      ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ R :=
    storedTwinReads_of_walk hW hG hB hagree hctx
  obtain ⟨rank', hR⟩ : ∃ rank',
      FamilyRanked ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ rank' :=
    ⟨_, familyRanked_of_edges hW
      (rankEdges_of hW hG hB hshape (FamRunCtx.famEdge_acyclic hW hG hB))⟩
  obtain ⟨hFR, -⟩ :=
    familyRun_of ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ hB hW
      (noBatchFields_of _ hW) hR
      (storedTwinField_of_block hSF (storedTwinBlock_of_reads hB hagree hreads))
  have hWalk' : Claim.TopWalk calls t seeds E₀ lim Top rank' :=
    topWalk_of_edges ⟨bAddr, hW, hG⟩ hR.closed hR.owner
  exact ⟨rank', _, _, _, _, hWalk', hFR, bAddr, innerChecked_of_gives hWalk' hFR
    (FamRunCtx.checks_of _ hB) (innerGives_of_owed hW hG hB hshape (innerOwed_of_walk hW))⟩

/-- **Row `familyGraph` with the inner records at the witness with its stored families, with what
the twin step reads of the run's choices**: `FamilyGraphRowInnerFam`'s conclusion at one binding
`bAddr` of the run, with the run's family checks at it (`FamilyChecksAt`), the block of every
twin with no family record in the graph a stored modeled block of the witness's store
(`StoredTwinBlock`), and, at a block with a family record and a twin, the record non-empty and in
the form `Pref` prefers when the twin is (the selector's choice, `FamRunCtx.twin_canonical`). -/
def FamilyGraphRowInnerFamT (Pref : RunPref) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∀ famOf, StoredFamilies t R envT famOf → RecordsAgree E₀ R →
      (∃ E, StepCtx.{u} calls t R envT E₀ E) →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop)
        (bAddr : _root_.Address),
        Claim.TopWalk calls t seeds E₀ lim Top rank' ∧
        FamilyRun calls t envT E₀ lim Top rank' fam twin adv Inner ∧
        InnerChecked calls bAddr t envT E₀ lim Top rank' fam twin Inner ∧
        FamilyChecksAt calls bAddr t E₀ lim fam twin adv Inner ∧
        StoredTwinBlock t R envT fam twin ∧
        ∀ B rb rb', fam B = some rb → twin rb' = some B →
          RecBlock E₀ rb ∧ (Pref calls bAddr t E₀ lim B rb' → Pref calls bAddr t E₀ lim B rb)

/-- **The graph row with its exports at the witness with its stored families, from what it is
owed**: as `familyGraphRowInnerFam_of_owed`, exporting the run's binding with its family checks
(`FamRunCtx.checks_of`), the stored twins' blocks (`storedTwinBlock_of_reads`) and the selector's
choice at a block with a twin (`FamRunCtx.twin_canonical`). -/
theorem familyGraphRowInnerFamT_of_owed {Pref : RunPref} (h : FamilyGraphInnerOwedFam.{u} Pref) :
    FamilyGraphRowInnerFamT.{u} Pref := by
  intro calls t seeds E₀ lim Top rank hWalk R envT hshape famOf hSF hagree hstore
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  have hB :=
    h calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape famOf hSF hagree hstore
  obtain ⟨E, hctx⟩ := hstore
  have hreads : StoredTwinReads
      ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ R :=
    storedTwinReads_of_walk hW hG hB hagree hctx
  obtain ⟨rank', hR⟩ : ∃ rank',
      FamilyRanked ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ rank' :=
    ⟨_, familyRanked_of_edges hW
      (rankEdges_of hW hG hB hshape (FamRunCtx.famEdge_acyclic hW hG hB))⟩
  have hblock := storedTwinBlock_of_reads hB hagree hreads
  obtain ⟨hFR, -⟩ :=
    familyRun_of ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ hB hW
      (noBatchFields_of _ hW) hR (storedTwinField_of_block hSF hblock)
  have hWalk' : Claim.TopWalk calls t seeds E₀ lim Top rank' :=
    topWalk_of_edges ⟨bAddr, hW, hG⟩ hR.closed hR.owner
  exact ⟨rank', _, _, _, _, bAddr, hWalk', hFR, innerChecked_of_gives hWalk' hFR
    (FamRunCtx.checks_of _ hB) (innerGives_of_owed hW hG hB hshape (innerOwed_of_walk hW)),
    FamRunCtx.checks_of _ hB, hblock, fun B rb rb' hf ht => FamRunCtx.twin_canonical hf ht⟩

/-! ## The public statement with the typing half at the witness with its stored families -/

/-- **The public statement from the open obligations, the typing half reading the witness's
stored families**: `circuitComposed_of_partsFamInner` with the typing half at `OverWFam L`
(`composed_skeleton_over_familyWFam`) and the graph row with the inner records reading the map
(`FamilyGraphRowInnerFam`). -/
theorem circuitComposed_of_partsFamInnerW
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : List (Call F) → BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOverW.{u} L (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupFamilies : ∀ calls, FamiliesChain (Run calls) (Fam calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) fun ρ t g =>
      ClosureStepOverFamilyW.{u} L ρ t g (Fam calls ρ t g))
    (groupWithoutRoleUnit : ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} L))
    (operationRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (familyGraph : FamilyGraphRowInnerFam.{u}) (innerSteps : InnerStepsChecked.{u} L)
    (familyBlock : FamilyBlockRow.{u} L) (familyTwin : FamilyTwinRow.{u} L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind) :
    CircuitComposed.{u} := by
  unfold CircuitComposed
  refine circuitSound_of_bounded l0 ?_
  intro dB valueB heapB callsB evB hbB
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  refine circuitSound_of_bounded l0 ?_
  intro dA valueA heapA callsA evA hbA
  show ComposedSpec.{u} callsA callsB dA dB
  exact composed_skeleton_over_familyWFam (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupFamilies callsB) (groupClosure callsB) (groupWithoutRoleUnit callsB)
    (operationRoleUnit callsB) (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familyStepsFam_of_graphInner familyGraph innerSteps familyBlock familyTwin
      standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor definitionBlock
      nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope callsA)

/-! ## The twin row's stored case at the witness's selected record -/

/-- **Every witness's selected family records are in the form `RFormS`**. `RFormS t R B rb` is
the twin seam's record-level form over the witness's store (the reconstruction's own type at every
member of the record `rb` of the block `B`). At the concrete form `FamilyRecon.RFormS` it is a
theorem (`storedFormAt_recon`): the stored families carry it (`StoredFamilies.form`). -/
def StoredFormAt (RFormS : StoredFormPred) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (famOf : _root_.Address → Option _root_.Address),
    TableShape.{u} t (fun _ => True) R envT → StoredFamilies t R envT famOf →
    StoredFamiliesRForm RFormS t R famOf

/-- **The selected records of every witness are in the reconstruction's form**: the stored
families carry it (`StoredFamilies.form`), from the binding run's family check of each selected
record under its group's validation (`GroupFamilyChecks.familyForm`), kept by the binding fold
(`FamilyWitnessForm`). -/
theorem storedFormAt_recon : StoredFormAt.{u} FamilyRecon.RFormS :=
  fun _ _ _ _ _ hSF => hSF.form

/-- **The typing half's premise at the witness with its stored families, the twin row's stored
case at the witness's selected record**: as `familyStepsFam_of_graphInner`, the twin conjunct
from the restated row at the graph's family record (`TwinFamily.familyTwinStep_graph_of_row`), the
stored conjunct from the restated row at the witness's selected record
(`TwinFamily.storedTwinSteps_of`), with the selected records' flattened families
(`StoredFamilies.flat`), their form (`StoredFormAt`) and the stored twins' blocks the graph row
exports. -/
theorem familyStepsFam_of_graphInnerT {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred}
    (familyGraph : FamilyGraphRowInnerFamT.{u} (fun _ _ t E₀ _ B r => RFormS t E₀ B r))
    (storedForm : StoredFormAt.{u} RFormS)
    (innerSteps : InnerStepsChecked.{u} L) (familyBlock : FamilyBlockRow.{u} L)
    (familyTwin : TwinFamily.FamilyTwinRowFam.{u} RFormS L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (calls : List (Call F)) :
    FamilyStepsFam.{u} L calls (Claim.TopWalk calls) := by
  intro t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore
  obtain ⟨rank, fam, twin, adv, Inner, bAddr, hWalk, hFR, hIC, -, hblock, htwin_canon⟩ :=
    familyGraph calls t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore
  exact ⟨rank, fam, twin, adv, Inner, hWalk, hFR.graph,
    topUnitSteps_family standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
      definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope hWalk hFR,
    innerSteps calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner bAddr hFR hIC,
    fun E => familyBlock calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR,
    fun E hctx A c B rb crb hW hc hlog htw hrb hcrb =>
      TwinFamily.familyTwinStep_graph_of_row familyTwin hWalk hFR hctx hW hc hlog htw hrb hcrb
        (htwin_canon B rb A hrb htw).1 (htwin_canon B rb A hrb htw).2,
    TwinFamily.storedTwinSteps_of (TwinFamily.storedTwinStepFam_of_row familyTwin) hWalk hFR
      ⟨famOf, hSF, hSF.flat, storedForm t R envT famOf hshape hSF⟩ hblock⟩

/-- **The public statement with the twin row's stored case at the witness's selected record**:
`circuitComposed_of_partsFamInnerW` with the graph row exporting the stored twins' blocks
(`FamilyGraphRowInnerFamT`), the selected records' form (`StoredFormAt`) and the restated twin row
(`TwinFamily.FamilyTwinRowFam`) in place of `FamilyTwinRow`. -/
theorem circuitComposed_of_partsFamInnerWT
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : List (Call F) → BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {RFormS : StoredFormPred}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOverW.{u} L (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupFamilies : ∀ calls, FamiliesChain (Run calls) (Fam calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) fun ρ t g =>
      ClosureStepOverFamilyW.{u} L ρ t g (Fam calls ρ t g))
    (groupWithoutRoleUnit : ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} L))
    (operationRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (familyGraph : FamilyGraphRowInnerFamT.{u} (fun _ _ t E₀ _ B r => RFormS t E₀ B r))
    (storedForm : StoredFormAt.{u} RFormS)
    (innerSteps : InnerStepsChecked.{u} L) (familyBlock : FamilyBlockRow.{u} L)
    (familyTwin : TwinFamily.FamilyTwinRowFam.{u} RFormS L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind) :
    CircuitComposed.{u} := by
  unfold CircuitComposed
  refine circuitSound_of_bounded l0 ?_
  intro dB valueB heapB callsB evB hbB
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  refine circuitSound_of_bounded l0 ?_
  intro dA valueA heapA callsA evA hbA
  show ComposedSpec.{u} callsA callsB dA dB
  exact composed_skeleton_over_familyWFam (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupFamilies callsB) (groupClosure callsB) (groupWithoutRoleUnit callsB)
    (operationRoleUnit callsB) (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familyStepsFam_of_graphInnerT familyGraph storedForm innerSteps familyBlock familyTwin
      standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor definitionBlock
      nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope callsA)

end IxVM.Refinement.Typing
