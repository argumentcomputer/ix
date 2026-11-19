import IxVMRefinement.Endpoint.WalkedKindSteps
import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.Assembly.NativeBlockWalked
import IxVMRefinement.Binding.TableAdmits
import IxVMRefinement.Binding.TableAdmitsValidate
import IxVMRefinement.Binding.AxiomValidation
import IxVMRefinement.Binding.GroupStores
import IxVMRefinement.FamilyAlias.BlockRowCheck
import IxVMRefinement.FamilyGraph.CompositionFam
import IxVMRefinement.Binding.RoleUnitW
import IxVMRefinement.Binding.BasisWalked
import IxVMRefinement.Binding.ClosureFamilyRun
import IxVMRefinement.Binding.ClosureUnitDispatch
import IxVMRefinement.FamilyGraph.ProducersAcyclic
import IxVMRefinement.FamilyGraph.ProducersInner
import IxVMRefinement.Binding.OpCertObs
import IxVMRefinement.FamilyAlias.ClosureFamilyStep
import IxVMRefinement.FamilyAlias.FamilyCall
import IxVMRefinement.Binding.CertProjFreeRun
import IxVMRefinement.Binding.ShapeIffNonemptyPins
import IxVMRefinement.FamilyGraph.ProducersStoredFam

/-! # The composed statement from its open obligations

`circuitComposed_residual` proves the public statement `IxVM.Consistency.CircuitComposed` from
named hypotheses, one for each obligation of the proof that has no unconditional theorem yet.
It claims nothing by itself: a hypothesis is typed by the interface its obligation has today,
whether or not that interface can be met. It fixes how the parts compose, and what is left.
A hypothesis is deleted when a theorem produces it. Its statement is printed in
`IxVMRefinement.Endpoint.ComposedResidualAudit`, which fails to build when the statement
changes.

The chain. `CircuitComposed` is the circuit statement, nested, of `ComposedSpec` for the calls
of two observed derivations. For every pair of bounded source derivations `ComposedSpec` is
`composed_skeleton_over_familyW`: the binding half and the typing half at one internal part
`OverWFam L` (the boundary facts and the fold's clause `FoldClauseWith L` at every record store,
with one registry, and one stored family map, `StoredFamilies`), joined by `binding_discharge`.
The binding half is the fold over the 77 groups in its family form (`binding_skeleton_overW`):
its invariant carries, beside the boundary invariant, the records the run checked stored
(`WalkedStored`) and the family map; a group's closure installs its modeled blocks with their
family records. The typing half is the fold over the family graph
(`typing_skeleton_over_family`), which reads the `OverW L` part of the witness for now: a block
the run routes as modeled is stepped together
with its family record, a second family record of a block (a twin) is a unit of its own, the
records a family check checks are units, and every other top-walked unit has a plain step. Its
premise is `FamilySteps`: the graph and those four kinds of step at every walk and witness. The
circuit statement follows through `L0`, once for each derivation (`circuitSound_of_bounded`,
`l0`). `L` is the link between a registered family's stored former and its telescope constant;
a typing step keeps the part of the clause beside the prefix invariant (`FoldExtra L`), and the
family block's and the twin's steps keep the family recursors' model companions beside it
(`TwinFamily.FamilyRecsModeled`). `circuitComposed_of_partsFam` is the composition for any link;
`circuitComposed_residual` is its instance at the opened head trace `FormerOpenTraceAt`, less
what is proved there. (`circuitComposed_of_parts` is the same composition with the binding half
without its family form, `binding_skeleton_over`.)

Proved inside, with no hypothesis left:

* the circuit-to-source step (`l0`), at both derivations;
* the typing claim's export, the walk's limit and the assembly's reading of the walk
  (`Claim.claimPhase_typing`, `TopWalkCore.topLim`, `Claim.TopWalk.graph`);
* the typing half's premise from its parts (`familySteps_of_graphInner`), and in it the step of every
  top-walked unit that has no family record and is no twin from the kinds of the plain fold
  (`topUnitSteps_family`): what every unit's step reads of the walk, the case split of a unit by
  the form of its record, and the two cases that do not arise there: a block of one inductive
  type off the native route and a block of two or more inductive types are on the modeled route,
  so they have a family record, and a non-empty block of recursors that no block claims is a
  twin;
* the steps of the proved kinds, at either limit (`IxVMRefinement.Endpoint.WalkedKindSteps` and
  the modules it imports): a standalone definition, a standalone theorem or opaque record, a
  block of definitions (the empty block inside `definitionBlock_of_nonempty`), a standalone
  recursor (`standaloneRecursor_of_freshNotBasis`, with `freshRecursorMajorNotBasis_walked`), a
  block of one inductive type on the native route whose former is declared at a definition
  (`nativeBlockAlias_walked`), and one whose former reads as a telescope of another length,
  which the circuit refuses (`nativeBlockOtherTelescope_step`); and, from the use-site reading
  of the projection guard alone, one whose former is declared at its telescope (the ordinary
  inductive type), for every checked unit (`nativeBlockTelescope_checked`) and every top-walked
  one (`nativeBlockTelescope_walked`);
* the step of a record checked inside a family check, by the step of its kind
  (`innerStepsChecked_of_kinds`, at the graph producer's choices): each proved kind is
  stated once for every checked unit;
* on the binding side, everything `binding_skeleton_overW` proves from its named hypotheses: the
  fold over the 77 groups with the walked records stored and the stored family map, the step of
  a group from its parts (at a group with no role unit the map and the walked records pass by
  store congruence), the raise past a group, the table's well-formedness from the claim's
  admission, and the witness with its stored families on every group;
* the invariant with its family form at the six basis groups (`Binding.basisOverW_bindingRun`:
  the walked records stored at the pinned keys; no basis block routes as modeled, so the family
  map is empty);
* the closure of a group in the family form from its three steps
  (`Binding.groupClosureFamily_of_steps`, through the closure fold `closureFoldStatement`), with
  the run's family checks of each group (`BindingRun.families`);
* the first of those steps, of a new unit with no family record that is no twin, at every group
  of every run (`Binding.closureUnitSteps_bindingRun`): a case split over the unit's kind onto
  the proved steps of the kinds, with what it reads of the unit's references among the run's
  facts at the group (`Binding.ClosureRunFacts.notInert`, `.needOk`, `.literals`, inside
  `groupStores`);
* of the binding claim's export (`Binding.bindingClaimExport_of_table_and_stores`): the
  claim's decode (an accepted `binding` claim's run calls the binding's validation on the
  claimed address, `Claim.verify_claim_decode_binding_spec`), the loaded table's admission and
  its prelude pin (`Binding.loadedTableAdmits`, `Binding.loadedTablePinsPrelude`), that the
  table binds every role, the observed validation of every role of every group, and the run's
  store;
* the stored shapes of every group with no role unit (`Binding.groupWithoutRoleUnit_bindingRun`),
  the role unit of a well-founded operation (`Binding.operationRoleUnitW_of_projFree` from
  `Binding.certProjFree_bindingRun`), and the role unit of a standard axiom at each group of a run,
  in the family form (`Binding.standardAxiomRoleUnitW_closed`, from the axiom's observed validation,
  `Binding.axiomValidationFacts`).

Left as hypotheses, at the binding claim layer's run predicate `Binding.BindingRun` (the run
record is the observed one, `observedRun`; the predicate holds the table's prelude pin, the
store after the six basis groups, the admission of each group with its reading clause and the
group's family checks, so the invariant at the basis groups, the two admission chains and the
families are its projections):

* binding: the part of the claim's export that remains, what is left of the clauses of the
  stores of a run and of its family checks (`RemainingStoreClausesOfRun`), and at each group of
  a run the closure's remaining step (a twin);
* typing: what an accepted run's family records, advice, twins and the records a family check
  checks are owed at the run's choices (`FamilyGraphInnerOwed`, from which `FamilyGraphRow` and
  the inner checks at the same choices are proved); what one accepted family check gives
  (`FamilyAlias.FamilyCallRow`, serving both halves) and the step of a twin (`FamilyTwinRow`).

The typing half takes nothing from the binding half but the table witness at `OverWFam L`, so
no further hypothesis joins the two.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Endpoint

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The units a family check checks -/

/-- **The step of every record checked inside a family check, at the opened head trace**, from
what the run gives of those records (`InnerCheckedRow`) and the step of every checked block of
one inductive type on the native route whose former is declared at its telescope: the premise
of `familySteps_of_parts` for those units. The other kinds' steps are proved for every checked
unit (`innerUnitSteps_of_kinds`). -/
theorem innerUnitSteps_of_innerChecked (innerChecked : InnerCheckedRow)
    (nativeBlockTelescope :
      CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind) :
    ∀ (calls : List (Call F)) t seeds E₀ lim Top rank,
      Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
        (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
        ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim A c := by
  intro calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR
  obtain ⟨bAddr, hIC⟩ :=
    innerChecked calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR
  obtain ⟨bAddrW, hW, hG⟩ := hWalk
  exact innerUnitSteps_of_kinds nativeBlockTelescope hG hFR.graph hIC hW.check_ok hW.runStore
    hW.hashedStored

/-! ## The composed statement -/

/-- **The public statement from the parts of the two halves, for any link.** `L` is the link
of the fold's clause and `Run` the binding claim layer's run predicate, by the run's calls. The
first eight hypotheses are the binding half's, those of `binding_skeleton_over` for every
bounded run: the claim export with the observed run record; the invariant at the six basis
groups; the admission of each group and its reading clause; and at each group from 6 to 76 of
a run the closure, the stored shapes where the group has no role unit, the role unit of an
operation and the role unit of a standard axiom. The other eleven are the typing half's, those
of `familySteps_of_parts`: the run's family graph; the step of every record a family check
checks; the step of a top-walked block with its family record and the step of a twin; and the
step of a top-walked unit of each kind of the plain fold. -/
theorem circuitComposed_of_parts
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOver.{u} L (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) (ClosureStepOver.{u} L))
    (groupWithoutRoleUnit : ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} L))
    (operationRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOver.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOver.{u} (· ∈ standardAxioms) L))
    (familyGraph : FamilyGraphRow.{u})
    (innerSteps : ∀ (calls : List (Call F)) t seeds E₀ lim Top rank,
      Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
        (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
        ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c)
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
  exact composed_skeleton_over_family (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupClosure callsB) (groupWithoutRoleUnit callsB) (operationRoleUnit callsB)
    (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familySteps_of_parts familyGraph innerSteps familyBlock familyTwin standaloneDefinition
      standaloneTheoremOrOpaque standaloneRecursor definitionBlock nativeBlockTelescope
      nativeBlockAlias nativeBlockOtherTelescope callsA)

/-- **The public statement from the parts of the two halves with the binding half's family form,
for any link.** As `circuitComposed_of_parts`, with the binding half's hypotheses those of
`Binding.binding_skeleton_overW` for every bounded run: the invariant at the six basis groups
with the walked records stored and a stored family map (`BasisOverW`); at each group a family
selection with the run's family checks `Fam` and their store side (`FamiliesChain`); the closure
in the family form (`ClosureStepOverFamilyW`, with the run's family checks of the group); and the
role units of an operation and of a standard axiom keeping the walked records and the map
(`RoleUnitStepOverW`). The two halves meet at the witness with its stored families
(`composed_skeleton_over_familyW`). -/
theorem circuitComposed_of_partsFam
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
    (familyGraph : FamilyGraphRow.{u})
    (innerSteps : ∀ (calls : List (Call F)) t seeds E₀ lim Top rank,
      Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
        (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
        ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c)
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
  exact composed_skeleton_over_familyW (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupFamilies callsB) (groupClosure callsB) (groupWithoutRoleUnit callsB)
    (operationRoleUnit callsB) (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familySteps_of_parts familyGraph innerSteps familyBlock familyTwin standaloneDefinition
      standaloneTheoremOrOpaque standaloneRecursor definitionBlock nativeBlockTelescope
      nativeBlockAlias nativeBlockOtherTelescope callsA)

/-- **The public statement from the open obligations** (module docstring):
`circuitComposed_of_partsFam` at the opened head trace `FormerOpenTraceAt`, with the steps that
are proved passed in. The binding claim layer's run predicate is `Binding.BindingRun`, by the
run's calls, and the run's family checks of a group are `Binding.ClosureFam`.

The first two hypotheses are the binding half's. One is the part of the claim's export that
remains (`Binding.bindingClaimExport_of_table_and_stores`; the claim's decode is proved,
`Claim.verify_claim_decode_binding_spec`, and so are the other two parts: that the table a
binding run loads is the admitted table of bytes the run hashed, `Binding.loadedTableAdmits`,
and that such a table binding every role pins the prelude, `Binding.loadedTablePinsPrelude`):
the stores of a run, with every clause of each group's admission but the observed validation
of its roles, reduced to what is left of their clauses over the run's records
(`groupStores`, `Binding.RemainingStoreClausesOfRun`: the operation-order scan's facts
`blockSteps` and `payloadOps`, from which the clauses `opsOwn` and `unitsLast` are proved,
`Binding.groupStore_opsOwn` and `Binding.groupStore_unitsLast`; the store
sequence and every other clause are proved, `Binding.groupStoresOfRun_of_remaining`, among them
the safety of the roots, `Binding.rootsAndTheoremsSafe_of_run`, and the reading clause,
`Binding.groupStore_reads`; with them the family clauses of each group's store and checks,
`Binding.RemainingFamilyClauses`, among them the run's facts at each group,
`Binding.ClosureRunFacts`, with what the closure's unit step reads of a unit's references: none
is an inert axiom's, each is one a step needs stored, and a one-inductive block's member key is
no literal function's). The invariant at the six basis groups with its family form is
proved (`Binding.basisOverW_bindingRun`); the two admission chains and the families of each
group are projections of the run predicate (`admitsChain_bindingRun`,
`admitsReadsChain_bindingRun`, `BindingRun.families`). The other is, for every bounded run
and each group from 6 to 76 of it:
* one of the closure's three steps, which give the closure in the family form
  (`Binding.groupClosureFamily_of_steps`): `closureTwinSteps`, the step of a new second family
  record (`Binding.ClosureTwinSteps`; open, after the circuit's family changes). The step of a
  new unit with no family record that is no twin is proved from the run
  (`Binding.closureUnitSteps_bindingRun`). The step of a new block with its selected family
  record, `Binding.ClosureFamilySteps`, is proved from the hypothesis `familyCall` below: the
  family check's facts at the closure (`FamilyAlias.closureFamilyCheck_of_call`: the family as
  read with the facts of its check, the selected annotated types and right-hand sides as the
  circuit loads them, and the companion facts of each recursor at its selected type, at a record
  store the run is good for; each of the family record's references covered at the group's
  validation limit, so stored by the table's shape, or needed), then the step
  (`FamilyAlias.closureFamilySteps_of_checkRow`: the step taken once at that store and the
  group's validation limit, the fold's clause kept with the same registry at every record store
  for the closure's store, the block's references from the run's facts
  `Binding.ClosureRunFacts.famNotInert`, `.famNeedOk`).

The stored shapes where a group has no role unit are proved for every group
(`Binding.groupWithoutRoleUnit_bindingRun`, joining the validated `Iff` and `Nonempty` member pins
in groups 16 and 17 to `Binding.groupWithoutRoleUnit_of_iffNonempty`). The role unit of an
operation is proved in the family form
(`Binding.operationRoleUnitW_of_projFree`, `Binding.RoleUnitStepOverW`: handed the closure's
store, the walked records stored there and the stored family map, it keeps both), through the
operations' certificate facts (`Binding.opCertFacts_of_projFree`), from
`Binding.certProjFree_bindingRun`: no certificate of a well-founded operation projects the
operation (`Binding.CertProjFree`), since `KernelSubst::subst_const`'s projection arm refuses a
projection whose structure is the operation it replaces (`Binding.subst_const_proj_ne`, through
`Binding.certProjFree_of_subst`). The role unit of a standard axiom is proved in that form
(`Binding.standardAxiomRoleUnitW_closed`, from the axiom's observed validation,
`Binding.axiomValidationFacts`).

The last three hypotheses are the typing half's; the second of them, `familyCall`, also gives the
binding half's closure step of a new block with its family record (above). Before them, `Pref`
is a parameter, not an
obligation (a relation, not a proposition): the twin preference, which the typing side
instantiates with the concrete record-level form once that form is defined. The step of the
ordinary inductive type takes the use-site reading of the projection guard, a theorem
(`Core.projGuardRunReading`).

* `familyGraph`: what the run's family graph and the records its family checks check are owed
  at the twin preference `Pref` (`Typing.FamilyGraphInnerOwedFam`): at every walk of an accepted
  typing claim and every witness of the table's shape, at the run's choices, the facts the
  circuit's functions give (`Typing.BatchGives`, the reference facts the ranking reads among
  them), the witness's reads of a stored twin's canonical record (`Typing.StoredTwinReads`: the
  stored twin's block is the one the binding side's stored family map selects), and what is owed
  of the records a
  family check checks (`Typing.InnerOwed`: no inert used reference, a covered or in-logic used
  reference, and no address listed twice by a family check's own advice walk). The obligation
  holds at any `Pref`, since it reads it only through the selector's choice of the family
  records and the twins. Proved from it (`Typing.familyGraphRowInnerFamT_of_owed`), at one
  binding with its family checks, the stored twins' blocks and the selected canonical record's
  completeness with the preference carried to it: the row
  `FamilyGraphRow`, in which the run's family records, advice, inner records and twins form a
  family graph where every top-walked non-empty block of recursors is a family record or a
  twin, every top-walked block on the modeled route has a family record, and each family record
  and twin had its family check at the walk's limit (`FamilyRun`); and, at the same choices,
  each record a family check checks was checked at the walk's limit, uses no inert axiom's
  reference, uses only references the witness's environment stores, that are covered, or that a
  checked record of smaller rank owns, and when it is a block no block claims and no twin, it is
  empty, a block of definitions or one inductive type on the native route (`InnerChecked`); its
  uses of its own constant addresses are proved from the walk and the family check's reference
  facts (`Typing.FamRunCtx.inner_ownRef`). The choices, the graph, the ranking with its
  acyclicity, and the facts of the functions that the circuit's family changes leave alone are
  proved. Producer open: the fields read off the circuit's functions as the family changes leave
  them, the witness's reads of the stored twins' records, the inner records'
  inert and in-logic facts from the assertion on the used references of the records a family
  check checks (`assert_inner_refs_safe`), and the advice walk's refusal of a listed address seen
  before, read through the set lookup.
* `familyCall`: what one accepted family check gives (`FamilyAlias.FamilyCallRow`): at every
  family check of a block with its family record on the modeled route, one selection, fixed by
  the check (the family as read, the advice, the selected annotated types and right-hand sides),
  with the selected forms as the check loads them (`FamilyAlias.FamilyTysCanon`), the major
  premises' heads among the family record's references, each reference of the family record
  covered at the check's limit or needed, and at every environment a step is handed, the family
  as read, the facts of the check (`Decl.FamilyAlias.FamilyCheckFacts`, kernel-checked at two
  compiled fixtures) and the companion facts of each recursor at its selected type over the
  check's store. Both family steps are theorems from it, with the companion facts carried from
  the check's store to every store the steps read (`FamilyAlias.famRecsCompanion_carry`): the
  closure's step of a new block with its selected family record (above), and the row's step of
  a top-walked block with a family record, an empty one included
  (`FamilyAlias.familyBlockCheckRow_of_call`, then `FamilyAlias.familyBlockRow_of_check`). The
  row (`FamilyBlockRow`: the step installs the block with its family record and keeps the fold's
  clause with the family recursors' companions beside it, `UnitStepFamily`) has proved: the
  block's record, the route fact at the block, the claim of the recursors, key freedom, the
  pinned equality, the keeping of the clause, all fourteen load facts and the companion facts at
  the step's new constants at the installation of the selected forms
  (`FamilyAlias.familyMembersCanon_of_tys`, `FamilyAlias.recCompanionFacts_of_tys`), and the
  block's own used references stored (from the walk's facts, `FamilyAlias.famUsedStored`, and
  for a covered one from the table's shape, `FamilyAlias.coveredAt_stored`). Producer: the
  circuit side, from the observed family check, after the circuit's family changes; the typing
  judgements of `Decl.FamilyAlias.FamilyCheckFacts` need the registry's judgements carried
  through the check's renaming (open).
* `familyTwin`: the step of a second family record of a block (a twin), handed the block's
  family record stored, installs it and keeps the fold's clause with the family recursors'
  companions beside it, at the concrete record form (`TwinFamily.FamilyTwinRowFam` at
  `Binding.FamilyRecon.RFormS`: every recursor's type is the circuit's reconstruction at its
  position and every rule follows the reconstructed body, both read canonically). In the stored
  case the canonical record is the one the binding side's stored family map selects, with its
  flattened family derived from the block and its form; that every selected record has the form
  is a theorem (`Typing.storedFormAt_recon`). Stated; one accepted pair was executed. Producer
  open: the step from `TwinFamily.TwinStepTarget` through `TwinFamily.familyInstalled_of_clause`,
  the target from `Decl.FamilyAlias.FamilyCheckFacts`, and the twin's comparison with the
  canonical record (its type part is `Binding.FamilyRecon.wrapRel_of_recon`). -/
theorem circuitComposed_residual
    (groupStores : ∀ calls, RemainingStoreClausesOfRun calls)
    (closureTwinSteps :
      ∀ calls, AtGroups (BindingRun calls) (ClosureTwinSteps.{u} FormerOpenTraceAt calls))
    (Pref : RunPref)
    (familyGraph : FamilyGraphInnerOwedFam.{u} Pref)
    (familyCall : FamilyAlias.FamilyCallRow.{u} FormerOpenTraceAt)
    (familyTwin : TwinFamily.FamilyTwinRowFam.{u} FamilyRecon.RFormS FormerOpenTraceAt) :
    CircuitComposed.{u} :=
  circuitComposed_of_partsFamInnerWT (Run := BindingRun) (Fam := ClosureFam)
    (bindingClaimExport_of_table_and_stores Binding.loadedTableAdmits
      Binding.loadedTablePinsPrelude fun calls => groupStoresOfRun_of_remaining (groupStores calls))
    (fun calls => basisOverW_bindingRun FormerOpenTraceAt calls) admitsChain_bindingRun
    admitsReadsChain_bindingRun (fun _ _ _ _ h => h.families)
    (groupClosureFamily_of_steps Binding.closureUnitSteps_bindingRun
      (FamilyAlias.closureFamilySteps_of_checkRow
        (FamilyAlias.closureFamilyCheck_of_call familyCall)) closureTwinSteps)
    Binding.groupWithoutRoleUnit_bindingRun.{u}
    (Binding.operationRoleUnitW_of_projFree.{u} Binding.certProjFree_bindingRun)
    Binding.standardAxiomRoleUnitW_closed
    (familyGraphRowInnerFamT_of_owed familyGraph) storedFormAt_recon
    (innerStepsChecked_of_kinds
      (nativeBlockTelescope_checked linkLaws_formerOpenTrace Core.projGuardRunReading))
    (FamilyAlias.familyBlockRow_of_check linkLaws_formerOpenTrace
      (FamilyAlias.familyBlockCheckRow_of_call familyCall)) familyTwin
    (standaloneDefinition_foldExtra linkLaws_formerOpenTrace)
    (standaloneTheoremOrOpaque_foldExtra linkLaws_formerOpenTrace)
    (standaloneRecursor_of_freshNotBasis freshRecursorMajorNotBasis_walked)
    (definitionBlock_of_nonempty (definitionBlock_foldExtra linkLaws_formerOpenTrace))
    (nativeBlockTelescope_walked linkLaws_formerOpenTrace Core.projGuardRunReading)
    nativeBlockAlias_walked
    nativeBlockOtherTelescope_step

end IxVM.Refinement.Endpoint
