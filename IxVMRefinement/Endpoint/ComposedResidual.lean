import IxVMRefinement.Endpoint.WalkedKindSteps
import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.Assembly.NativeBlockWalked
import IxVMRefinement.Binding.TableAdmits
import IxVMRefinement.Binding.TableAdmitsValidate

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
`composed_skeleton_over_family`: the binding half and the typing half at one internal part
`OverW L` (the boundary facts and the fold's clause `FoldClauseWith L` at every record store,
with one registry), joined by `binding_discharge`. The typing half is the fold over the family
graph (`typing_skeleton_over_family`): a block the run routes as modeled is stepped together
with its family record, a second family record of a block (a twin) is a unit of its own, the
records a family check checks are units, and every other top-walked unit has a plain step. Its
premise is `FamilySteps`: the graph and those four kinds of step at every walk and witness. The
circuit statement follows through `L0`, once for each derivation (`circuitSound_of_bounded`,
`l0`). `L` is the link between a registered family's stored former and its telescope constant;
a typing step keeps the part of the clause beside the prefix invariant (`FoldExtra L`), and the
family block's and the twin's steps keep the family recursors' model companions beside it
(`TwinFamily.FamilyRecsModeled`). `circuitComposed_of_parts` is the composition for any link;
`circuitComposed_residual` is its instance at the opened head trace `FormerOpenTraceAt`, less
what is proved there.

Proved inside, with no hypothesis left:

* the circuit-to-source step (`l0`), at both derivations;
* the typing claim's export, the walk's limit and the assembly's reading of the walk
  (`Claim.claimPhase_typing`, `TopWalkCore.topLim`, `Claim.TopWalk.graph`);
* the typing half's premise from its parts (`familySteps_of_parts`), and in it the step of every
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
  (`innerUnitSteps_of_innerChecked`, through `innerUnitSteps_of_kinds`): each proved kind is
  stated once for every checked unit;
* on the binding side, everything `binding_skeleton_over` proves from its named hypotheses: the
  fold over the 77 groups, the step of a group from its parts, the raise past a group, the
  table's well-formedness from the claim's admission, and the witness on every group;
* of the binding claim's export (`Binding.bindingClaimExport_of_table_and_stores`): the
  claim's decode (an accepted `binding` claim's run calls the binding's validation on the
  claimed address, `Claim.verify_claim_decode_binding_spec`), that the table binds every role,
  the observed validation of every role of every group, and the run's store.

Left as hypotheses, at the binding claim layer's run predicate `Binding.BindingRun` (the run
record is the observed one, `observedRun`; the predicate holds the table's prelude pin, the
store after the six basis groups and the admission of each group with its reading clause, so
the invariant at the basis groups and the two admission chains are its projections):

* binding: the three parts of the claim's export that remain (the loaded table's admission,
  its prelude pin, and the stores of a run; the claim's decode is proved); and at each group of
  a run the closure, the stored shapes where the group has no role unit, and the role unit of
  an operation and of a standard axiom;
* typing: what an accepted run gives of its family records, advice and twins
  (`FamilyGraphRow`) and of the records a family check checks (`InnerCheckedRow`); the step of a top-walked block with its
  family record (`FamilyBlockRow`) and the step of a twin (`FamilyTwinRow`).

The typing half takes nothing from the binding half but the table witness at `OverW L`, so no
further hypothesis joins the two.
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

/-- **The public statement from the open obligations** (module docstring):
`circuitComposed_of_parts` at the opened head trace `FormerOpenTraceAt`, with the steps that
are proved passed in. The binding claim layer's run predicate is `Binding.BindingRun`, by the
run's calls.

The first five hypotheses are the binding half's. One is the part of the claim's export that
remains (`Binding.bindingClaimExport_of_table_and_stores`; the claim's decode is proved,
`Claim.verify_claim_decode_binding_spec`, and so are the other two parts: that the table a
binding run loads is the admitted table of bytes the run hashed, `Binding.loadedTableAdmits`,
and that such a table binding every role pins the prelude, `Binding.loadedTablePinsPrelude`):
the stores of a run, with every clause of each group's admission but the observed validation
of its roles (`groupStores`). The invariant at the six basis groups
and the two admission chains are projections of the run predicate (`basisOver_bindingRun`,
`admitsChain_bindingRun`, `admitsReadsChain_bindingRun`). The other four are, for every bounded
run and each group from 6 to 76 of it, the closure, the stored shapes where the group has no
role unit, the role unit of an operation and the role unit of a standard axiom.

The last four hypotheses are the typing half's. The step of the ordinary inductive type takes
the use-site reading of the projection guard, a theorem (`Core.projGuardRunReading`).

* `familyGraph`: at every walk of an accepted typing claim and every witness of the table's
  shape, the run's family records, advice, inner records and twins form a family graph in which
  every top-walked non-empty block of recursors is a family record or a twin, every top-walked
  block on the modeled route has a family record, and each family record and twin had its
  family check at the walk's limit (`FamilyRun`). Stated; its graph part (`FamilyGraph`) is
  inhabited at two compiled fixtures (`GraphCheck.familyGraph_of_checks`, from record checks
  evaluated by execution). Producer open: the graph from the run's family
  checks; that a top-walked block of recursors is claimed or a twin is read off the circuit's
  family checks as they are to be changed, not proved.
* `innerChecked`: at every walk and every such run, each record checked inside a family check
  was checked at the walk's limit, uses no inert axiom's reference, uses only references that
  the witness's environment stores, that are covered, or that a checked record of smaller rank
  owns, and, when it is a block that no block claims and that is no twin, it is empty, a block
  of definitions or one inductive type on the native route (`InnerChecked`). Stated; the circuit
  was observed by execution to check each advice record and witness once inside the family check
  at two fixtures. Producer: the check of an advice record declaring one constant is proved
  (`Decl.adviceRecords_checked`); open without a circuit change: a block among the advice,
  a container's recursor and the kinds of an inner block; open until the circuit asserts it of
  inner references: the inert and in-logic parts of the used references, and their order (an
  advice record is no witnessed reference).
* `familyBlock`: the step of a top-walked block with a family record, an empty one included,
  handed its advice and what the advice uses, installs the block with its family record and
  keeps the fold's clause with the family recursors' companions beside it (`UnitStepFamily`).
  Stated; the model side's facts (`Decl.FamilyAlias.FamilyCheckFacts`) are kernel-checked at two
  compiled fixtures. Producer: `FamilyAlias.FamilyStepTarget` with
  `FamilyAlias.modelSide_of_target` on the model side (left: the companions after the step, the
  advice's ties from `FamilyRun.famCall` and the family record's inert clause); the circuit
  side, from the observed family check to the facts, open until the circuit's family changes.
* `familyTwin`: the step of a second family record of a block (a twin), handed the block's
  family record stored, installs it and keeps the fold's clause with the family recursors'
  companions beside it (`UnitStepTwin`). Stated; one accepted pair was executed. Producer open:
  the step from `TwinFamily.TwinStepTarget` through `TwinFamily.familyInstalled_of_clause`, and
  the target from `Decl.FamilyAlias.FamilyCheckFacts`. -/
theorem circuitComposed_residual
    (groupStores : ∀ calls, GroupStoresOfRun calls)
    (groupClosure :
      ∀ calls, AtGroups (BindingRun calls) (ClosureStepOver.{u} FormerOpenTraceAt))
    (groupWithoutRoleUnit :
      ∀ calls, AtGroups (BindingRun calls) (RoleFreeShapes.{u} FormerOpenTraceAt))
    (operationRoleUnit : ∀ calls,
      AtGroups (BindingRun calls)
        (RoleUnitStepOver.{u} (· ∈ RoleOps.opRoles) FormerOpenTraceAt))
    (standardAxiomRoleUnit : ∀ calls,
      AtGroups (BindingRun calls)
        (RoleUnitStepOver.{u} (· ∈ standardAxioms) FormerOpenTraceAt))
    (familyGraph : FamilyGraphRow.{u})
    (innerChecked : InnerCheckedRow)
    (familyBlock : FamilyBlockRow.{u} FormerOpenTraceAt)
    (familyTwin : FamilyTwinRow.{u} FormerOpenTraceAt) :
    CircuitComposed.{u} :=
  circuitComposed_of_parts
    (bindingClaimExport_of_table_and_stores Binding.loadedTableAdmits
      Binding.loadedTablePinsPrelude groupStores)
    (fun calls => basisOver_bindingRun FormerOpenTraceAt calls) admitsChain_bindingRun
    admitsReadsChain_bindingRun
    groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit
    familyGraph
    (innerUnitSteps_of_innerChecked innerChecked
      (nativeBlockTelescope_checked linkLaws_formerOpenTrace Core.projGuardRunReading))
    familyBlock familyTwin
    (standaloneDefinition_foldExtra linkLaws_formerOpenTrace)
    (standaloneTheoremOrOpaque_foldExtra linkLaws_formerOpenTrace)
    (standaloneRecursor_of_freshNotBasis freshRecursorMajorNotBasis_walked)
    (definitionBlock_of_nonempty (definitionBlock_foldExtra linkLaws_formerOpenTrace))
    (nativeBlockTelescope_walked linkLaws_formerOpenTrace Core.projGuardRunReading)
    nativeBlockAlias_walked
    nativeBlockOtherTelescope_step

end IxVM.Refinement.Endpoint
