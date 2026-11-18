import Ix.IxVM.Consistency.L0
import IxVMRefinement.Binding.ClaimDecode
import IxVMRefinement.Claim.TopSafeExport
import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.TypingDefnBlock
import IxVMRefinement.Assembly.ValueUnitStep
import IxVMRefinement.Assembly.FoldClauseSteps
import IxVMRefinement.Assembly.FoldClauseAlias
import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.Assembly.TypingRecLateRegistered
import IxVMRefinement.Assembly.TypingRecBasisFresh
import IxVMRefinement.Assembly.TypingKeyFree
import IxVMRefinement.Assembly.RawQueryCoverage
import IxVMRefinement.Assembly.NativeAliasWalked
import IxVMRefinement.Assembly.WalkedUnitKinds
import IxVMRefinement.Endpoint.WalkedUnit

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
`composed_skeleton_over`: the binding half and the typing half at one internal part
`OverW L` (the boundary facts and the fold's clause `FoldClauseWith L` at every record store,
with one registry), joined by `binding_discharge`. The circuit statement follows through `L0`,
once for each derivation (`circuitSound_of_bounded`, `l0`). `L` is the link between a
registered family's stored former and its telescope constant; a typing step keeps the part of
the clause beside the prefix invariant (`FoldExtra L`). `circuitComposed_of_parts` is the
composition for any link; `circuitComposed_residual` is its instance at the opened head trace
`FormerOpenTraceAt`, less what is proved there.

Proved inside, with no hypothesis left:

* the circuit-to-source step (`l0`), at both derivations;
* the typing claim's export, the walk's limit and the assembly's reading of the walk
  (`Claim.claimPhase_typing`, `TopWalkCore.topLim`, `Claim.TopWalk.graph`);
* what every unit's step reads of the walk (`unitSteps_of_kinds`): the table's check, the run
  store, the store the step runs against and its coverage of the run's hashed records
  (`canonicalHashCoverage_frame`), the inert clause, the cover clause (from
  `coverAt_of_graph` and `Claim.TopWalk.need`), the check of the record at the walk's limit,
  that the witness's environment stores none of the record's constant addresses and that
  their keys are free (`keyFree_of_not_stored`), and for a block of one inductive type its
  member and constructor projection records;
* the case split of a unit by the form of its record (`unitSteps_of_kinds`);
* the step of a standalone definition, at either limit (`standaloneDefinition_foldExtra`, from
  `unitStep_defn_foldExtra`);
* the step of a standalone theorem or opaque record and the step of a non-empty block of
  definitions, at either limit (`standaloneTheoremOrOpaque_foldExtra`,
  `definitionBlock_foldExtra`, from the value step stated once for both folds,
  `ValueUnitStep`);
* the step of a standalone recursor, at any limit (`standaloneRecursor_of_freshNotBasis`, from
  `unitStep_recLate_walked`, with the basis exclusion at a fresh record,
  `freshRecursorMajorNotBasis_walked`, from `recMajorFreshNotBasis_of_walk`): the check's output
  at the family the registry reads at the parent that heads the record's major premise
  (`recLateOut_of_walk`: a family with a telescope former or one whose former only
  head-reduces to a telescope), and the parent itself, which the circuit's route reads as a
  stored former of a native block (`recParent_of_arm_tied`). **The case of a recursor with no
  native parent is empty because the circuit refuses it today**: the `Rec` arm of
  `check_const` asserts that the recursor's family block is not modeled, and
  `check_recursor_member` asserts the same of the block of the major premise's parent, so no
  accepted run checks a recursor of a mutual or nested family. Three lemmas read the first
  assertion (`Typing.check_const_rec_route`, `Typing.check_const_rec_arm`,
  `Claim.TopWalkCore.recFamilyNative`: each closes the `Rec_other` path of `check_const` by
  it) and two read the second (`Typing.native_rec_route_calls`,
  `Typing.native_rec_member_full`: the member check has one path, with the route's answer
  `0`). When the source stops refusing those recursors, these five lemmas stop building at
  exactly those paths, the parent of `recParent_of_arm_tied` is no longer always native, and
  the recursor of a mutual or nested family is a case of its own, for the family's step;
* the step of a block of one inductive type on the native route whose former is declared at a
  definition, at either limit (`nativeBlockAlias_walked`);
* the step of a block of one inductive type on the native route whose former reads as a
  telescope of another length: the circuit refuses the block
  (`nativeBlockOtherTelescope_step`);
* the step of an empty block, which installs nothing (inside `definitionBlock_of_nonempty`);
* that a block of one inductive type off the native route is on the modeled route in the run
  and at the step's store (`oneTypeBlockOffNativeRoute_of_modeled`), and that a block which
  is no block of definitions and no block of one inductive type is a block of two or more
  inductive types on the modeled route or a non-empty block of recursors, a block of mixed
  kinds being refused (`otherBlock_of_kinds`);
* on the binding side, everything `composed_skeleton_over` proves from its named hypotheses:
  the fold over the 77 groups, the step of a group from its parts, the raise past a group, the
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
* typing, for a top-walked unit by the form of its record (`WalkedUnit`, `WalkedUnitStep`, in
  `IxVMRefinement.Endpoint.WalkedUnit`): the step of a block of one inductive type on the native
  route whose former is declared at its telescope; and, given that the block is modeled at the
  step's store, of a block of one inductive type on the modeled route and of a block of two or
  more inductive types on the modeled route; the step of a non-empty block of recursors.

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

/-! ## The typing half -/

/-- **The step of every top-walked unit, from the step of each kind.** The premises common to
all kinds are read off the walk, and the unit's record is split by its form: a definition
record by its kind; a recursor record; a block by whether every member is a definition, whether
it is one inductive type (then by the circuit's dispatch on it in the run and by the reading of
its former), or neither. -/
theorem unitSteps_of_kinds
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    (standaloneDefinition : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (oneTypeBlockOffNativeRoute : WalkedUnitStep.{u} X fun calls _ E₀ B cb =>
      ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ¬ NativeRouteAt calls B)
    (otherBlock : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ ¬ DefnBlock ms ∧
        ∀ ind : Ixon.Inductive, ms ≠ #[.indc ind]) :
    ∀ t seeds E₀ lim Top rank, Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t E) t envT E₀ E lim A c := by
  intro t seeds E₀ lim Top rank hWalk R envT E hctx A c hT hc hlog hk
  have hneed := Claim.TopWalk.need hWalk hT hc hk hlog
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  have ht : t.check = .ok () := hW.check_ok
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hinert : InertClause t c := hW.inertClause hT hc
  have hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c :=
    coverAt_of_graph hG hctx.shape htwf hT hc hneed
  have hcanon₀ : L1.CanonicalHashCoverage E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hW.hashedStored bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage E calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hctx.recordsFor.1
      (fun a v h => hctx.runRecord a v ((hW.runStore.recordOf_eq_recordAt a).trans h))
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hT
    have e : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e] at h
    exact h
  have step : ∀ {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address →
      Ixon.Constant → Prop}, WalkedUnitStep.{u} X Kind → Kind calls t E₀ A c →
      UnitStep.{u} (X t E) t envT E₀ E lim A c := by
    intro Kind h hkind env hext hnd hinv hXe href hfresh
    have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
      intro x hx hst
      obtain ⟨ci, hci, hname⟩ := hst
      have hs : (env.find? (keyOf t x)).isSome = true :=
        find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
      rw [hfresh x hx] at hs
      simp at hs
    exact h calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind
      ht hW.runStore hW.hashedStored hctx.toStepStore hcanon hinert hcover hchk hns
      (fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx))
      env hext hnd hinv hXe href hfresh
  rcases hk with ⟨d, hinfo⟩ | ⟨rc, hinfo⟩ | ⟨ms, hinfo⟩
  · by_cases hkind : d.kind = .defn
    · exact step standaloneDefinition ⟨d, hinfo, hkind⟩
    · exact step standaloneTheoremOrOpaque ⟨d, hinfo, hkind⟩
  · exact step standaloneRecursor ⟨rc, hinfo⟩
  · by_cases hdefs : DefnBlock ms
    · exact step definitionBlock ⟨ms, hinfo, hdefs⟩
    · by_cases hone : ∃ ind : Ixon.Inductive, ms = #[.indc ind]
      · obtain ⟨ind, hms⟩ := hone
        rw [hms] at hinfo
        have hmem := hG.members A c #[.indc ind] hT hc hinfo 0 (.indc ind) (by rfl)
        have hrec : BlockUnitRecord E₀ A c ind :=
          ⟨hc, hinfo, hlog, hmem.1, fun j hj => hmem.2 ind j rfl hj⟩
        by_cases hnat : NativeRouteAt calls A
        · rcases formerAt_cases t E₀ A c ind with htele | halias | hother
          · exact step nativeBlockTelescope ⟨ind, hrec, hnat, htele⟩
          · exact step nativeBlockAlias ⟨ind, hrec, hnat, halias⟩
          · exact step nativeBlockOtherTelescope ⟨ind, hrec, hnat, hother⟩
        · exact step oneTypeBlockOffNativeRoute ⟨ind, hrec, hnat⟩
      · exact step otherBlock ⟨ms, hinfo, hdefs, fun ind h => hone ⟨ind, h⟩⟩

/-- **The step of a top-walked standalone definition keeps the fold's clause**, at the walk's
limit, for any link that satisfies the link laws. -/
theorem standaloneDefinition_foldExtra
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L) :
    WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨d, hinfo, hk⟩ := hkind
  have hchk' : Claim.CheckedLimAt calls bAddr t A lim := by
    rcases hchk with ⟨ms, hms, -⟩ | h
    · have e := hinfo.symm.trans hms
      cases e
    · exact h
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩
  exact unitStep_defn_foldExtra hL ht hS hst hc hinfo hlog hk hchk' (hkeys A hown) hinert hcover

/-- **The step of a top-walked standalone theorem or opaque record keeps the fold's clause**, at
the walk's limit, for any link that satisfies the link laws. -/
theorem standaloneTheoremOrOpaque_foldExtra
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L) :
    WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨d, hinfo, hk⟩ := hkind
  have hchk' : Claim.CheckedLimAt calls bAddr t A lim := by
    rcases hchk with ⟨ms, hms, -⟩ | h
    · have e := hinfo.symm.trans hms
      cases e
    · exact h
  exact unitStep_value_foldExtra hL ht hS hst hc hinfo hlog hchk' hkeys hinert hcover

/-- **The step of a top-walked non-empty block of definitions keeps the fold's clause**, at the
walk's limit, for any link that satisfies the link laws. A block record is checked member by
member: the walk's check of the record itself does not arise (`Claim.checked_not_block`). The
step holds of the empty block as well (`unitStep_defnBlock_foldExtra`); the kind is the one the
composed statement asks. -/
theorem definitionBlock_foldExtra
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L) :
    WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ 0 < ms.size ∧ DefnBlock ms := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ms, hmuts, -, hdefs⟩ := hkind
  have hchk' : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim := by
    rcases hchk with ⟨ms', hms', h⟩ | h
    · have e : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hms')
      rw [e]
      exact h
    · exact (Claim.checked_not_block hS hc hmuts h).elim
  exact unitStep_defnBlock_foldExtra hL ht hS hcov hst hc hmuts hlog hdefs hchk' hkeys hinert
    hcover

/-- **At a top-walked standalone recursor record, a native parent that heads the major premise
is at no reserved basis name**, where the witness's environment does not store the record's
address (`recMajorFreshNotBasis_of_walk`, from what the walk hands every unit's step). -/
theorem freshRecursorMajorNotBasis_walked :
    WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
      fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
        RecMajorFreshNotBasis.{u} t envT E₀ E lim A c rc := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys rc hinfo
  exact recMajorFreshNotBasis_of_walk hW hctx hT hc hinfo ht hS hst hinert hcover
    (hns A (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩))

/-- **The step of a top-walked standalone recursor keeps the fold's clause**, at the walk's
limit and at the opened head trace, from one fact: at a record whose address the witness's
environment does not store, a native parent that heads the major premise is at no reserved
basis name (`freshNotBasis`). The check's output at the parent's registered family and the
parent itself are read off the walk (`unitStep_recLate_walked`). The parent is always native
because the circuit refuses a recursor of a modeled family (module docstring). -/
theorem standaloneRecursor_of_freshNotBasis
    (freshNotBasis :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
          RecMajorFreshNotBasis.{u} t envT E₀ E lim A c rc) :
    WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨rc, hinfo⟩ := hkind
  exact unitStep_recLate_walked hW hT hc hlog hinfo ht hS hcov hst hinert hcover
    (hkeys A (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩))
    (freshNotBasis calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog
      ⟨rc, hinfo⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys rc hinfo)

/-! ## The composed statement -/

/-- **The public statement from the parts of the two halves, for any link.** `L` is the link
of the fold's clause and `Run` the binding claim layer's run predicate, by the run's calls. The
first eight hypotheses are the binding half's, those of `composed_skeleton_over` for every
bounded run: the claim export with the observed run record; the invariant at the six basis
groups; the admission of each group and its reading clause; and at each group from 6 to 76 of
a run the closure, the stored shapes where the group has no role unit, the role unit of an
operation and the role unit of a standard axiom. The other nine are the typing half's: the
step of a top-walked unit of each kind. -/
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
    (oneTypeBlockOffNativeRoute : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls _ E₀ B cb =>
      ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ¬ NativeRouteAt calls B)
    (otherBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ ¬ DefnBlock ms ∧
        ∀ ind : Ixon.Inductive, ms ≠ #[.indc ind]) :
    CircuitComposed.{u} := by
  unfold CircuitComposed
  refine circuitSound_of_bounded l0 ?_
  intro dB valueB heapB callsB evB hbB
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  refine circuitSound_of_bounded l0 ?_
  intro dA valueA heapA callsA evA hbA
  show ComposedSpec.{u} callsA callsB dA dB
  exact composed_skeleton_over (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupClosure callsB) (groupWithoutRoleUnit callsB) (operationRoleUnit callsB)
    (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (unitSteps_of_kinds (X := FoldExtra.{u} L) standaloneDefinition standaloneTheoremOrOpaque
      standaloneRecursor definitionBlock nativeBlockTelescope nativeBlockAlias
      nativeBlockOtherTelescope oneTypeBlockOffNativeRoute otherBlock)

/-- **The public statement from the open obligations** (module docstring):
`circuitComposed_of_parts` at the opened head trace `FormerOpenTraceAt`, with the steps that
are proved passed in and the others reduced to smaller ones. The binding claim layer's run
predicate is `Binding.BindingRun`, by the run's calls. The first seven hypotheses are the
binding half's. Three are the parts of the claim's export that remain
(`Binding.bindingClaimExport_of_table_and_stores`; the claim's decode is proved,
`Claim.verify_claim_decode_binding_spec`): that the table a binding run loads is the admitted
table of bytes the run hashed (`tableAdmits`), that such a table binding every role pins the
prelude (`preludePins`), and the stores of a run, with every clause of each group's admission
but the observed validation of its roles (`groupStores`). The invariant at the six basis groups
and the two admission chains are projections of the run predicate (`basisOver_bindingRun`,
`admitsChain_bindingRun`, `admitsReadsChain_bindingRun`). The other four are, for every bounded
run and each group from 6 to 76 of it, the closure, the stored shapes where the group has no
role unit, the role unit of an operation and the role unit of a standard axiom. The last four
hypotheses are the typing half's, for a top-walked unit: the step of a one-type native block
whose former is declared at its telescope; of a one-type block and of a block of two or more
inductive types on the modeled route, each given that the block is modeled at the step's
store; and of a non-empty block of recursors. -/
theorem circuitComposed_residual
    (tableAdmits : LoadedTableAdmits)
    (preludePins : LoadedTablePinsPrelude)
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
    (nativeBlockTelescope :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (oneTypeBlockModeled :
      WalkedUnit.{u} (fun calls _ E₀ B cb =>
          ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ModeledRouteAt calls B)
        fun _ t envT E₀ E lim B cb =>
          ModeledAt E B →
            UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim B cb)
    (mutualBlock :
      WalkedUnit.{u} (fun calls _ _ B cb =>
          ∃ ms : Array Ixon.MutConst, cb.info = .muts ms ∧ 2 ≤ ms.size ∧
            (∀ m ∈ ms.toList, ∃ i, m = Ixon.MutConst.indc i) ∧ ModeledRouteAt calls B)
        fun _ t envT E₀ E lim B cb =>
          ModeledAt E B →
            UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim B cb)
    (recursorBlock :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun _ _ _ _ c =>
        ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ 0 < ms.size ∧
          ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) :
    CircuitComposed.{u} :=
  circuitComposed_of_parts
    (bindingClaimExport_of_table_and_stores tableAdmits preludePins groupStores)
    (fun calls => basisOver_bindingRun FormerOpenTraceAt calls) admitsChain_bindingRun
    admitsReadsChain_bindingRun
    groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit
    (standaloneDefinition_foldExtra linkLaws_formerOpenTrace)
    (standaloneTheoremOrOpaque_foldExtra linkLaws_formerOpenTrace)
    (standaloneRecursor_of_freshNotBasis freshRecursorMajorNotBasis_walked)
    (definitionBlock_of_nonempty (definitionBlock_foldExtra linkLaws_formerOpenTrace))
    nativeBlockTelescope
    nativeBlockAlias_walked
    nativeBlockOtherTelescope_step
    (oneTypeBlockOffNativeRoute_of_modeled oneTypeBlockModeled)
    (otherBlock_of_kinds mutualBlock recursorBlock)

end IxVM.Refinement.Endpoint
