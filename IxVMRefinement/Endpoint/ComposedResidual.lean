import Ix.IxVM.Consistency.L0
import IxVMRefinement.Binding.ClauseFold
import IxVMRefinement.Claim.TopSafeExport
import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.TypingDefnBlock
import IxVMRefinement.Assembly.ValueUnitStep
import IxVMRefinement.Assembly.FoldClauseSteps
import IxVMRefinement.Assembly.FoldClauseAlias
import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.Assembly.TypingKeyFree
import IxVMRefinement.Assembly.RawQueryCoverage

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
* the step of a standalone theorem or opaque record and the step of a block of definitions, at
  either limit (`standaloneTheoremOrOpaque_foldExtra`, `definitionBlock_foldExtra`, from the
  value step stated once, `ValueUnitStep`);
* the step of a standalone recursor whose major premise is headed, at every environment the
  step is asked at, by a parent the circuit treats as native: the registry and the late
  relation's bookkeeping, at any limit (`standaloneRecursor_of_parts`, from
  `unitStep_recLate_foldExtra`). What is left of it is the check's output at the family the
  registry reads at that parent;
* on the binding side, everything `composed_skeleton_over` proves from its named hypotheses:
  the fold over the 77 groups, the step of a group from its parts, the raise past a group, the
  table's well-formedness from the claim's admission, and the witness on every group.

Left as hypotheses, for a run predicate `Run` that the binding claim layer is to supply (the
run record is the observed one, `observedRun`; the predicate relating it to the table and the
store sequence is not fixed):

* binding: the claim export with the observed run record; the invariant at the six basis
  groups; the admission of each group and its reading clause; and at each group of a run the
  closure, the stored shapes where the group has no role unit, the role unit of an operation
  and of a standard axiom, and the load contract's guard at the limits a closed group brings
  within range;
* typing, for a top-walked unit by the form of its record (`WalkedUnit`, `WalkedUnitStep`): for
  a standalone recursor, the check's output at a native parent's registered family, and the
  step where no such parent heads the major premise; the step of a block of one inductive type
  on the native route, by the three cases of its former's reading (`formerAt_cases`); of a
  block of one inductive type off the native route; of any block that is neither a block of
  definitions nor one inductive type.

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

/-- **A fact about every top-walked unit of one kind**, as the composition asks it. `Kind`
reads the run's calls, the table, the run's store, the unit's address and its record; `Goal`
also reads the witness's environment, the store the step runs against and the walk's limit.
For a walk export at the binding `bAddr`, the assembly's reading of it, a step context and a
top-walked record `c` at `A` in Lean's logic of that kind, the producer of `Goal` is handed
what holds of every unit whose step is asked: the table's check, the run store, that the run's
hashed records are stored, the store the step runs against and that it holds every record the
run hashed with its exact decoding, that no reference the record uses is an inert axiom's, the
cover clause at every environment the skeleton hands the step, the walk's check of the record
at the walk's limit (every member of a block, or the record), that the witness's environment
stores none of the record's constant addresses, and that their keys are free. -/
def WalkedUnit
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop)
    (Goal : List (Call F) → Ix.Kernel.RoleTable → Ix.Kernel.Env .anon → Ixon.Env → Ixon.Env →
      Option Nat → _root_.Address → Ixon.Constant → Prop) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (seeds : List _root_.Address) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
    Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank → TopGraph t E₀ seeds Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env),
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant),
        Top A → recordOf E₀ A = some c → InLogic c → Kind calls t E₀ A c →
        t.check = .ok () → LoadedReads.RunStore calls E₀ →
        LoadedReads.HashedRecordsStored calls E₀ → StepStore calls t E₀ E →
        L1.CanonicalHashCoverage E calls →
        InertClause t c → (∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) →
        ((∃ ms, c.info = .muts ms ∧
            ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
          Claim.CheckedLimAt calls bAddr t A lim) →
        (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
        (∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)) →
        Goal calls t envT E₀ E lim A c

/-- **The step of every top-walked unit of one kind**: `WalkedUnit` at the unit's step for the
carried clause `X` at the step's store, at the walk's limit. -/
def WalkedUnitStep
    (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop) : Prop :=
  WalkedUnit.{u} Kind fun _ t envT E₀ E lim A c => UnitStep.{u} (X t E) t envT E₀ E lim A c

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

/-- **The step of a top-walked block of definitions keeps the fold's clause**, at the walk's
limit, for any link that satisfies the link laws. A block record is checked member by member:
the walk's check of the record itself does not arise (`Claim.checked_not_block`). -/
theorem definitionBlock_foldExtra
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L) :
    WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ms, hmuts, hdefs⟩ := hkind
  have hchk' : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim := by
    rcases hchk with ⟨ms', hms', h⟩ | h
    · have e : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hms')
      rw [e]
      exact h
    · exact (Claim.checked_not_block hS hc hmuts h).elim
  exact unitStep_defnBlock_foldExtra hL ht hS hcov hst hc hmuts hlog hdefs hchk' hkeys hinert
    hcover

/-- **The step of a top-walked standalone recursor keeps the fold's clause, from its two
parts.** The recursor's major premise is headed by a parent the circuit treats as native at
every environment the step is asked at, or it is not. In the first case the registry holds the
parent's family and the step is the late recursor step, given the check's output at that
family (`atNativeParent`); the second case is taken whole (`withoutNativeParent`). -/
theorem standaloneRecursor_of_parts
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L)
    (atNativeParent :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
          ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → LvClauses env →
            RecParent t E env P ip → RecMajorTie t E₀ A c rc P →
            FamReadAt L t E env P ip fam → RecLateOut t E₀ E A env fam)
    (withoutNativeParent :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
          ¬ (∀ env, StepAt.{u} t envT E₀ E lim A c env →
              ∃ P ip, RecParent t E env P ip ∧ RecMajorTie t E₀ A c rc P) →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) :
    WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨rc, hinfo⟩ := hkind
  by_cases hN : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip ∧ RecMajorTie t E₀ A c rc P
  · exact unitStep_recLate_foldExtra hL (RecMajorTie t E₀ A c rc) ht hinfo
      (address_size_of_record hS hc) hN
      (fun env P ip fam hstep hlv hpar htie hread =>
        atNativeParent calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog
          ⟨rc, hinfo⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys rc hinfo env P ip fam
          hstep hlv hpar htie hread)
  · exact withoutNativeParent calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc
      hlog ⟨rc, hinfo⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys rc hinfo hN

/-! ## The composed statement -/

/-- **The public statement from the parts of the two halves, for any link.** `L` is the link
of the fold's clause and `Run` the binding claim layer's run predicate, by the run's calls. The
first nine hypotheses are the binding half's, those of `composed_skeleton_over` for every
bounded run: the claim export with the observed run record; the invariant at the six basis
groups; the admission of each group and its reading clause; and at each group from 6 to 76 of
a run the closure, the stored shapes where the group has no role unit, the role unit of an
operation, the role unit of a standard axiom and the guard at the raised limits. The other
nine are the typing half's: the step of a top-walked unit of each kind. -/
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
    (raisedLimitGuard :
      ∀ calls, AtGroups (Run calls) (fun _ t g => RaisedLimitGuard.{u} L t g))
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
    (standardAxiomRoleUnit callsB) (raisedLimitGuard callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (unitSteps_of_kinds (X := FoldExtra.{u} L) standaloneDefinition standaloneTheoremOrOpaque
      standaloneRecursor definitionBlock nativeBlockTelescope nativeBlockAlias
      nativeBlockOtherTelescope oneTypeBlockOffNativeRoute otherBlock)

/-- **The public statement from the open obligations** (module docstring):
`circuitComposed_of_parts` at the opened head trace `FormerOpenTraceAt`, with the steps of a
standalone definition, of a standalone theorem or opaque record and of a block of definitions
proved, and the step of a standalone recursor reduced to its two parts.
`Run` is the binding claim layer's run predicate, by the run's calls. The first nine
hypotheses are the binding half's, for every bounded run: the claim export with the observed
run record; the invariant at the six basis groups; the admission of each group and its reading
clause; and at each group from 6 to 76 of a run the closure, the stored shapes where the group
has no role unit, the role unit of an operation, the role unit of a standard axiom and the
guard at the raised limits. The other seven are the typing half's, for a top-walked unit of
each remaining kind: its step, and for a standalone recursor the check's output at a native
parent's registered family and the step where no native parent heads its major premise. -/
theorem circuitComposed_residual
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOver.{u} FormerOpenTraceAt (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) (ClosureStepOver.{u} FormerOpenTraceAt))
    (groupWithoutRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} FormerOpenTraceAt))
    (operationRoleUnit : ∀ calls,
      AtGroups (Run calls) (RoleUnitStepOver.{u} (· ∈ RoleOps.opRoles) FormerOpenTraceAt))
    (standardAxiomRoleUnit : ∀ calls,
      AtGroups (Run calls) (RoleUnitStepOver.{u} (· ∈ standardAxioms) FormerOpenTraceAt))
    (raisedLimitGuard : ∀ calls,
      AtGroups (Run calls) (fun _ t g => RaisedLimitGuard.{u} FormerOpenTraceAt t g))
    (recursorAtNativeParent :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
          ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → LvClauses env →
            RecParent t E env P ip → RecMajorTie t E₀ A c rc P →
            FamReadAt FormerOpenTraceAt t E env P ip fam → RecLateOut t E₀ E A env fam)
    (recursorWithoutNativeParent :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
          ¬ (∀ env, StepAt.{u} t envT E₀ E lim A c env →
              ∃ P ip, RecParent t E env P ip ∧ RecMajorTie t E₀ A c rc P) →
          UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim A c)
    (nativeBlockTelescope :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (oneTypeBlockOffNativeRoute :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls _ E₀ B cb =>
        ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ¬ NativeRouteAt calls B)
    (otherBlock :
      WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun _ _ _ _ c =>
        ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ ¬ DefnBlock ms ∧
          ∀ ind : Ixon.Inductive, ms ≠ #[.indc ind]) :
    CircuitComposed.{u} :=
  circuitComposed_of_parts bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
    groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit raisedLimitGuard
    (standaloneDefinition_foldExtra linkLaws_formerOpenTrace)
    (standaloneTheoremOrOpaque_foldExtra linkLaws_formerOpenTrace)
    (standaloneRecursor_of_parts linkLaws_formerOpenTrace recursorAtNativeParent
      recursorWithoutNativeParent)
    (definitionBlock_foldExtra linkLaws_formerOpenTrace) nativeBlockTelescope nativeBlockAlias
    nativeBlockOtherTelescope oneTypeBlockOffNativeRoute otherBlock

end IxVM.Refinement.Endpoint
