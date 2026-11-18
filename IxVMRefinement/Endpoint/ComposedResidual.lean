import Ix.IxVM.Consistency.L0
import IxVMRefinement.Binding.GlueStore
import IxVMRefinement.Claim.TopSafeExport
import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.TypingDefnBlock
import IxVMRefinement.Assembly.TypingDefnLimKeyed
import IxVMRefinement.Assembly.TypingKeyFree

/-! # The composed statement from its open obligations

`circuitComposed_residual` proves the public statement `IxVM.Consistency.CircuitComposed` from
named hypotheses, one for each obligation of the proof that has no unconditional theorem yet.
It claims nothing by itself: a hypothesis is typed by the interface its obligation has today,
whether or not that interface can be met. It fixes how the parts compose, and what is left.
A hypothesis is deleted when a theorem produces it. Its statement is printed in
`IxVMRefinement.Endpoint.ComposedResidualAudit`, which fails to build when the statement
changes.

The chain. `CircuitComposed` follows from the two halves of the deployed circuit for one
internal part `Facts` (`circuitComposed_of_halves`); a half of the circuit follows from the same
half of every bounded source derivation, through `L0` (`circuitSound_of_bounded`, `l0`). Both
halves are taken at `Facts := BW (StoreX X)` for one carried clause `X`.
`circuitComposed_of_parts` is the composition for any `X`; `circuitComposed_residual` is its
instance at the clause the steps carry today, `NativeBlockXR`, less what is proved there.

Proved inside, with no hypothesis left:

* the circuit-to-source step (`l0`);
* the typing claim's export, the walk's limit and the assembly's reading of the walk
  (`Claim.claimPhase_typing`, `TopWalkCore.topLim`, `Claim.TopWalk.graph`);
* what every unit's step reads of the walk (`unitSteps_of_kinds`): the table's check, the run
  store, the store the step runs against, the inert clause, the cover clause (from
  `coverAt_of_graph` and `Claim.TopWalk.need`), the check of the record at the walk's limit,
  that the witness's environment stores none of the record's constant addresses and that
  their keys are free (`keyFree_of_not_stored`), and for a block of one inductive type its
  member and constructor projection records;
* the case split of a unit by the form of its record (`unitSteps_of_kinds`);
* the step of a standalone definition, at either limit, for a carried clause that a checked
  value constant at a hashed key keeps (`standaloneDefinition_of_keepsValuesKeyed`, from
  `unitStep_defn_lim_keyed`); `NativeBlockXR` is such a clause;
* on the binding side, the store congruence of the invariant and the passage of the carried
  clause from the 77 groups to every group (`bndCongr_storeX`, `xAllGroups_storeX`), and that
  the table of an accepted binding claim is well formed (`bindingClaimExport_wellFormed`: the
  group step asks it of the run, and the claim export holds the admission that gives it).

Left as hypotheses, for a run predicate `Run` that the binding claim layer is to supply:

* binding: the claim export, the invariant at the six basis groups, the admission of each group
  and its reading clause, and at each group the closure, the facts at a group with no role
  unit, and the role unit of an operation and of a standard axiom;
* typing: the step of a top-walked unit, by the form of its record (`WalkedUnitStep` at each
  kind): a standalone theorem or opaque; a standalone recursor; a block of definitions; a
  block of one inductive type on the native route, by the three cases of its former's reading
  (`formerAt_cases`); a block of one inductive type off the native route; any other block.

The typing half takes nothing from the binding half but the table witness at `BW (StoreX X)`,
so no further hypothesis joins the two.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Endpoint

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-! ## The typing half -/

/-- **The step of every top-walked unit of one kind**, as the composition asks it. `Kind` reads
the run's calls, the table, the run's store, the unit's address and its record. For a walk
export at the binding `bAddr`, the assembly's reading of it, a step context and a top-walked
record `c` at `A` in Lean's logic of that kind, the step is handed what holds of every unit:
the table's check, the run store, that the run's hashed records are stored, the store the step
runs against, that no reference the record uses is an inert axiom's, the cover clause at every
environment the skeleton hands the step, the walk's check of the record at the walk's limit
(every member of a block, or the record), that the witness's environment stores none of the
record's constant addresses, and that their keys are free. It must give the unit's step for
the carried clause `X` at the step's store, at the walk's limit. -/
def WalkedUnitStep
    (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop) : Prop :=
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
        InertClause t c → (∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) →
        ((∃ ms, c.info = .muts ms ∧
            ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
          Claim.CheckedLimAt calls bAddr t A lim) →
        (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
        (∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)) →
        UnitStep.{u} (X t E) t envT E₀ E lim A c

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
      ht hW.runStore hW.hashedStored hctx.toStepStore hinert hcover hchk hns
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

/-- **The step of a top-walked standalone definition, at the walk's limit, for a carried
clause that a checked value constant at a hashed key keeps** (`KeepsValuesKeyed`). -/
theorem standaloneDefinition_of_keepsValuesKeyed
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    (hX : ∀ (t : Ix.Kernel.RoleTable) (E : Ixon.Env), t.wf = true →
      KeepsValuesKeyed t (X t E)) :
    WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hinert hcover hchk hns hkeys
  obtain ⟨d, hinfo, hk⟩ := hkind
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hchk' : Claim.CheckedLimAt calls bAddr t A lim := by
    rcases hchk with ⟨ms, hms, -⟩ | h
    · have e := hinfo.symm.trans hms
      cases e
    · exact h
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩
  exact unitStep_defn_lim_keyed ht hS hst hc hinfo hlog hk hchk' (hkeys A hown) hinert hcover
    (hX t E htwf)

/-- **The typing half of a bounded source derivation, from the steps of its walk's units**: the
claim export, the walk's limit and the assembly's reading of the walk are the claim layer's. -/
theorem typingSpecOn_of_steps
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {d : Digest} {value : Aiur.SourceValue F} {heap : Aiur.Heap F} {calls : List (Call F)}
    (hb : Bounded calls)
    (ev : Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim [digestValue d] []
      value heap calls)
    (hstep : ∀ t seeds E₀ lim Top rank, Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t E) t envT E₀ E lim A c) :
    TypingSpecOn.{u} (BW.{u} (StoreX X)) calls d :=
  typing_skeleton_carried hb (Claim.claimPhase_typing ev)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h) hstep

/-! ## The binding half -/

/-- **The table of an accepted binding claim is well formed**: the claim export holds the
table's admission, so the run predicate may carry the table's well-formedness, which the group
step asks of the run. -/
theorem bindingClaimExport_wellFormed
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {calls : List (Call F)} {d : Digest} (h : BindingClaimExport Run calls d) :
    BindingClaimExport (fun t ρ Rs => t.wf = true ∧ Run t ρ Rs) calls d := by
  intro bytes spec a hde hdig V
  rcases h bytes spec a hde hdig V with hcol | ⟨tb, t, htb, hadm, hall, ρ, Rs, hload, hrun⟩
  · exact Or.inl hcol
  · have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have htwf : t.wf = true := by
      unfold Ix.Kernel.RoleTable.wf
      rw [ht]
      rfl
    exact Or.inr ⟨tb, t, htb, hadm, hall, ρ, Rs, hload, htwf, hrun⟩

/-- **The binding half of a source derivation, from the parts of its fold**: the claim export,
the basis groups, the two admission chains and the four parts of each group's step, for the
carried clause at every record store. -/
theorem bindingSpecOn_of_parts
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {calls : List (Call F)} {d : Digest}
    (hclaim : BindingClaimExport Run calls d) (hbase : BasisBase.{u} (StoreX X) Run)
    (hadm : AdmitsChain Run) (hrd : AdmitsReadsChain Run)
    (hclosure : ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      ClosureStep.{u} (StoreX X) ρ t g)
    (hnone : ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      RoleNoneFacts.{u} (StoreX X) t g)
    (hop : ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      RoleUnitStep.{u} (· ∈ RoleOps.opRoles) (StoreX X) ρ t g)
    (hax : ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      RoleUnitStep.{u} (· ∈ standardAxioms) (StoreX X) ρ t g) :
    BindingSpecOn.{u} (BW.{u} (StoreX X)) calls d :=
  binding_skeleton_r (Run := fun t ρ Rs => t.wf = true ∧ Run t ρ Rs)
    (bindingClaimExport_wellFormed hclaim)
    (fun t ρ Rs h hall => hbase t ρ Rs h.2 hall)
    (fun t ρ Rs h => hadm t ρ Rs h.2)
    (fun t ρ Rs h => hrd t ρ Rs h.2)
    (groupStepsR_of_parts (bndCongr_storeX X) (fun _ _ _ h => h.1)
      (fun t ρ Rs h hall g hg6 hg =>
        ⟨hclosure t ρ Rs h.2 hall g hg6 hg, hnone t ρ Rs h.2 hall g hg6 hg,
          hop t ρ Rs h.2 hall g hg6 hg, hax t ρ Rs h.2 hall g hg6 hg⟩))
    (xAllGroups_storeX X)

/-! ## The composed statement -/

/-- **The public statement from the parts of the two halves, for any carried clause.** `X` is
the carried clause and `Run` the binding claim layer's run predicate, by the run's calls. The
first eight hypotheses are the binding half's: the claim export of every bounded run; the
invariant at the six basis groups; the admission of each group and its reading clause; and at
each group from 6 to 76 the closure, the facts at a group with no role unit, the role unit of
an operation and the role unit of a standard axiom. The other nine are the typing half's: the
step of a top-walked unit of each kind. -/
theorem circuitComposed_of_parts
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExport (Run calls) calls d)
    (basisGroups : ∀ calls, BasisBase.{u} (StoreX X) (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupClosure : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      ClosureStep.{u} (StoreX X) ρ t g)
    (groupWithoutRoleUnit : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t →
      ∀ g, 6 ≤ g → g < 77 → RoleNoneFacts.{u} (StoreX X) t g)
    (operationRoleUnit : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t →
      ∀ g, 6 ≤ g → g < 77 → RoleUnitStep.{u} (· ∈ RoleOps.opRoles) (StoreX X) ρ t g)
    (standardAxiomRoleUnit : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t →
      ∀ g, 6 ≤ g → g < 77 → RoleUnitStep.{u} (· ∈ standardAxioms) (StoreX X) ρ t g)
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
    CircuitComposed.{u} := by
  apply circuitComposed_of_halves
  unfold CircuitConsistentOn
  refine ⟨BW.{u} (StoreX X), circuitSound_of_bounded l0 ?_, circuitSound_of_bounded l0 ?_⟩
  · intro d value heap calls ev hb
    exact bindingSpecOn_of_parts (bindingClaimExport d value heap calls ev hb)
      (basisGroups calls) (groupAdmissions calls) (groupAdmissionReads calls)
      (groupClosure calls) (groupWithoutRoleUnit calls) (operationRoleUnit calls)
      (standardAxiomRoleUnit calls)
  · intro d value heap calls ev hb
    exact typingSpecOn_of_steps hb ev
      (unitSteps_of_kinds standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
        definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope
        oneTypeBlockOffNativeRoute otherBlock)

/-- **The public statement from the open obligations** (module docstring):
`circuitComposed_of_parts` at the registered-family clause `NativeBlockXR`, where the step of a
standalone definition is proved. `Run` is the binding claim layer's run predicate, by the run's
calls. The first eight hypotheses are the binding half's: the claim export of every bounded
run; the invariant at the six basis groups; the admission of each group and its reading
clause; and at each group from 6 to 76 the closure, the facts at a group with no role unit,
the role unit of an operation and the role unit of a standard axiom. The other eight are the
typing half's: the step of a top-walked unit of each remaining kind. -/
theorem circuitComposed_residual
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExport (Run calls) calls d)
    (basisGroups : ∀ calls, BasisBase.{u} (StoreX NativeBlockXR.{u}) (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupClosure : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      ClosureStep.{u} (StoreX NativeBlockXR.{u}) ρ t g)
    (groupWithoutRoleUnit : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t →
      ∀ g, 6 ≤ g → g < 77 → RoleNoneFacts.{u} (StoreX NativeBlockXR.{u}) t g)
    (operationRoleUnit : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t →
      ∀ g, 6 ≤ g → g < 77 →
        RoleUnitStep.{u} (· ∈ RoleOps.opRoles) (StoreX NativeBlockXR.{u}) ρ t g)
    (standardAxiomRoleUnit : ∀ calls t ρ Rs, Run calls t ρ Rs → AllBound t →
      ∀ g, 6 ≤ g → g < 77 →
        RoleUnitStep.{u} (· ∈ standardAxioms) (StoreX NativeBlockXR.{u}) ρ t g)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} NativeBlockXR.{u} fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} NativeBlockXR.{u} fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} NativeBlockXR.{u} fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} NativeBlockXR.{u} fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} NativeBlockXR.{u} fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} NativeBlockXR.{u} fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (oneTypeBlockOffNativeRoute : WalkedUnitStep.{u} NativeBlockXR.{u} fun calls _ E₀ B cb =>
      ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ¬ NativeRouteAt calls B)
    (otherBlock : WalkedUnitStep.{u} NativeBlockXR.{u} fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ ¬ DefnBlock ms ∧
        ∀ ind : Ixon.Inductive, ms ≠ #[.indc ind]) :
    CircuitComposed.{u} :=
  circuitComposed_of_parts bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
    groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit
    (standaloneDefinition_of_keepsValuesKeyed
      fun _ E htwf => keepsValuesKeyed_nativeBlockXR htwf E)
    standaloneTheoremOrOpaque standaloneRecursor definitionBlock nativeBlockTelescope
    nativeBlockAlias nativeBlockOtherTelescope oneTypeBlockOffNativeRoute otherBlock

end IxVM.Refinement.Endpoint
