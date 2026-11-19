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

/-! # The proved steps of the kinds of top-walked unit

The steps of the kinds of top-walked unit that are proved at the fold's clause, stated as
`WalkedUnitStep`, and the case split of a top-walked unit by the form of its record. The
composed statement (`IxVMRefinement.Endpoint.ComposedResidual`) takes them through the typing
half over the family graph (`IxVMRefinement.FamilyGraph.Composition`), which imports this module
and is imported by the composed statement.

* `unitSteps_of_kinds`: what every unit's step reads of the walk (the table's check, the run
  store, the store the step runs against and its coverage of the run's hashed records
  (`canonicalHashCoverage_frame`), the inert clause, the cover clause (from `coverAt_of_graph`
  and `Claim.TopWalk.need`), the check of the record at the walk's limit, that the witness's
  environment stores none of the record's constant addresses and that their keys are free
  (`keyFree_of_not_stored`), and for a block of one inductive type its member and constructor
  projection records), and the case split of a unit by the form of its record, for a fold in
  which every top-walked unit has a plain `UnitStep`;
* `standaloneDefinition_foldExtra`: the step of a standalone definition, at either limit (from
  `unitStep_defn_foldExtra`);
* `standaloneTheoremOrOpaque_foldExtra`, `definitionBlock_foldExtra`: the step of a standalone
  theorem or opaque record and the step of a non-empty block of definitions, at either limit
  (from the value step stated once for both folds, `ValueUnitStep`);
* `freshRecursorMajorNotBasis_walked`, `standaloneRecursor_of_freshNotBasis`: the step of a
  standalone recursor, at any limit (from `unitStep_recLate_walked`, with the basis exclusion at
  a fresh record from `recMajorFreshNotBasis_of_walk`): the check's output at the family the
  registry reads at the parent that heads the record's major premise (`recLateOut_of_walk`: a
  family with a telescope former or one whose former only head-reduces to a telescope), and the
  parent itself, which the circuit's route reads as a stored former of a native block
  (`recParent_of_arm_tied`). **The case of a standalone recursor with no native parent is
  empty**: when the recursor's family block is modeled, the `Rec` arm of `check_const` runs
  `check_family` at the recursor's own record, which refuses at a standalone record (the record
  is its own block, `family_recs` gives one recursor and `check_recs` asks for at least two;
  `Claim.familyCheckRefused_of_recr`), and `check_recursor_member` asserts that the block of the
  major premise's parent is not modeled. Three lemmas take that refusal as a premise, which the
  arm facts carry (`Typing.check_const_rec_route`, `Typing.check_const_rec_arm`,
  `Claim.TopWalkCore.recFamilyNative`: each closes the `Rec_other` path of `check_const` by it),
  and two read the second assertion (`Typing.native_rec_route_calls`,
  `Typing.native_rec_member_full`: the member check has one path, with the route's answer `0`).
  A recursor of a mutual or nested family is checked through its family record, by the family's
  step, not by this one. -/

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
because the circuit's family check refuses a modeled family at a standalone record (module
docstring). -/
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

end IxVM.Refinement.Endpoint
