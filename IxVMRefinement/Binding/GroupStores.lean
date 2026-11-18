import IxVMRefinement.Binding.StoreStanding
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Binding.RootSafety
import IxVMRefinement.Binding.StoreReads
import IxVMRefinement.Assembly.TypingBasisInv
import IxVMRefinement.Binding.RunFamilies
import IxVMRefinement.Binding.StoreOpOrder

/-! # The stores of a binding run: the sequence and what is left of its clauses

`GroupStoresOfRun calls` (`IxVMRefinement.Binding.ClaimExport`) from the store sequence
`groupStore t E₀ Pay` over the run's records at the run's payload (`runPayload`), the clauses
proved of it in
`IxVMRefinement.Binding.RunStores` and `IxVMRefinement.Binding.StoreClausesWalk`, and the
clauses that are left, named in `RemainingStoreClauses`.

* `basisRolesStored_of_pinned`: at a table that pins the prelude, the bound record of a walked
  role of a group below 6 is a basis row.
* `RemainingStoreClauses t E₀ Pay`: what is not proved of the sequence: two facts of the
  operation order the circuit does not check today (`blockSteps`, in the well-founded block;
  `payloadOps`, the records the payload reaches), from which the clauses `opsOwn` and
  `unitsLast` are proved (`IxVMRefinement.Binding.StoreOpOrder`). The reading clause of
  `AdmitsReads` is proved (`groupStore_reads`). The safety
  of the roots
  (`RootsAndTheoremsSafe`, `rootsAndTheoremsSafe_of_run`; with `certRefs_of_run`, `RootsSafe`)
  is proved of every run (`IxVMRefinement.Binding.RootSafety`), and the clauses `logic`
  and `standing` are proved (`logic_of_rootsSafe`, `standing_of_rootsSafe`). The two facts
  about the run's records the proved clauses read are proved
  (`IxVMRefinement.Binding.StoreFieldsRun`):
  the basis rows are records the run loaded as the basis store holds them (`basisRows_of_run`),
  and the record a standard axiom is bound to is a safe axiom record (`axiomRoles_of_run`).
* `RemainingStoreClausesOfRun calls`: `RemainingStoreClauses` at the run's records and payload,
  and what is left of the run's family checks (`RemainingFamilyClauses`,
  `IxVMRefinement.Binding.RunFamilies`), at every table the run's binding claim admits and
  validates, in the alternative without a collision.
* `groupStoresOfRun_of_remaining`: `GroupStoresOfRun calls` from `RemainingStoreClausesOfRun`.
  Every other clause of every group's admission is proved; the rank of a group is the walk's
  (`walkRank`, `groupRanked_walk`) where the group has no payload, and the family form's
  clauses (`ClosureFam`, `FamilyAdmits`) are given by `families_of_remaining`.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

set_option maxRecDepth 100000 in
private theorem basis_group_walked (r : Ix.Kernel.Role) :
    Ix.SpecDigest.groupOf r < 6 → walkedRole r = true → r ∈ TableInhabit.basisRoleOrder := by
  cases r <;> decide +kernel

/-- **At a table that pins the prelude, the bound record of a walked role of a group below 6 is
a basis row.** -/
theorem basisRolesStored_of_pinned {t : Ix.Kernel.RoleTable} (hpre : PreludePinned t) :
    BasisRolesStored t := by
  intro r hlt hw a had
  have hr : r ∈ TableInhabit.basisRoleOrder := basis_group_walked r hlt hw
  have hrows := List.all_eq_true.mp basisRoles_rows r hr
  simp only [← addressOf_basis hpre hr, had] at hrows
  have hrec : (recordOf basisStore a).isSome = true := StoreInhabit.isSome_of_hasKey hrows
  cases hg : basisStore.consts.get? a with
  | none =>
    unfold recordOf at hrec
    rw [hg] at hrec
    exact absurd hrec (by simp)
  | some lc => rfl

/-- **What is left of the store sequence's clauses**, over the run's records `E₀`: two facts about
the operation order that the circuit does not check today. With them the clauses `opsOwn` and
`unitsLast` are proved at every group (`groupStore_opsOwn`, `groupStore_unitsLast`,
`IxVMRefinement.Binding.StoreOpOrder`): below the well-founded block from
`KernelRoles::assert_op_reached_in_order` in `KernelRoles::walk_ctx`, from limit 41 on because
every operation is in force (`walkStepsOrdered_of_run`).

Status: stated only; nothing proves either field of any run. (The safety of the roots, which
this structure held as `rootsSafe`, is proved of every run: `rootsAndTheoremsSafe_of_run`; so is
the reading clause it held as `reads`: `groupStore_reads`.)
* `blockSteps`: in the well-founded block (groups 33 to 40, validated at limit 33, where
  `walk_ctx`'s assertion is off), every reference the group's walk follows is bound to no
  operation of the group or a later one (`WalkStepsOrdered`). Producer: the operation-order scan
  (`KernelRoles::op_order_scan`) changed to go on through the anchors no validation walks and to
  refuse a call at an operation neither in force nor needed, instead of entering it: its
  regenerated observation (`RoleVal.OpOrderScanStep` in that form), the specifications of
  `op_order_scan_except` and of the two call sites in `validate_op` and `validate_op_equations`,
  and an induction showing that the scan follows every reference the walk follows up to a stop,
  behind which the records were walked by an earlier group (`WalkStepsOrdered` at that group).
* `payloadOps`: below limit 41, a record the group's payload reaches (`PayReach`: a family
  check's family record, advice records, container recursors, and what they reference that is
  not covered) is bound to no operation of the group or a later one. No walk and no scan of
  today's circuit passes these records. Producer: the same scan extended to the records a
  family's payload reaches. From limit 41 on it holds of every run (`payloadOpEarlier_all`). -/
structure RemainingStoreClauses (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) :
    Prop where
  blockSteps : ∀ g, 33 ≤ g → g ≤ 40 → WalkStepsOrdered t E₀ g
  payloadOps : ∀ g, 6 ≤ g → g < 41 → ∀ x, PayReach t E₀ Pay g x → OpEarlier t g x

/-- **What is left of the store sequence's clauses, for a run**: at every table that bytes the
run hashed admit at a binding address, binding every role, pinning the prelude and with every
role of the 77 groups validated by the run, the run's records without a collision have
`RemainingStoreClauses` at the run's payload (`runPayload`), and what is left of the run's
family checks (`RemainingFamilyClauses`). -/
def RemainingStoreClausesOfRun (calls : List (Call F)) : Prop :=
  ∀ (a : _root_.Address) (tb : ByteArray) (t : Ix.Kernel.RoleTable),
    Hashed calls tb →
    Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t →
    AllBound t → PreludePinned t →
    (∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r) →
    CollisionFreeRun calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) →
    RemainingStoreClauses t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) (runPayload calls a t) ∧
      RemainingFamilyClauses calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls)

/-- **The stores of a binding run, from what is left of the sequence's clauses**: for every run,
`GroupStoresOfRun calls` with the stores `groupStore t E₀ (runPayload calls a t)` over the run's
records, at each group a rank of its new records (`GroupRanked`: the walk's rank where the group
has no payload, `RemainingFamilyClauses.payloadRanked` where it has one), and the run's family
selection (`runFamOf`, `runAdv`, `runCont`), if the run's records without a collision have
`RemainingStoreClauses` and `RemainingFamilyClauses` (`RemainingStoreClausesOfRun`). -/
theorem groupStoresOfRun_of_remaining {calls : List (Call F)}
    (hrem : RemainingStoreClausesOfRun calls) :
    GroupStoresOfRun calls := by
  intro V extra hextra a tb t htb hadm hall hpin hval
  by_cases hcol : V.HashedCollision extra calls
  · exact Or.inl hcol
  right
  have hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂ := by
    rcases Claim.noColl_or_hashedCollision V extra calls with h | h
    · exact absurd h hcol
    · exact h
  have hw0 : Claim.WalkedL6 calls t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) [] :=
    Claim.walkedL6_envOfRecs (seeds := []) hnoColl [] hadm (by simp)
      (by intro r hr; cases hr)
  have hload : LoadedBy calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    Claim.envOfRecs_loadedBy (t := t) ⟨a, tb⟩ calls []
  have hS := LoadedReads.RunStore.of_walkedL6 hload hw0
  have hH := LoadedReads.hashedRecordsStored_of_walkedL6 hw0
  have hC : CollisionFreeRun calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    collisionFreeRun_of_no_collision hextra hcol hS hH
  have hR := hrem a tb t htb hadm hall hpin hval hC
  have hb := basisRows_of_run hC hpin hval
  have hax := axiomRoles_of_run hC hval
  have hbr : BasisRolesStored t := basisRolesStored_of_pinned hpin
  have hcheck : t.check = .ok () :=
    ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
  have hroots : RootsSafe t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    RootsSafe.of_run hC hval (rootsAndTheoremsSafe_of_run hC hval)
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  obtain ⟨hRS, hRF⟩ := hR
  have hP := hRF.payloadFacts
  have hws : ∀ k, ∃ recs, GroupWalked calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) k recs :=
    fun k => groupWalked_exists hH (hvalAll k)
  have hrk : ∀ g, ∃ r : _root_.Address → Nat, 6 ≤ g → g < 77 →
      GroupRanked t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) (runPayload calls a t) g
        (runFamOf calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) g) (runAdv calls a t g)
        (runCont calls a t g) r := by
    intro g
    by_cases hr : 6 ≤ g ∧ g < 77
    · by_cases hpay : ∃ B x, runPayload calls a t g B x
      · obtain ⟨r, hr'⟩ := hRF.payloadRanked g hr.1 hr.2 hpay
        exact ⟨r, fun _ _ => hr'⟩
      · exact ⟨_, fun _ _ => groupRanked_walk hC hb hbr hax hP hws hr.1
          (Classical.choose_spec (hws g)) (fun B x h => hpay ⟨B, x, h⟩)
          (fun B rb h => runFamOf_payload h)⟩
    · exact ⟨fun _ => 0, fun h6 h77 => absurd ⟨h6, h77⟩ hr⟩
  refine ⟨fun g => Classical.choose (hrk g),
    groupStore t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) (runPayload calls a t),
    groupStore_basis_consts, groupStore_basis_blobs, fun g hg6 hg => ⟨?_, ?_, ?_⟩⟩
  · have hw := Classical.choose_spec (hws g)
    have hrank := Classical.choose_spec (hrk g) hg6 hg
    exact
      { mono := groupStore_mono hb hg6
        monoBlobs := groupStore_monoBlobs hg6
        loaded := groupStore_loaded hb (Nat.le_succ_of_le hg6)
        loadedBlobs := groupStore_loadedBlobs (Nat.lt_succ_of_le hg6)
        hashed := groupStore_hashed hS hb (Nat.lt_succ_of_le hg6)
        usedClosed :=
          groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6)
        committed := groupStore_committed hC hb (Nat.le_succ_of_le hg6)
        zeroFree := groupStore_zeroFree hC hb (Nat.lt_succ_of_le hg6)
        rankUsed := hrank.used
        rankOwner := hrank.owner
        projMember := groupStore_projMember hC hb hax hP hg6 hw
        standing := standing_of_rootsSafe hC hb hpin hP hval hroots
          g hg6 hg
        logic := logic_of_rootsSafe hC hb hP hval hroots g hg6 hg
        validated := fun _ _ => trivial
        kept := groupStore_kept hC hb hax hg6 hw
        opsOwn := groupStore_opsOwn hC hb hax hP hcheck hvalAll hg6 hw
          (walkStepsOrdered_all hC hvalAll hRS.blockSteps g)
          (payloadOpEarlier_all hRS.payloadOps g hg6)
        unitsLast := groupStore_unitsLast hC hb hax hP hpin hws hg6 (hvalAll g) hw
          (walkStepsOrdered_all hC hvalAll hRS.blockSteps g)
          (payloadOpEarlier_all hRS.payloadOps g hg6)
        evidenceRefs := groupStore_evidenceRefs hC hb hbr hax hP hws hg6 hw }
  · exact
      { blobs := groupStore_reads_blobs (Nat.lt_succ_of_le hg6)
        reads := groupStore_reads hcheck hC hb hbr hax hP hws hg6 }
  · exact ⟨_, _, _, families_of_remaining (rk := fun g => Classical.choose (hrk g)) hC hb hax hRF
      hcheck hroots hpin hg6 hg (hvalAll g) (Classical.choose_spec (hws g))
      (Classical.choose_spec (hrk g) hg6 hg) (payloadOpEarlier_all hRS.payloadOps g hg6)
      (groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6))⟩

end IxVM.Refinement.Binding
