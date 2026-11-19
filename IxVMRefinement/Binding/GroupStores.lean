import IxVMRefinement.Binding.StoreStanding
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Binding.RootSafety
import IxVMRefinement.Binding.StoreReads
import IxVMRefinement.Assembly.TypingBasisInv
import IxVMRefinement.Binding.RunFamilies
import IxVMRefinement.Binding.StoreOpOrder
import IxVMRefinement.Binding.PayloadClosed
import IxVMRefinement.Binding.PayloadRanked

/-! # The stores of a binding run: the sequence and what is left of its clauses

`GroupStoresOfRun calls` (`IxVMRefinement.Binding.ClaimExport`) from the store sequence
`groupStore t E₀ Pay` over the run's records at the run's payload (`runPayload`), the clauses
proved of it across `RunStores`, `StoreClausesWalk`, `StoreOpOrder`, `OpOrderBlock`,
`PayloadClosed`, and `PayloadRanked`, and the remaining family clauses (`RemainingFamilyClauses`:
`familyFlat` and `familyForm`).

* `basisRolesStored_of_pinned`: at a table that pins the prelude, the bound record of a walked
  role of a group below 6 is a basis row.
* `RemainingStoreClausesOfRun calls`: what is left of the run's family checks
  (`RemainingFamilyClauses`, `IxVMRefinement.Binding.RunFamilies`: `familyFlat` and `familyForm`),
  at every table the run's binding claim admits and validates, in the alternative without a
  collision.
* `groupStoresOfRun_of_remaining`: `GroupStoresOfRun calls` from `RemainingStoreClausesOfRun`.
  Every store-sequence, operation-order, payload-closure, ranking, claimed-family, run-facts, and
  payload-checked clause of every group's admission is proved (`blockSteps_of_run`,
  `payloadFacts_of_run`, `payloadOps_of_run`, `claimed_of_run`, `payloadChecked_of_run`,
  `runFactsLeft_of_run`, `payloadRanked_of_run`), and the family form's clauses (`ClosureFam`,
  `FamilyAdmits`) are assembled by `families_of_remaining`.
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
private theorem basis_group_all (r : Ix.Kernel.Role) :
    Ix.SpecDigest.groupOf r < 6 → r ∈ TableInhabit.basisRoleOrder := by
  cases r <;> decide +kernel

/-- **At a table that pins the prelude, the bound record of every role of a group below 6 is a
basis row.** -/
theorem basisRolesStored_of_pinned {t : Ix.Kernel.RoleTable} (hpre : PreludePinned t) :
    BasisRolesStored t := by
  intro r hlt a had
  have hr : r ∈ TableInhabit.basisRoleOrder := basis_group_all r hlt
  have hrows := List.all_eq_true.mp basisRoles_rows r hr
  simp only [← addressOf_basis hpre hr, had] at hrows
  have hrec : (recordOf basisStore a).isSome = true := StoreInhabit.isSome_of_hasKey hrows
  cases hg : basisStore.consts.get? a with
  | none =>
    unfold recordOf at hrec
    rw [hg] at hrec
    exact absurd hrec (by simp)
  | some lc => rfl

/-- **What is left of the store sequence's clauses, for a run**: for a bounded run, at every
table that bytes the run hashed admit at a binding address, binding every role, pinning the
prelude and with every role of the 77 groups validated by the run, the run's records without a
collision have `RemainingFamilyClauses` (`familyFlat` and `familyForm`). The clauses are asked of
bounded runs only (`Bounded calls`), the only runs the export consumes (`GroupStoresOfRun`). -/
def RemainingStoreClausesOfRun (calls : List (Call F)) : Prop :=
  IxVM.Consistency.Bounded calls →
  ∀ (a : _root_.Address) (tb : ByteArray) (t : Ix.Kernel.RoleTable),
    Hashed calls tb →
    Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t →
    AllBound t → PreludePinned t →
    (∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r) →
    CollisionFreeRun calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) →
    RemainingFamilyClauses calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls)

/-- **The stores of a binding run, from what is left of its family clauses**: for every run,
`GroupStoresOfRun calls` with the stores `groupStore t E₀ (runPayload calls a t)` over the run's
records, the three-tier potential rank (`payloadRanked_of_run`), and the run's family selection
(`runFamOf`, `runAdv`, `runCont`), given `RemainingStoreClausesOfRun` (`familyFlat` and
`familyForm`). -/
theorem groupStoresOfRun_of_remaining {calls : List (Call F)}
    (hrem : RemainingStoreClausesOfRun calls) :
    GroupStoresOfRun calls := by
  intro hbd V extra hextra a tb t htb hadm hall hpin hval
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
  have hRF := hrem hbd a tb t htb hadm hall hpin hval hC
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
  have hws : ∀ k, ∃ recs, GroupWalked calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) k recs :=
    fun k => groupWalked_exists hH (hvalAll k)
  have hstep := runStepStores_of_noCollision t hS hbd hextra hcol
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hblock := blockSteps_of_run hC hvalAll hws
  have hpayOps := payloadOps_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hclaimedAll := claimed_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hrunFactsAll := runFactsLeft_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hpayChkAll := payloadChecked_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hrankedAll := payloadRanked_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hrk : ∀ g, ∃ r : _root_.Address → Nat, 6 ≤ g → g < 77 →
      GroupRanked t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) (runPayload calls a t) g
        (runFamOf calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) g) (runAdv calls a t g)
        (runCont calls a t g) r := by
    intro g
    by_cases hr : 6 ≤ g ∧ g < 77
    · obtain ⟨r, hr'⟩ := hrankedAll g hr.1 hr.2
      exact ⟨r, fun _ _ => hr'⟩
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
          (walkStepsOrdered_all hC hvalAll hblock g)
          (payloadOpEarlier_all hpayOps g hg6)
        unitsLast := groupStore_unitsLast hC hb hax hP hpin hws hg6 (hvalAll g) hw
          (walkStepsOrdered_all hC hvalAll hblock g)
          (payloadOpEarlier_all hpayOps g hg6)
        evidenceRefs := groupStore_evidenceRefs hC hb hbr hax hP hws hg6 hw }
  · exact
      { blobs := groupStore_reads_blobs (Nat.lt_succ_of_le hg6)
        reads := groupStore_reads hcheck hC hb hbr hax hP hws hg6 }
  · exact ⟨_, _, _, families_of_remaining (rk := fun g => Classical.choose (hrk g)) hC hb hax hP hRF
      hcheck hroots hpin hg6 hg hvalAll (Classical.choose_spec (hws g))
      (Classical.choose_spec (hrk g) hg6 hg) (payloadOpEarlier_all hpayOps g hg6)
      (groupStore_usedClosed_all hC hb hbr hax hP hws g hg6)
      (groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6))
      hstep
      (groupStore_unitsLast hC hb hax hP hpin hws hg6 (hvalAll g) (Classical.choose_spec (hws g))
        (walkStepsOrdered_all hC hvalAll hblock g)
        (payloadOpEarlier_all hpayOps g hg6))
      (logic_of_rootsSafe hC hb hP hval hroots g hg6 hg)
      (hclaimedAll g hg6 hg)
      (hrunFactsAll g hg6 hg (fun g => Classical.choose (hrk g)))
      (hpayChkAll g hg6 hg)⟩

end IxVM.Refinement.Binding
