import IxVMRefinement.Binding.StoreFieldsRun
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Assembly.TypingBasisInv

/-! # The stores of a binding run: the sequence and what is left of its clauses

`GroupStoresOfRun calls` (`IxVMRefinement.Binding.ClaimExport`) from the store sequence
`groupStore t E₀` over the run's records, the clauses proved of it in
`IxVMRefinement.Binding.RunStores` and `IxVMRefinement.Binding.StoreClausesWalk`, and the
clauses that are left, named in `RemainingStoreClauses`.

* `basisRolesStored_of_pinned`: at a table that pins the prelude, the bound record of a walked
  role of a group below 6 is a basis row.
* `RemainingStoreClauses t E₀`: what is not proved of the sequence. One fact about the run's
  records (the basis rows are records the run loaded as the basis store holds them) and five
  clauses (`standing`, `logic`, `opsOwn`, `unitsLast`, and the reading clause of
  `AdmitsReads`). That the record a standard axiom is bound to is a safe axiom record is proved
  (`axiomRoles_of_run`, `IxVMRefinement.Binding.StoreFieldsRun`).
* `groupStoresOfRun_of_remaining`: `GroupStoresOfRun calls` from `RemainingStoreClauses` at
  the run's records, in the alternative without a collision. Every other clause of every
  group's admission is proved: the rank is `walkRank` over a closed list of the records the
  group's validations walked.
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

/-- **What is left of the store sequence's clauses**, over the run's records `E₀`.

Status: stated only; nothing proves any field of any run.
* `basisRows`: the run's store holds the basis rows as the basis store does. Its producer is
  the validation of the groups below 6 at a table that pins the prelude: each of those
  validations loads its role's record, the pin fixes the address, and the alternative without a
  collision fixes the bytes.
* `standing`, `logic`: a new axiom or quotient record is the group's standard axiom; a new
  record is in Lean's logic. The walk's check of an axiom record asks for a standing role in
  force; a walked record's references are guarded against a safe source
  (`Claim.RecordRefsIn.safe`), and a root's safety is asserted by its role's validation.
* `opsOwn`, `unitsLast`: no new record is another group's operation, and none uses the record
  of a role unit of the group: below the well-founded block from
  `KernelRoles::assert_op_reached_in_order` in `KernelRoles::walk_ctx`, in the block from
  `KernelRoles::op_order_scan` as it will be after the next change of the circuit source
  (`RoleVal.OpOrderScanStep`).
* `reads`: a reading over the run's records of a constant address of a new record is a reading
  over the store after the group. -/
structure RemainingStoreClauses (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop where
  basisRows : BasisRowsLoaded E₀
  standing : ∀ g, 6 ≤ g → g < 77 → ∀ a c,
    New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a →
    recordOf (groupStore t E₀ (g + 1)) a = some c → IsAxiomLike c →
    ∃ r ∈ roleGroup g, r ∈ standardAxioms ∧ t.addressOf? r = some a
  logic : ∀ g, 6 ≤ g → g < 77 → ∀ a c,
    New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a →
    recordOf (groupStore t E₀ (g + 1)) a = some c → InLogic c
  opsOwn : ∀ g, 6 ≤ g → g < 77 → ∀ a r,
    New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a → t.addressOf? r = some a →
    r ∈ RoleOps.opRoles → r ∈ roleGroup g
  unitsLast : ∀ g, 6 ≤ g → g < 77 → ∀ x a,
    New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) x →
    UsedRef (groupStore t E₀ (g + 1)) x a → ¬ RoleUnitAt t g a
  reads : ∀ g, 6 ≤ g → g < 77 → ∀ A c x ci₀,
    New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) A →
    recordOf (groupStore t E₀ (g + 1)) A = some c → ConstAddrOf A c x →
    Reads t E₀ x ci₀ → Reads t (groupStore t E₀ (g + 1)) x ci₀

/-- **The stores of a binding run, from what is left of the sequence's clauses**: for every run,
`GroupStoresOfRun calls` with the stores `groupStore t E₀` over the run's records and the rank
`walkRank` over a closed list of the records each group's validations walked, if the run's
records without a collision have `RemainingStoreClauses`. -/
theorem groupStoresOfRun_of_remaining {calls : List (Call F)}
    (hrem : ∀ (a : _root_.Address) (tb : ByteArray) (t : Ix.Kernel.RoleTable),
      Hashed calls tb →
      Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t →
      AllBound t → PreludePinned t →
      (∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r) →
      CollisionFreeRun calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) →
      RemainingStoreClauses t (Claim.runEnv ⟨a, tb⟩ (t := t) calls)) :
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
  have hb := hR.basisRows
  have hax := axiomRoles_of_run hC hval
  have hbr : BasisRolesStored t := basisRolesStored_of_pinned hpin
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  have hws : ∀ k, ∃ recs, GroupWalked calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) k recs :=
    fun k => groupWalked_exists hH (hvalAll k)
  refine ⟨fun g x => walkRank (Classical.choose (hws g)) x,
    groupStore t (Claim.runEnv ⟨a, tb⟩ (t := t) calls), groupStore_basis_consts,
    groupStore_basis_blobs, fun g hg6 hg => ⟨?_, ?_⟩⟩
  · have hw := Classical.choose_spec (hws g)
    exact
      { mono := groupStore_mono hb hg6
        monoBlobs := groupStore_monoBlobs hg6
        loaded := groupStore_loaded hb (Nat.le_succ_of_le hg6)
        loadedBlobs := groupStore_loadedBlobs (Nat.lt_succ_of_le hg6)
        hashed := groupStore_hashed hS hb (Nat.lt_succ_of_le hg6)
        usedClosed := groupStore_usedClosed_all hC hb hbr hax hws (g + 1) (Nat.le_succ_of_le hg6)
        committed := groupStore_committed hC hb (Nat.le_succ_of_le hg6)
        zeroFree := groupStore_zeroFree hC hb (Nat.lt_succ_of_le hg6)
        rankUsed := groupStore_rankUsed hC hb hbr hax hws hg6 hw
        rankOwner := groupStore_rankOwner hC hb hax hg6 hw
        projMember := groupStore_projMember hC hb hax hg6 hw
        standing := hR.standing g hg6 hg
        logic := hR.logic g hg6 hg
        checked := groupStore_checked hC hb hax hg6 hw
        validated := fun _ _ => trivial
        kept := groupStore_kept hC hb hax hg6 hw
        opsOwn := hR.opsOwn g hg6 hg
        unitsLast := hR.unitsLast g hg6 hg }
  · exact
      { blobs := groupStore_reads_blobs (Nat.lt_succ_of_le hg6)
        reads := hR.reads g hg6 hg }

end IxVM.Refinement.Binding
