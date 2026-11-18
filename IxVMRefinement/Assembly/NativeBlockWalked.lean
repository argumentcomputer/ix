import IxVMRefinement.Assembly.NativeBlockUnitStep
import IxVMRefinement.Assembly.NativeAliasWalked
import IxVMRefinement.Endpoint.WalkedUnit

/-! # The checked unit of a block whose former is declared at its telescope

The composed statement takes, for each kind of top-walked unit, the unit's step for the fold's
clause from the facts the walk hands every unit (`Endpoint.WalkedUnitStep`). A record that only
a family check checks needs the same step and is not top-walked. This module proves the step of
a one-type native block whose former is declared at its telescope, the ordinary inductive type,
from what the run gives of the unit's own record however the run came to check it, and from two
readings of a run, both closed propositions:

* `Core.ProjGuardRunReading`: the reading of a projection guard's run;
* `Core.CheckedSortsRunReading`: the reading of the classifier's field loop for given sorts.

* `nativeBlockTelescope_checked`: the step from a step context, the record in Lean's logic,
  the kind, the table's check, the run store, the step store's coverage of the run's hashed
  records, the check of the record at the limit (every member of a block, or the record), the
  inert and cover clauses, and the freedom of the keys. Neither the walk nor its graph is read,
  nor that the record is top-walked.
* `nativeBlockTelescope_walked`: the obligation of the composed statement for this kind of
  unit, for any link that satisfies the link laws, at the walk's limit under either validator.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

/-- **The step of every checked one-type native block whose former is declared at its telescope
keeps the fold's clause**, at the limit of its check under either role context, for any link
that satisfies the link laws, from the two readings of a run (module docstring). A block record
is never checked as a record, so the member was checked. -/
theorem nativeBlockTelescope_checked {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hread : Core.ProjGuardRunReading)
    (hfields : Core.CheckedSortsRunReading) :
    ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
      (E₀ : Ixon.Env) (lim : Option Nat) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
      (E : Ixon.Env),
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant),
        recordOf E₀ A = some c → InLogic c →
        (∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ A c ind ∧ NativeRouteAt calls A ∧ FormerAtTele t E₀ A c ind) →
        t.check = .ok () → LoadedReads.RunStore calls E₀ →
        LoadedReads.HashedRecordsStored calls E₀ → L1.CanonicalHashCoverage E calls →
        ((∃ ms, c.info = .muts ms ∧
            ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
          Claim.CheckedLimAt calls bAddr t A lim) →
        InertClause t c → (∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) →
        (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
        (∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)) →
        UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c := by
  intro calls bAddr t E₀ lim R envT E hctx B cb hc hlog hkind ht hS hcov hcanon hchk hinert
    hcover hns hkeys
  obtain ⟨ind, hrec, hnat, htele⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hchk 0 (by simp)
  exact unitStep_nativeBlockTele hL ht hS hctx.toStepStore hrec hmem hnat htele hkeys hinert
    hcover hcanon hread hfields

/-- **The step of every top-walked one-type native block whose former is declared at its
telescope keeps the fold's clause**: what the walk hands a unit is what
`nativeBlockTelescope_checked` asks. -/
theorem nativeBlockTelescope_walked {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hread : Core.ProjGuardRunReading)
    (hfields : Core.CheckedSortsRunReading) :
    Endpoint.WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx B cb hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  exact nativeBlockTelescope_checked hL hread hfields calls bAddr t E₀ lim R envT E hctx B cb hc
    hlog hkind ht hS hcov hcanon hchk hinert hcover hns hkeys

end IxVM.Refinement.Typing
