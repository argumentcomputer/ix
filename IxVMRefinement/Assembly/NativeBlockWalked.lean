import IxVMRefinement.Assembly.NativeBlockUnitStep
import IxVMRefinement.Assembly.NativeAliasWalked
import IxVMRefinement.Endpoint.WalkedUnit

/-! # The walked unit of a block whose former is declared at its telescope

The composed statement takes, for each kind of top-walked unit, the unit's step for the fold's
clause from the facts the walk hands every unit (`Endpoint.WalkedUnitStep`). This module proves
that obligation for a one-type native block whose former is declared at its telescope, the
ordinary inductive type, from two readings of a run, both closed propositions:

* `Core.ProjGuardRunReading`: the reading of a projection guard's run;
* `Core.CheckedSortsRunReading`: the reading of the classifier's field loop for given sorts.

`nativeBlockTelescope_walked` is the obligation of the composed statement for this kind of
unit, for any link that satisfies the link laws, at the walk's limit under either validator.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

/-- **The step of every top-walked one-type native block whose former is declared at its
telescope keeps the fold's clause**, at the walk's limit under either validator, for any link
that satisfies the link laws, from the two readings of a run (module docstring). A block
record is never checked as a record, so the walk checked the member. -/
theorem nativeBlockTelescope_walked {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hread : Core.ProjGuardRunReading)
    (hfields : Core.CheckedSortsRunReading) :
    Endpoint.WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx B cb hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ind, hrec, hnat, htele⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hchk 0 (by simp)
  exact unitStep_nativeBlockTele hL ht hS hst hrec hmem hnat htele hkeys hinert hcover hcanon
    hread hfields

end IxVM.Refinement.Typing
