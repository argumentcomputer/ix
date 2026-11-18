import IxVMRefinement.Assembly.NativeBlockUnitStep
import IxVMRefinement.Assembly.NativeAliasWalked
import IxVMRefinement.FamilyGraph.CheckedUnit

/-! # The checked unit of a block whose former is declared at its telescope

The composed statement takes, for each kind of top-walked unit, the unit's step for the fold's
clause from the facts the walk hands every unit (`Endpoint.WalkedUnitStep`). A record that only
a family check checks needs the same step and is not top-walked. This module proves the step of
a one-type native block whose former is declared at its telescope, the ordinary inductive type,
from what the run gives of the unit's own record however the run came to check it, and from one
reading of a run, a closed proposition: `Core.ProjGuardRunReading`, the reading of a projection
guard's run.

* `nativeBlockTelescope_checked`: the step of every checked unit of the kind
  (`CheckedUnitStep`): from a step context, the record in Lean's logic, the kind, the table's
  check, the run store, the step store's coverage of the run's hashed records, and what the run
  gives of the unit's own record (`CheckedUnit`). Neither the walk nor its graph is read, nor
  that the record is top-walked.
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
that satisfies the link laws, from the reading of a projection guard's run (module docstring). A block record
is never checked as a record, so the member was checked. -/
theorem nativeBlockTelescope_checked {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hread : Core.ProjGuardRunReading) :
    CheckedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind := by
  intro calls bAddr t E₀ lim R envT E hctx B cb hc hlog hkind ht hS hcov hcanon hu
  obtain ⟨ind, hrec, hnat, htele⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hu.checked 0 (by simp)
  exact unitStep_nativeBlockTele hL ht hS hctx.toStepStore hrec hmem hnat htele hu.keys hu.inert
    hu.cover hcanon hcov hread

/-- **The step of every top-walked one-type native block whose former is declared at its
telescope keeps the fold's clause**: what the walk hands a unit is what a checked unit's step
asks (`walkedUnitStep_of_checked`). -/
theorem nativeBlockTelescope_walked {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hread : Core.ProjGuardRunReading) :
    Endpoint.WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind :=
  walkedUnitStep_of_checked (nativeBlockTelescope_checked hL hread)

end IxVM.Refinement.Typing
