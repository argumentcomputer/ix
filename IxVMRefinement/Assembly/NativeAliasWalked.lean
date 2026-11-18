import IxVMRefinement.Assembly.NativeAliasInstallOut
import IxVMRefinement.Endpoint.ComposedResidual
import IxVMRefinement.Claim.TopProj

/-! # The walked unit of a block whose former is declared at a definition

The composed statement takes, for each kind of top-walked unit, the unit's step for the fold's
clause from the facts the walk hands every unit (`Endpoint.WalkedUnitStep`). This module
proves that obligation for a one-type native block whose former is declared at a definition.

* `memberChecked_of_walked_block`: the walk hands a unit either the check of every member of
  its block or the check of its record; a block record is never checked as a record
  (`Claim.checked_not_block`), so at a block record the walk checked every member. Stated for
  any block record.
* `nativeBlockAlias_walked`: **the obligation, with no premise**: at either validator's limit,
  from the member check the walk hands, `unitStep_nativeBlockAlias`.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency

/-- **At a block record the walk checked every member**: of the two checks the walk hands a
unit, the check of the record itself does not occur at a block record. -/
theorem memberChecked_of_walked_block {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {bAddr B : _root_.Address} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} {c : Ixon.Constant} {ms₀ : Array Ixon.MutConst}
    (hc : recordOf E₀ B = some c) (hms : c.info = .muts ms₀)
    (hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t B lim) :
    ∀ k, k < ms₀.size → Claim.MemberCheckedLimAt calls bAddr t B ms₀ k lim := by
  rcases hchk with ⟨ms, hms', hall⟩ | hdirect
  · have e : ms = ms₀ := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
    rw [← e]
    exact hall
  · exact (Claim.checked_not_block hS hc hms hdirect).elim

/-- **The step of every top-walked one-type native block whose former is declared at a
definition keeps the fold's clause at the opened head trace**, at the walk's limit under
either validator: the obligation of the composed statement for this kind of unit. -/
theorem nativeBlockAlias_walked :
    Endpoint.WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx B cb hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ind, hrec, hnat, halias⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hchk 0 (by simp)
  exact unitStep_nativeBlockAlias ht hS hctx hrec hmem hnat halias hkeys hinert hcover hcanon

end IxVM.Refinement.Typing
