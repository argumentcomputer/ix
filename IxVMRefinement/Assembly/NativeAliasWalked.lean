import IxVMRefinement.Assembly.NativeAliasInstallOut
import IxVMRefinement.Claim.TopProj

/-! # The walked unit of a block whose former is declared at a definition

The composed statement takes, for each kind of top-walked unit, the unit's step for the fold's
clause from the facts the walk hands every unit. This module proves that obligation for a
one-type native block whose former is declared at a definition. It is stated with the walk's
facts written out, so that the statement of the composed result can use it: it is the
obligation of that statement for this kind of unit, at the fold's clause at the opened head
trace.

* `memberChecked_of_walked_block`: the walk hands a unit either the check of every member of
  its block or the check of its record; a block record is never checked as a record
  (`Claim.checked_not_block`), so at a block record the walk checked every member. Stated for
  any block record.
* `nativeBlockAlias_walked`: **the obligation, with no premise**: at the walk's limit under
  either validator, from the member check the walk hands, `unitStep_nativeBlockAlias`.
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
either validator. For a walk export at the binding `bAddr`, the assembly's reading of it, a
step context and a top-walked record `c` at `A` in Lean's logic that is such a block, from what
the walk hands every unit: the table's check, the run store, that the run's hashed records are
stored, the store the step runs against and its coverage of the run's hashed records, the
inert and cover clauses, the walk's check of the record at the walk's limit, that the witness's
environment stores none of the record's constant addresses, and that their keys are free. -/
theorem nativeBlockAlias_walked :
    ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
      (seeds : List _root_.Address) (E₀ : Ixon.Env) (lim : Option Nat)
      (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
      Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank → TopGraph t E₀ seeds Top rank →
      ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env),
        StepCtx.{u} calls t R envT E₀ E →
        ∀ (A : _root_.Address) (c : Ixon.Constant),
          Top A → recordOf E₀ A = some c → InLogic c →
          (∃ ind : Ixon.Inductive,
            BlockUnitRecord E₀ A c ind ∧ NativeRouteAt calls A ∧ FormerAtAlias t E₀ A c ind) →
          t.check = .ok () → LoadedReads.RunStore calls E₀ →
          LoadedReads.HashedRecordsStored calls E₀ → StepStore calls t E₀ E →
          L1.CanonicalHashCoverage E calls →
          InertClause t c → (∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) →
          ((∃ ms, c.info = .muts ms ∧
              ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
            Claim.CheckedLimAt calls bAddr t A lim) →
          (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
          (∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)) →
          UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim A c := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx B cb hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ind, hrec, hnat, halias⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hchk 0 (by simp)
  exact unitStep_nativeBlockAlias ht hS hctx hrec hmem hnat halias hkeys hinert hcover hcanon

end IxVM.Refinement.Typing
