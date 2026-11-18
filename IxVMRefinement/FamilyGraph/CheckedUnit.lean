import IxVMRefinement.Endpoint.WalkedUnit
import IxVMRefinement.Assembly.TypingDefnStep

/-! # What a unit's step reads of the run about its own record

A step of the typing fold is asked of two sorts of records: those the walk reached, and those a
family check checked (its advice records, a container's recursor). The steps of the kinds of
record are the same for both. This module states what a step reads of the run about the unit's
own record, apart from how the run came to check it:

* `CheckedUnit`: the record was checked at the fold's limit (every member of a block, or the
  record); no reference it uses is an inert axiom's; at every environment the fold hands its
  step, the other references it uses are stored; the witness's environment stores none of its
  constant addresses; and their keys are free.
* `CheckedUnitFact Kind Goal`: the fact `Goal` of every checked unit of the kind `Kind`, with
  the facts about the run and the store that do not depend on the unit;
  `CheckedUnitStep X Kind` is it at the unit's step for the carried clause `X`.
* `walkedUnit_of_checked`: a fact about every checked unit of a kind is the fact about every
  top-walked unit of the kind (`Endpoint.WalkedUnit`), which hands exactly `CheckedUnit`.

So a kind's step is stated once, as a `CheckedUnitStep`; the walked form follows, and so does
the step of a unit checked inside a family check, from what that check gives. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **What a step reads of the run about the unit's own record** `c` at `A` (module
docstring). -/
structure CheckedUnit (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (lim : Option Nat)
    (A : _root_.Address) (c : Ixon.Constant) : Prop where
  /-- The check of the record at the limit: every member of a block, or the record. -/
  checked : (∃ ms, c.info = .muts ms ∧
      ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
    Claim.CheckedLimAt calls bAddr t A lim
  /-- No reference the record uses is an inert axiom's. -/
  inert : InertClause t c
  /-- At an environment the fold hands the step, the other used references are stored. -/
  cover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c
  /-- The witness's environment stores none of the record's constant addresses. -/
  fresh : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x
  /-- The keys of the record's constant addresses are free. -/
  keys : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)

/-- **A fact about every checked unit of one kind.** `Kind` reads the run's calls, the table,
the run's store, the unit's address and its record; `Goal` also reads the witness's
environment, the store the step runs against and the limit. The producer of `Goal` is handed a
step context, the record in Lean's logic, the kind, the table's check, the run store, that the
run's hashed records are stored, that the step's store holds every record the run hashed with
its exact decoding, and what the run gives of the unit's own record (`CheckedUnit`). -/
def CheckedUnitFact
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop)
    (Goal : List (Call F) → Ix.Kernel.RoleTable → Ix.Kernel.Env .anon → Ixon.Env → Ixon.Env →
      Option Nat → _root_.Address → Ixon.Constant → Prop) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (lim : Option Nat) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env),
    StepCtx.{u} calls t R envT E₀ E →
    ∀ (A : _root_.Address) (c : Ixon.Constant),
      recordOf E₀ A = some c → InLogic c → Kind calls t E₀ A c →
      t.check = .ok () → LoadedReads.RunStore calls E₀ →
      LoadedReads.HashedRecordsStored calls E₀ → L1.CanonicalHashCoverage E calls →
      CheckedUnit calls bAddr t envT E₀ lim A c →
      Goal calls t envT E₀ E lim A c

/-- **The step of every checked unit of one kind**, for the carried clause `X` at the step's
store, at the limit of the check. -/
def CheckedUnitStep
    (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop) : Prop :=
  CheckedUnitFact.{u} Kind fun _ t envT E₀ E lim A c => UnitStep.{u} (X t E) t envT E₀ E lim A c

/-- **A fact about every checked unit of a kind is the fact about every top-walked unit of the
kind**: what the composition hands a top-walked unit is `CheckedUnit`. -/
theorem walkedUnit_of_checked
    {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop}
    {Goal : List (Call F) → Ix.Kernel.RoleTable → Ix.Kernel.Env .anon → Ixon.Env → Ixon.Env →
      Option Nat → _root_.Address → Ixon.Constant → Prop}
    (h : CheckedUnitFact.{u} Kind Goal) : Endpoint.WalkedUnit.{u} Kind Goal := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  exact h calls bAddr t E₀ lim R envT E hctx A c hc hlog hkind ht hS hcov hcanon
    ⟨hchk, hinert, hcover, hns, hkeys⟩

/-- The step of every checked unit of a kind is the step of every top-walked unit of it. -/
theorem walkedUnitStep_of_checked
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop}
    (h : CheckedUnitStep.{u} X Kind) : Endpoint.WalkedUnitStep.{u} X Kind :=
  walkedUnit_of_checked h

end IxVM.Refinement.Typing
