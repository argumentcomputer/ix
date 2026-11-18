import IxVMRefinement.Claim.TopWalk
import IxVMRefinement.L1.TraceRecords

/-! # The shape of a fact about every top-walked unit of one kind

The composed statement (`Endpoint.circuitComposed_residual`) takes what is still open about a
typing run kind by kind: a fact about every top-walked unit whose record has a given form,
with what holds of every unit handed over. This module holds the two definitions of that
shape, apart from the composition, so that a module which proves or splits such a fact can be
imported by the composed statement:

* `WalkedUnit Kind Goal`: the fact `Goal` of every top-walked unit of the kind `Kind`;
* `WalkedUnitStep X Kind`: `WalkedUnit` at the unit's step for the carried clause `X`.
-/

universe u

namespace IxVM.Refinement.Endpoint

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **A fact about every top-walked unit of one kind**, as the composition asks it. `Kind`
reads the run's calls, the table, the run's store, the unit's address and its record; `Goal`
also reads the witness's environment, the store the step runs against and the walk's limit.
For a walk export at the binding `bAddr`, the assembly's reading of it, a step context and a
top-walked record `c` at `A` in Lean's logic of that kind, the producer of `Goal` is handed
what holds of every unit whose step is asked: the table's check, the run store, that the run's
hashed records are stored, the store the step runs against and that it holds every record the
run hashed with its exact decoding, that no reference the record uses is an inert axiom's, the
cover clause at every environment the skeleton hands the step, the walk's check of the record
at the walk's limit (every member of a block, or the record), that the witness's environment
stores none of the record's constant addresses, and that their keys are free. -/
def WalkedUnit
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop)
    (Goal : List (Call F) → Ix.Kernel.RoleTable → Ix.Kernel.Env .anon → Ixon.Env → Ixon.Env →
      Option Nat → _root_.Address → Ixon.Constant → Prop) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (seeds : List _root_.Address) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
    Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank → TopGraph t E₀ seeds Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env),
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant),
        Top A → recordOf E₀ A = some c → InLogic c → Kind calls t E₀ A c →
        t.check = .ok () → LoadedReads.RunStore calls E₀ →
        LoadedReads.HashedRecordsStored calls E₀ → StepStore calls t E₀ E →
        L1.CanonicalHashCoverage E calls →
        InertClause t c → (∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) →
        ((∃ ms, c.info = .muts ms ∧
            ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
          Claim.CheckedLimAt calls bAddr t A lim) →
        (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
        (∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)) →
        Goal calls t envT E₀ E lim A c

/-- **The step of every top-walked unit of one kind**: `WalkedUnit` at the unit's step for the
carried clause `X` at the step's store, at the walk's limit. -/
def WalkedUnitStep
    (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop) : Prop :=
  WalkedUnit.{u} Kind fun _ t envT E₀ E lim A c => UnitStep.{u} (X t E) t envT E₀ E lim A c

end IxVM.Refinement.Endpoint
