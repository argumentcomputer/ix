import IxVMRefinement.Endpoint.ComposedResidual
import IxC.Kernel.Audit.Axioms

/-! # The open obligations of the composed statement, printed

`IxVM.Refinement.Endpoint.circuitComposed_residual` proves the public statement
`IxVM.Consistency.CircuitComposed` from one named hypothesis for each obligation of the proof
that has no unconditional theorem yet. This module prints its statement (`#check`), the shape of
a unit kind's step (`#print` of `WalkedUnit` and `WalkedUnitStep`, the form the composition
takes the kinds of a top-walked unit in, and of `CheckedUnitFact` and `CheckedUnitStep`, the
form of a kind's step for every checked unit) and the axioms it reaches. A change to any of them
fails the build.

How to read it. The explicit arguments are the open obligations: the first two are the
binding half's, and the third is the typing half's (the step of a twin). The family graph, inner
checks, canonical twin selection (`Typing.familyGraphRowInnerFamT_closed`), and both family-check
steps (`FamilyAlias.closureFamilyCheck_of_run`, `FamilyAlias.familyBlockCheckRow_of_run`) are
proved unconditionally. The binding half's run
predicate is `IxVM.Refinement.Binding.BindingRun`. The first argument is the part of the binding
claim's export that remains (`familyFlat` and `familyForm`; the loaded table's admission, prelude
pin, group store closures, and remaining family clauses are theorems). The second is the closure's
remaining step in the family form (a twin; the step of a unit with no family record and no twin is
a theorem, `Binding.closureUnitSteps_bindingRun`, and the step of a new block with its selected
family record is a theorem, `FamilyAlias.closureFamilyCheck_of_run`). The run predicate holds the prelude pin, the store after the
basis groups, the admission of each group with its reading clause and the group's family checks,
so the fold's hypotheses about those are its projections and are not listed; the basis groups'
family form, the stored shapes of groups with no role unit (`Binding.groupWithoutRoleUnit_bindingRun`),
the role unit of an operation (`Binding.operationRoleUnitW_of_projFree` from
`Binding.certProjFree_bindingRun`) and the standard axioms' role unit are theorems. A hypothesis
is typed by the interface its obligation has today, so the theorem claims nothing by itself; it
fixes how the parts compose and what is left.

How to change it. When a theorem produces a hypothesis, apply it inside
`circuitComposed_residual`, delete the hypothesis and update the expected output here in the
same commit. When the interface of an obligation changes, retype its hypothesis the same way.
The proof is complete when the theorem has no explicit argument.

What this module does not print. A definition that a hypothesis reads
(`RemainingStoreClausesOfRun`, `BindingRun`, `AtGroups`,
`ClosureTwinSteps`, `FamilyRecon.RFormS`,
`FamilyTwinRowFam`, `FoldExtra`, `UnitStep` and the others) appears by name only: its own
module holds it. The public statement and what it reads are printed in
`Ix.IxVM.ConsistencyAudit` and `Ix.IxVM.ConsistencyModelAudit`. The module is outside any
namespace, so every name prints in full. -/

/-! ## The theorem -/

/--
info: IxVM.Refinement.Endpoint.circuitComposed_residual.{u}
  (groupStores :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
      IxVM.Refinement.Binding.RemainingStoreClausesOfRun calls)
  (closureTwinSteps :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
      IxVM.Refinement.Binding.AtGroups (IxVM.Refinement.Binding.BindingRun calls)
        (IxVM.Refinement.Binding.ClosureTwinSteps IxVM.Refinement.Typing.FormerOpenTraceAt calls))
  (familyTwin :
    IxVM.Refinement.Typing.TwinFamily.FamilyTwinRowFam IxVM.Refinement.Binding.FamilyRecon.RFormS
      IxVM.Refinement.Typing.FormerOpenTraceAt) :
  IxVM.Consistency.CircuitComposed
-/
#guard_msgs in
#check IxVM.Refinement.Endpoint.circuitComposed_residual

/-! ## The shape of a typing hypothesis -/

/--
info: def IxVM.Refinement.Endpoint.WalkedUnit.{u} : (List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
    Ix.Kernel.RoleTable → Ixon.Env → Address → Ixon.Constant → Prop) →
  (List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
      Ix.Kernel.RoleTable →
        Ix.Kernel.Env Ix.Kernel.Mode.anon → Ixon.Env → Ixon.Env → Option ℕ → Address → Ixon.Constant → Prop) →
    Prop :=
fun Kind Goal =>
  ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) (bAddr : Address) (t : Ix.Kernel.RoleTable)
    (seeds : List Address) (E₀ : Ixon.Env) (lim : Option ℕ) (Top : Address → Prop) (rank : Address → ℕ),
    IxVM.Refinement.Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank →
      IxVM.Refinement.Typing.TopGraph t E₀ seeds Top rank →
        ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env Ix.Kernel.Mode.anon) (E : Ixon.Env),
          IxVM.Refinement.Typing.StepCtx calls t R envT E₀ E →
            ∀ (A : Address) (c : Ixon.Constant),
              Top A →
                IxVM.Consistency.recordOf E₀ A = some c →
                  IxVM.Consistency.InLogic c →
                    Kind calls t E₀ A c →
                      t.check = Except.ok () →
                        IxVM.Refinement.LoadedReads.RunStore calls E₀ →
                          IxVM.Refinement.LoadedReads.HashedRecordsStored calls E₀ →
                            IxVM.Refinement.Typing.StepStore calls t E₀ E →
                              IxVM.Refinement.L1.CanonicalHashCoverage E calls →
                                IxVM.Refinement.Typing.InertClause t c →
                                  (∀ (env : Ix.Kernel.Env Ix.Kernel.Mode.anon),
                                      IxVM.Refinement.Typing.HandedRefs t envT E₀ A c env →
                                        IxVM.Refinement.Typing.CoverAt t env c) →
                                    (∃ ms,
                                          c.info = Ixon.ConstantInfo.muts ms ∧
                                            ∀ k < ms.size,
                                              IxVM.Refinement.Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
                                        IxVM.Refinement.Claim.CheckedLimAt calls bAddr t A lim →
                                      (∀ (x : Address),
                                          IxVM.Refinement.Typing.ConstAddrOf A c x →
                                            ¬IxVM.Refinement.Typing.StoredAt t envT x) →
                                        (∀ (x : Address),
                                            IxVM.Refinement.Typing.ConstAddrOf A c x →
                                              IxVM.Refinement.Decl.KeyFree (IxVM.Consistency.keyOf t x)) →
                                          Goal calls t envT E₀ E lim A c
-/
#guard_msgs in
#print IxVM.Refinement.Endpoint.WalkedUnit

/--
info: def IxVM.Refinement.Endpoint.WalkedUnitStep.{u} : (Ix.Kernel.RoleTable →
    Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop) →
  (List (Aiur.Generic.SourceSemantics.Call IxVM.F) → Ix.Kernel.RoleTable → Ixon.Env → Address → Ixon.Constant → Prop) →
    Prop :=
fun X Kind =>
  IxVM.Refinement.Endpoint.WalkedUnit Kind fun x t envT E₀ E lim A c =>
    IxVM.Refinement.Typing.UnitStep (X t E) t envT E₀ E lim A c
-/
#guard_msgs in
#print IxVM.Refinement.Endpoint.WalkedUnitStep

/--
info: def IxVM.Refinement.Typing.CheckedUnitFact.{u} : (List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
    Ix.Kernel.RoleTable → Ixon.Env → Address → Ixon.Constant → Prop) →
  (List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
      Ix.Kernel.RoleTable →
        Ix.Kernel.Env Ix.Kernel.Mode.anon → Ixon.Env → Ixon.Env → Option ℕ → Address → Ixon.Constant → Prop) →
    Prop :=
fun Kind Goal =>
  ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) (bAddr : Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (lim : Option ℕ) (R : Ixon.Env) (envT : Ix.Kernel.Env Ix.Kernel.Mode.anon) (E : Ixon.Env),
    IxVM.Refinement.Typing.StepCtx calls t R envT E₀ E →
      ∀ (A : Address) (c : Ixon.Constant),
        IxVM.Consistency.recordOf E₀ A = some c →
          IxVM.Consistency.InLogic c →
            Kind calls t E₀ A c →
              t.check = Except.ok () →
                IxVM.Refinement.LoadedReads.RunStore calls E₀ →
                  IxVM.Refinement.LoadedReads.HashedRecordsStored calls E₀ →
                    IxVM.Refinement.L1.CanonicalHashCoverage E calls →
                      IxVM.Refinement.Typing.CheckedUnit calls bAddr t envT E₀ lim A c → Goal calls t envT E₀ E lim A c
-/
#guard_msgs in
#print IxVM.Refinement.Typing.CheckedUnitFact

/--
info: def IxVM.Refinement.Typing.CheckedUnitStep.{u} : (Ix.Kernel.RoleTable →
    Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop) →
  (List (Aiur.Generic.SourceSemantics.Call IxVM.F) → Ix.Kernel.RoleTable → Ixon.Env → Address → Ixon.Constant → Prop) →
    Prop :=
fun X Kind =>
  IxVM.Refinement.Typing.CheckedUnitFact Kind fun x t envT E₀ E lim A c =>
    IxVM.Refinement.Typing.UnitStep (X t E) t envT E₀ E lim A c
-/
#guard_msgs in
#print IxVM.Refinement.Typing.CheckedUnitStep

/-! ## Axioms

The theorem reaches the three standard axioms and no other. -/

#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_residual [propext, Classical.choice, Quot.sound]
