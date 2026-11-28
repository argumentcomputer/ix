import IxVMRefinement.Endpoint.ComposedResidual
import IxCK.Kernel.Audit.Axioms

/-! # The open obligations of the composed statement, printed

`IxVM.Refinement.Endpoint.circuitComposed_residual` proves the public statement
`IxVM.Consistency.CircuitComposed` from one named hypothesis for each obligation of the proof
that has no unconditional theorem yet. This module prints its statement (`#check`), the shape of
a unit kind's step (`#print` of `WalkedUnit` and `WalkedUnitStep`, the form the composition
takes the kinds of a top-walked unit in, and of `CheckedUnitFact` and `CheckedUnitStep`, the
form of a kind's step for every checked unit) and the axioms it reaches. A change to any of them
fails the build.

How to read it. Zero explicit arguments remain: both `circuitComposed_residual` and its
zero-argument alias `circuitComposed` prove `IxVM.Consistency.CircuitComposed` unconditionally on
`[propext, Classical.choice, Quot.sound]`. Every binding and typing obligation is discharged:
the binding claim export (`Binding.FamilyRecon.groupStoresOfRun_closed` through
`Binding.groupStoresOfRun_of_remainingNC`), the basis groups' family form, the role-free group
shapes (`Binding.groupWithoutRoleUnit_bindingRun`), the operation and standard-axiom role units
(`Binding.operationRoleUnitW_of_projFree`, `Binding.standardAxiomRoleUnitW_closed`), all three
steps of every group's closure (`Binding.closureUnitSteps_bindingRun`,
`FamilyAlias.closureFamilyCheck_of_run`, `TwinFamily.closureTwinSteps_closed`), the family graph,
inner checks, canonical twin selection (`Typing.familyGraphRowInnerFamT_closed`), the family-block
step (`FamilyAlias.familyBlockCheckRow_of_run`), and the twin step
(`TwinFamily.familyTwinWF_closed`).

The public statement and what it reads are printed in `Ix.IxVM.ConsistencyAudit` and
`Ix.IxVM.ConsistencyModelAudit`. The module is outside any namespace, so every name prints in full. -/

/-! ## The theorem -/

/--
info: IxVM.Refinement.Endpoint.circuitComposed_residual.{u} : IxVM.Consistency.CircuitComposed
-/
#guard_msgs in
#check IxVM.Refinement.Endpoint.circuitComposed_residual

/--
info: IxVM.Refinement.Endpoint.circuitComposed.{u} : IxVM.Consistency.CircuitComposed
-/
#guard_msgs in
#check IxVM.Refinement.Endpoint.circuitComposed

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
                              IxVM.Refinement.Ingress.CanonicalHashCoverage E calls →
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
                    IxVM.Refinement.Ingress.CanonicalHashCoverage E calls →
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
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed [propext, Classical.choice, Quot.sound]
