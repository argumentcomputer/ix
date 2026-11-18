import IxVMRefinement.Endpoint.ComposedResidual
import IxC.Kernel.Audit.Axioms

/-! # The open obligations of the composed statement, printed

`IxVM.Refinement.Endpoint.circuitComposed_residual` proves the public statement
`IxVM.Consistency.CircuitComposed` from one named hypothesis for each obligation of the proof
that has no unconditional theorem yet. This module prints its statement (`#check`), the shape of
its typing hypotheses (`#print` of `WalkedUnit` and `WalkedUnitStep`) and the axioms it
reaches. A change to any of them fails the build.

How to read it. The explicit arguments are the open obligations: the first eight are the
binding half's, the others the typing half's, for each kind of top-walked unit that has no
step yet. The implicit argument `Run` is the binding claim layer's run predicate, which nothing
supplies yet. A hypothesis is typed by the interface its obligation has today, so the theorem
claims nothing by itself; it fixes how the parts compose and what is left.

How to change it. When a theorem produces a hypothesis, apply it inside
`circuitComposed_residual`, delete the hypothesis and update the expected output here in the
same commit. When the interface of an obligation changes, retype its hypothesis the same way.
The proof is complete when the theorem has no explicit argument.

What this module does not print. A definition that a hypothesis reads (`BindingClaimExport`,
`BasisBase`, `ClosureStep`, `FoldClauseOver`, `FoldExtra`, `UnitStep` and the others) appears by
name only: its own module holds it. The public statement and what it reads are printed in
`Ix.IxVM.ConsistencyAudit` and `Ix.IxVM.ConsistencyModelAudit`. The module is outside any
namespace, so every name prints in full. -/

/-! ## The theorem -/

/--
info: IxVM.Refinement.Endpoint.circuitComposed_residual.{u}
  {Run :
    List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
      Ix.Kernel.RoleTable → IxVM.Refinement.Binding.BRun → (ℕ → Ixon.Env) → Prop}
  (bindingClaimExport :
    IxVM.Consistency.SourceSoundBounded fun calls d => IxVM.Refinement.Binding.BindingClaimExport (Run calls) calls d)
  (basisGroups :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
      IxVM.Refinement.Binding.BasisBase
        (IxVM.Refinement.Binding.FoldClauseOver IxVM.Refinement.Typing.FormerOpenTraceAt) (Run calls))
  (groupAdmissions :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)), IxVM.Refinement.Binding.AdmitsChain (Run calls))
  (groupAdmissionReads :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)), IxVM.Refinement.Binding.AdmitsReadsChain (Run calls))
  (groupClosure :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) (t : Ix.Kernel.RoleTable)
      (ρ : IxVM.Refinement.Binding.BRun) (Rs : ℕ → Ixon.Env),
      Run calls t ρ Rs →
        IxVM.Consistency.AllBound t →
          ∀ (g : ℕ),
            6 ≤ g →
              g < 77 →
                IxVM.Refinement.Binding.ClosureStep
                  (IxVM.Refinement.Binding.FoldClauseOver IxVM.Refinement.Typing.FormerOpenTraceAt) ρ t g)
  (groupWithoutRoleUnit :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) (t : Ix.Kernel.RoleTable)
      (ρ : IxVM.Refinement.Binding.BRun) (Rs : ℕ → Ixon.Env),
      Run calls t ρ Rs →
        IxVM.Consistency.AllBound t →
          ∀ (g : ℕ),
            6 ≤ g →
              g < 77 →
                IxVM.Refinement.Binding.RoleNoneFacts
                  (IxVM.Refinement.Binding.FoldClauseOver IxVM.Refinement.Typing.FormerOpenTraceAt) t g)
  (operationRoleUnit :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) (t : Ix.Kernel.RoleTable)
      (ρ : IxVM.Refinement.Binding.BRun) (Rs : ℕ → Ixon.Env),
      Run calls t ρ Rs →
        IxVM.Consistency.AllBound t →
          ∀ (g : ℕ),
            6 ≤ g →
              g < 77 →
                IxVM.Refinement.Binding.RoleUnitStep (fun x => x ∈ IxVM.Refinement.RoleOps.opRoles)
                  (IxVM.Refinement.Binding.FoldClauseOver IxVM.Refinement.Typing.FormerOpenTraceAt) ρ t g)
  (standardAxiomRoleUnit :
    ∀ (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) (t : Ix.Kernel.RoleTable)
      (ρ : IxVM.Refinement.Binding.BRun) (Rs : ℕ → Ixon.Env),
      Run calls t ρ Rs →
        IxVM.Consistency.AllBound t →
          ∀ (g : ℕ),
            6 ≤ g →
              g < 77 →
                IxVM.Refinement.Binding.RoleUnitStep (fun x => x ∈ IxVM.Consistency.standardAxioms)
                  (IxVM.Refinement.Binding.FoldClauseOver IxVM.Refinement.Typing.FormerOpenTraceAt) ρ t g)
  (standaloneTheoremOrOpaque :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun x x_1 x_2 x_3 c => ∃ d, c.info = Ixon.ConstantInfo.defn d ∧ d.kind ≠ Ix.DefKind.defn)
  (recursorAtNativeParent :
    IxVM.Refinement.Endpoint.WalkedUnit (fun x x_1 x_2 x_3 c => ∃ rc, c.info = Ixon.ConstantInfo.recr rc)
      fun x t envT E₀ E lim A c =>
      ∀ (rc : Ixon.Recursor),
        c.info = Ixon.ConstantInfo.recr rc →
          ∀ (env : Ix.Kernel.Env Ix.Kernel.Mode.anon) (P : Address) (ip : Ixon.InductiveProj)
            (fam : Ix.Kernel.Semantics.NativeFam Ix.Kernel.Mode.anon),
            IxVM.Refinement.Typing.StepAt t envT E₀ E lim A c env →
              IxVM.Refinement.Typing.LvClauses env →
                IxVM.Refinement.Typing.RecParent t E env P ip →
                  IxVM.Refinement.Typing.RecMajorTie t E₀ A c rc P →
                    IxVM.Refinement.Typing.FamReadAt IxVM.Refinement.Typing.FormerOpenTraceAt t E env P ip fam →
                      IxVM.Refinement.Typing.RecLateOut t E₀ E A env fam)
  (recursorWithoutNativeParent :
    IxVM.Refinement.Endpoint.WalkedUnit (fun x x_1 x_2 x_3 c => ∃ rc, c.info = Ixon.ConstantInfo.recr rc)
      fun x t envT E₀ E lim A c =>
      ∀ (rc : Ixon.Recursor),
        c.info = Ixon.ConstantInfo.recr rc →
          (¬∀ (env : Ix.Kernel.Env Ix.Kernel.Mode.anon),
                IxVM.Refinement.Typing.StepAt t envT E₀ E lim A c env →
                  ∃ P ip,
                    IxVM.Refinement.Typing.RecParent t E env P ip ∧ IxVM.Refinement.Typing.RecMajorTie t E₀ A c rc P) →
            IxVM.Refinement.Typing.UnitStep
              (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt t E) t envT E₀ E lim A c)
  (definitionBlock :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun x x_1 x_2 x_3 c => ∃ ms, c.info = Ixon.ConstantInfo.muts ms ∧ IxVM.Refinement.Typing.DefnBlock ms)
  (nativeBlockTelescope :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun calls t E₀ B cb =>
      ∃ ind,
        IxVM.Refinement.Typing.BlockUnitRecord E₀ B cb ind ∧
          IxVM.Refinement.Typing.NativeRouteAt calls B ∧ IxVM.Refinement.Typing.FormerAtTele t E₀ B cb ind)
  (nativeBlockAlias :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun calls t E₀ B cb =>
      ∃ ind,
        IxVM.Refinement.Typing.BlockUnitRecord E₀ B cb ind ∧
          IxVM.Refinement.Typing.NativeRouteAt calls B ∧ IxVM.Refinement.Typing.FormerAtAlias t E₀ B cb ind)
  (nativeBlockOtherTelescope :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun calls t E₀ B cb =>
      ∃ ind,
        IxVM.Refinement.Typing.BlockUnitRecord E₀ B cb ind ∧
          IxVM.Refinement.Typing.NativeRouteAt calls B ∧ IxVM.Refinement.Typing.FormerTeleOther t E₀ B cb ind)
  (oneTypeBlockOffNativeRoute :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun calls x E₀ B cb =>
      ∃ ind, IxVM.Refinement.Typing.BlockUnitRecord E₀ B cb ind ∧ ¬IxVM.Refinement.Typing.NativeRouteAt calls B)
  (otherBlock :
    IxVM.Refinement.Endpoint.WalkedUnitStep (IxVM.Refinement.Typing.FoldExtra IxVM.Refinement.Typing.FormerOpenTraceAt)
      fun x x_1 x_2 x_3 c =>
      ∃ ms,
        c.info = Ixon.ConstantInfo.muts ms ∧
          ¬IxVM.Refinement.Typing.DefnBlock ms ∧ ∀ (ind : Ixon.Inductive), ms ≠ #[Ixon.MutConst.indc ind]) :
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

/-! ## Axioms

The theorem reaches the three standard axioms and no other. -/

#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_residual [propext, Classical.choice, Quot.sound]
