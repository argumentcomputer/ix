import IxVMRefinement.Binding.OpInstall
import IxVMRefinement.Binding.RunPredicate
import IxVMRefinement.Binding.RunStepStores
import IxVMRefinement.Binding.WalkedStored
import IxVMRefinement.Assembly.FoldClauseAlias

/-! # The operations' role unit of the binding fold

The step of a group whose one role is an operation (`RoleUnitStepOver` at membership in the
operations), for every group of a binding run: from the invariant over the fold's clause below
the group at the closure's store and environment, the invariant before the raise past the group
at the store with the operation's record and the environment with the operation installed.

* `OpValidationFacts L calls`: **what the run's validation of an operation gives the fold**, at
  the closure's environment, given the record stores of the run (`RunStepStores`): the
  operation's check facts (`RoleOps.OpChecked`), the stored type
  and value annotating the record's reading, the reading itself, the record a standalone
  definition at an address of 32 bytes, and the stored constant the one every load of the
  record represents. It is the premise of this file; the record stores are the run predicate's
  (`BindingRun.stepStores`).
* `operationRoleUnit_of_validation`: the role unit's step from that premise, by the install
  step (`OpInstall.roleOp_step`).
* `operationRoleUnit`: the same at the link the composed fold carries, in the form the composed
  residual takes its hypothesis.

What `OpValidationFacts` is made of, and from what. The run's validation of the role is the
observed call of `KernelRoles::validate_role` under the group's context (the admission's
clause), which at an operation is `validate_op`:

* the record is a standalone safe definition with no universe parameter (asserted), at the
  address the table binds, whose bytes the run hashed (32 bytes);
* the walked check of the record gives the definition's check at the closure's environment
  (`OpRefine.opFront_of_checked`), with the stored terms the record's canonical annotations
  (the reload, `LoadedReads.get_ci_defn_canon`);
* the pinned type: the record's type is compared structurally with `role_type(tbl, r)`, which
  is the specified type up to binder data (`roleTypeRenders`), so the stored type has the
  operation's shape (`RoleOps.OpTyShape`);
* a structural operation: each recurrence's two sides (`opEquationLhsRenders`,
  `opEquationRhsRenders`), opened and with the operation replaced by its value
  (`OpOpen.op_equation_side_spec`), compared by `k_is_def_eq` (`OpRefine.eqs_of_obs`);
* a well-founded operation: each certificate statement (`opCertificateRenders`), substituted
  and opened along its `Forall` spine (`OpOpen.subst_const_forallSpine`,
  `OpOpen.open_foralls_spec`), checked against the applied proof (`OpRefine.certFacts_of_obs`);
* the prefix half from the invariant (`OpRefine.opPrefix_of_bnd`, `OpRefine.wfPrefix_of_bnd`).

All of these read the circuit's calls at a record store for the closure's store that the run's
calls are good for (`Typing.StepStore`). The facts are asked under `RunStepStores` at the run's
store, which the run predicate holds (`BindingRun.stepStores`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **What a binding run's validation of an operation gives the fold** (module docstring): at
every group `g` whose one role is the operation `r` bound at `a`, every admission of `g` by the
run from `R` to `R'`, and every store `R₁` and environment `env₁` with the invariant below `g`
such that `R'` is `R₁` and the record at `a`. -/
def OpValidationFacts (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env),
    BindingRun calls t ρ Rs → RunStepStores calls t ρ.E₀ → AllBound t → t.check = .ok () →
    ∀ (g : Nat) (r : Ix.Kernel.Role) (a : _root_.Address) (R R₁ R' : Ixon.Env)
      (env₁ : Ix.Kernel.Env .anon),
      6 ≤ g → g < 77 → roleGroup g = [r] → r ∈ RoleOps.opRoles → t.addressOf? r = some a →
      Admits ρ t g R R' → AdmitsReads ρ t R R' → BndOver.{u} L t (· < g) R₁ env₁ →
      AddsAt R₁ R' a →
      ∃ (ty₀ val₀ ty val tyD valD : Core.KExpr) (hint : Ix.Kernel.ReducibilityHint),
        RoleOps.OpChecked env₁ (.role r) ty₀ val₀ ty val ∧
        Annotates ty tyD ∧ Annotates val valD ∧
        Reads t R' a (.defnInfo ⟨.role r, [], tyD⟩ valD hint) ∧
        (∃ c d, recordOf R' a = some c ∧ c.info = .defn d) ∧ a.hash.size = 32 ∧
        ∀ E, RecordsFor R' E →
          Decl.ReloadsAs E t (RoleOps.installed env₁ (.role r) ty val hint)
            (.defnInfo ⟨.role r, [], ty⟩ val hint)

/-- **`OpValidationFacts` with the closure's coverage handed**: the same facts, at every store
and environment after the closure that also satisfy `WalkedStored` and hold the store before
the group (`StoreLe R R₁`, so that the operation's record is new). -/
def OpValidationFactsW (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env),
    BindingRun calls t ρ Rs → RunStepStores calls t ρ.E₀ → AllBound t → t.check = .ok () →
    ∀ (g : Nat) (r : Ix.Kernel.Role) (a : _root_.Address) (R R₁ R' : Ixon.Env)
      (env₁ : Ix.Kernel.Env .anon),
      6 ≤ g → g < 77 → roleGroup g = [r] → r ∈ RoleOps.opRoles → t.addressOf? r = some a →
      Admits ρ t g R R' → AdmitsReads ρ t R R' → BndOver.{u} L t (· < g) R₁ env₁ →
      AddsAt R₁ R' a → StoreLe R R₁ → WalkedStored ρ t (· < g) R₁ env₁ →
      ∃ (ty₀ val₀ ty val tyD valD : Core.KExpr) (hint : Ix.Kernel.ReducibilityHint),
        RoleOps.OpChecked env₁ (.role r) ty₀ val₀ ty val ∧
        Annotates ty tyD ∧ Annotates val valD ∧
        Reads t R' a (.defnInfo ⟨.role r, [], tyD⟩ valD hint) ∧
        (∃ c d, recordOf R' a = some c ∧ c.info = .defn d) ∧ a.hash.size = 32 ∧
        ∀ E, RecordsFor R' E →
          Decl.ReloadsAs E t (RoleOps.installed env₁ (.role r) ty val hint)
            (.defnInfo ⟨.role r, [], ty⟩ val hint)

/-- **The operations' role unit, from the validation facts.** -/
theorem operationRoleUnit_of_validation {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} (hv : OpValidationFacts.{u} L calls) :
    AtGroups (BindingRun calls)
      (RoleUnitStepOver.{u} (fun x => x ∈ RoleOps.opRoles) L) := by
  intro t ρ Rs hrun hall ht g h6 h77 r a R R₁ R' env₁ hgrp hop ha hadm hreads hb hadds
  obtain ⟨ty₀, val₀, ty, val, tyD, valD, hint, hc, hty, hval, hrd, hsolo, hsize, hreload⟩ :=
    hv t ρ Rs hrun hrun.stepStores hall ht g r a R R₁ R' env₁ h6 h77 hgrp hop ha hadm hreads hb
      hadds
  exact ⟨RoleOps.installed env₁ (.role r) ty val hint, fun ci hci => List.mem_cons_of_mem _ hci,
    OpInstall.roleOp_step hL hall hgrp hop ha hadm hb hadds hc hty hval hrd hsolo hsize hreload⟩

/-- **The operations' role unit at the link the composed fold carries**, in the form the
composed residual takes it. -/
theorem operationRoleUnit
    (hv : ∀ calls : List (Call F), OpValidationFacts.{u} FormerOpenTraceAt calls) :
    ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (RoleUnitStepOver.{u} (fun x => x ∈ RoleOps.opRoles) FormerOpenTraceAt) :=
  fun calls => operationRoleUnit_of_validation linkLaws_formerOpenTrace (hv calls)

end IxVM.Refinement.Binding
