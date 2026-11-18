import IxVMRefinement.Binding.StoreClausesWalk
import IxVMRefinement.RoleVal.AxiomRecordLim
import IxVMRefinement.Claim.RefSafety

/-! # Facts of the store sequence's run, from the observed validations

Premises of the store sequence's clauses (`IxVMRefinement.Binding.RunStores`,
`IxVMRefinement.Binding.StoreClausesWalk`) proved of a run whose roles have their observed
validations, in the alternative without a collision.

* `axiomRoles_of_run`: the record the table binds a standard axiom to is a safe axiom record of
  the run (`AxiomRolesDeclared`): the validation of the role loads the record with
  `Ingress::get_ci`, and `KernelRoles::validate_standard_axiom` matches it as an axiom and
  asserts it safe.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The record a standard axiom is bound to is a safe axiom record of the run.** -/
theorem axiomRoles_of_run (hC : CollisionFreeRun calls E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    AxiomRolesDeclared t E₀ := by
  intro r hr a had
  have hv := hval (Ix.SpecDigest.groupOf r) (RoleVal.groupOf_lt_77 r) r (role_mem_roleGroup r)
  obtain ⟨a', raw, c, ax, had', hsz, hh, hblk, hde, hdeE, hinfo, hsafe⟩ :=
    RoleVal.ValidateRoleIn.axiom_record
      (show RoleVal.ValidateRoleIn calls bAddr t _ r from hv)
      ((RoleVal.specKind_three_iff r).mpr hr)
  have e : a = a' := Option.some.inj (had.symm.trans had')
  subst e
  refine ⟨c, ax, ?_, hinfo, hsafe⟩
  rw [← hblk]
  exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE

end Run

end IxVM.Refinement.Binding
