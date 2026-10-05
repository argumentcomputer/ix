import IxC.Kernel.Audit.Axioms
import Ix.Resource.Admit

/-! Exact trust manifest for the executable resource-state invariants.
No native, upstream, pending, or sorry axioms are admitted. Each check fails
on a missing or an additional axiom (`Ix.Kernel.Audit`), replacing the
retired `Ix.Tc.Verify.Audit` manifest checker. -/

#guard_kernel_axioms Ix.Resource.root_scopeTree [propext]
#guard_kernel_axioms Ix.Resource.push_scopeTree [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Resource.ancestor_older []
#guard_kernel_axioms Ix.Resource.outlivesAux_sound [propext, Quot.sound]
#guard_kernel_axioms Ix.Resource.outlives_sound [propext, Quot.sound]
#guard_kernel_axioms Ix.Resource.fresh_scope_cannot_escape [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Resource.checkOrigins_sound [propext, Quot.sound]
#guard_kernel_axioms Ix.Resource.endLoan_live []
#guard_kernel_axioms Ix.Resource.endLoan_unique []
#guard_kernel_axioms Ix.Resource.moveOwner_requires [propext]
#guard_kernel_axioms Ix.Resource.shareOwner_permanent [propext]
#guard_kernel_axioms Ix.Resource.checkUnrestricted_sound [propext]
#guard_kernel_axioms Ix.Resource.joinOwner_live [propext]
#guard_kernel_axioms Ix.Resource.joinOwner_unique [propext]
#guard_kernel_axioms Ix.Resource.checkDemand_sound [propext, Quot.sound]
