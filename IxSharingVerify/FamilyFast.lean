import Ix.Sharing.FamilyFast
import IxC.Kernel.Audit.Axioms

#guard_kernel_axioms Ix.Sharing.Family.localPhi_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.component_eq_fast [propext, Classical.choice, Quot.sound]
