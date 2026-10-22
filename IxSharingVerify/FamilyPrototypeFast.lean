import Ix.Sharing.FamilyPrototypeFast
import IxC.Kernel.Audit.Axioms

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.localPhi_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.component_eq_fast [propext, Classical.choice, Quot.sound]
