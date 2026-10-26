import Ix.Sharing.FamilyCached
import IxC.Kernel.Audit.Axioms

#guard_kernel_axioms Ix.Sharing.Family.cachedStep_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.componentsCachedWith_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.components_eq_cached [propext, Classical.choice, Quot.sound]
