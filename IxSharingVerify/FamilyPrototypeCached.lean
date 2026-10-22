import Ix.Sharing.FamilyPrototypeCached
import IxC.Kernel.Audit.Axioms

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.cachedStep_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.componentsCachedWith_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.components_eq_cached [propext, Classical.choice, Quot.sound]
