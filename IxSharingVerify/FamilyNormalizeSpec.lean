import Ix.Sharing.FamilyNormalizeSpec
import IxC.Kernel.Audit.Axioms

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.cachedComponent_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyStep_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyFold_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyComponents_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyUniform_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyAtWidth_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyReferenceExpanded_eq_cached [propext, Classical.choice, Quot.sound]
