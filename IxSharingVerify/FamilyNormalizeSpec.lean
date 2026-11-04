import Ix.Sharing.FamilyNormalizeArea
import IxC.Kernel.Audit.Axioms

#guard_kernel_axioms Ix.Sharing.Family.cachedComponent_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyStep_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyFold_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyComponents_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyUniform_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyAtWidth_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyReferenceExpanded_eq_cached [propext, Classical.choice, Quot.sound]

#guard_kernel_axioms Ix.Sharing.Family.familyAreaPhi_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyTraceArea_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyAreaEvaluation_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyStepArea_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyFoldArea_eq_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyComponentsArea_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyUniformArea_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyAtWidthArea_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_eq_area [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.normalizeFamily_eq_area [propext, Classical.choice, Quot.sound]
