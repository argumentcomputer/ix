import Ix.Sharing.FamilyNormalize
import IxC.Kernel.Audit.Axioms

-- This audits only the charged evaluator field. Family leastness and the
-- semantic model/finish bridge are deliberately not claimed by this module.
#guard_kernel_axioms Ix.Sharing.Family.phiE_work [propext, Classical.choice, Quot.sound]
