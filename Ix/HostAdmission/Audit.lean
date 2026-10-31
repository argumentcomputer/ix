import Ix.HostAdmission.Theorems
import Ix.RoleBinding.ArtifactAudit
import Ix.SpecDigest.Audit

/-! This host boundary retains the existing exact BLAKE3 and proved TagN
runtime rulings. No new runtime assumption or partial-code allowance. The
additional closure derives canonical roots and the current specification,
encodes/decodes the separate host envelope, and compares replayed identities.
The current specification's frozen-value guards are imported here
and by the established certificate audit. -/
/- Shared optional-order preparation and materialization add eight compiled
functions to the combined host closure. All changed symbols are Artifact
helpers or their specializations; every execution allowance is unchanged. -/
-- Keeping the fallback's recursors off the input's blocks (`fallbackIndexed`, `indexedRecords`,
-- through `contextOf`) adds four compiled functions. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Declining an inductive read whose declarations repeat a name (`lowerInductive` over
-- `lowerInductiveDecls`) adds 11 compiled functions, the entry's
-- (`IxC/Kernel/Audit/Roots.lean`). Measured against a walk that stops at the guard; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Leaving out of the index an input recursor filed under a block only the fallback supplies
-- (`inputIndexed`) adds 32 compiled functions, the reader's (`IxC/Kernel/Audit/Roots.lean`):
-- the predicate and the derived equality of `Ixon.Constant` that compares a record with the
-- fallback's. Measured before refreezing; externs, implemented_by, unsafe, csimp and all
-- ruling counts are unchanged.
-- The role-shape validation merge adds the entry's four compiled functions
-- (`IxC/Kernel/Audit/Roots.lean`), measured with the fallback-record guard.
-- Execution allowances are unchanged.
-- The expanded specification adds 706 compiled helpers: 496 from Roles, 208
-- from Key and two from SpecDigest, and removes eight old specializations.
-- The complete extern, unsafe, direct and reached implementation, csimp,
-- replacement and opaque entry sets are unchanged, as are all runtime rulings.
/-- info: runtime closure of [Ix.HostAdmission.certify,
 Ix.HostAdmission.verifyAddressed]: 7162 compiled functions; inherited externs 125, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 27 -/
#guard_msgs (whitespace := lax) in
run_cmd do
  Ix.Kernel.Audit.checkRuntimeWith #[``Ix.HostAdmission.certify, ``Ix.HostAdmission.verifyAddressed]
    #[`Init, `Std] Ix.RoleBinding.Artifact.Audit.rulings

#guard_kernel_axioms Ix.HostAdmission.Merkle.next_length_lt [propext, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Merkle.tree_some_of_nonempty [propext, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.bindingAndMain [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.logicalModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.tierTyped [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.currentSpec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.contentRoot [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.closed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.mainMember [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.HostAdmission.Checked.kindAgreement [propext, Classical.choice, Quot.sound]
