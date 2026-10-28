import Ix.HostAdmission.Theorems
import Ix.RoleBinding.ArtifactAudit
import Ix.SpecDigest.Audit

/-! This host boundary retains the existing exact BLAKE3 and proved TagN
runtime rulings. No new runtime assumption or partial-code allowance. The
additional closure derives canonical roots and the current specification,
encodes/decodes the separate host envelope, and compares replayed identities.
The current specification's unchanged frozen-value guards are imported here
and by the established certificate audit. -/
/- Shared optional-order preparation and materialization add eight compiled
functions to the combined host closure. All changed symbols are Artifact
helpers or their specializations; every execution allowance is unchanged. -/
-- Keeping the fallback's recursors off the input's blocks (`fallbackIndexed`, `indexedRecords`,
-- through `contextOf`) adds four compiled functions. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
/-- info: runtime closure of [Ix.HostAdmission.certify,
 Ix.HostAdmission.verifyAddressed]: 6418 compiled functions; inherited externs 125, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 26 -/
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
