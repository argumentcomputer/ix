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
-- The specification digest's encoding version 2, with the committed data as a
-- record the renderer reads back (`Ix.SpecDigest.Committed`), adds 371
-- compiled functions, measured by diffing the closures by name.
-- `Ix.SpecDigest` grows 47 -> 291. 186 encode the role names (`Row.ofRole`,
-- with `Role.leanName`'s table inlined), 42 are `nativeOp`'s table, and 26 are
-- the rows, the schedule and the record's encoder (`Committed`, `encode`,
-- `row`, `schedule`, `nameParts`, `str`, `index`, `inert`, `quotKind`), less 10
-- of the old `specBytes`'s own. `Ix.SpecDigest.Schedule` adds 127: 73 for
-- `groupOrder`'s closed terms and 54 for the schedule's checks. The decoder
-- (`Ix/SpecDigest/Decode.lean`) is not reached. Externs, implemented_by,
-- unsafe, csimp and every ruling are unchanged.
-- The decisions' `of_decide_eq_*` dependencies (`Role.deps`) add 7 compiled functions
-- to each closure here (`IxC/Kernel/Audit/Roots.lean`).
-- Specification version 5 (the compiler-trust roles) adds 66: the entry's 49 and 17 in the
-- specification digest's encoder and schedule (the five roles' rows, inertness and groups).
-- Lifting the parameters of a nested occurrence's index arguments in the in-model generator
-- (`genNested`'s `fieldIdxAt` and `ctorIdxAt`) adds 2 compiled functions to each closure
-- here, the entry's (`IxC/Kernel/Audit/Roots.lean`).
-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Declining the rules the kernel cannot certify, instead of storing them inert, adds 17
-- compiled functions here (`IxC/Kernel/Audit/Roots.lean`).
-- The level-count bound (`Ixon.maxLevelCount`, the canonical check's and the compiler's)
-- adds 38 compiled functions. Externs, implemented_by, unsafe, csimp and every ruling are
-- unchanged.
/-- info: runtime closure of [Ix.HostAdmission.certify,
 Ix.HostAdmission.verifyAddressed]: 7695 compiled functions; inherited externs 125, implemented_by 0, unsafe 26, csimp 8; ruled assumed 4, computed_field 21, csimp 28 -/
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
