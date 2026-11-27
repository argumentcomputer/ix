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
-- (`IxCK/Kernel/Audit/Roots.lean`). Measured against a walk that stops at the guard; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Leaving out of the index an input recursor filed under a block only the fallback supplies
-- (`inputIndexed`) adds 32 compiled functions, the reader's (`IxCK/Kernel/Audit/Roots.lean`):
-- the predicate and the derived equality of `Ixon.Constant` that compares a record with the
-- fallback's. Measured before refreezing; externs, implemented_by, unsafe, csimp and all
-- ruling counts are unchanged.
-- The role-shape validation merge adds the entry's four compiled functions
-- (`IxCK/Kernel/Audit/Roots.lean`), measured with the fallback-record guard.
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
-- to each closure here (`IxCK/Kernel/Audit/Roots.lean`).
-- Specification version 4 (the compiler-trust roles) adds 66: the entry's 49 and 17 in the
-- specification digest's encoder and schedule (the five roles' rows, inertness and groups).
-- Lifting the parameters of a nested occurrence's index arguments in the in-model generator
-- (`genNested`'s `fieldIdxAt` and `ctorIdxAt`) adds 2 compiled functions to each closure
-- here, the entry's (`IxCK/Kernel/Audit/Roots.lean`).
-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Declining the rules the kernel cannot certify, instead of storing them inert, adds 17
-- compiled functions here (`IxCK/Kernel/Audit/Roots.lean`).
-- The level-count bound (`Ixon.maxLevelCount`, the canonical check's and the compiler's)
-- adds 38 compiled functions. Externs, implemented_by, unsafe, csimp and every ruling are
-- unchanged.
-- Modes in records (`Constant.modesCanonical` and the mode readers) and the reader's canonical
-- natural-literal check (`ECx.natAt`) add 24 compiled functions and one inherited extern, as for
-- `Admission.checkBytes`.
-- Indexing and lowering twin recursor records (`RecIndex.twins`, `readRecursor`, `lowerTwin`)
-- add 24 compiled functions (`IxCK/Kernel/Audit/Roots.lean`). Externs, implemented_by, unsafe,
-- csimp and every ruling are unchanged.
-- The schedule's third boundary (the first literal-support group, `tailBoundaries`) adds 12
-- compiled functions; measured with the same roots and rulings, the closure was already 7826
-- with csimp 29 at the commit before it.
-- Factoring `Ixon.CheckOrder.postorder` out of `order` adds 1 compiled function; externs and rulings are unchanged.
-- Transitive logical-body `scanLogical` walk in `Runtime.lean` catches 3 multi-hop inlined ruled `@[csimp]`s (29 -> 32).
-- Hardened `Runtime.lean` surfaces specialized kernel helpers, ruled overrides, and all 5 `Blake3.Rust` externs.
-- Kernel hardening updates counts (refreshed in reconciliation).
-- Strict admission (`Prepared.admitPins`: `admitPinnedRoles` over the committed default table,
-- decoded and checked; `admitLevels`), divide-and-conquer literal reading, and saturating Géran
-- bounds add 63 compiled functions and one inherited extern, as for `Ix.RoleBinding.Artifact.check`.
/-- info: runtime closure of [Ix.HostAdmission.certify,
 Ix.HostAdmission.verifyAddressed]: 9136 compiled functions; inherited externs 130, implemented_by 0, unsafe 43, csimp 9; ruled assumed 6, computed_field 31, implemented_by 1, csimp 42 -/
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
