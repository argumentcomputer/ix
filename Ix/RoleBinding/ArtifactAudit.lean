import Ix.RoleBinding.ArtifactTheorems
import Ix.RoleBinding.ArtifactTieredTheorems
import Ix.RoleBinding.ArtifactOrderTheorems
import Ix.Ixon.Authenticated.Audit

/-! The Env-based entry imports the host's existing proved TagN inlining
rewrite. Its separate audit pins that exact rewrite; the old authenticated
entry audit and the inherited assumed substitutions are unchanged. -/
namespace Ix.RoleBinding.Artifact.Audit

def rulings : Ix.Kernel.Audit.RuntimeRulings :=
  { Ixon.Authenticated.Audit.rulings with
    csimpModules := Ixon.Authenticated.Audit.rulings.csimpModules.push `Ix.Ixon }

open Lean in
run_cmd do
  let env ← getEnv
  let entries := (Ix.Kernel.Audit.allCSimpEntries env).filter fun entry =>
    (Ix.Kernel.Audit.moduleOf env entry.thmName).any (fun name => (`Ix.Ixon).isPrefixOf name)
  unless entries.size == 1 && entries.all (fun entry =>
      entry.fromDeclName == ``Ixon.putTagN && entry.toDeclName == ``Ixon.putTagNI &&
        entry.thmName == ``Ixon.putTagN_eq_I) do
    throwError "artifact audit: the host csimp allowance is not exactly putTagN_eq_I"

/- The optional order selector and extracted materialization loop add six
compiled functions to each default closure; all changed symbols belong to
Artifact or its specializations. Explicit entries share these helpers and
replace only their entry/preparation wrappers. No runtime ruling changes. -/
-- Keeping the fallback's recursors off the input's blocks (`fallbackIndexed`, `indexedRecords`,
-- through `contextOf`) adds four compiled functions. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Declining an inductive read whose declarations repeat a name (`lowerInductive` over
-- `lowerInductiveDecls`) adds 11 compiled functions to each of the four closures, the entry's
-- (`IxC/Kernel/Audit/Roots.lean`). Measured against a walk that stops at the guard; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Leaving out of the index an input recursor filed under a block only the fallback supplies
-- (`inputIndexed`) adds 32 compiled functions to each of the four closures, the reader's
-- (`IxC/Kernel/Audit/Roots.lean`): the predicate and the derived equality of `Ixon.Constant`
-- that compares a record with the fallback's. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- The role-shape validation merge adds the entry's four compiled functions
-- (`IxC/Kernel/Audit/Roots.lean`) to each closure, measured with the fallback-record
-- guard. Execution allowances are unchanged.
-- The expanded catalog adds 703 compiled functions (495 role and 208 key
-- helpers) and removes eight specializations from each artifact closure.
-- These entries use the supplied binding, so they gain no committed-fixture
-- helpers. All direct and reached implementation, extern, unsafe, csimp,
-- replacement and opaque entries were compared exactly and are unchanged.
-- The decisions' `of_decide_eq_*` dependencies (`Role.deps`) add 7 compiled functions
-- to each closure here (`IxC/Kernel/Audit/Roots.lean`).
-- Specification version 5 (the compiler-trust roles) adds the entry's 49 to each
-- closure here, the conditional entries' included (`IxC/Kernel/Audit/Roots.lean`).
-- Lifting the parameters of a nested occurrence's index arguments in the in-model generator
-- (`genNested`'s `fieldIdxAt` and `ctorIdxAt`) adds 2 compiled functions to each closure
-- here, the entry's (`IxC/Kernel/Audit/Roots.lean`).
-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- The Ixon v5 binder-data section (its parser and the local canonical check that
-- `Admission.decodeRecords` runs on every record) adds 38 compiled functions to each closure
-- here, as for `Admission.checkBytes`. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Modes in records (`Constant.modesCanonical` and the mode readers) and the reader's canonical
-- natural-literal check (`ECx.natAt`) add 24 compiled functions to each closure and one inherited
-- extern, as for `Admission.checkBytes`.
-- Indexing and lowering twin recursor records (`RecIndex.twins`, `readRecursor`, `lowerTwin`)
-- add 24 compiled functions to each closure (`IxC/Kernel/Audit/Roots.lean`). Externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.check]: 6994 compiled functions; inherited externs 116, implemented_by 0, unsafe 26, csimp 8; ruled assumed 4, computed_field 21, csimp 28 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.check] #[`Init, `Std] rulings

-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Modes in records (`Constant.modesCanonical` and the mode readers) and the reader's canonical
-- natural-literal check (`ECx.natAt`) add 24 compiled functions to each closure and one inherited
-- extern, as for `Admission.checkBytes`.
-- Indexing and lowering twin recursor records (`RecIndex.twins`, `readRecursor`, `lowerTwin`)
-- add 24 compiled functions to each closure (`IxC/Kernel/Audit/Roots.lean`). Externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkTiered]: 7128 compiled functions; inherited externs 116, implemented_by 0, unsafe 26, csimp 8; ruled assumed 4, computed_field 21, csimp 28 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.checkTiered] #[`Init, `Std] rulings

-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Modes in records (`Constant.modesCanonical` and the mode readers) and the reader's canonical
-- natural-literal check (`ECx.natAt`) add 24 compiled functions to each closure and one inherited
-- extern, as for `Admission.checkBytes`.
-- Indexing and lowering twin recursor records (`RecIndex.twins`, `readRecursor`, `lowerTwin`)
-- add 24 compiled functions to each closure (`IxC/Kernel/Audit/Roots.lean`). Externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkAt]: 6994 compiled functions; inherited externs 116, implemented_by 0, unsafe 26, csimp 8; ruled assumed 4, computed_field 21, csimp 28 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.checkAt] #[`Init, `Std] rulings

-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Modes in records (`Constant.modesCanonical` and the mode readers) and the reader's canonical
-- natural-literal check (`ECx.natAt`) add 24 compiled functions to each closure and one inherited
-- extern, as for `Admission.checkBytes`.
-- Indexing and lowering twin recursor records (`RecIndex.twins`, `readRecursor`, `lowerTwin`)
-- add 24 compiled functions to each closure (`IxC/Kernel/Audit/Roots.lean`). Externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkTieredAt]: 7128 compiled functions; inherited externs 116, implemented_by 0, unsafe 26, csimp 8; ruled assumed 4, computed_field 21, csimp 28 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.checkTieredAt] #[`Init, `Std] rulings

/- `ix check-lean --allow-user-axioms` runs the entries that admit user axioms
in place of `check` and `checkTiered`. When the kernel lists no user axiom,
their receipt is the certified one (`ReceiptConditional.toReceipt`,
`TierReceiptConditional.toTierReceipt`, T1) and a host statement is derived
from it, so their closure is frozen here with the same rulings. It has 61
more compiled functions than `checkTiered`'s (the fold under the axiom policy
and the list); the extern, implemented_by, unsafe and csimp counts and every
ruling are those of `check` and `checkTiered`. Their kernel entries (`Admission.checkBytesUnder`,
`checkBytesTieredUsingUnder`) are frozen apart in
`IxC/Kernel/Audit/Roots.lean` (`userAxiomOperations`). -/
-- Lifting the parameters of a nested occurrence's index arguments in the in-model generator
-- (`genNested`'s `fieldIdxAt` and `ctorIdxAt`) adds 2 compiled functions to each closure
-- here, the entry's (`IxC/Kernel/Audit/Roots.lean`).
-- Reflexive fields, members behind definitions and erasing fields in the in-model generator
-- (`fieldKind`, `fieldNorm`, `substMembers`, `ihBinder`) and the reader's K check on a nested
-- block add 21 compiled functions. Externs, implemented_by, unsafe, csimp and all ruling
-- counts are unchanged.
-- Indexing and lowering twin recursor records (`RecIndex.twins`, `readRecursor`, `lowerTwin`)
-- add 24 compiled functions (`IxC/Kernel/Audit/Roots.lean`). Externs, implemented_by, unsafe,
-- csimp and all ruling counts are unchanged.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkConditional,
 Ix.RoleBinding.Artifact.checkTieredConditional]: 7189 compiled functions; inherited externs 116, implemented_by 0, unsafe 26, csimp 8; ruled assumed 4, computed_field 21, csimp 28 -/
#guard_msgs (whitespace := lax) in
run_cmd do
  Ix.Kernel.Audit.checkRuntimeWith
    #[``Ix.RoleBinding.Artifact.checkConditional, ``Ix.RoleBinding.Artifact.checkTieredConditional]
    #[`Init, `Std] rulings

#guard_kernel_axioms Ixon.putTagN_eq_I [propext, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.Receipt.strongModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.Receipt.authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.TierReceipt.strongModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.TierReceipt.authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.TierReceipt.typed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.materializeOrder_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareRecordsAt_order [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.Materialized.complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareRecordsAt_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareRecordsAt_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.decodeRecordsPar_eq [propext, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareRecordsForPar_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareRecordsPar_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareAt_obligations [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareTieredAt_obligations [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedReceipt.complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedTierReceipt.complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedReceipt.target_unique [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedTierReceipt.target_unique [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedReceipt.authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedTierReceipt.authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.ReceiptConditional.toReceipt [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.TierReceiptConditional.toTierReceipt [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.ReceiptConditional.strongModel_of_nil [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.TierReceiptConditional.strongModel_of_nil [propext, Classical.choice, Quot.sound]

end Ix.RoleBinding.Artifact.Audit
