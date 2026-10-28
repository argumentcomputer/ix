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
  let entries := (Compiler.CSimp.ext.getState env).map.fold (init := #[])
    fun entries _ entry =>
      if (Ix.Kernel.Audit.moduleOf env entry.thmName).any (fun name => (`Ix.Ixon).isPrefixOf name) then
        entries.push entry
      else entries
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
-- Specification version 3 adds four, the entry's (`IxC/Kernel/Audit/Roots.lean`): `iffFamily`,
-- `nonemptyFamily`, `sorryAxSpecTy` and its two closed terms in, `Role.spec._closed_1` out.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.check]: 6040 compiled functions; inherited externs 115, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 26 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.check] #[`Init, `Std] rulings

-- Specification version 3 adds four, the entry's (`IxC/Kernel/Audit/Roots.lean`): `iffFamily`,
-- `nonemptyFamily`, `sorryAxSpecTy` and its two closed terms in, `Role.spec._closed_1` out.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkTiered]: 6174 compiled functions; inherited externs 115, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 26 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.checkTiered] #[`Init, `Std] rulings

-- Specification version 3 adds four, the entry's (`IxC/Kernel/Audit/Roots.lean`): `iffFamily`,
-- `nonemptyFamily`, `sorryAxSpecTy` and its two closed terms in, `Role.spec._closed_1` out.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkAt]: 6040 compiled functions; inherited externs 115, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 26 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.checkAt] #[`Init, `Std] rulings

-- Specification version 3 adds four, the entry's (`IxC/Kernel/Audit/Roots.lean`): `iffFamily`,
-- `nonemptyFamily`, `sorryAxSpecTy` and its two closed terms in, `Role.spec._closed_1` out.
/-- info: runtime closure of [Ix.RoleBinding.Artifact.checkTieredAt]: 6174 compiled functions; inherited externs 115, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 26 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.checkTieredAt] #[`Init, `Std] rulings

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
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareAt_obligations [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.prepareTieredAt_obligations [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedReceipt.complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedTierReceipt.complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedReceipt.target_unique [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedTierReceipt.target_unique [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedReceipt.authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.OrderedTierReceipt.authentic [propext, Classical.choice, Quot.sound]

end Ix.RoleBinding.Artifact.Audit
