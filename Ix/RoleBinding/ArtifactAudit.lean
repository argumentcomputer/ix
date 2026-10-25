import Ix.RoleBinding.ArtifactTheorems
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

/-- info: runtime closure of [Ix.RoleBinding.Artifact.check]: 6013 compiled functions; inherited externs 115, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 26 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.RoleBinding.Artifact.check] #[`Init, `Std] rulings

#guard_kernel_axioms Ixon.putTagN_eq_I [propext, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.Receipt.strongModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.Artifact.Receipt.authentic [propext, Classical.choice, Quot.sound]

end Ix.RoleBinding.Artifact.Audit
