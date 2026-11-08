module

public import Ix.CompileCertified
public import Ix.EnvScope
public import Tests.Ix.IxVM.Harness

/-! # Decision results under a compiled binding

A native `Nat` or `Int` decision answers `Decidable.isTrue p (of_decide_eq_true
p d rfl)` or `Decidable.isFalse p (of_decide_eq_false p d rfl)` (IxVM's
`dec_result`), and IxVM refuses the claim unless the role binding binds the
role it uses. A compiled artifact binds the roles its closure reaches, closed
under `Role.deps` (`Ix.RoleBinding.Compile.supportInput`), so a decision's
dependencies name both `of_decide_eq_*` roles (`IxC/Kernel/Roles.lean`).

Before they did, the binding of `agg-med`, the closure of `Array.extract_append`
and `Nat.add_comm` over `Init`, bound 92 of the 103 roles, without
`of_decide_eq_false`, and 10 of its 32 shards were refused. The smallest held
`Array.extract_append._proof_1_1`.

The case compiles that constant's closure as `ix compile --consts` does
(`Ix.CompileM.compileAndFinalize`). It checks that the binding binds `Nat.decEq`
with both `of_decide_eq_*` roles, then submits the constant as a one-constant
shard (`buildShardCheckEnvWitness`), validating the binding as `ix prove
--aggregate` does.
-/

public section

namespace Tests.Ix.IxVM.DecisionRoles

open IxVM.ClaimHarness
open Ix.Kernel (Role RoleTable)

/-- `Array.extract_append._proof_1_1`. -/
def leaf : Lean.Name := "Array.extract_append._proof_1_1".toName

/-- The roles the leaf's check uses, which its binding must bind. -/
def required : List Role := [.natDecEq, .ofDecideEqTrue, .ofDecideEqFalse]

def run (env : Lean.Environment) : IO UInt32 := do
  unless env.constants.contains leaf do
    IO.eprintln s!"[ixvm-decision-roles] {leaf} is not in the environment"
    return 1
  let constants := Ix.EnvScope.collectSelectedDeps env [leaf]
  let started ← IO.monoMsNow
  let artifact ← match ← Ix.CompileM.compileAndFinalize env constants 8 (allowPartial := false) with
    | .ok (_, .done artifact _) => pure artifact
    | .ok (out, .refused) =>
      throw (IO.userError s!"{out.failures.toMap.size} constants failed to compile")
    | .ok (_, .failed e) => throw (IO.userError s!"finalization failed: {e}")
    | .error e => throw (IO.userError s!"the compile failed: {e}")
  let some binding := artifact.roleBinding
    | throw (IO.userError "the artifact carries no role binding")
  let some table := RoleTable.ofBytes binding.bytes
    | throw (IO.userError "the role binding does not decode")
  let bound := table.bound.toList.map (·.1)
  IO.println s!"[ixvm-decision-roles] compiled {constants.length} constants in \
    {(← IO.monoMsNow) - started} ms; the binding binds {bound.length} of {Role.all.length} roles"
  let mut failures := 0
  for r in required do
    unless bound.contains r do
      IO.eprintln s!"[ixvm-decision-roles] FAIL: the binding does not bind {repr r}"
      failures := failures + 1
  let target ← lookupAddr artifact leaf
  let code ← Tests.Ix.IxVM.runCases "ixvm-decision-roles" #[fun _ => do
    let (_, witness) ← buildShardCheckEnvWitness artifact #[target]
    return { label := s!"shard CheckEnv of {leaf} under its compiled binding",
             accept := true, witness }]
  return if failures == 0 && code == 0 then 0 else 1

end Tests.Ix.IxVM.DecisionRoles

end
