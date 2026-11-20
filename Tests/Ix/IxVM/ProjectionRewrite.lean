import Ix.IxVM.Model
import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.IndVariationsDefs

namespace Tests.Ix.IxVM.ProjectionRewrite

open Ix.Kernel.Reader
open _root_.IxVM
open _root_.IxVM.ClaimHarness

/-- At each fixture, whether IxC rewrites the declaration's own body. -/
private def fixtures : Array (Lean.Name × Bool) := #[
  (`IxIV.Constraint.value, true), (`IxIV.Constraint.reason, true), (`IxIV.NS.kids, true),
  (`IxIV.Pt.x, false), (`IxIV.Constraint.valueRec, false), (`IxIV.Constraint.value_mk, false)]

/-- Encode the recursor body at its own content address, with binder data
computed for the reconstructed syntax. -/
private def rewrittenAddress (env : Ixon.Env) (names : Model.Names) (name : Lean.Name)
    (source : Address) (decl : CDecl .anon) : Except String Address := do
  let .defnDecl cv body hint := decl | throw s!"{name}: expected a rewritten definition"
  let enc ← Model.encDefinition names cv body .defn (some hint)
  let #[(_, record)] := enc.records | throw s!"{name}: expected one definition record"
  let env := { env with blobs := enc.blobs.foldl (fun m (a, bytes) => m.insert a bytes) env.blobs }
  let record ← _root_.IxVM.RecordSections.withSection env record
  let target := Model.addressOf record
  if source == target then throw s!"{name}: the rewrite preserved the source address"
  return target

private def checkMissingRecursor (leanEnv : Lean.Environment) : IO Unit := do
  let name := `IxIV.Constraint.value
  let inputs := Ix.EnvScope.collectDeps leanEnv [name] {}
  if inputs.any (·.1 == `IxIV.Constraint.rec) then throw (IO.userError "expected a missing recursor")
  let prepared ← IO.ofExcept (Ix.Compile.ProjectionAccessors.prepare leanEnv inputs)
  let constants := Std.HashMap.ofList prepared
  let some (.defnInfo d) := constants[name]? | throw (IO.userError "missing prepared accessor")
  let refs := d.value.getUsedConstants
  unless refs.contains `IxIV.Constraint.rec && refs.all constants.contains do
    throw (IO.userError "the prepared accessor did not bring its dependencies")

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  checkMissingRecursor leanEnv
  let roots := fixtures.toList.map Prod.fst
  let inputs := Ix.EnvScope.collectSelectedDeps leanEnv roots
  let original ← IO.ofExcept (← Ix.CompileM.compileCertifiedPrepared inputs false (binderData := true))
  let normalized ← IO.ofExcept (← Ix.CompileM.compileCertified leanEnv inputs)
  unless original.failures.isEmpty && normalized.failures.isEmpty do
    throw (IO.userError "the accessor fixture failed to compile")
  let env ← IO.ofExcept (withDefaultRoleBinding original.env)
  let checkEnv ← IO.ofExcept (withDefaultRoleBinding normalized.env)
  let native ← lookupAddr env `IxIV.Pt.x
  let mut pending : Std.HashMap Address (Lean.Name × Bool) := {}
  for (name, rewrites) in fixtures do
    pending := pending.insert (← lookupAddr env name) (name, rewrites)
  let (table, pre) ← IO.ofExcept (_root_.IxVM.RecordSections.chosenOf env)
  let names : Model.Names := { roles := table.bound.foldl (fun m (r, a) => m.insert r a) {} }
  let records ← env.consts.toArray.mapM fun (a, lc) => do
    let some c := lc.get? | throw (IO.userError s!"invalid record {a}")
    return (a, c)
  let hints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore (Std.HashMap.ofList records.toList) env.anonHints
  let cx : Ctx .anon := contextOf table records env.blobs.toList (pre.records ++ pre.evidence)
    pre.blobs hints.lookup (Ix.Kernel.Admission.projectionAddress Address.blake3)
  let mut st := pre.state
  let mut targets : Array (Lean.Name × Address) := #[]
  for a in Ixon.CheckOrder.wholeEnv table pre records do
    let some c := env.getConst? a | throw (IO.userError s!"missing record {a}")
    match readRecord cx st a c with
    | .error why =>
      if pending.contains a then throw (IO.userError s!"cannot read fixture {a}: {why}")
    | .ok r =>
      if let some (name, rewrites) := pending[a]? then
        pending := pending.erase a
        unless r.projRewrites == (if rewrites then 1 else 0) do
          throw (IO.userError s!"{name}: unexpected rewrite count {r.projRewrites}")
        if rewrites then
          let #[decl] := r.decls | throw (IO.userError s!"{name}: expected one declaration")
          let target ← IO.ofExcept (rewrittenAddress env names name a decl)
          unless (← lookupAddr checkEnv name) == target do
            throw (IO.userError s!"{name}: compiler output differs from IxC's reconstructed accessor")
          targets := targets.push (name, target)
      st := st.commit r
    if pending.isEmpty then break
  unless pending.isEmpty do throw (IO.userError s!"missing fixtures: {pending.toList.map (·.2.1)}")
  unless (← lookupAddr checkEnv `IxIV.Pt.x) == native do
    throw (IO.userError "the native projection changed")
  let theoremAddr ← lookupAddr checkEnv `IxIV.Constraint.value_mk
  if theoremAddr == (← lookupAddr env `IxIV.Constraint.value_mk) then
    throw (IO.userError "the computation theorem still names the old accessor")
  targets := targets.push (`IxIV.Constraint.value_mk, theoremAddr)
  let cases : Array Builder := targets.map fun (name, target) _ => do
    let (_, witness) ← buildShardCheckEnvWitness checkEnv #[target] (assumeBinding := true)
    return { label := s!"compiled {name}", witness, accept := true }
  runCases "ixvm-projection-rewrite" cases

end Tests.Ix.IxVM.ProjectionRewrite
