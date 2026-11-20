import Ix.IxVM.ProjectionAccessor
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
private def storeRewritten (env : Ixon.Env) (names : Model.Names) (name : Lean.Name)
    (source : Address) (decl : CDecl .anon) : Except String (Ixon.Env × Address) := do
  let .defnDecl cv body hint := decl | throw s!"{name}: expected a rewritten definition"
  let enc ← Model.encDefinition names cv body .defn (some hint)
  let #[(_, record)] := enc.records | throw s!"{name}: expected one definition record"
  let env := { env with blobs := enc.blobs.foldl (fun m (a, bytes) => m.insert a bytes) env.blobs }
  let record ← _root_.IxVM.RecordSections.withSection env record
  let target := Model.addressOf record
  if source == target then throw s!"{name}: the rewrite preserved the source address"
  let env := env.storeConst target record
  let env := { env with anonHints := env.anonHints.insert target (Model.hintOf hint) }
  return (env, target)

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let env ← loadSharedIxonEnv (fixtures.map Prod.fst) leanEnv
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
  let mut rewrittenEnv := env
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
        let some lc := env.consts[a]? | throw (IO.userError s!"missing bytes for {name}")
        match ProjectionAccessor.readStored? cx st a lc.rawBytes with
        | none =>
          if rewrites then throw (IO.userError s!"{name}: accessor reconstruction failed")
        | some decl =>
          unless rewrites && r.decls == #[decl] do
            throw (IO.userError s!"{name}: reconstructed declaration differs from the reader")
          if (ProjectionAccessor.readStored? cx st native lc.rawBytes).isSome then
            throw (IO.userError s!"{name}: reconstructed at a different source address")
          let (env', target) ← IO.ofExcept (storeRewritten rewrittenEnv names name a decl)
          rewrittenEnv := env'
          targets := targets.push (name, target)
      st := st.commit r
    if pending.isEmpty then break
  unless pending.isEmpty do throw (IO.userError s!"missing fixtures: {pending.toList.map (·.2.1)}")
  let checkEnv ← IO.ofExcept (withDefaultRoleBinding rewrittenEnv)
  let cases : Array Builder := targets.map fun (name, target) _ => do
    let (_, witness) ← buildShardCheckEnvWitness checkEnv #[target] (assumeBinding := true)
    return { label := s!"IxC recursor body for {name}", witness, accept := true }
  runCases "ixvm-projection-rewrite" cases

end Tests.Ix.IxVM.ProjectionRewrite
