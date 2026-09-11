import Ix.Compiler.CallReuse.PolicyExamples

/-! Fail-closed map specialization and policy regression matrix. -/

namespace Ix.Compiler.CallReuse.Examples

open Lean Ix.Compiler.Ixon

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def replace (entries : List (Address × IxIR0.Decl)) (address : Address)
    (declaration : IxIR0.Decl) : List (Address × IxIR0.Decl) :=
  entries.map fun entry => if entry.1 == address then (address, declaration) else entry

def rejectionChecks : Except String (List String) := do
  let mut names ← PolicyExamples.checks
  let source ← Examples.source [1, 2, 3] 42 false
  let compilation ← source.compile.mapError reprStr
  let .recovered recovery _ := compilation.outcome | throw "rejection fixture did not specialize"
  let p := recovery.checked.plan
  let s := p.schema
  let entries := compilation.source.erasure.result.raw
  for (name, changed) in [
      ("map-wrong-worker", replace entries s.worker (.defn .shared (.lam .many (.var 0)))),
      ("map-wrong-step", replace entries s.step (.defn .shared (.lam .many (.lam .many (.lam .many (.var 0)))))),
      ("map-wrong-base", replace entries s.base (.defn .shared .erased)),
      ("map-wrong-recursor", replace entries s.recursor (.recursor 2 true #[])),
      ("map-wrong-cons-arity", replace entries s.cons (.ctor 1 1)),
      ("map-wrong-nil-tag", replace entries s.nil (.ctor 1 0)),
      ("map-wrong-alias", replace entries s.alias (.defn .unique (.ref s.recursor))),
      ("map-wrong-entry", replace entries source.root (.defn .shared (.ref s.base)))] do
    need ((IxIR0.MapRecovery.check changed (.ref source.root) p).isNone) s!"{name}: proposal accepted"
    match IxIR0.MapRecovery.select changed (.ref source.root) with
    | .recovered _ => throw s!"{name}: automatic recovery accepted"
    | .literal _ => pure ()
    names := names ++ [name]
  let collision := (recovery.address, .defn .shared .erased) :: entries
  match IxIR0.MapRecovery.selectWith collision (.ref source.root) (some p) with
  | .literal .addressConflict => pure ()
  | _ => throw "map specialization reused an existing declaration identity"
  names := names ++ ["map-address-conflict"]
  match lowerMap recovery 1000 0 with
  | .error (.attachment (.lowering _)) => pure ()
  | .error error => throw s!"map backend fallback failed for wrong reason: {repr error}"
  | .ok _ => throw "map backend depth limit was ignored"
  names := names ++ ["map-backend-fallback"]
  let skipped ← (compileMap source.constants source.root source.config 1000 1000 1000 1000 0).mapError reprStr
  match skipped.outcome with
  | .literal (.attachment (.lowering _)) =>
      need (skipped.source.artifact.main.bytes == compilation.source.artifact.main.bytes &&
        Coverage.ir1Entries skipped.source.artifact.targetDecls == Coverage.ir1Entries compilation.source.artifact.targetDecls)
        "map fallback changed the literal compiler artifact"
      let (store, value) ← (IxIR1.runOwnedMain
        { decls := skipped.source.artifact.targetDeclEnv } .shared skipped.source.artifact.main 10000).mapError reprStr
      let released ← (IxIR1.dropVal { decls := skipped.source.artifact.targetDeclEnv } 10000 store value).mapError reprStr
      need (released.live == 0 && released.frees == released.allocs) "literal map fallback did not reclaim"
  | _ => throw "map compilation did not select its literal fallback"
  names := names ++ ["map-literal-fallback-execution"]
  return names

def runAll : Except String (List CaseResult × List String) := do
  let results ← cases.mapM fun (name, values, replacement, aliased, uniquePrefix) =>
    (runCase name values replacement aliased uniquePrefix).mapError (fun message => s!"{name}: {message}")
  return (results, ← rejectionChecks)

def report (results : List CaseResult) (checks : List String) : Json :=
  Json.mkObj [("format", toJson "compilatrix/source-call-reuse-report/1"),
    ("cases", toJson (results.map (·.summary))), ("policy_and_rejection_checks", toJson checks)]

end Ix.Compiler.CallReuse.Examples
