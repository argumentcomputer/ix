import Ix.Cert.SourceAccounting
import Ix.Meta
import Ix.EnvScope
import Tests.Ix.Compile.GroundRefusal
import Tests.Ix.Compile.ClaimConflict
import Tests.Ix.Kernel.TierIndDefs

namespace Tests.Ix.Compile.SourceAccounting
open _root_.Ix (Name)
open _root_.Ix.Compile.SourceGraph.Accounting

def ordinary : Nat := 7
private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def refuses (want : Issue) : Except Issue Unit → Bool
  | .error got => decide (got = want)
  | .ok _ => false
private def facts (out : _root_.Ix.CompileM.LeanPipelineOut) : Except String (_root_.Ix.Map Name _root_.Ix.Compile.SourceGraph.Node) :=
  match out.sourceNodes? with
  | none => .error "source facts unavailable"
  | some nodes => .ok nodes
private def compile (env : Lean.Environment) (raw : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat := 1) :
    IO _root_.Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((_root_.Ix.Compile.compileInputFromEnv env raw).mapError toString)
  IO.ofExcept (← _root_.Ix.CompileM.compileLeanInput input (numWorkers := workers))

private def audit (label : String) (out : _root_.Ix.CompileM.LeanPipelineOut) : IO Nat := do
  let nodes ← IO.ofExcept (facts out)
  let named := out.env.named
  let failed := out.cenv.ungrounded
  let report := scan nodes named failed
  let both := report.uncovered.filter failed.contains
  let neither := report.uncovered.filter (!failed.contains ·)
  let (publishedOnly, failedOnly, regenerated) := nodes.fold (init := (0, 0, 0)) fun (p, f, r) n _ =>
    (p + if named.contains n && !failed.contains n then 1 else 0,
     f + if failed.contains n && !named.contains n then 1 else 0,
     r + if (named.get? n).any (·.original.isSome) then 1 else 0)
  IO.println s!"accounting {label}: input={nodes.size} published-only={publishedOnly} failed-only={failedOnly} both={both.size} neither={neither.size} outside={report.outside.size} regenerated-original={regenerated}"
  for n in report.uncovered ++ report.outside do
    IO.println s!"  anomaly {n.pretty}: input={nodes.contains n} published={named.contains n} failure={repr (failed.get? n)}"
  need (check nodes named failed |>.isOk) s!"genuine final producer accounting anomaly: {label}"
  return regenerated

private def mutations (out partialOut : _root_.Ix.CompileM.LeanPipelineOut) : IO Unit := do
  let nodes ← IO.ofExcept (facts out)
  let named := out.env.named
  let failed := out.cenv.ungrounded
  let some n := nodes.toList.findSome? (fun (n, _) =>
      if named.contains n && !failed.contains n then some n else none)
    | throw (IO.userError "mutation requires a published original")
  need (refuses (.neither n) (check nodes (named.erase n) failed)) "missing-publication mutation escaped"
  need (refuses (.both n) (check nodes named (failed.insert n "planted failure"))) "both mutation escaped"
  let outside := Name.fromLeanName `Accounting.absent
  need (!nodes.contains outside) "outside mutation is not outside the input"
  need (refuses (.outside outside) (check nodes named (failed.insert outside "planted outsider"))) "outside failure escaped"
  need ((check nodes (named.insert outside { addr := default }) failed).isOk) "generated non-input publication rejected"
  -- A retained error under a structural alias stays in the original key
  -- class. This accounting control makes no grounding-history claim.
  let aliasName : Name := .str .mkAnon "retained-error" n.getHash
  need (aliasName == n && !Name.beqRaw aliasName n) "alias control is not structurally distinct"
  let one := nodes.filter (fun k _ => k == n)
  let oldError : _root_.Ix.Map Name String := .ofList [(aliasName, "earlier error")]
  need (one.size == 1 && (check one {} oldError).isOk && refuses (.both n) (check one named oldError))
    "BEq alias failure was lost, treated as outside, or exempted from XOR"
  let partialNodes ← IO.ofExcept (facts partialOut)
  let some (bad, _) := partialNodes.toList.find? (fun (n, _) => partialOut.cenv.ungrounded.contains n)
    | throw (IO.userError "partial mutation requires an actual failure")
  need (!partialOut.env.named.contains bad) "partial negative starts already both"
  need (refuses (.both bad) (check partialNodes (partialOut.env.named.insert bad { addr := default }) partialOut.cenv.ungrounded))
    "failed-only to both mutation escaped"
  let f : _root_.Ix.Cert.Failures :=
    { ungrounded := .ofList [(n, "ground")], blocks := .ofList [(n, "block"), (outside, "other")] }
  need (f.toMap.get? n == some "ground" && [n, outside].all (fun k => f.toMap.contains k == f.failed k))
    "merged membership/diagnostic precedence control failed"
  IO.println "accounting mutations: neither/both/outside/failed-only-to-both rejected; generated publication allowed; BEq classes and overlapping report messages preserved"

def run : IO Unit := do
  let env ← getCompileEnv #[`Tests.Ix.Compile.SourceAccounting]
  let empty ← compile env []
  let _ ← audit "empty" empty
  need ((facts empty).isOk && !(facts { empty with sourceNodes? := none }).isOk) "unavailable facts became empty"
  let raw := _root_.Ix.EnvScope.collectDeps env [``ordinary, `Nat.rec, `Nat.brecOn, `List.rec]
  let normal ← compile env raw
  let regenerated ← audit "ordinary/regenerated" normal
  need (regenerated > 0) "regenerated input witness is empty"
  let groundRaw := GroundRefusal.closure env (· == `Nat.add)
  let partialOut ← compile env groundRaw 2
  let _ ← audit "ground-refusal partial" partialOut
  for (n, msg) in GroundRefusal.expected do
    need (partialOut.cenv.ungrounded.get? (Name.fromLeanName n.toName) == some msg) "existing ground refusal changed"
  need (partialOut.cenv.ungrounded.size == GroundRefusal.expected.size) "unexpected ground-refusal count"
  let conflicts ← IO.ofExcept (ClaimConflict.conflictClosure env)
  for workers in [1, 4] do
    let out ← compile env conflicts workers
    let _ ← audit s!"claim-conflict/{workers}" out
    need (!out.cenv.ungrounded.isEmpty) "claim-conflict census is vacuous"
  need (ClaimConflict.promotionCases.all (·.2)) "existing promotion/withdrawal controls failed"
  let tierRaw := _root_.Ix.EnvScope.collectDeps env
    [`Tests.Ix.Kernel.TierIndDefs.spin, `Tests.Ix.Kernel.TierIndDefs.kdef]
  let tier ← compile env tierRaw
  let _ ← audit "partial/unsafe source" tier
  for n in [`Tests.Ix.Kernel.TierIndDefs.spin, `Tests.Ix.Kernel.TierIndDefs.kdef] do
    need (tier.env.named.contains (Name.fromLeanName n) && !tier.cenv.ungrounded.contains (Name.fromLeanName n))
      "typed partial/unsafe input was not positively published"
  mutations normal partialOut

/-- info: 'Ix.Cert.SourceAccounting.check_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceAccounting.check_success_iff
/-- info: 'Ix.Cert.SourceAccounting.failures_toMap_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceAccounting.failures_toMap_contains
/-- info: 'Ix.Cert.SourceAccounting.produced_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceAccounting.produced_check_iff
/-- info: 'Ix.Cert.SourceAccounting.produced_uncovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceAccounting.produced_uncovered
/-- info: 'Ix.Cert.SourceAccounting.produced_outside_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceAccounting.produced_outside_empty_iff
/-- info: 'Ix.Cert.SourceAccounting.produced_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceAccounting.produced_published
end Tests.Ix.Compile.SourceAccounting
