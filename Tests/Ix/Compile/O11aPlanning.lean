/- Focused producer-plan regressions, including actual recursive O2 effects. -/
import Tests.Ix.Compile.O11aCopies
import Tests.Ix.Compile.O11aDecline
import Ix.Compile.Pass.Opt.ProducerPlan
open Lean
namespace Tests.Ix.Compile.O11aPlanning
open _root_.Ix.Compile.Pass.Opt
open Tests.Ix.Compile.Harness
open Tests.Ix.Compile.O11aDecline (dropWithDependents references)

def nm (s : String) := _root_.Ix.Name.fromLeanName s.toName

def graph (names : Array _root_.Ix.Name) (edges : Array (_root_.Ix.Name × _root_.Ix.Name)) :
    _root_.Ix.CondensedBlocks := Id.run do
  let mut out : _root_.Ix.CondensedBlocks := ⟨{}, {}, {}⟩
  for n in names do
    out := { out with
      lowLinks := out.lowLinks.insert n n
      blocks := out.blocks.insert n (({} : _root_.Ix.Set _root_.Ix.Name).insert n)
      blockRefs := out.blockRefs.insert n {} }
  for (a, b) in edges do out := { out with
    blockRefs := out.blockRefs.insert a ((out.blockRefs.getD a {}).insert b) }
  return out

/-- Whole-proposal cycle analysis, zero-length reachability and reverse propagation. -/
def graphControls : Bool := Id.run do
  let p := nm "P"; let q := nm "Q"; let a := nm "A"; let b := nm "B"
  let self := planProducerDeps (graph #[p] #[]) #[(p, p)]
  let base := graph #[p, q, a, b] #[(p, a), (q, b)]
  let pairs := #[(a, q), (b, p)]
  let forward := planProducerDeps base pairs
  let reverse := planProducerDeps base pairs.reverse
  let parent := planProducerDeps (graph #[p, a, b] #[(b, a)]) #[(a, p)]
  let absent := planProducerDeps (graph #[a] #[]) #[(a, p)]
  return (self.2.getD p {}).contains p && (self.1.blockRefs.getD p {}).isEmpty &&
    (forward.2.getD a {}).contains q && (forward.2.getD b {}).contains p &&
    (forward.2.getD a {}).get? q == (reverse.2.getD a {}).get? q &&
    (forward.2.getD b {}).get? p == (reverse.2.getD b {}).get? p &&
    !(forward.1.blockRefs.getD a {}).contains q &&
    !(forward.1.blockRefs.getD b {}).contains p &&
    (parent.1.blockRefs.getD a {}).contains p && (parent.1.blockRefs.getD b {}).contains p &&
    parent.2.isEmpty && (absent.2.getD a {}).contains p &&
    (absent.1.blockRefs.getD a {}).isEmpty

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def checkUnit (u : CUnit) : IO (Ix.CompileM.LeanPipelineOut × Bool) := do
  let (out, same) ← Tests.Ix.Compile.O11aCopies.compareSchedules u
  let dir ← IO.FS.createTempDir
  try
    let (bytes, status) ← Tests.Ix.Compile.ClosureHarness.rustClosure u.env u.closure (dir / "rust.ixe")
    let reports := status.nonCanonical.qsort (·.1 < ·.1)
    let ok := same && status.ungrounded.isEmpty && bytes == out.bytes &&
      reports == Tests.Ix.Compile.O11aCopies.causes out.cenv
    IO.println s!"[o11a-planning] {u.name}: four schedules and Rust {ok}"
    for (n, why) in out.cenv.p3NonCanonical do
      IO.println s!"[o11a-planning] {u.name}: {n.pretty}: {why}"
    return (out, ok)
  finally IO.FS.removeDirAll dir

def run : IO UInt32 := do
  let mut ok := graphControls
  IO.println s!"[o11a-planning] graph controls {ok}"
  let env ← getFileEnv "Tests/Ix/Compile/Pass/O11aProducers.lean"
  let caller := `O11aProducers.Cycle.caller
  let inst := `O11aProducers.Cycle.B._sizeOf_inst
  let good := `O11aProducers.Cycle.good
  let unrelated := `O11aProducers.Cycle.unrelated
  let some (.defnInfo sizeFn) := env.find? `O11aProducers.Cycle.B.sizeFn
    | throw <| IO.userError "missing cycle size function"
  unless sizeFn.value.getUsedConstants.contains caller do
    throw <| IO.userError "cycle fixture lost its binder-domain dependency"
  let seeds := #[caller, good, unrelated, inst]
  let (cyc, passed) ← checkUnit {
    name := "cycle", env, seeds
    closure := Ix.EnvScope.collectSelectedDeps env seeds.toList }
  ok := ok && passed && has (cyc.cenv.p3NonCanonical.getD (ixN caller) "") "dependency cycle" &&
    !cyc.cenv.p3NonCanonical.contains (ixN good) &&
    !cyc.cenv.p3NonCanonical.contains (ixN unrelated)
  ok := ok && !(← IO.ofExcept (references cyc.env caller inst)) &&
    (← IO.ofExcept (references cyc.env good inst))

  let root := `O11aProducers.Chain.X._sizeOf_1
  let missing := `O11aProducers.Chain.Y._sizeOf_inst
  let lower := `O11aProducers.Chain.Z._sizeOf_inst
  let cs := dropWithDependents (Ix.EnvScope.collectSelectedDeps env [root]) [missing]
  let (chain, passed) ← checkUnit { name := "recursive absent middle", env, seeds := #[root], closure := cs }
  ok := ok && passed && has (chain.cenv.p3NonCanonical.getD (ixN root) "") missing.toString &&
    (← IO.ofExcept (references chain.env root lower))

  -- A later failed producer must be reported through the chosen recursive
  -- O2 path, even when the outer occurrence already has a missing-instance cause.
  let failedLower := { chain.cenv with
    ungrounded := chain.cenv.ungrounded.insert (ixN lower) "injected terminal failure" }
  let (_, recursivePub) ← IO.ofExcept ((Ix.Compile.Pass.prepareBlock failedLower
    (({} : _root_.Ix.Set _root_.Ix.Name).insert (ixN root)) (ixN root)).mapError toString)
  let recursiveReport := recursivePub.declines.any fun (n, why) =>
    n == ixN root && has why missing.toString && has why lower.toString && has why "failed compilation"
  IO.println s!"[o11a-planning] recursive failed-producer report: {recursiveReport}"
  ok := ok && recursiveReport

  let mixed := `O11aProducers.Mixed.A._sizeOf_1
  let (mix, passed) ← checkUnit {
    name := "mixed alias", env, seeds := #[mixed]
    closure := Ix.EnvScope.collectSelectedDeps env [mixed] }
  ok := ok && passed && has (mix.cenv.p3NonCanonical.getD (ixN mixed) "") "recursive fields" &&
    !(← IO.ofExcept (references mix.env mixed `O11aProducers.Mixed.B._sizeOf_inst))
  let dir ← IO.FS.createTempDir
  try
    let checked ← kernelRun dir mix.bytes #[(ixN mixed).pretty] (anon := true)
    let report ← IO.ofExcept (Tests.Ix.Compile.KernelReport.parse
      (← IO.FS.readFile (dir / "out.jsonl")))
    let verdict ← IO.ofExcept (Tests.Ix.Compile.ClosureHarness.verdictOf report mix.env mixed)
    IO.println s!"[o11a-planning] mixed alias {mixed}: certified {verdict.outcome}; checked {checked.checked}"
    IO.println s!"[o11a-planning] mixed alias kernel failures: {checked.failed.size}"
    for (leg, n, why) in checked.failed do IO.println s!"[o11a-planning] {leg}: {n}: {why}"
    ok := ok && verdict.outcome == "accept" && checked.failed.isEmpty &&
      checked.checked.all (fun (_, count) => count > 0)
  finally IO.FS.removeDirAll dir

  let env ← getFileEnv "Tests/Ix/Compile/Pass/O2Split.lean"
  let root := `PassO2.SA._sizeOf_1
  let producer := ixN `PassO2.SB._sizeOf_inst
  let full := Ix.EnvScope.collectSelectedDeps env [root]
  let base ← compileUnit { name := "producer-failure", env, seeds := #[root], closure := full } 1
  for failure in [true, false] do
    let cause := if failure then "failed compilation" else "outside the grounded input"
    let cenv := if failure then
        { base.cenv with ungrounded := base.cenv.ungrounded.insert producer "injected terminal failure" }
      else
        { base.cenv with
          p3O11aPlans := base.cenv.p3O11aPlans.insert (ixN root)
            (({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName String).insert producer
              s!"producer {producer.pretty} is {cause}") }
    let (_, pub) ← IO.ofExcept ((Ix.Compile.Pass.prepareBlock cenv
      (({} : _root_.Ix.Set _root_.Ix.Name).insert (ixN root)) (ixN root)).mapError toString)
    let reported := pub.declines.any fun (n, why) => n == ixN root && has why cause
    IO.println s!"[o11a-planning] present producer {cause}: {reported}"
    ok := ok && reported
  let missingProjection := dropWithDependents full [``SizeOf.sizeOf]
  let (proj, passed) ← checkUnit {
    name := "missing projection", env, seeds := #[root]
    closure := missingProjection }
  ok := ok && passed && has (proj.cenv.p3NonCanonical.getD (ixN root) "") "SizeOf.sizeOf" &&
    has (proj.cenv.p3NonCanonical.getD (ixN root) "") "absent from the input"
  IO.println s!"[o11a-planning] {if ok then "PASS" else "FAIL"}"
  return if ok then 0 else 1

end Tests.Ix.Compile.O11aPlanning
