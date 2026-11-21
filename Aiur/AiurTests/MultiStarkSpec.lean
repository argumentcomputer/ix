import Aiur.MultiStarkSpec
import Aiur.Library.U32.Goldilocks
import Aiur.Modules.Frontend
import Aiur.Trace.Export

/-!
# Parity & Certificate Tests for `Aiur.MultiStarkSpec` (`WS 2B-2`) and `WS 2B-1`

Cross-checks:
1. Exact agreement between `Aiur.MultiStarkSpec.retune` and
   `crates/aiur/src/trace/stark/lookup_groups.rs` on all mixed-degree and
   quotient-preserving unit-test circuits.
2. Exact agreement between `Aiur.MultiStarkSpec.lowerFullSystem` and
   `crates/aiur/src/trace/stark.rs` (`Backend::statistics()` +
   `circuit.constraint_count` + `circuit.max_constraint_degree`) on the
   `crates/aiur/tests/fixtures/depth.ixa` program (verified symmetrically in
   `crates/aiur/src/trace/stark/tests/spec_parity.rs`).
3. Executable `WS 2B-1` checkers (`Depth.certify`, `Depth.checkGoldilocks`,
   `Depth.checkGoldilocksPlan`, `Grouping.checkPlanCertificate`,
   `Plan.checkWellFormedActivation`).
-/

namespace AiurMultiStarkSpecTests

open Aiur Aiur.MultiStarkSpec Aiur.Optimized

private abbrev GF := Library.U32.Goldilocks.F

private def linPush (col : Nat) : AirLookup GF :=
  AirLookup.push (.main 0) [.main col]

private def quadPush (col : Nat) : AirLookup GF :=
  AirLookup.push (.main 0) [.mul (.main col) (.main col)]

private def retuneSummary (mainWidth : Nat) (lookups : List (AirLookup GF))
    (blowup : Nat := 4) (extDeg : Nat := 2) : CompiledCircuit GF :=
  let inp : CircuitInput GF := {
    name := "synthetic"
    mainWidth := mainWidth
    constraints := []
    lookups := lookups
    lookupGroupSize := 1 }
  retune (compileCircuit inp extDeg) blowup extDeg

/-- Mirror of `lookup_groups.rs:336-383`:
- 14 quadratic lookups at `blowup = 4` -> `group = 2, q = 4, s2 = 14`.
- `[lin, quad, lin]` at `blowup = 4` -> balanced packing puts `quad` in the
  trailing remainder chunk -> `group = 2, q = 2, s2 = 4` with reordered degrees
  `[(1, 1), (1, 1), (1, 2)]`. -/
private def checkMixedDegreeRetune : Bool :=
  let c0 := retuneSummary 4 ((List.range 14).map fun i => quadPush (1 + i % 3)) 4 2
  let c1 := retuneSummary 4 [linPush 1, quadPush 2, linPush 3] 4 2
  let c2 := retuneSummary 2 (List.replicate 11 (linPush 1)) 4 2
  let c3 := retuneSummary 2 (List.replicate 28 (linPush 1)) 4 2
  c0.lookupGroupSize == 2 && c0.quotientDegree == 4 && c0.stage2Width == 14 &&
    c0.constraintCount == 14 && c0.maxConstraintDegree == 5 &&
  c1.lookupGroupSize == 2 && c1.quotientDegree == 2 && c1.stage2Width == 4 &&
    c1.constraintCount == 4 && c1.maxConstraintDegree == 3 &&
    lookupDegrees c1.lookups == [(1, 1), (1, 1), (1, 2)] &&
  c2.lookupGroupSize == 2 && c2.quotientDegree == 2 && c2.stage2Width == 12 &&
    c2.constraintCount == 12 && c2.maxConstraintDegree == 3 &&
  c3.lookupGroupSize == 4 && c3.quotientDegree == 4 && c3.stage2Width == 14 &&
    c3.constraintCount == 14 && c3.maxConstraintDegree == 5

#guard checkMixedDegreeRetune

/-- Same source program as `Aiur/Examples/Depth.lean` (`crates/aiur/tests/fixtures/depth.ixa`). -/
private def depthFixtureProgram : Modules.Program Nat := aiur_modules% "
module Depth {
  fn loop(x: Field) -> Field { loop(x) }
  fn even(n: Field) -> Field { match n { 0 => 1, _ => odd(n - 1) } }
  fn odd(n: Field) -> Field { match n { 0 => 0, _ => even(n - 1) } }
  fn fib(n: Field) -> Field { match n { 0 => 0, 1 => 1, _ => fib(n - 1) + fib(n - 2) } }
  fn run(n: Field) -> Field { even(n) + fib(n) }
  fn owned(n: Field) -> () { match n { 0 => (), _ => link(n - 1) } }
  fn link(n: Field) -> () { owned(n) }
  fn top(n: Field) -> Field { let _unit = owned(n); n + 1 }
}
"

private def depthFixtureEntries : List String :=
  ["Depth::run", "Depth::fib", "Depth::loop", "Depth::top"]

/-- Extract `FixedMapMeta` from `Execution.Bytecode` exactly as
`crates/aiur/src/trace/stark/tables.rs` reads it. -/
private def fixedMapsOfBytecode [Field F] (bc : Execution.Bytecode F) : List FixedMapMeta :=
  let fnCount := bc.functions.length
  bc.maps.zipIdx.map fun (m, mi) =>
    let inTable := bc.tables[m.input]?.getD ⟨"", .tuple [], []⟩
    let inWidth := (inTable.rows.head?.map List.length).getD 0
    let outTable := bc.tables[m.output]?.getD ⟨"", .tuple [], []⟩
    let outWidth := (outTable.rows.head?.map List.length).getD 0
    { name := m.name
      callableId := fnCount + mi
      inputTableId := m.input
      outputTableId := m.output
      inputTableName := inTable.name
      rowCount := inTable.rows.length
      inputWidth := inWidth
      outputWidth := outWidth }

/-- Expected `CircuitSummary` table for `depth.ixa` at `logBlowup = 1`, `segmented = true`.
Mirrored identically in `crates/aiur/src/trace/stark/tests/spec_parity.rs`. -/
def expectedDepthFixtureSummaries : List CircuitSummary := [
  { name := "Depth::run", stage1Width := 7, stage2Width := 6,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 3, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 9, maxConstraintDegree := 2 },
  { name := "Depth::even", stage1Width := 7, stage2Width := 2,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 2, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 11, maxConstraintDegree := 3 },
  { name := "Depth::odd", stage1Width := 7, stage2Width := 2,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 2, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 11, maxConstraintDegree := 3 },
  { name := "Depth::fib", stage1Width := 14, stage2Width := 8,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 7, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 24, maxConstraintDegree := 3 },
  { name := "Depth::loop", stage1Width := 5, stage2Width := 4,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 2, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 7, maxConstraintDegree := 2 },
  { name := "Depth::top", stage1Width := 4, stage2Width := 4,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 2, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 7, maxConstraintDegree := 2 },
  { name := "Depth::owned", stage1Width := 6, stage2Width := 2,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 2, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 10, maxConstraintDegree := 3 },
  { name := "Depth::link", stage1Width := 4, stage2Width := 4,
    preprocessedWidth := 0, preprocessedHeight := 0,
    lookups := 2, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 7, maxConstraintDegree := 2 },
  { name := "<table:Depth::range16_inputs>", stage1Width := 1, stage2Width := 2,
    preprocessedWidth := 2, preprocessedHeight := 65536,
    lookups := 1, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 2, maxConstraintDegree := 2 },
  { name := "<table:Depth::range8_inputs>", stage1Width := 1, stage2Width := 2,
    preprocessedWidth := 2, preprocessedHeight := 256,
    lookups := 1, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 2, maxConstraintDegree := 2 }
]

def run : IO Unit := do
  let source := depthFixtureProgram.toField GF
  let prepared ← IO.ofExcept (Modules.prepare source depthFixtureEntries)
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let artifact := compiled.circuit.artifact
  let physical ← IO.ofExcept (Physical.prepare artifact)
  let cfg ← IO.ofExcept (Trace.depthConfig Library.U32.Goldilocks.modulus physical)
  unless Depth.checkGoldilocks cfg physical.system do
    throw (IO.userError "WS 2B-1: Depth.checkGoldilocks rejected depth fixture")
  let bytecode := Trace.depthBytecode cfg exported.bytecode
  let depthSys := Depth.system cfg physical.system
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let idFn : String → Except String Nat := fun name =>
    if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown callable {name}"
  let plan ← IO.ofExcept (Grouping.preparePlan depthSys idFn [])
  unless Depth.checkGoldilocksPlan cfg physical.system plan do
    throw (IO.userError "WS 2B-1: Depth.checkGoldilocksPlan rejected depth fixture plan")
  unless plan.checkWellFormedActivation do
    throw (IO.userError "WS 2B-1: Plan.checkWellFormedActivation rejected depth fixture plan")
  let callableId (name : String) : Nat := callableNames.idxOf name
  let fixedMaps := fixedMapsOfBytecode bytecode
  let lowered := lowerFullSystem callableId plan fixedMaps [] 1 true
  let summaries := lowered.map CompiledCircuit.summary
  unless summaries == expectedDepthFixtureSummaries do
    throw (IO.userError s!"WS 2B-2 depth.ixa parity mismatch!\nactual:\n{reprStr summaries}\nexpected:\n{reprStr expectedDepthFixtureSummaries}")
  -- Also test a grouped layout (`even` + `odd`) through `lowerFullSystem` and `checkGoldilocksPlan`.
  let groupChips := depthSys.chips.filter fun c => c.name == "Depth::even" || c.name == "Depth::odd"
  let checkedGroup ← IO.ofExcept (Grouping.compile "even_odd" idFn groupChips)
  let groupedPlan ← IO.ofExcept (Grouping.preparePlan depthSys idFn [⟨groupChips, checkedGroup⟩])
  unless Depth.checkGoldilocksPlan cfg physical.system groupedPlan do
    throw (IO.userError "WS 2B-1: Depth.checkGoldilocksPlan rejected grouped plan")
  let groupedLowered := lowerFullSystem callableId groupedPlan fixedMaps [] 1 true
  let some eo := groupedLowered.find? (·.name == "even_odd")
    | throw (IO.userError "WS 2B-2: missing grouped even_odd circuit")
  unless eo.mainWidth == checkedGroup.layout.width + 1 && eo.lookups.length == 1 + checkedGroup.layout.sends.length do
    throw (IO.userError "WS 2B-2: grouped even_odd width/lookup count mismatch")
  IO.println s!"MultiStarkSpec: verified retune + depth.ixa ({summaries.length} circuits) + grouped plan + WS 2B-1 certificates"

end AiurMultiStarkSpecTests
