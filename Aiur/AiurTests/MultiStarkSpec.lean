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

/-- Real Aiur module exercising `C2` cross-channel intra-chip compaction:
- `dispatch3`: 3 mutually-exclusive calls to distinct channels (`f1`, `f2`, `f3`)
  -> compacts `3 → 1` slot in a 1-member group!
- `dispatch2`: 2 mutually-exclusive deg-1 calls (`f1`, `f2`) -> guarded by the
  `retune` `g=4→2` threshold (`≥ 3`), stays `2` deg-1 slots!
- `dispatch2_quad`: 2 mutually-exclusive calls with a deg-2 arg (`f1(x * x)`)
  -> `hadDeg2` allows `2 → 1` compaction! -/
private def compactTestProgram : Modules.Program Nat := aiur_modules% "
module CompactTest {
  fn f1(x: Field) -> Field { x + 1 }
  fn f2(x: Field) -> Field { x + 2 }
  fn f3(x: Field) -> Field { x + 3 }
  fn dispatch3(tag: Field, x: Field) -> Field {
    match tag {
      0 => f1(x),
      1 => f2(x),
      _ => f3(x),
    }
  }
  fn dispatch2(tag: Field, x: Field) -> Field {
    match tag {
      0 => f1(x),
      _ => f2(x),
    }
  }
  fn dispatch2_quad(tag: Field, x: Field) -> Field {
    match tag {
      0 => f1(x),
      1 => f1(x + 1),
      _ => f2(x),
    }
  }
}
"

private def testC7AndC2 : IO Unit := do
  -- 1. `C7a`: Per-member slot sorting aligns deg-2 lookups instead of smearing across deg-1 slots.
  -- `enable := .var 0` places `var 0` in `privateCols`, so `.var 0` stays degree 1 while
  -- `.mul (.var 0) (.var 1)` stays degree 2 (no lifting).
  let deg1Send (ch : String) : Circuit.Send GF :=
    { enable := .var 0, channel := ch, args := [.field (.var 0)], result := .field 0 }
  let deg2Send (ch : String) : Circuit.Send GF :=
    { enable := .var 0, channel := ch, args := [.field (.mul (.var 0) (.var 1))], result := .field 0 }
  let chipA : Circuit.Chip GF := {
    name := "c7a_a", numVars := 2
    inputs := [.field 0, .field 1], output := .field (.var 0)
    constraints := [], sends := [deg1Send "h1", deg2Send "h2"], memory := [] }
  let chipB : Circuit.Chip GF := {
    name := "c7a_b", numVars := 2
    inputs := [.field 0, .field 1], output := .field (.var 0)
    constraints := [], sends := [deg2Send "h2", deg1Send "h1"], memory := [] }
  let c7aId : String → Except String Nat
    | "c7a_a" => .ok 0
    | "c7a_b" => .ok 1
    | "h1" => .ok 2
    | "h2" => .ok 3
    | s => .error s!"unknown {s}"
  let unsorted ← IO.ofExcept (Grouping.compile "c7a_unsorted" c7aId [chipA, chipB] false false)
  let sorted ← IO.ofExcept (Grouping.compile "c7a_sorted" c7aId [chipA, chipB] true false)
  let countDeg2 (l : Grouping.Layout GF) : Nat :=
    l.sends.countP fun s => (s.args.foldl (fun acc p => max acc p.degree) 0) ≥ 2
  unless countDeg2 unsorted.layout == 2 && countDeg2 sorted.layout == 1 do
    throw (IO.userError s!"C7a: expected deg-2 slots 2 → 1, got {countDeg2 unsorted.layout} → {countDeg2 sorted.layout}")

  -- 2. `C7b`: Relaxing constraint cap 3 → 5 on q=4 groups reduces width while keeping q ≤ 4.
  let cubicChip (nm : String) (numSends : Nat) : Circuit.Chip GF := {
    name := nm, numVars := 4
    inputs := [.field 0, .field 1, .field 2], output := .field (.var 3)
    constraints := [.mul (.var 0) (.mul (.var 1) (.var 2))]
    sends := (List.range numSends).map fun _ =>
      { enable := .const 1, channel := "h1", args := [.field (.var 0)], result := .field 3 }
    memory := [] }
  let c7bId : String → Except String Nat
    | "c7b_a" => .ok 0
    | "c7b_b" => .ok 1
    | "h1" => .ok 2
    | s => .error s!"unknown {s}"
  let c7bSources := [cubicChip "c7b_a" 20, cubicChip "c7b_b" 20]
  let cap3 ← IO.ofExcept (Grouping.compile "c7b_cap3" c7bId c7bSources true false (some 3))
  let autoQ4 ← IO.ofExcept (Grouping.compile "c7b_auto" c7bId c7bSources true false none)
  let maxDegAuto := autoQ4.layout.constraints.foldl (fun acc p => max acc p.degree) 0
  unless autoQ4.layout.width < cap3.layout.width && maxDegAuto ≤ 5 &&
      quotientDegreeFromMax maxDegAuto ≤ 4 do
    throw (IO.userError s!"C7b: expected width {autoQ4.layout.width} < {cap3.layout.width}, maxDeg={maxDegAuto}")
  -- Small q=2 group stays at cap=3 (maxDeg ≤ 3, q ≤ 2).
  let smallSources := [cubicChip "c7b_a" 1, cubicChip "c7b_b" 1]
  let autoSmall ← IO.ofExcept (Grouping.compile "c7b_small" c7bId smallSources true false none)
  let maxDegSmall := autoSmall.layout.constraints.foldl (fun acc p => max acc p.degree) 0
  unless maxDegSmall ≤ 3 do
    throw (IO.userError s!"C7b: small q=2 group exceeded degree 3 (got {maxDegSmall})")

  -- 3. `C2`: Real Aiur program — 1-member group + cross-channel compaction + retune guard + negative check.
  let c2Src := compactTestProgram.toField GF
  let c2Prep ← IO.ofExcept (Modules.prepare c2Src
    ["CompactTest::dispatch3", "CompactTest::dispatch2", "CompactTest::dispatch2_quad"])
  let c2Exp ← IO.ofExcept c2Prep.exportExecution
  let c2Comp ← IO.ofExcept c2Prep.compileOptimized
  let c2Phys ← IO.ofExcept (Physical.prepare c2Comp.circuit.artifact)
  let c2Callables := c2Exp.bytecode.functions.map (·.name) ++ c2Exp.bytecode.maps.map (·.name)
  let c2Id : String → Except String Nat := fun name =>
    if c2Callables.contains name then pure (c2Callables.idxOf name)
    else throw s!"unknown callable {name}"
  let findChip (nm : String) : IO (Circuit.Chip GF) :=
    match c2Phys.system.findChip? nm with
    | some c => pure c
    | none => throw (IO.userError s!"missing chip {nm}")
  let d3Chip ← findChip "CompactTest::dispatch3"
  let d2Chip ← findChip "CompactTest::dispatch2"
  let d2qChip ← findChip "CompactTest::dispatch2_quad"

  let d3NoCompact ← IO.ofExcept (Grouping.compile "d3_plain" c2Id [d3Chip] true false)
  let d3Compact ← IO.ofExcept (Grouping.compile "d3_compact" c2Id [d3Chip] true true)
  unless d3NoCompact.layout.sends.length == 3 && d3Compact.layout.sends.length == 1 do
    throw (IO.userError s!"C2 dispatch3: expected sends 3 → 1, got {d3NoCompact.layout.sends.length} → {d3Compact.layout.sends.length}")

  let d2Compact ← IO.ofExcept (Grouping.compile "d2_compact" c2Id [d2Chip] true true)
  unless d2Compact.layout.sends.length == 2 do
    throw (IO.userError s!"C2 dispatch2 retune guard: expected 2 deg-1 slots preserved, got {d2Compact.layout.sends.length}")

  let d2qNoCompact ← IO.ofExcept (Grouping.compile "d2q_plain" c2Id [d2qChip] true false)
  let d2qCompact ← IO.ofExcept (Grouping.compile "d2q_compact" c2Id [d2qChip] true true)
  unless d2qNoCompact.layout.sends.length == 2 && d2qCompact.layout.sends.length == 1 do
    throw (IO.userError s!"C2 dispatch2_quad: expected sends 2 → 1, got {d2qNoCompact.layout.sends.length} → {d2qCompact.layout.sends.length}")

  -- Negative tamper test: stripping exclusion constraints from `d3Chip` must be rejected by `certify`.
  let strippedOrigin : Circuit.Chip GF := { d3Chip with constraints := [] }
  let tamperedLayout : Grouping.Layout GF :=
    { d3Compact.layout with members := d3Compact.layout.members.map fun m => { m with origin := strippedOrigin } }
  match Grouping.certify [strippedOrigin] c2Id tamperedLayout with
  | .ok _ => throw (IO.userError "C2 negative test: certify accepted compacted slot without exclusion constraints")
  | .error _ => pure ()
  -- Negative tamper test: perturbing a compacted slot word must be rejected by `certify`.
  let badWordLayout : Grouping.Layout GF :=
    { d3Compact.layout with
      sends := d3Compact.layout.sends.map fun s =>
        { s with args := s.args.take 2 ++ [.add (Grouping.word s.args 2) (.const 1)] ++ s.args.drop 3 } }
  match Grouping.certify [d3Chip] c2Id badWordLayout with
  | .ok _ => throw (IO.userError "C2 negative test: certify accepted tampered compacted slot argument")
  | .error _ => pure ()
  IO.println s!"MultiStarkSpec C7+C2: C7a deg2 2→1, C7b width {cap3.layout.width}→{autoQ4.layout.width} (maxDeg={maxDegAuto}), C2 dispatch3 3→1, dispatch2 guard=2, dispatch2_quad 2→1, negative checks rejected"

/-- Exact `C6` vectorized ROM circuit summaries for widths `[1, 3, 5, 13]` at
`blowup = 4`, `segmented = true`, mirrored in
`crates/aiur/src/trace/stark/tests/spec_parity.rs`. -/
def expectedVectorizedRomSummaries : List CircuitSummary := [
  { name := "<ROM:1>", stage1Width := 25, stage2Width := 10, preprocessedWidth := 0,
    preprocessedHeight := 0, lookups := 10, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 35, maxConstraintDegree := 3 },
  { name := "<ROM:3>", stage1Width := 41, stage2Width := 10, preprocessedWidth := 0,
    preprocessedHeight := 0, lookups := 10, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 35, maxConstraintDegree := 3 },
  { name := "<ROM:5>", stage1Width := 29, stage2Width := 6, preprocessedWidth := 0,
    preprocessedHeight := 0, lookups := 6, lookupGroupSize := 2, quotientDegree := 2,
    constraintCount := 19, maxConstraintDegree := 3 },
  { name := "<ROM:13>", stage1Width := 16, stage2Width := 6, preprocessedWidth := 0,
    preprocessedHeight := 0, lookups := 3, lookupGroupSize := 1, quotientDegree := 1,
    constraintCount := 10, maxConstraintDegree := 2 }
]

def testVectorizedRom : IO Unit := do
  let widths := [1, 3, 5, 13]
  let vecSummaries :=
    (lowerVectorizedRomCircuits (F := GF) widths true).map fun inp =>
      (retune (compileCircuit inp) 4).summary
  unless vecSummaries == expectedVectorizedRomSummaries do
    throw (IO.userError s!"C6 vectorized ROM parity mismatch!\nactual:\n{reprStr vecSummaries}\nexpected:\n{reprStr expectedVectorizedRomSummaries}")
  let scalarRom3 := (retune (compileCircuit (lowerScalarRomCircuit (F := GF) 3 true)) 4).summary
  let vecRom3 := (retune (compileCircuit (lowerVectorizedRomCircuit (F := GF) 3 true)) 4).summary
  -- Compare total committed cells per 8 `<ROM:3>` entries (main + stage2 + quotient*ext).
  let scalarCells8 := (scalarRom3.stage1Width + scalarRom3.stage2Width + scalarRom3.quotientDegree * 2) * 8
  let vecCells8 := (vecRom3.stage1Width + vecRom3.stage2Width + vecRom3.quotientDegree * 2) * 1
  unless scalarCells8 == 112 && vecCells8 == 55 do
    throw (IO.userError s!"C6 <ROM:3> cell delta mismatch: scalar={scalarCells8}, vec={vecCells8}")
  IO.println s!"MultiStarkSpec C6: vectorized ROM [1,3,5,13] matches spec, <ROM:3> cells/8-entries {scalarCells8}→{vecCells8} (-50.9%, -3 max_log)"

def run : IO Unit := do
  testC7AndC2
  testVectorizedRom
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
