module

import Scripts.Performance.SharingScratch
import Ix.Sharing.Exact
import Ix.Ixon
import all Ix.Sharing.FamilyContext

public section

open Ix.Sharing.Exact Ix.Sharing.Family

private def sameComponent (a b : CompResult) : Bool :=
  a.members == b.members && a.bestDelta == b.bestDelta &&
    a.bestSet == b.bestSet && a.bySize == b.bySize

private def sameMeter : Except SharingError MeterState → Except SharingError MeterState → Bool
  | .error a, .error b => a == b
  | .ok (a, states, work), .ok (b, states', work') =>
    states == states' && work == work' && a.size == b.size &&
      (a.zip b).all fun (x, y) => sameComponent x y
  | _, _ => false

private structure Sample where
  address : Address
  expanded : Expanded

private structure WidthCase where
  address : Address
  expanded : Expanded
  stage : UStage
  width : Nat
  parents : Array (Array Nat)

private def loadSamples (path : String) : IO (Array Sample) := do
  let environment ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  let records := environment.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  records.mapM fun (address, stored) => do
    let constant ← IO.ofExcept stored.get
    let expanded ← IO.ofExcept ((expand {} constant.sharing
      (constantInfoRoots constant.info) true).mapError toString)
    return { address, expanded }

private def prepareCases (samples : Array Sample) : Array WidthCase := Id.run do
  let mut cases := #[]
  for sample in samples do
    let prep := Prep.ofDag sample.expanded.dag
    let facts := graphFacts sample.expanded.dag sample.expanded.roots
    let parents := parentsOf sample.expanded.dag
    for width in #[1, 2, 3] do
      cases := cases.push {
        address := sample.address
        expanded := sample.expanded
        stage := uniformStageF width sample.expanded prep facts
        width := width
        parents := parents }
  return cases

private def runCase (mode : String) (config : Config) (limits : Limits) (sample : WidthCase) :
    Except SharingError MeterState :=
  if mode == "reference" then
    LightContext.components config limits sample.expanded sample.stage sample.width sample.parents
  else
    Ix.Sharing.Scratch.components (mode == "reuse") config limits sample.expanded
      sample.stage sample.width sample.parents

private def checkRows (sample : WidthCase) : IO Nat := do
  let ex := sample.expanded
  let stage := sample.stage
  let base := TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq
  let mut count := 0
  for members in stage.comps.extract 0 4 do
    let (full, closurePositions) := mkSCtxL ex stage.f stage.up stage.cand stage.b0
      stage.vis0 stage.rootCount stage.slack stage.theta stage.baseEv stage.widthCs
      stage.allTrue stage.unc sample.parents (Array.replicate ex.dag.size 0) members
    let positions := setPositions (Array.replicate ex.dag.size 0) full.area
    let malformed := positions.map (· + full.area.size + 2)
    let huge : TBase := { base with
      cost := base.cost.map (· + 2 ^ 80), inl := base.inl.map (· + 2 ^ 80),
      sides := base.sides.map (· + 2 ^ 80) }
    for positions in #[positions, malformed, Array.replicate ex.dag.size 0] do
      for base in #[base, huge] do
        let n := full.area.size
        let poison : Ix.Sharing.Scratch.Rows :=
          { cost := Array.replicate (n + 3) (2 ^ 90), inl := #[999],
            sides := Array.replicate (n + 1) 37, below := Array.replicate (n + 2) 91 }
        let mut scratch := poison
        let flagSize := 2 * n + 4
        unless positions.all (fun position => position == 0 || position - 1 < flagSize) do
          throw (IO.userError s!"row-control flags do not cover positions at {sample.address}")
        for flags in #[Array.replicate flagSize false, Array.replicate flagSize true,
            Array.ofFn (n := flagSize) (fun i => i.val % 2 == 0)] do
          let reference := areaFold stage.up.prep stage.up.opaq base sample.width
            full.area positions flags
          scratch := Ix.Sharing.Scratch.evaluateRows stage.up.prep stage.up.opaq base
            sample.width full.area positions flags scratch
          unless scratch.prefix n == reference do
            throw (IO.userError s!"scratch row mismatch at {sample.address}")
          count := count + 1
    let zeroPositions := Array.replicate ex.dag.size 0
    let light := { full with area := #[] }
    let zeroInline := { base with inl := Array.replicate ex.dag.size 0 }
    let aux : AAux := { csize := full.closure.size, K := 0, rootsA := #[], storedA := #[0] }
    let fallback := fun _ : Unit => (full, closurePositions)
    let reference := phiA light zeroPositions zeroInline aux fallback (fun _ => false) #[]
    let expected := phiEL2 full zeroPositions closurePositions (fun _ => false) #[]
    let (actual, _) := Ix.Sharing.Scratch.phi light zeroPositions zeroInline aux fallback
      (fun _ => false) #[] {}
    unless reference == expected && actual == expected do
      throw (IO.userError s!"scratch opacity fallback mismatch at {sample.address}")
    count := count + 1
  return count

private def controls (cases : Array WidthCase) : IO Unit := do
  let mut rows := 0
  for (sample, index) in cases.zipIdx do
    IO.println s!"control begin index={index} address={sample.address} width={sample.width}"
    (← IO.getStdout).flush
    let reference := runCase "reference" canonicalFamilyConfig {} sample
    for mode in ["fresh", "reuse"] do
      unless sameMeter reference (runCase mode canonicalFamilyConfig {} sample) do
        throw (IO.userError s!"family-stage mismatch {mode} at {sample.address}/{sample.width}")
    if index < 24 then
      rows := rows + (← checkRows sample)
      for limit in #[{ maxStates := 0 : Limits }, { maxCostEvals := 0 : Limits }] do
        let refused := runCase "reference" canonicalFamilyConfig limit sample
        for mode in ["fresh", "reuse"] do
          unless sameMeter refused (runCase mode canonicalFamilyConfig limit sample) do
            throw (IO.userError s!"family-stage refusal mismatch {mode} at {sample.address}")
      let greedy : Config := ⟨0⟩
      let reference := runCase "reference" greedy {} sample
      for mode in ["fresh", "reuse"] do
        unless sameMeter reference (runCase mode greedy {} sample) do
          throw (IO.userError s!"greedy table mismatch {mode} at {sample.address}")
    IO.println s!"control pass index={index} rows={rows}"
    (← IO.getStdout).flush
  IO.println s!"scratch controls PASS width_cases={cases.size} row_cases={rows}"

@[noinline] private def timed (mode : String) (cases : Array WidthCase)
    (expected : Array (Except SharingError MeterState)) : IO Unit := do
  let start ← IO.monoNanosNow
  let outputs ← IO.lazyPure fun _ =>
    (Task.spawn fun _ => cases.map (runCase mode canonicalFamilyConfig {})).get
  let elapsed := (← IO.monoNanosNow) - start
  unless outputs.size == expected.size && (outputs.zip expected).all (fun (a, b) => sameMeter a b) do
    throw (IO.userError s!"timed family-stage mismatch: {mode}")
  IO.println s!"family-stage mode={mode} ns={elapsed} width_cases={cases.size}"

public def main (args : List String) : IO Unit := do
  let mode :: path :: rest := args
    | throw (IO.userError "expected controls CORPUS or bench CORPUS TRIALS")
  let samples ← loadSamples path
  let cases ← IO.lazyPure fun _ => prepareCases samples
  if mode == "controls" && rest.isEmpty then
    controls cases
  else if mode == "bench" then
    let [count] := rest | throw (IO.userError "expected one trial count")
    let some count := count.toNat? | throw (IO.userError "invalid trial count")
    unless 0 < count && count ≤ 8 do throw (IO.userError "trial count must be 1 to 8")
    let expected ← IO.lazyPure fun _ => cases.map (runCase "reference" canonicalFamilyConfig {})
    for trial in [:count] do
      IO.println s!"trial={trial}"
      for mode in (if trial % 2 == 0 then ["reference", "fresh", "reuse"]
          else ["reuse", "fresh", "reference"]) do
        timed mode cases expected
  else throw (IO.userError "unknown scratch benchmark mode")
