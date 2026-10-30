module

import Scripts.Performance.SharingParallelStage
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

private structure WidthCase where
  address : Address
  expanded : Expanded
  stage : UStage
  width : Nat
  parents : Array (Array Nat)

private def prepareCases (path : String) : IO (Array WidthCase) := do
  let environment ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  let records := environment.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  let mut cases := #[]
  for (address, stored) in records do
    let constant ← IO.ofExcept stored.get
    let expanded ← IO.ofExcept ((expand {} constant.sharing
      (constantInfoRoots constant.info) true).mapError toString)
    let prep := Prep.ofDag expanded.dag
    let facts := graphFacts expanded.dag expanded.roots
    let parents := parentsOf expanded.dag
    for width in #[1, 2, 3] do
      cases := cases.push { address, expanded, stage := uniformStageF width expanded prep facts,
        width, parents }
  return cases

private def runCase (mode : String) (config : Config) (limits : Limits) (sample : WidthCase) :
    Except SharingError MeterState :=
  if mode == "reference" then
    LightContext.components config limits sample.expanded sample.stage sample.width sample.parents
  else
    ParallelStage.components (if mode == "four" then 2 else 3) config limits
      sample.expanded sample.stage sample.width sample.parents

private def tableControls : IO Unit := do
  let left : CTable := #[some (0, #[1]), none, none]
  let right : CTable := #[none, some (-1, #[3]), none, none]
  unless Parallel.merge left right == #[some (0, #[1]), some (-1, #[3]), none, none] &&
      Parallel.merge left #[] == left && Parallel.merge #[] right == right do
    throw (IO.userError "complete table merge lost a trailing empty cell")
  let mut cases := 0
  for size in [0, 1, 3, 11, 12, 16, 17] do
    for duplicate in [false, true] do
      let members := (List.range size).reverse.map fun n => if duplicate then n % 4 else n
      for costMode in [0, 1, 2] do
        let cost : Cost := fun selected =>
          if costMode == 0 then 0
          else if costMode == 1 then -((selected.foldl (fun total n => total + n) 0 : Nat) : _root_.Int)
          else (2 ^ 90 : _root_.Int) + selected.size
        let config : Config := ⟨if size == 17 then 32 else 16⟩
        let expected := Family.table config cost members
        for depth in [2, 3, 20] do
          unless Parallel.tableWithDepth depth config cost members == expected do
            throw (IO.userError s!"exact table mismatch size={size} duplicate={duplicate} cost={costMode} depth={depth}")
        cases := cases + 1
  IO.println s!"parallel table controls PASS cases={cases}; ties, duplicates, boundaries, offline limits"

private def controls (cases : Array WidthCase) : IO Unit := do
  tableControls
  let mut selected := 0
  for (sample, index) in cases.zipIdx do
    selected := selected + (sample.stage.comps.filter fun members =>
      12 ≤ members.size && members.size ≤ 16).size
    let expected := runCase "reference" canonicalFamilyConfig {} sample
    for mode in ["four", "eight"] do
      unless sameMeter expected (runCase mode canonicalFamilyConfig {} sample) do
        throw (IO.userError s!"complete family-stage mismatch {mode} at {sample.address}/{sample.width}")
    if index < 24 then
      for limit in #[{ maxStates := 0 : Limits }, { maxCostEvals := 0 : Limits }] do
        let refused := runCase "reference" canonicalFamilyConfig limit sample
        for mode in ["four", "eight"] do
          unless sameMeter refused (runCase mode canonicalFamilyConfig limit sample) do
            throw (IO.userError s!"family refusal mismatch {mode} at {sample.address}")
      let greedy : Config := ⟨0⟩
      let expected := runCase "reference" greedy {} sample
      for mode in ["four", "eight"] do
        unless sameMeter expected (runCase mode greedy {} sample) do
          throw (IO.userError s!"greedy fallback mismatch {mode} at {sample.address}")
  IO.println s!"parallel stage controls PASS width_cases={cases.size} selected_components={selected}"

@[noinline] private def timed (mode : String) (cases : Array WidthCase)
    (expected : Array (Except SharingError MeterState)) : IO Unit := do
  let start ← IO.monoNanosNow
  let outputs ← IO.lazyPure fun _ =>
    (Task.spawn fun _ => cases.map (runCase mode canonicalFamilyConfig {})).get
  let elapsed := (← IO.monoNanosNow) - start
  unless outputs.size == expected.size && (outputs.zip expected).all (fun (a, b) => sameMeter a b) do
    throw (IO.userError s!"timed parallel family mismatch: {mode}")
  IO.println s!"family-stage mode={mode} ns={elapsed} width_cases={cases.size}"

public def main (args : List String) : IO Unit := do
  let mode :: path :: rest := args
    | throw (IO.userError "expected controls CORPUS or bench CORPUS TRIALS")
  let cases ← prepareCases path
  if mode == "controls" && rest.isEmpty then
    controls cases
  else if mode == "bench" then
    let [text] := rest | throw (IO.userError "expected one trial count")
    let some count := text.toNat? | throw (IO.userError "invalid trial count")
    unless 0 < count && count ≤ 8 do throw (IO.userError "trial count must be 1 to 8")
    let expected ← IO.lazyPure fun _ =>
      (Task.spawn fun _ => cases.map (runCase "reference" canonicalFamilyConfig {})).get
    for trial in [:count] do
      IO.println s!"trial={trial}"
      for mode in (if trial % 2 == 0 then ["reference", "four", "eight"]
          else ["eight", "four", "reference"]) do
        timed mode cases expected
  else throw (IO.userError "unknown parallel-family benchmark mode")
