module

import Scripts.Performance.DeferredSharing
import all Ix.Sharing.FamilyContext

public section

open Ix.Sharing.Exact Ix.Sharing.Family

deriving instance BEq for ExactSharingResult
deriving instance BEq for UniformSharingResult
deriving instance BEq for TieredStats
deriving instance BEq for TieredSharingResult

private structure Sample where
  address : Address
  raw : ByteArray
  constant : Ixon.Constant
  expanded : Expanded

private def load (path : String) : IO (Array Sample) := do
  let environment ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  let records := environment.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  records.mapM fun (address, stored) => do
    let constant ← IO.ofExcept stored.get
    let expanded ← IO.ofExcept ((expand {} constant.sharing (constantInfoRoots constant.info) true).mapError toString)
    return { address, raw := stored.rawBytes, constant, expanded }

private def reference (constant : Ixon.Constant) (limits : Limits) :
    Except SharingError (Ixon.Constant × TieredSharingResult) :=
  LightContext.normalize canonicalFamilyConfig .tagN constant limits

private def sameResult : Except SharingError (Ixon.Constant × TieredSharingResult) →
    Except SharingError (Ixon.Constant × TieredSharingResult) → Bool
  | .error first, .error second => first == second
  | .ok (first, firstDetails), .ok (second, secondDetails) =>
    Ixon.serConstant first == Ixon.serConstant second && firstDetails == secondDetails
  | _, _ => false

private def checked (sample : Sample) (limits : Limits) : IO Unit := do
  let original ← IO.lazyPure fun _ => reference sample.constant limits
  let candidate ← IO.lazyPure fun _ => Ix.Sharing.Deferred.normalize .tagN sample.constant limits
  unless sameResult original candidate do
    throw (IO.userError s!"deferred result/refusal differs at {sample.address}: {repr limits}")
  if let .ok (constant, _) := candidate then
    unless Ixon.serConstant constant == sample.raw do
      throw (IO.userError s!"deferred canonical bytes changed at {sample.address}")

private def controls (samples : Array Sample) : IO Unit := do
  let mut planned := 0
  let mut fallback := 0
  for (sample, index) in samples.zipIdx do
    IO.println s!"deferred control begin index={index} address={sample.address}"
    (← IO.getStdout).flush
    checked sample {}
    let ex := sample.expanded
    let prep := Prep.ofDag ex.dag
    let facts := graphFacts ex.dag ex.roots
    let parents := parentsOf ex.dag
    for width in #[1, 2, 3] do
      let candidate ← IO.ofExcept ((Ix.Sharing.Deferred.prepareCandidate canonicalFamilyConfig
        .tagN {} ex prep facts parents (Ix.Sharing.Deferred.wireReady ex) width).mapError toString)
      let materialized ← IO.ofExcept ((rematerializeP prep .tagN {} ex
        candidate.allocation.order candidate.phase1Bytes).mapError toString)
      unless candidate.predicted == materialized.bytes do
        throw (IO.userError s!"deferred key differs at {sample.address}, width={width}")
      if candidate.materialized.isNone then planned := planned + 1
      else fallback := fallback + 1
    for limits in #[{ maxStates := 0 : Limits }, { maxCostEvals := 0 : Limits },
        { maxMaterialize := 0 : Limits }, { maxMaterializeWork := 0 : Limits },
        { maxOutputBytes := 0 : Limits }, { maxKnapsackCells := 0 : Limits },
        { maxDepth := ex.dag.size : Limits }, { maxExprVisits := ex.visits : Limits },
        { maxNodes := ex.internedNodes : Limits }] do
      checked sample limits
    IO.println s!"deferred control pass index={index} planned={planned} fallback={fallback}"
    (← IO.getStdout).flush
  IO.println s!"deferred controls PASS records={samples.size} candidate_keys={planned + fallback} planned={planned} fallback={fallback}"

@[noinline] private def timed (label : String) (samples : Array Sample)
    (run : Ixon.Constant → Except SharingError (Ixon.Constant × TieredSharingResult)) : IO Unit := do
  let start ← IO.monoNanosNow
  let results ← IO.lazyPure fun _ => (Task.spawn fun _ => samples.map (fun sample => run sample.constant)).get
  let elapsed := (← IO.monoNanosNow) - start
  for (sample, result) in samples.zip results do
    let (constant, _) ← IO.ofExcept (result.mapError toString)
    unless Ixon.serConstant constant == sample.raw do
      throw (IO.userError s!"timed canonical bytes changed at {sample.address}")
  IO.println s!"complete-normalization mode={label} ns={elapsed} records={samples.size}"

def main (args : List String) : IO Unit := do
  let mode :: path :: rest := args | throw (IO.userError "expected controls CORPUS or bench CORPUS TRIALS")
  let samples ← load path
  if mode == "controls" && rest.isEmpty then controls samples
  else if mode == "bench" then
    let [count] := rest | throw (IO.userError "expected one trial count")
    let some count := count.toNat? | throw (IO.userError "invalid trial count")
    unless 0 < count && count ≤ 6 do throw (IO.userError "trial count must be 1 to 6")
    let warm ← IO.lazyPure fun _ => (Task.spawn fun _ => samples.map (fun sample => reference sample.constant {})).get
    unless warm.all (fun result => result.isOk) do throw (IO.userError "reference warmup refused")
    for trial in [:count] do
      IO.println s!"trial={trial}"
      if trial % 2 == 0 then
        timed "reference" samples (fun constant => reference constant {})
        timed "deferred" samples (fun constant => Ix.Sharing.Deferred.normalize .tagN constant {})
      else
        timed "deferred" samples (fun constant => Ix.Sharing.Deferred.normalize .tagN constant {})
        timed "reference" samples (fun constant => reference constant {})
  else throw (IO.userError "unknown deferred benchmark mode")
