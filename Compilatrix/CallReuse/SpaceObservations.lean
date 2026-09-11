import Compilatrix.CallReuse.Observations
import Compilatrix.CallReuse.SpaceSim
import Compilatrix.X86.ArenaSpace

/-! Fresh Ixon compilations exercise the finite-storage runner. Diagnostic
prefixes retain the complete heap and explicit caller frames so a separate
checker can recompute every size and identify the first rejected state. -/

namespace Compilatrix.CallReuse.SpaceExamples

open Lean Compilatrix.IxIR2 Compilatrix.IxIR2.Eval

deriving instance ToJson for CreditPresence
deriving instance ToJson for Credit
deriving instance ToJson for Space.Demand
deriving instance ToJson for Space.Layout

def layout : Space.Layout := { fields := 2 }
def fuel : Nat := 10000

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def resultJson (result : Result) : Json := Json.mkObj [
  ("store", toJson result.store), ("value", toJson result.value),
  ("control_remaining", toJson result.controlRemaining), ("heap_remaining", toJson result.heapRemaining)]

private def frameJson (frame : Frame) : Json := Json.mkObj [
  ("definition", toJson frame.definition), ("block", toJson frame.block), ("pc", toJson frame.pc),
  ("values", toJson frame.values), ("credits", toJson frame.credits),
  ("reservations", toJson frame.reservations), ("bytes", toJson (Space.frameBytes frame))]

private def continuationJson : Continuation → Json
  | .resume frame => Json.mkObj [("kind", toJson "resume"), ("frame", frameJson frame),
      ("arguments", toJson (#[] : Array RVal)),
      ("bytes", toJson (Space.continuationBytes (.resume frame)))]
  | .applyMore arguments frame => Json.mkObj [("kind", toJson "applyMore"), ("frame", frameJson frame),
      ("arguments", toJson arguments),
      ("bytes", toJson (Space.continuationBytes (.applyMore arguments frame)))]

private def machineJson (step : Nat) (machine : Machine) : Json :=
  let (active, saved, returned) := match machine.control with
    | .halted value => (Json.null, #[], toJson value)
    | .running frame stack => (frameJson frame, (stack.map continuationJson).toArray, Json.null)
  Json.mkObj [
    ("step", toJson step), ("store", toJson machine.store),
    ("heap_remaining", toJson machine.heapFuel),
    ("active", active), ("saved", Json.arr saved), ("returned", returned),
    ("slots", toJson machine.store.slots), ("live", toJson machine.store.live),
    ("reservations", toJson machine.reservations),
    ("live_bytes", toJson (layout.liveBytes machine)),
    ("reserved_bytes", toJson (layout.reservedBytes machine)),
    ("occupied_bytes", toJson (layout.occupiedBytes machine)),
    ("retained_free_bytes", toJson (layout.retainedFreeBytes machine)),
    ("demand", toJson (layout.demand machine))]

private def capacityFailure (context : Context) (policy : CreditPolicy) (initial : Machine)
    (controlFuel : Nat) (capacity : Space.Capacity) : Except String Json := do
  match Space.run layout capacity policy context controlFuel initial with
  | .error (.capacity needed available remaining) =>
      need (available == capacity && !needed.within available) "capacity fault does not exceed its budget"
      return Json.mkObj [("capacity", toJson available), ("needed", toJson needed),
        ("step", toJson (controlFuel - remaining))]
  | .error error => throw s!"expected capacity failure, got {repr error}"
  | .ok _ => throw "insufficient capacity was accepted"

structure CaseResult where
  name : String
  summary : Json
  snapshot : Json

def runCase (name : String) (values : List Nat) (replacement : Nat) (aliased : Bool)
    (uniquePrefix : Nat := 0) : Except String CaseResult := do
  let sourceArtifact ← Examples.runCase name values replacement aliased uniquePrefix
  let source ← Examples.source values replacement aliased uniquePrefix
  let compilation ← source.compile.mapError (fun error => s!"source compilation: {repr error}")
  let .recovered _ lowered := compilation.outcome | throw "finite map did not reach checked lowering"
  let program := lowered.reuse.target
  let policy := lowered.reuse.policy
  let context := lowered.spaceContext
  let initial := initialMachine program.main #[] fuel
  let observed ← (Space.profile layout policy context fuel initial).mapError
    (fun error => s!"space profile: {repr error}")
  let funded ← (Space.run layout observed.demand policy context fuel initial).mapError
    (fun error => s!"exact capacity: {repr error}")
  need (resultJson funded.result == resultJson observed.result && funded.demand == observed.demand)
    "exact capacity changed the physical execution"
  let larger : Space.Capacity := ⟨observed.demand.heap + 1, observed.demand.control + 1⟩
  let ample ← (Space.run layout larger policy context fuel initial).mapError
    (fun error => s!"ample capacity: {repr error}")
  need (resultJson ample.result == resultJson observed.result && ample.demand == observed.demand)
    "additional capacity changed the physical execution"
  let original ← sourceArtifact.snapshot.getObjVal? "observations" >>= (·.getObjVal? "selected_physical")
  need ((← original.getObjVal? "store") == toJson observed.result.store)
    "finite runner disagrees with ordinary source-selected execution"
  let (reclaimed, _) ← (releaseShared fuel observed.result.store observed.result.value).mapError
    (fun error => s!"finite result reclamation: {repr error}")
  need (reclaimed.live == 0 && reclaimed.heap.frees == reclaimed.heap.allocs &&
    reclaimed.slots == observed.result.store.slots) "finite result was not fully reclaimed"
  let heapShort ← capacityFailure context policy initial fuel
    ⟨observed.demand.heap - 1, observed.demand.control⟩
  let controlShort ← capacityFailure context policy initial fuel
    ⟨observed.demand.heap, observed.demand.control - 1⟩
  let noDescriptor ← capacityFailure context policy initial fuel ⟨Space.descriptorBytes - 1, observed.demand.control⟩
  let noControl ← capacityFailure context policy initial fuel ⟨observed.demand.heap, 0⟩
  let mut machine := initial
  let mut prefixes := #[]
  let mut witness := Json.null
  let mut maximum : Space.Demand := ⟨0, 0⟩
  for index in [:fuel + 1] do
    prefixes := prefixes.push (machineJson index machine)
    maximum := maximum.join (layout.demand machine)
    if let .halted value := machine.control then
      need (value == observed.result.value && toJson machine.store == toJson observed.result.store &&
        index + observed.result.controlRemaining == fuel && maximum == observed.demand)
        "finite profile differs from the actual prefix sequence"
      break
    let next ← (Policy.step policy context .physical machine).mapError
      (fun error => s!"space prefix: {repr error}")
    let savedReservations := match machine.control with
      | .running _ stack => stack.flatMap Continuation.reservations
      | .halted _ => []
    if witness == Json.null && !savedReservations.isEmpty && next.store.slots == machine.store.slots + 1 then
      let available : Space.Capacity := ⟨(layout.demand next).heap - 1, observed.demand.control⟩
      need ((layout.demand machine).within available &&
        next.reservations == machine.reservations &&
        (layout.demand next).heap - layout.reservedBytes next ≤ available.heap)
        "callee allocation did not expose the cost of suspended reservations"
      let failed ← capacityFailure context policy machine (fuel - index) available
      need ((← failed.getObjValAs? Nat "step") == 1) "callee allocation did not fail at its next state"
      witness := Json.mkObj [("before_step", toJson index), ("after_step", toJson (index + 1)),
        ("saved_reservations", toJson savedReservations), ("failure", failed)]
    machine := next
  let hot := if aliased then uniquePrefix else values.length
  need ((witness != Json.null) == (hot > 0)) "missing callee-allocation reservation witness"
  need (observed.demand.heap == layout.committedBytes observed.result.store)
    "maximum committed bytes differs from terminal backing arena"
  let summary := Json.mkObj [("name", toJson name), ("snapshot", toJson s!"{name}.json"),
    ("source_root", toJson source.root), ("input", toJson values), ("replacement", toJson replacement),
    ("aliased", toJson aliased), ("unique_prefix", toJson uniquePrefix),
    ("demand", toJson observed.demand), ("fresh_slots", toJson observed.result.store.slots),
    ("peak_live_nodes", toJson observed.result.store.peakLiveNodes),
    ("prefixes", toJson prefixes.size), ("reserved_allocation", toJson (witness != Json.null))]
  return { name, summary, snapshot := Json.mkObj [
    ("format", toJson "compilatrix/source-space-case/1"), ("summary", summary),
    ("policy", toJson Space.policyTag), ("layout", toJson layout),
    ("fuel", toJson fuel), ("source_artifact", sourceArtifact.snapshot),
    ("result", resultJson observed.result), ("reclaimed", toJson reclaimed),
    ("reclaimed_committed_bytes", toJson (layout.committedBytes reclaimed)),
    ("prefixes", Json.arr prefixes), ("reserved_allocation", witness),
    ("failures", Json.mkObj [("heap_short", heapShort), ("control_short", controlShort),
      ("no_descriptor", noDescriptor), ("no_control", noControl)])] }

def cases : List (String × List Nat × Nat × Bool × Nat) := [
  ("empty-hot", [], 42, false, 0), ("empty-cold", [], 42, true, 0),
  ("singleton-hot", [17], 42, false, 0), ("singleton-cold", [17], 42, true, 0),
  ("three-hot", [1, 2, 3], 42, false, 0), ("three-cold", [1, 2, 3], 42, true, 0),
  ("mixed-ownership", [5, 4, 3, 2, 1], 0, true, 2),
  ("word-boundary", [0, UInt64.size - 1, 7], UInt64.size - 1, false, 0),
  ("sixteen-hot", List.range 16, 7, false, 0)]

def boundaryChecks : Except String (List String) := do
  let source ← Examples.source [17] 42 false
  let compilation ← source.compile.mapError (fun error => s!"boundary compilation: {repr error}")
  let .recovered _ lowered := compilation.outcome | throw "boundary lowering failed"
  let initial := initialMachine lowered.reuse.target.main #[] fuel
  let observed ← (Space.profile layout lowered.reuse.policy lowered.spaceContext fuel initial).mapError
    (fun error => s!"boundary profile: {repr error}")
  need (match Space.run layout observed.demand lowered.reuse.policy lowered.spaceContext 0 initial with
    | .error (.evaluation .controlFuel) => true | _ => false) "control fuel was confused with storage capacity"
  need (match Space.run layout observed.demand lowered.reuse.policy lowered.spaceContext fuel
      (initialMachine lowered.reuse.target.main #[] 0) with
    | .error (.evaluation .heapFuel) => true | _ => false) "heap traversal fuel was confused with storage capacity"
  for (values, replacement) in [([UInt64.size], 0), ([0], UInt64.size)] do
    let source ← Examples.source values replacement false
    let compilation ← source.compile.mapError (fun error => s!"word boundary compilation: {repr error}")
    let .recovered _ lowered := compilation.outcome | throw "word boundary lowering failed"
    need (match Space.profile layout lowered.reuse.policy lowered.spaceContext fuel
        (initialMachine lowered.reuse.target.main #[] fuel) with
      | .error .representation => true | _ => false) "unrepresentable Nat was admitted to the Word space model"
  need (match Space.profile { fields := 1 } lowered.reuse.policy lowered.spaceContext fuel initial with
    | .error .representation => true | _ => false) "oversized payload was admitted to a fixed slot"
  need (match Space.profile { fields := (UInt64.size - 96) / 16 }
      lowered.reuse.policy lowered.spaceContext 1 initial with
    | .error .representation => true | _ => false) "descriptor plus cell bytes overflowed the Word representation"
  return ["control-fuel-distinct", "heap-fuel-distinct", "input-word-overflow", "result-word-overflow",
    "payload-too-wide", "descriptor-plus-cell-overflow"]

def arenaMatrix : Json := toJson ((List.range 65).map fun n => Json.mkObj [
  ("length", toJson n), ("required_bytes", toJson (X86.UniqueABI.requiredBytes n)),
  ("short_cells", toJson (X86.UniqueABI.cellsForBytes (X86.UniqueABI.requiredBytes n - 1))),
  ("exact_cells", toJson (X86.UniqueABI.cellsForBytes (X86.UniqueABI.requiredBytes n)))])

def runAll : Except String (List CaseResult × List String) := do
  let results ← cases.mapM fun (name, values, replacement, aliased, prefixLength) =>
    runCase name values replacement aliased prefixLength
  return (results, ← boundaryChecks)

def report (results : List CaseResult) (checks : List String) : Json := Json.mkObj [
  ("format", toJson "compilatrix/source-space-report/1"), ("policy", toJson Space.policyTag),
  ("layout", toJson layout), ("cases", toJson (results.map (·.summary))),
  ("boundary_checks", toJson checks), ("native_arena", arenaMatrix)]

end Compilatrix.CallReuse.SpaceExamples
