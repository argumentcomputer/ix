import Ix.Compiler.Tools.Check
import Blake3.Rust

/-! Independent artifact and resource checker. Only the shared CLI helpers
and the existing hash primitive are imported; compiler and evaluator modules
are absent. Canonical mode, graph, source, and policy preimages are rebuilt
from the exported fields before comparing two fresh compiler processes. -/

open Lean System Ix.Compiler.Tools.Check

namespace Ix.Compiler.Tools.UniqueCheck


def number (value : Json) (key : String) : IO Nat := do nat (← field value key)
def bytes (value : Json) : IO ByteArray := do checked (unhex (← string value))
def byteField (value : Json) (key : String) : IO ByteArray := do bytes (← field value key)
def tag (value : Nat) : ByteArray := ByteArray.mk #[value.toUInt8]
def uleb (value : Nat) : ByteArray :=
  if value < 128 then tag value else tag (128 + value % 128) ++ uleb (value / 128)
termination_by value
decreasing_by apply Nat.div_lt_self <;> omega
def blob (value : ByteArray) : ByteArray := uleb value.size ++ value
def vector (values : Array ByteArray) : ByteArray := uleb values.size ++ values.foldl (· ++ ·) ByteArray.empty
def digest (value : ByteArray) : String :=
  (Blake3.Rust.hash value).val.data.foldl (fun output byte =>
    output ++ (if byte.toNat < 16 then "0" else "") ++ hexNat byte.toNat) ""

def hashField (value : Json) (payload key label : String) : IO Unit := do
  need (digest (← byteField value payload) == (← strField value key)) s!"{label}: hash disagreement"

private def mode (value : Json) : IO ByteArray := do
  match ← string value with
  | "unique" => return tag 0
  | "shared" => return tag 1
  | _ => throw (IO.userError "unknown recursor world")

private def inspectInstance (value : Json) (arguments : List String) : IO Unit := do
  need ((← field value "arguments") == toJson arguments &&
    (← field value "fields") == toJson ([[], ["unique", "unique"]] : List (List String)) &&
    (← strField value "result") == "unique" && (← field value "well_shaped") == toJson true)
    "recursor world vector disagreement"
  let args ← (← arrField value "arguments").mapM mode
  let fields ← (← arrField value "fields").mapM fun row => do return vector (← (← array row).mapM mode)
  let expected := "compilatrix/ixir0/recursor-instance/1\x00".toUTF8 ++ blob (← byteField value "declaration") ++
    vector args ++ vector fields ++ (← mode (← field value "result"))
  need (expected == (← byteField value "bytes")) "recursor canonical preimage disagreement"
  hashField value "bytes" "identity" "recursor"

def inspectList (schema heap root : Json) (expected : Array Json) : IO Unit := do
  let nodes ← arrField heap "nodes"
  let mut current := root
  let mut visited : List Nat := []
  for index in [:expected.size + 1] do
    let location ← number (← field current "loc") "l"
    need (location < nodes.size && !visited.contains location) "unique list pointer is invalid or cyclic"
    visited := location :: visited
    let box := nodes[location]!
    need ((← strField box "world") == "unique" && (← number box "rc") == 1) "unique list box has the wrong ownership"
    let ctor ← field (← field box "node") "ctorN"
    let identity ← field ctor "cid"
    let isCons := index < expected.size
    need ((← number identity "indIdx") == 0 && (← number identity "cidx") == (if isCons then 1 else 0) &&
      (← field identity "block") == (← field schema (if isCons then "cons" else "nil"))) "unique list constructor identity disagreement"
    let fields ← arrField ctor "fields"
    need (fields.size == (if isCons then 2 else 0)) "unique list field arity disagreement"
    if isCons then
      let value ← field (← field (← field fields[0]! "lit") "l") "nat"
      need ((← field value "n") == expected[index]!) "unique list payload disagreement"
      current := fields[1]!
  need (visited.length == nodes.countP (· != Json.null)) "unique result does not own every live node"

def inspectSnapshot (row snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-unique-reuse-case/1" &&
    (← field snapshot "summary") == row) "unique snapshot/report disagreement"
  let input ← arrField row "input"
  let count := input.size
  need ((← field row "value") == Json.arr input.reverse) "source reversal disagreement"
  let optimized := (← field row "optimized") == toJson true
  let reused := if optimized then count else 0
  let source ← field snapshot "source"
  need ((← field source "root") == (← field row "source_root") &&
    (← field source "identity") == (← field row "source_identity")) "source identity disagreement"
  let constants ← arrField source "constants"
  need (constants.size == 8) "source inventory disagreement"
  let constantBytes ← constants.mapM fun entry => do
    hashField entry "bytes" "key" "Ixon constant"
    return (← byteField entry "key") ++ blob (← byteField entry "bytes")
  let refs ← (← arrField source "entry_refs").mapM bytes
  let univs ← (← arrField source "entry_univs").mapM fun value => do return blob (← bytes value)
  let sourceBytes := "compilatrix/closed-ixon-input/1\x00".toUTF8 ++ vector constantBytes ++ vector refs ++ vector univs ++
    blob (← byteField source "entry")
  need (sourceBytes == (← byteField source "input_bytes")) "source canonical preimage disagreement"
  hashField source "input_bytes" "identity" "source"
  let specialization ← field snapshot "specialization"
  need ((← strField specialization "policy") == "unique-reverse-specialize/1") "specialization policy disagreement"
  let original ← field specialization "source_instance"
  let direct ← field specialization "direct_instance"
  inspectInstance original ["shared", "unique", "unique"]
  inspectInstance direct ["unique", "unique"]
  need ((← field original "identity") == (← field row "source_instance") &&
    (← field direct "identity") == (← field row "specialized_instance")) "instance identity disagreement"
  let ir0 ← field snapshot "ixir0"
  for name in ["raw", "raw_main", "declarations", "main", "groups", "blocks", "address_map"] do
    need ((← field ir0 name) != Json.null) s!"missing IxIR0 artifact: {name}"
  let graph ← field snapshot "ixir1"
  need ((← field graph "root") == (← field row "ixir1_root")) "IxIR1 graph identity disagreement"
  let artifacts ← arrField graph "artifacts"
  need (artifacts.size == 1) "consuming graph has an unexpected artifact inventory"
  let artifactBytes ← artifacts.mapM fun artifact => do
    need ((← strField artifact "kind") == "ordinary") "consuming function has no canonical ordinary address"
    hashField artifact "preimage" "root" "IxIR1 declaration"
    return tag 1 ++ (← byteField artifact "root") ++ blob (← byteField artifact "preimage")
  let graphBytes := "compilatrix/ixir1/optimizer-graph/1\x00".toUTF8 ++ vector artifactBytes ++ blob (← byteField graph "main")
  need (digest graphBytes == (← strField graph "root")) "IxIR1 graph preimage disagreement"
  let provenance ← field snapshot "provenance"
  for (key, expected) in [("kind", "ixir1-plus-policy"), ("usage", "recursor-modes/1"),
      ("lowering", "consuming-unique-recursor/1"), ("reuse", "static-unique-reuse/1"), ("execution", "call-local/0")] do
    need ((← strField provenance key) == expected) s!"unique provenance policy disagreement: {key}"
  need ((← field provenance "identity") == (← field row "provenance") &&
    (← number provenance "outcome") == (if optimized then 2 else 1)) "unique provenance outcome disagreement"
  let target ← field snapshot "ixir2_diagnostic"
  let limits ← field target "limits"
  let limitValues ← ["maxDeclarations", "maxBlocks", "maxBlocksPerFunction", "maxInstructionsPerBlock", "maxValueParams",
    "maxCreditParams", "maxOperands", "maxAlternatives", "maxValueRegisters", "maxCreditRegisters", "maxScalarLeafFacts",
    "maxFlowWork"].toArray.mapM fun key => do return uleb (← number limits key)
  let policyBytes := "compilatrix/unique-reuse-provenance/1\x00".toUTF8 ++
    (← byteField source "identity") ++ (← byteField graph "root") ++ (← byteField original "identity") ++
    (← byteField direct "identity") ++ uleb (← number provenance "check_fuel") ++ uleb (← number provenance "erase_fuel") ++
    vector limitValues ++ blob "recursor-modes/1".toUTF8 ++ blob "unique-reverse-specialize/1".toUTF8 ++
    blob "consuming-unique-recursor/1".toUTF8 ++ blob "static-unique-reuse/1".toUTF8 ++
    blob "call-local/0".toUTF8 ++ uleb (if optimized then 2 else 1)
  need (policyBytes == (← byteField provenance "bytes")) "policy canonical preimage disagreement"
  hashField provenance "bytes" "identity" "provenance"
  for key in ["baseline", "selected", "baseline_stats", "selected_stats", "schemas"] do
    need ((← field target key) != Json.null) s!"missing target artifact: {key}"
  if !optimized then need ((← field target "baseline") == (← field target "selected")) "checked fallback changed its program"
  let observations ← field snapshot "observations"
  for stage in ["ixir1", "baseline_logical", "baseline_physical", "selected_logical", "selected_physical"] do
    let observed ← field observations stage
    need ((← field observed "value") == (← field row "value")) s!"{stage}: value disagreement"
    let physical := stage == "selected_physical"
    let saved := if physical then reused else 0
    for phase in ["store", "reclaimed"] do
      let store ← field observed phase
      let heap ← if stage == "ixir1" then pure store else field store "heap"
      if phase == "store" then
        inspectList (← field (← field specialization "plan") "schema") heap (← field observed "result") (← arrField row "value")
      let live := (← arrField heap "nodes").countP (· != Json.null)
      need ((← number heap "rcops") == 0) s!"{stage}/{phase}: RC work in unique path"
      need ((← number heap "allocs") + saved == 2 * count + 2 && (← number heap "reuses") == saved)
        s!"{stage}/{phase}: FIP allocation disagreement"
      need (live + (← number heap "frees") == (← number heap "allocs")) s!"{stage}/{phase}: allocation balance"
      need (live == (if phase == "store" then count + 1 else 0)) s!"{stage}/{phase}: incomplete reclamation or wrong live count"
      if stage != "ixir1" then
        need ((← number store "peakLiveNodes") == count + 2) s!"{stage}/{phase}: peak disagreement"
        need ((← number store "reusedPayloadUnits") == 2 * saved) s!"{stage}/{phase}: payload disagreement"
        for key in ["resetAttempts", "hotResets", "coldResets"] do
          need ((← number store key) == 0) s!"{stage}/{phase}: shared reset in unique path"
    if stage != "ixir1" then
      let cost := (if stage.startsWith "selected" && optimized then 5 else 6) * count + 7
      need ((← number observed "control_remaining") + cost == 10000 &&
        (← number observed "heap_remaining") == 0 && (← number observed "reclamation_remaining") == 0)
        s!"{stage}: independent budget disagreement"
  for (stage, key) in [("baseline_physical", "baseline"), ("selected_logical", "logical"), ("selected_physical", "physical")] do
    let store ← field (← field observations stage) "store"
    let heap ← field store "heap"
    let counters ← field row key
    for name in ["allocs", "frees", "reuses", "rcops"] do
      need ((← field heap name) == (← field counters name)) "summary heap counters disagree"
    for name in ["peakLiveNodes", "reusedPayloadUnits", "resetAttempts", "hotResets", "coldResets"] do
      need ((← field store name) == (← field counters name)) "summary observation counters disagree"
  let prefixes ← arrField snapshot "prefixes"
  need (prefixes.size == (if optimized then 5 else 6) * count + 8 && prefixes.size == (← number row "prefixes"))
    "prefix inventory disagreement"
  for index in [:prefixes.size] do
    let state := prefixes[index]!
    need ((← number state "step") == index) "prefix sequence gap"
    let owners ← (← arrField state "owners").toList.mapM nat
    let emptySlots ← (← arrField state "empty_slots").toList.mapM nat
    need (owners.eraseDups.length == owners.length) "duplicate reservation owner"
    need (owners.all emptySlots.contains) "reservation aliases a live slot"
    let counters ← field state "counters"
    let live ← number state "live"
    need (live + (← number counters "frees") + owners.length == (← number counters "allocs")) "prefix allocation balance"
    need ((← number counters "rcops") == 0) "prefix RC disagreement"
    need (live ≤ (← number counters "peakLiveNodes") && (← number counters "peakLiveNodes") ≤ count + 2) "prefix peak disagreement"
  need ((← field prefixes.back! "counters") == (← field row "physical")) "prefix terminal counters disagree"

def replaceAt (value : Json) (path : List String) (replacement : Json) : IO Json := do
  match path with
  | [] => return replacement
  | key :: rest =>
      let entries ← pairs value
      let changed ← replaceAt (← field value key) rest replacement
      return Json.mkObj (entries.map fun (name, old) => (name, if name == key then changed else old))

def rejects (label fragment : String) (action : IO Unit) : IO Unit := do
  let error ← try action; pure none catch error => pure (some error.toString)
  let some error := error | throw (IO.userError s!"{label}: checker accepted corruption")
  need (error.contains fragment) s!"{label}: wrong rejection: {error}"

def regressionChecks (row snapshot : Json) : IO Unit := do
  for phase in ["store", "reclaimed"] do
    let changed ← replaceAt snapshot ["observations", "selected_physical", phase, "heap", "rcops"] (toJson (1 : Nat))
    rejects "RC corruption" "RC work in unique path" (inspectSnapshot row changed)
    let changed ← replaceAt snapshot ["observations", "selected_physical", phase, "peakLiveNodes"] (toJson (6 : Nat))
    rejects "peak corruption" "peak disagreement" (inspectSnapshot row changed)
  let changed ← replaceAt snapshot ["specialization", "source_instance", "arguments"] (toJson ["shared", "unique", "shared"])
  rejects "mode corruption" "world vector disagreement" (inspectSnapshot row changed)
  let changed ← replaceAt snapshot ["provenance", "execution"] (toJson "suspended-direct-calls/1")
  rejects "policy corruption" "provenance policy disagreement" (inspectSnapshot row changed)
  let changed ← replaceAt snapshot ["provenance", "bytes"] (toJson "00")
  rejects "preimage corruption" "policy canonical preimage disagreement" (inspectSnapshot row changed)
  let changed ← replaceAt snapshot ["ixir1", "main"] (toJson "00")
  rejects "main corruption" "graph preimage disagreement" (inspectSnapshot row changed)
  let nodes ← arrField (← field (← field (← field (← field snapshot "observations") "selected_physical") "store") "heap") "nodes"
  let some live := nodes.findIdx? (· != Json.null) | throw (IO.userError "no live regression node")
  for (name, path, replacement, fragment) in [
      ("shared result corruption", ["world"], toJson "shared", "unique list box has the wrong ownership"),
      ("constructor corruption", ["node", "ctorN", "cid", "block"], toJson "wrong", "constructor identity disagreement")] do
    let changedNode ← replaceAt nodes[live]! path replacement
    let changed ← replaceAt snapshot ["observations", "selected_physical", "store", "heap", "nodes"]
      (Json.arr (nodes.set! live changedNode))
    rejects name fragment (inspectSnapshot row changed)
  let prefixes ← arrField snapshot "prefixes"
  let some index := prefixes.findIdx? (fun row => (row.getObjVal? "owners" |>.bind Json.getArr?).toOption.any (!·.isEmpty))
    | throw (IO.userError "regression case has no reservation")
  let state := prefixes[index]!
  let changedState ← replaceAt state ["owners"] (toJson ([0, 0] : List Nat))
  let changed ← replaceAt snapshot ["prefixes"] (Json.arr (prefixes.set! index changedState))
  rejects "duplicate owner corruption" "duplicate reservation owner" (inspectSnapshot row changed)
  let changedState ← replaceAt state ["empty_slots"] (toJson ([] : List Nat))
  let changed ← replaceAt snapshot ["prefixes"] (Json.arr (prefixes.set! index changedState))
  rejects "live reservation corruption" "reservation aliases a live slot" (inspectSnapshot row changed)

end Ix.Compiler.Tools.UniqueCheck
