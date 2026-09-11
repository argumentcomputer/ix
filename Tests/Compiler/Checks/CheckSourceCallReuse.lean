import Ix.Compiler.Tools.Check

/-! Independent fresh-process artifact, resource, and reservation gate.
This checker imports no compiler, optimizer, evaluator, or fixture code. -/

open Lean System Ix.Compiler.Tools.Check

private def requireFields (value : Json) (keys : List String) : IO Unit := do
  for key in keys do need ((← field value key) != Json.null) s!"missing map snapshot field {key}"

private def number (value : Json) (key : String) : IO Nat := do nat (← field value key)

private def inspectSnapshot (row snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-call-reuse-case/1") "unknown map snapshot format"
  need ((← field snapshot "summary") == row) "map snapshot/report disagreement"
  let source ← field snapshot "source"
  requireFields source ["root", "limits", "fuel", "constants", "literals"]
  need ((← field source "root") == (← field row "source_root")) "map source identity disagreement"
  need ((← arrField source "constants").size == (← number row "source_constants")) "source inventory disagreement"
  let ir0 ← field snapshot "ixir0"
  requireFields ir0 ["raw", "raw_main", "groups", "declarations", "main", "blocks", "address_map"]
  for (key, rootKey) in [("ixir1", "ixir1_root"), ("literal_ixir1", "literal_ixir1_root")] do
    let graph ← field snapshot key
    requireFields graph ["root", "raw_declarations", "raw_main", "artifacts", "declarations", "main", "address_map", "reserved"]
    need ((← field graph "root") == (← field row rootKey)) s!"{key} identity disagreement"
  let specialization ← field snapshot "map_specialization"
  requireFields specialization ["policy", "plan", "derived_key", "declarations", "main"]
  need ((← strField specialization "policy") == "closed-map-specialize/1" &&
    (← field specialization "derived_key") == (← field row "map_specialization")) "map specialization identity disagreement"
  let lowering ← field snapshot "ownership_lowering"
  for key in ["declarations", "main"] do
    need ((← field lowering key) == (← field specialization key)) s!"ownership lowering changed specialized {key}"
  for key in ["source_rows_selected", "source_externs_rejected", "target_externs_rejected"] do
    need ((← field lowering key) == toJson true) s!"ownership certificate failed: {key}"
  let hpt ← field snapshot "hpt"
  requireFields hpt ["producer_limits", "producer_stats", "candidate", "artifacts"]
  let artifacts ← arrField hpt "artifacts"
  need (!artifacts.isEmpty && (← artifacts.mapM (field · "root")) == (← arrField row "hpt_roots")) "map HPT identity disagreement"
  for artifact in artifacts do requireFields artifact ["program_root", "cache_key", "root", "dependencies", "members", "bytes"]
  let sidecars ← field snapshot "sidecars"
  requireFields sidecars ["input_declarations", "input_main", "main_world", "parameter_worlds", "constructors", "recursor_origins", "hpt_certificate"]
  let graph ← field snapshot "ixir1"
  need ((← field sidecars "input_declarations") == (← field graph "declarations") &&
    (← field sidecars "input_main") == (← field graph "main")) "sidecar input differs from specialized IxIR1"
  need ((← field sidecars "hpt_certificate") == (← field hpt "candidate")) "sidecar HPT certificate disagreement"
  let provenance ← field snapshot "provenance"
  requireFields provenance ["kind", "identity", "bytes", "lowering_version", "pass", "execution_policy", "optimized", "specialization"]
  need ((← strField provenance "kind") == "ixir1-plus-policy" &&
    (← field provenance "identity") == (← field row "provenance")) "map provenance identity disagreement"
  need ((← strField provenance "pass") == "shared-call-reuse/1" &&
    (← field provenance "pass") == (← field row "pass") &&
    (← strField provenance "execution_policy") == "suspended-direct-calls/1" &&
    (← field provenance "execution_policy") == (← field row "policy")) "map execution policy disagreement"
  requireFields (← field snapshot "ixir2_diagnostic") ["baseline", "baseline_stats", "selected", "selected_stats", "reuse", "max_depth", "schemas"]
  let observations ← field snapshot "observations"
  for stage in ["literal_raw_ixir1", "literal_ixir1", "raw_ixir1", "ixir1",
      "baseline_logical", "baseline_physical", "selected_logical", "selected_physical"] do
    let observation ← field observations stage
    need ((← field observation "value") == (← field row "value")) s!"{stage}: map value disagreement"
    let returned ← field observation "store"
    let heap ← if stage.endsWith "ixir1" then pure returned else field returned "heap"
    let live := (← arrField heap "nodes").countP (· != Json.null)
    need (live + (← number heap "frees") == (← number heap "allocs")) s!"{stage}: terminal allocation balance"
    let released ← field observation "reclaimed"
    let releasedHeap ← if stage.endsWith "ixir1" then pure released else field released "heap"
    need ((← arrField releasedHeap "nodes").all (· == Json.null)) s!"{stage}: incomplete reclamation"
    need ((← field releasedHeap "allocs") == (← field releasedHeap "frees")) s!"{stage}: reclaimed allocation balance"
  let baseline ← field observations "baseline_physical"
  let selected ← field observations "selected_physical"
  for phase in ["store", "reclaimed"] do
    let base ← field baseline phase
    let physical ← field selected phase
    let b ← field base "heap"
    let p ← field physical "heap"
    let reuses ← number p "reuses"
    need ((← number b "reuses") == 0) s!"{phase}: baseline executed reuse"
    need ((← number b "allocs") == (← number p "allocs") + reuses) s!"{phase}: selected allocation law"
    need ((← number b "frees") == (← number p "frees") + reuses) s!"{phase}: selected free law"
    need ((← number p "rcops") ≤ (← number b "rcops")) s!"{phase}: selected RC bound"
    need ((← number physical "peakLiveNodes") ≤ (← number base "peakLiveNodes")) s!"{phase}: selected peak bound"
  for (stage, summary) in [("baseline_physical", "baseline"), ("selected_logical", "logical"), ("selected_physical", "physical")] do
    let store ← field (← field observations stage) "store"
    let heap ← field store "heap"
    let counters ← field row summary
    for key in ["allocs", "reuses", "frees", "rcops"] do
      need ((← field counters key) == (← field heap key)) s!"{stage}: report heap counters disagree"
    for key in ["resetAttempts", "hotResets", "coldResets", "reusedPayloadUnits", "peakLiveNodes"] do
      need ((← field counters key) == (← field store key)) s!"{stage}: report observation counters disagree"
  let base ← field row "baseline"
  let prefixes ← arrField snapshot "prefixes"
  need (!prefixes.isEmpty && prefixes.size == (← number row "prefixes")) "map prefix inventory disagreement"
  let mut maximum := 0
  for index in [:prefixes.size] do
    let state := prefixes[index]!
    need ((← number state "step") == index) "map prefix sequence has a gap"
    let counters ← field state "counters"
    let live ← number state "live"
    let owners ← (← arrField state "owners").toList.mapM (fun owner => do (← array owner).toList.mapM nat)
    let locations := owners.flatten
    let emptySlots ← (← arrField state "empty_slots").toList.mapM nat
    need (locations.eraseDups.length == locations.length) "prefix duplicates a reservation owner"
    need (locations.all emptySlots.contains) "prefix reservation aliases a live heap slot"
    need (live + (← number counters "frees") + locations.length == (← number counters "allocs")) "prefix reservation accounting"
    need ((← number counters "rcops") ≤ (← number base "rcops")) "prefix RC bound"
    need (live ≤ (← number counters "peakLiveNodes") &&
      (← number counters "peakLiveNodes") ≤ (← number base "peakLiveNodes")) "prefix peak bound"
    let counts ← (← arrField state "credit_counts").toList.mapM nat
    maximum := max maximum counts.sum
  need (maximum == (← number row "maximum_credits")) "maximum suspended credit count disagreement"
  need ((← field prefixes.back! "counters") == (← field row "physical")) "prefix terminal counters disagree"

private def replaceAt (value : Json) (path : List String) (replacement : Json) : IO Json := do
  match path with
  | [] => return replacement
  | key :: rest =>
      let entries ← pairs value
      need (entries.any (·.1 == key)) s!"regression field absent: {key}"
      let changed ← replaceAt (← field value key) rest replacement
      return Json.mkObj (entries.map fun (name, old) => (name, if name == key then changed else old))

private def rejects (label fragment : String) (action : IO Unit) : IO Unit := do
  let error ← try action; pure none catch error => pure (some error.toString)
  let some error := error | throw (IO.userError s!"{label}: checker accepted corruption")
  need (error.contains fragment) s!"{label}: wrong checker rejection: {error}"

private def regressionChecks (row snapshot : Json) : IO Unit := do
  for phase in ["store", "reclaimed"] do
    let base ← field (← field (← field snapshot "observations") "baseline_physical") phase
    let raisedRC := (← number (← field base "heap") "rcops") + 1
    let changed ← replaceAt snapshot ["observations", "selected_physical", phase, "heap", "rcops"] (toJson raisedRC)
    rejects s!"{phase} RC corruption" s!"{phase}: selected RC bound" (inspectSnapshot row changed)
    let raisedPeak := (← number base "peakLiveNodes") + 1
    let changed ← replaceAt snapshot ["observations", "selected_physical", phase, "peakLiveNodes"] (toJson raisedPeak)
    rejects s!"{phase} peak corruption" s!"{phase}: selected peak bound" (inspectSnapshot row changed)
  let changed ← replaceAt snapshot ["provenance", "execution_policy"] (toJson "call-local/0")
  rejects "old policy corruption" "map execution policy disagreement" (inspectSnapshot row changed)
  let prefixes ← arrField snapshot "prefixes"
  let some index := prefixes.findIdx? (fun state =>
    ((state.getObjVal? "owners").bind Json.getArr?).toOption.any fun owners =>
      owners.any (fun owner => owner.getArr?.toOption.any (!·.isEmpty)))
    | throw (IO.userError "regression case has no physical reservation")
  let state := prefixes[index]!
  let changedState ← replaceAt state ["owners"] (toJson ([[0, 0]] : List (List Nat)))
  let changed ← replaceAt snapshot ["prefixes"] (Json.arr (prefixes.set! index changedState))
  rejects "duplicate reservation corruption" "prefix duplicates a reservation owner" (inspectSnapshot row changed)
  let changedState ← replaceAt state ["empty_slots"] (toJson ([] : List Nat))
  let changed ← replaceAt snapshot ["prefixes"] (Json.arr (prefixes.set! index changedState))
  rejects "live-slot reservation corruption" "prefix reservation aliases a live heap slot" (inspectSnapshot row changed)

def main (args : List String) : IO UInt32 := cli "source call reuse check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-call-reuse/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      let result ← run exe #[output.toString]
      requireAll result ["source-call-reuse ok:"] "source map producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed source map, policy, address, counter, or rejection matrix drifted"
    let rows ← arrField report "cases"
    need (!rows.isEmpty) "source map matrix has no cases"
    need (!(← arrField report "policy_and_rejection_checks").isEmpty) "source map rejection matrix is empty"
    let mut inventory := ["report.json"]
    for row in rows do
      let name ← strField row "snapshot"
      need (!name.isEmpty && !name.startsWith "." && !name.contains ".." &&
        name.toList.all (fun c => c.isAlphanum || c == '-' || c == '.') && !inventory.contains name)
        "invalid or duplicate source map snapshot name"
      inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "fresh map artifact inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected directory in map artifacts"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
        s!"fresh compiler processes produced different map artifacts: {name}"
    for row in rows do inspectSnapshot row (← readJson (first / (← strField row "snapshot")))
    let some hot := rows.find? (fun row => (row.getObjValAs? String "name").toOption == some "three-hot")
      | throw (IO.userError "missing hot map regression case")
    regressionChecks hot (← readJson (first / (← strField hot "snapshot")))
    IO.println s!"source call reuse check ok: {rows.size} Ixon maps, two fresh artifact sets, 7 corruption regressions, all prefixes and reclaimed heaps checked"
