import Ix.Compiler.Tools.Check

/-! Independent process/file gate for recursion recovery. The producer builds
each Ixon program from scratch; this checker imports no compiler or evaluator.
-/

open Lean System Ix.Compiler.Tools.Check

private def safeName (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c => c.isAlphanum || c == '-' || c == '.') &&
    !name.contains ".." && !name.startsWith "."

private def requireFields (value : Json) (keys : List String) : IO Unit := do
  for key in keys do
    let child ← field value key
    need (child != Json.null) s!"missing recursion snapshot field {key}"

private def inspectSnapshot (directory : FilePath) (row : Json) : IO Unit := do
  let snapshot ← readJson (directory / (← strField row "snapshot"))
  need ((← strField snapshot "format") == "compilatrix/source-recursion-case/2") "unknown snapshot format"
  need ((← field snapshot "summary") == row) "snapshot/report disagreement"
  let source ← field snapshot "source"
  need ((← field source "root") == (← field row "source_root")) "source root disagreement"
  need ((← arrField source "constants").size == (← nat (← field row "source_constants"))) "source inventory disagreement"
  requireFields source ["constants", "limits", "fuel", "literals"]
  requireFields (← field snapshot "literal_ixir0")
    ["raw", "raw_main", "groups", "declarations", "main", "blocks", "address_map"]
  for (graphKey, root) in [("literal_ixir1", "literal_ixir1_root"),
      ("recovered_ixir1", "recovered_ixir1_root")] do
    let graph ← field snapshot graphKey
    requireFields graph ["root", "raw_declarations", "raw_main", "artifacts", "declarations", "main", "address_map", "reserved"]
    need ((← field graph "root") == (← field row root)) s!"{graphKey} root disagreement"
  let recovery ← field snapshot "recovery"
  requireFields recovery ["plan", "derived_key", "declarations", "main"]
  need ((← field recovery "derived_key") == (← field row "recovered_recursion_root")) "derived recursor root disagreement"
  let lowering ← field snapshot "ownership_lowering"
  for key in ["declarations", "main"] do
    need ((← field lowering key) == (← field recovery key)) s!"ownership lowering changed recovered {key}"
  for key in ["source_rows_selected", "source_externs_rejected", "target_externs_rejected"] do
    need ((← field lowering key) == toJson true) s!"ownership lowering certificate failed: {key}"
  let hpt ← field snapshot "hpt"
  requireFields hpt ["producer_limits", "producer_stats", "candidate", "artifacts"]
  let hptArtifacts ← arrField hpt "artifacts"
  let hptRoots ← hptArtifacts.mapM (field · "root")
  need (!hptRoots.isEmpty && hptRoots == (← arrField row "hpt_roots")) "snapshot/report HPT identity disagreement"
  for candidate in ← arrField hpt "candidate" do
    requireFields candidate ["program_root", "members"]
  for artifact in hptArtifacts do
    requireFields artifact ["program_root", "cache_key", "root", "dependencies", "members", "bytes"]
  let sidecars ← field snapshot "sidecars"
  requireFields sidecars
    ["input_declarations", "input_main", "main_world", "parameter_worlds", "constructors", "recursor_origins", "hpt_certificate"]
  let recoveredGraph ← field snapshot "recovered_ixir1"
  need ((← field sidecars "input_declarations") == (← field recoveredGraph "declarations") &&
    (← field sidecars "input_main") == (← field recoveredGraph "main")) "sidecar input differs from recovered IxIR1"
  need ((← field sidecars "hpt_certificate") == (← field hpt "candidate")) "sidecars use a different HPT certificate"
  requireFields (← field snapshot "ixir2_diagnostic")
    ["baseline", "baseline_stats", "selected", "selected_stats", "parameters", "schemas", "case_constructors", "max_depth", "reuse"]
  let observations ← field snapshot "observations"
  for stage in ["literal_raw_ixir1", "literal_ixir1", "recovered_raw_ixir1", "recovered_ixir1",
      "baseline_logical", "baseline_physical", "reuse_logical", "reuse_physical"] do
    let observation ← field observations stage
    need ((← field observation "value") == (← field row "value")) s!"{stage}: value disagreement"
    let returned ← field observation "store"
    let returnedHeap ← if stage.endsWith "ixir1" then pure returned else field returned "heap"
    let live := (← arrField returnedHeap "nodes").countP (· != Json.null)
    need (live + (← nat (← field returnedHeap "frees")) ==
      (← nat (← field returnedHeap "allocs"))) s!"{stage}: terminal allocation balance disagrees"
    let reclaimed ← field observation "reclaimed"
    let heap ← if stage.endsWith "ixir1" then pure reclaimed else field reclaimed "heap"
    need ((← arrField heap "nodes").all (· == Json.null)) s!"{stage}: returned heap was not fully reclaimed"
    need ((← field heap "allocs") == (← field heap "frees")) s!"{stage}: reclaimed allocator balance disagrees"
  let baseline ← field observations "baseline_physical"
  let selected ← field observations "reuse_physical"
  for phase in ["store", "reclaimed"] do
    let baselineStore ← field baseline phase
    let selectedStore ← field selected phase
    let baselineHeap ← field baselineStore "heap"
    let selectedHeap ← field selectedStore "heap"
    let reuses ← nat (← field selectedHeap "reuses")
    need ((← nat (← field baselineHeap "reuses")) == 0) s!"{phase}: physical baseline executed reuse"
    need ((← nat (← field baselineHeap "allocs")) ==
      (← nat (← field selectedHeap "allocs")) + reuses)
      s!"{phase}: physical baseline/selected allocation law disagrees"
    need ((← nat (← field baselineHeap "frees")) ==
      (← nat (← field selectedHeap "frees")) + reuses)
      s!"{phase}: physical baseline/selected free law disagrees"
    need ((← nat (← field selectedHeap "rcops")) ≤ (← nat (← field baselineHeap "rcops")))
      s!"{phase}: physical selected RC operations exceed baseline"
    need ((← nat (← field selectedStore "peakLiveNodes")) ≤ (← nat (← field baselineStore "peakLiveNodes")))
      s!"{phase}: physical selected peak live nodes exceed baseline"

def main (args : List String) : IO UInt32 := cli "source recursion check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-recursion/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      let result ← run exe #[output.toString]
      requireAll result ["source-recursion ok:"] "source recursion producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed source recursion, address, counter, or rejection matrix drifted"
    let rows ← arrField report "cases"
    need (!rows.isEmpty) "source recursion matrix has no cases"
    let mut inventory := ["report.json"]
    for row in rows do
      let name ← strField row "snapshot"
      need (safeName name && !inventory.contains name) s!"invalid or duplicate snapshot name: {name}"
      inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      let actual := files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)
      need (actual == inventory) "fresh compiler output inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected directory in compiler output"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
        s!"fresh compiler processes produced different program artifacts: {name}"
    for row in rows do inspectSnapshot first row
    IO.println s!"source recursion check ok: {rows.size} Ixon cases, two fresh program artifact sets, all heaps reclaimed"
