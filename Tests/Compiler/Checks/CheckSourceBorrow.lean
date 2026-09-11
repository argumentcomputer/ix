import Ix.Compiler.Tools.BorrowExecution

/-! Two fresh compiler processes, independent caller/callee reconstruction
and full execution replay, fixed source roots, and corrupted-artifact guards.
No compiler, optimizer, ownership-validator, evaluator, or fixture imports. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.BorrowCheck

private def fieldsPresent (value : Json) (keys : List String) : IO Unit := do
  for key in keys do
    let _ ← field value key

private def inspectSnapshot (row snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-borrow-case/1" &&
    (← field snapshot "summary") == row) "borrow snapshot/report mismatch"
  let depth ← number row "depth"
  let successorCase := (← field row "successor") == toJson true
  let expected := if successorCase then 22 else 11
  need (depth ≤ 8 && (← number row "number") == expected &&
    (← strField row "origin") == "synthetic-ixon") "borrow source-domain mismatch"
  let compilation ← field snapshot "compilation"
  need ((← strField compilation "format") == "compilatrix/compiler-snapshot/1") "missing compiler attachment"
  let source ← field compilation "source"
  need ((← field source "root") == (← field row "source_root") &&
    (← arrField source "constants").size == 6) "source inventory mismatch"
  for constant in ← arrField source "constants" do hashField constant "bytes" "key"
  for stage in ["ixir0", "ixir1"] do
    fieldsPresent (← field compilation stage)
      ["raw_declarations", "raw_main", "declarations", "main", "address_map"]
  let hpt ← field compilation "hpt"
  fieldsPresent hpt ["producer_limits", "producer_stats", "candidate", "artifacts"]
  need (!(← arrField hpt "artifacts").isEmpty) "missing checked HPT artifacts"
  let diagnostics ← field compilation "ixir2_diagnostic"
  fieldsPresent diagnostics ["validation_stats", "parameter_worlds", "constructors", "recursor_origins"]
  let baseline ← field diagnostics "program"
  let rewritten ← field snapshot "rewritten"
  let inference ← field row "inference"
  let summaries ← arrField inference "summaries"
  need (summaries.size == depth + 3 && (← number inference "attempts") == depth + 3 &&
    (← number inference "rounds") == 2 && (← number inference "rejected") == 0) "borrow inference work mismatch"
  inspectRewrite baseline rewritten summaries
  need ((← field row "baseline_size") == (← programSize baseline) &&
    (← field row "borrowed_size") == (← programSize rewritten)) "borrow artifact growth mismatch"
  let options ← field snapshot "options"
  need ((← number options "maxCandidates") == 32 && (← number options "maxRounds") == 16 &&
    (← number options "maxAttempts") == 256 && (← number options "sourceFuel") == 1000 &&
    (← number (← field options "budget") "control") == 1000 &&
    (← number (← field options "budget") "heap") == 1000) "borrow checking budget changed"
  let observations ← field snapshot "observations"
  for stage in ["ixon", "raw_ixir0", "ixir0"] do
    need ((← nat (← field observations stage)) == expected) s!"{stage} result mismatch"
  for stage in ["raw_ixir1", "ixir1", "logical_ixir2", "physical_ixir2"] do
    let observation ← field observations stage
    need ((← number observation "nat") == expected) s!"{stage} result mismatch"
    let heap ← field observation "heap"
    need ((← number heap "allocs") == 3 && (← number heap "frees") == 3 &&
      (← number heap "rcops") == 5 && (← number heap "live") == 0 && (← number heap "reuses") == 0)
      s!"{stage} baseline resource mismatch"
  need ((← field observations "logical_ixir2") == (← field observations "physical_ixir2"))
    "baseline interpretation disagreement"
  for (label, program, rcops, extraSteps) in [
      ("baseline", baseline, 5, 0), ("borrowed", rewritten, 3, 3)] do
    let result ← field snapshot s!"{label}_execution"
    inspectExecution program (← field snapshot s!"{label}_prefixes") result expected
    let summary ← field row label
    let store ← field result "store"
    let heap ← field store "heap"
    for key in ["allocs", "frees", "rcops", "reuses"] do
      need ((← field summary key) == (← field heap key)) s!"{label} report counter mismatch"
    for key in ["peakLiveNodes", "resetAttempts", "hotResets", "coldResets", "reusedPayloadUnits"] do
      need ((← field summary key) == (← field store key)) s!"{label} report resource mismatch"
    need ((← number summary "rcops") == rcops && (← number summary "allocs") == 3 &&
      (← number summary "frees") == 3 && (← number summary "peakLiveNodes") == 2) "RC or peak policy mismatch"
    let steps := 21 + 2 * depth + (if successorCase then 2 else 0) + extraSteps
    let work := (if label == "baseline" then 6 else 5) + (if successorCase then 1 else 0)
    need ((← number row s!"{label}_control_steps") == steps &&
      (← number row s!"{label}_heap_work") == work &&
      (← number result "control_remaining") + steps == 1000 &&
      (← number result "heap_remaining") + work == 1000) "borrow execution cost mismatch"
    need ((← strField row s!"native_{label}") == "missingConstructorSchema") "native selection boundary changed"
  let fallbacks ← arrField snapshot "fallbacks"
  need (fallbacks.size == (if depth == 0 && !successorCase then 3 else 0)) "fallback coverage mismatch"
  for fallback in fallbacks do
    need ((← field fallback "program") == baseline) "fallback changed the checked baseline"
    need (!(← strField fallback "reason").isEmpty) "missing fallback reason"

private def alter (value : Json) (path : List String) (replacement : Json) : IO Json := do
  match path with
  | [] => return replacement
  | key :: rest =>
      match value with
      | .arr values =>
          let some index := key.toNat? | throw (IO.userError "invalid mutation array index")
          let old ← present values[index]? "mutation array index out of bounds"
          return toJson (values.set! index (← alter old rest replacement))
      | _ => replace value key (← alter (← field value key) rest replacement)

private def corruptionGuards (snapshot : Json) : IO Nat := do
  let row ← field snapshot "summary"
  let baseline ← field (← field (← field snapshot "compilation") "ixir2_diagnostic") "program"
  let baseCount := (← arrField baseline "declarations").size
  let variant := toString baseCount
  let mutations : List (List String × Json) := [
    (["rewritten", "declarations", "1", "1", "fn", "definition", "blocks", "0", "instructions", "1"],
      tagged "releaseShared" [("target", reg 1)]),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "signature", "params", "0", "passing"], toJson "owned"),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "blocks", "0", "valueParams", "0"], owned),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "blocks", "1", "terminator"],
      tagged "ret" [("value", reg 0)]),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "signature", "papSafe"], toJson true),
    (["borrowed_execution", "store", "heap", "rcops"], toJson (2 : Nat)),
    (["borrowed_execution", "store", "peakLiveNodes"], toJson (1 : Nat)),
    (["borrowed_prefixes", "3", "store", "heap", "nodes", "0", "rc"], toJson (17 : Nat)),
    (["borrowed_prefixes", "3", "control", "values", "0", "loc", "l"], toJson (99 : Nat)),
    (["borrowed_prefixes", "3", "heap_remaining"], toJson (0 : Nat)),
    (["borrowed_execution", "store", "heap", "nodes", "0"], obj [("fake", toJson true)]),
    (["fallbacks", "0", "program", "main", "blocks", "0", "terminator"], tagged "ret" [("value", reg 0)]),
    (["compilation", "source", "constants", "0", "bytes"], toJson "00")]
  for (path, value) in mutations do
    let corrupted ← alter snapshot path value
    let rejected ← try
        inspectSnapshot row corrupted
        pure false
      catch _ => pure true
    need rejected s!"independent checker accepted corrupted artifact at {path}"
  return mutations.length

private def compareFiles (first second : FilePath) (rows : Array Json) : IO Unit := do
  let expected := ("report.json" :: (← rows.toList.mapM (strField · "snapshot"))).mergeSort (· ≤ ·)
  need (expected.eraseDups.length == expected.length && expected.all (fun name =>
    !name.contains '/' && !name.contains '\\' && !name.contains ".." && !name.startsWith "."))
    "invalid or duplicate borrow artifact path"
  for directory in [first, second] do
    let entries ← directory.readDir
    need ((entries.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == expected) "borrow artifact inventory mismatch"
    for entry in entries do need (!(← entry.path.isDir)) "unexpected nested borrow artifact directory"
  for name in expected do
    need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
      s!"borrow artifacts differ between fresh compiler processes: {name}"

def main (args : List String) : IO UInt32 := cli "source borrow check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-borrow/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      let message ← run fixture #[output.toString]
      requireAll message ["source-borrow ok: 18 accepted Ixon cases"] "borrow producer"
      IO.print message
    let report ← readJson (first / "report.json")
    need ((← strField report "format") == "compilatrix/source-borrow/1" &&
      (← strField report "policy") == "closed-scalar-borrow/1" &&
      (← strField report "peak_policy") == "nonincreasing-peak-live-heap-nodes") "unknown borrow policy"
    let rows ← arrField report "cases"
    let expectedRows ← arrField expected "cases"
    need (rows.size == 18 && expectedRows.size == rows.size &&
      (← field report "negative_guards") == (← field expected "negative_guards")) "borrow coverage inventory mismatch"
    compareFiles first second rows
    for index in [:rows.size] do
      let row := rows[index]!
      for key in ["name", "depth", "successor", "source_root", "number"] do
        need ((← field row key) == (← field expectedRows[index]! key)) s!"borrow source pin drifted: {key}"
      inspectSnapshot row (← readJson (first / (← strField row "snapshot")))
    let corruptions ← corruptionGuards (← readJson (first / "read-tag-0-zero.json"))
    IO.println s!"source borrow check ok: {rows.size} complete artifact sets, independent rewrite and heap replay, {corruptions} corrupted artifacts rejected"
