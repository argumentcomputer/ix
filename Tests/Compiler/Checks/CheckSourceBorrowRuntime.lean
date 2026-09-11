import Ix.Compiler.Tools.BorrowRuntimeCheck

/-! Two fresh compiler processes, pinned source inputs, independently rebuilt
borrowed graphs and caller heaps, and every exported runtime transition. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.BorrowCheck Ix.Compiler.Tools.BorrowRuntimeCheck

private def inspectSnapshot (row snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-borrow-runtime-case/1" &&
    (← field snapshot "summary") == row && (← strField row "origin") == "synthetic-ixon" &&
    (← number row "depth") ≤ 8) "runtime snapshot/report mismatch"
  let compilation ← field snapshot "compilation"
  need ((← strField compilation "format") == "compilatrix/compiler-snapshot/1") "missing original compiler attachment"
  let source ← field compilation "source"
  need ((← field source "root") == (← field row "source_root") &&
    (← arrField source "constants").size == 5) "runtime source inventory changed"
  for constant in ← arrField source "constants" do hashField constant "bytes" "key"
  let literals ← arrField source "literal_inputs"
  need (literals.size == 2 && (← number literals[0]! "nat") == 11 && (← number literals[1]! "nat") == 22)
    "runtime payload leaked into compiler source inputs"
  for stage in ["ixir0", "ixir1"] do
    let graph ← field compilation stage
    for key in ["raw_declarations", "raw_main", "declarations", "main", "address_map"] do
      let _ ← field graph key
  let hpt ← field compilation "hpt"
  need (!(← arrField hpt "artifacts").isEmpty) "missing checked HPT artifacts"
  let diagnostics ← field compilation "ixir2_diagnostic"
  for key in ["validation_stats", "parameter_worlds", "constructors", "recursor_origins"] do
    let _ ← field diagnostics key
  let baseline ← field diagnostics "program"
  let rewritten ← field snapshot "rewritten"
  inspectGraph row baseline rewritten
  let depth ← number row "depth"
  let inference ← field row "inference"
  need ((← arrField inference "summaries").size == depth + 2 && (← number inference "attempts") == depth + 2 &&
    (← number inference "rounds") == 2 && (← number inference "rejected") == 0) "runtime inference work mismatch"
  let options ← field snapshot "options"
  need ((← number options "maxCandidates") == 32 && (← number options "maxRounds") == 16 &&
    (← number options "maxAttempts") == 256 && (← number options "maxSourceDepth") == 32 &&
    (← number (← field options "policy") "maxDepth") == 32 &&
    (← field (← field options "policy") "enabled") == toJson true) "runtime structural policy changed"
  need ((← pairs options).length == 5) "unexpected runtime replay option"
  let observations ← arrField snapshot "observations"
  need (observations.size == expectedInputs.size && (← number row "runtime_inputs") == expectedInputs.size)
    "runtime input matrix mismatch"
  for index in [:expectedInputs.size] do
    let (name, argument) := expectedInputs[index]!
    inspectInput row baseline rewritten observations[index]! name argument
  inspectLender row rewritten (← field snapshot "lender")
  need ((← strField row "native_baseline") == "missingConstructorSchema" &&
    (← strField row "native_borrowed") == "missingConstructorSchema") "native borrowing boundary changed"
  let fallbacks ← arrField snapshot "fallbacks"
  let expectedFallbacks := #["disabled", "inference-budget", "target-structure-budget", "source-structure-budget"]
  need (fallbacks.size == 4) "missing runtime fallback coverage"
  for index in [:4] do
    need ((← strField fallbacks[index]! "name") == expectedFallbacks[index]! &&
      (← field fallbacks[index]! "program") == baseline && !(← strField fallbacks[index]! "reason").isEmpty)
      "open-input fallback changed the checked baseline"

private def alter (value : Json) (path : List String) (replacement : Json) : IO Json := do
  match path with
  | [] => return replacement
  | key :: rest =>
      match value with
      | .arr values =>
          let some index := key.toNat? | throw (IO.userError "invalid corruption index")
          let old ← present values[index]? "corruption index out of bounds"
          return toJson (values.set! index (← alter old rest replacement))
      | _ => replace value key (← alter (← field value key) rest replacement)

private def corruptionGuards (snapshot : Json) : IO Nat := do
  let row ← field snapshot "summary"
  let baseline ← field (← field (← field snapshot "compilation") "ixir2_diagnostic") "program"
  let variant := toString (← arrField baseline "declarations").size
  let mutations : List (List String × Json) := [
    (["rewritten", "declarations", "1", "1", "fn", "definition", "blocks", "0", "instructions", "1"],
      tagged "releaseShared" [("target", reg 1)]),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "signature", "params", "0", "passing"], toJson "owned"),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "blocks", "0", "valueParams", "0"], owned),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "blocks", "1", "terminator"], ret (reg 0)),
    (["rewritten", "declarations", variant, "1", "fn", "definition", "signature", "papSafe"], toJson true),
    (["observations", "0", "input_store", "heap", "nodes", "0", "rc"], toJson (2 : Nat)),
    (["observations", "0", "input_value", "loc", "l"], toJson (8 : Nat)),
    (["observations", "0", "paths", "0", "borrowed", "store", "heap", "rcops"], toJson (0 : Nat)),
    (["observations", "0", "paths", "0", "borrowed", "store", "peakLiveNodes"], toJson (2 : Nat)),
    (["observations", "0", "paths", "0", "borrowed_prefixes", "2", "control", "values", "0", "loc", "l"], toJson (10 : Nat)),
    (["observations", "0", "paths", "1", "borrowed_prefixes", "2", "heap_remaining"], toJson (0 : Nat)),
    (["observations", "6", "paths", "0", "borrowed", "store", "heap", "frees"], toJson (1 : Nat)),
    (["observations", "3", "argument", "succ", "payload", "scalar", "value"], toJson (42 : Nat)),
    (["lender", "input_store", "heap", "nodes", "8", "rc"], toJson (1 : Nat)),
    (["lender", "prefixes", "3", "store", "heap", "nodes", "8", "rc"], toJson (2 : Nat)),
    (["lender", "cleanup_store", "heap", "frees"], toJson (0 : Nat)),
    (["fallbacks", "0", "program", "main", "blocks", "0", "terminator"], ret (atomNat 11)),
    (["compilation", "source", "constants", "0", "bytes"], toJson "00"),
    (["compilation", "source", "literal_inputs", "0", "nat"], toJson (42 : Nat)),
    (["options", "maxSourceDepth"], toJson (0 : Nat))]
  for (path, value) in mutations do
    let corrupted ← alter snapshot path value
    let rejected ← try
        inspectSnapshot row corrupted
        pure false
      catch _ => pure true
    need rejected s!"runtime checker accepted corrupted artifact at {path}"
  return mutations.length

private def compareFiles (first second : FilePath) (rows : Array Json) : IO Unit := do
  let expected := ("report.json" :: (← rows.toList.mapM (strField · "snapshot"))).mergeSort (· ≤ ·)
  need (expected.eraseDups.length == expected.length && expected.all (fun name =>
    !name.contains '/' && !name.contains '\\' && !name.contains ".." && !name.startsWith ".")) "invalid runtime artifact path"
  for directory in [first, second] do
    let entries ← directory.readDir
    need ((entries.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == expected) "runtime artifact inventory mismatch"
    for entry in entries do need (!(← entry.path.isDir)) "unexpected nested runtime artifact directory"
  for name in expected do
    need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
      s!"runtime artifacts differ between fresh processes: {name}"

def main (args : List String) : IO UInt32 := cli "source borrow runtime check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-borrow-runtime/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      let message ← run fixture #[output.toString]
      requireAll message ["source-borrow-runtime ok: 9 source functions; 72 runtime inputs"] "borrow runtime producer"
      IO.print message
    let report ← readJson (first / "report.json")
    need ((← strField report "format") == "compilatrix/source-borrow-runtime/1" &&
      (← strField report "policy") == "open-shared-tag-borrow/1" &&
      (← strField report "input_policy") == "one-owned-shared-root-allocation-ordered-heap" &&
      (← strField report "peak_policy") == "nonincreasing-peak-live-heap-nodes") "unknown runtime borrowing policy"
    let rows ← arrField report "cases"
    let expectedRows ← arrField expected "cases"
    need (rows.size == 9 && expectedRows.size == rows.size) "runtime source matrix mismatch"
    for key in ["structural_guards", "ownership_guards"] do
      need ((← field report key) == (← field expected key)) "runtime guard matrix mismatch"
    compareFiles first second rows
    for index in [:rows.size] do
      let row := rows[index]!
      for key in ["name", "depth", "source_root", "entry", "borrowed_entry", "factory"] do
        need ((← field row key) == (← field expectedRows[index]! key)) s!"runtime source/export pin drifted: {key}"
      inspectSnapshot row (← readJson (first / (← strField row "snapshot")))
    let corruptions ← corruptionGuards (← readJson (first / "read-tag-runtime-0.json"))
    IO.println s!"source borrow runtime check ok: 9 source functions, 72 runtime inputs, 144 independent direct/PAP comparisons, 9 aliased lenders, {corruptions} corrupted artifacts rejected"
