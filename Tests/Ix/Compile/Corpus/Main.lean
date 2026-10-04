import Tests.Ix.Compile.Corpus.Report

open Lean
open Tests.Ix.Compile.Corpus

private def usage : String :=
  "aux-shape-sweep <inventory|generate|filter|assemble|aggregate|run|compare|matrix|self-check|verify-legacy|verify-round2>\n" ++
  "  --dir PATH --select all|curated|smoke|id,... --data PATH\n" ++
  "  --jobs N --workers N --timeout SECONDS --mode off|on|both\n" ++
  "  --phases comma,list --revision COMMIT --expected FILE --cases FILE\n" ++
  "  --local --keep-envs --legacy FILE --size N --ix PATH --cert PATH\n" ++
  "Run requires --revision. Outputs are immutable per run directory; no silent resume.\n"

private def options (args : List String) : Except String (Std.HashMap String String) := do
  let mut result := {}
  let mut pending : Option String := none
  for arg in args do
    if let some key := pending then
      if arg.startsWith "--" then throw s!"missing value for {key}"
      result := result.insert key arg
      pending := none
    else
      unless #["--dir", "--select", "--data", "--jobs", "--workers", "--timeout", "--mode",
        "--phases", "--revision", "--expected", "--cases", "--local", "--keep-envs", "--legacy", "--size", "--ix", "--cert"].contains arg do
        throw s!"unknown option {arg}"
      if result.contains arg then throw s!"duplicate option {arg}"
      if #["--local", "--keep-envs"].contains arg then result := result.insert arg "true"
      else pending := some arg
  if let some key := pending then throw s!"missing value for {key}"
  return result

private def natOption (opts : Std.HashMap String String) (key : String) (default : Nat) : IO Nat :=
  match opts[key]? with
  | none => pure default
  | some value => match value.toNat? with
    | some n => pure n
    | none => throw <| IO.userError s!"invalid natural number for {key}: {value}"

private def selfCheck (data : System.FilePath) : IO UInt32 := do
  let shapes ← loadCatalog data
  let check (label : String) (ok : Bool) : IO Unit := do
    unless ok do throw <| IO.userError s!"self-check failed: {label}"
    IO.println s!"[corpus] PASS {label}"
  check "complete historical shape count plus70 round2 bases" (shapes.size == 1395)
  check "single grid792" ((singles.filter (·.family == "single")).size == 792)
  check "nested grid22×5" ((nestedShapes.filter (·.family == "nested")).size == 110)
  check "4-case smoke selection" ((← IO.ofExcept (select shapes "smoke")).size == 4)
  let selected := curated shapes
  check "curated sort/recursion cells36" ((selected.filter (·.family == "single")).size == 36)
  check "curated container/form cells110" ((selected.filter (·.family == "nested")).size == 110)
  check "curated all44 mutuals and70 round2 neighbors"
    ((selected.filter (·.family == "mutual")).size == 44 && (selected.filter (·.family == "round2")).size == 70)
  check "token-aware substitution" (substitute "$T $Tree $A.foo" renamedNames == "Zq $Tree Kq.foo")
  check "token-aware inverse names" (unrename "AY.Test.Zq.fooZq" == "AX.Test.T.fooZq")
  check "all3-member permutations" ((permutations [0,1,2]).length == 6)
  let shape : Shape := { id := "x", family := "test", decl := "", members := #["a", "b"] }
  check "duplicate permutation rejected" ((shape.permuted [0,0] #[]).toOption.isNone)
  let candidates : Array Candidate := #[⟨"x", "x", none, "x.lean"⟩]
  check "missing elaboration result rejected" ((checkedElaborations candidates #[]).toOption.isNone)
  let row : Elaboration := ⟨"x", "accepted", 0, "x.log"⟩
  check "duplicate elaboration result rejected" ((checkedElaborations candidates #[row,row]).toOption.isNone)
  check "inconsistent elaboration result rejected"
    ((checkedElaborations candidates #[{ row with exitCode := 124 }]).toOption.isNone)
  let (differences, _, _, same) := compareNamed #[("AX.C.T", "aaa")] #[("AY.C.Zq", "bbb")] true
  check "wrong variant address detected" (!differences.isEmpty && !same)
  let (differences, onlyBase, onlyVariant, same) := compareNamed #[("AX.C.T", "aaa")] #[("AY.C.Zq", "aaa")] true
  check "renamed matching address accepted" (differences.isEmpty && onlyBase.isEmpty && onlyVariant.isEmpty && same)
  let expected : Array Expected := #[⟨"x", "on", "compile", "known diagnostic", "documented defect"⟩]
  let infrastructure : Verdict := ⟨"x", "on", "compile", "infrastructure-error", "known diagnostic", ""⟩
  check "expectation cannot suppress infrastructure error"
    ((applyExpected expected infrastructure "known diagnostic").status == "infrastructure-error")
  check "expectation cannot hide unexpected pass"
    ((applyExpected expected { infrastructure with status := "pass" } "").status == "fail")
  check "exact documented failure classified"
    ((applyExpected expected { infrastructure with status := "fail" } "known diagnostic").status == "known-unsupported")
  check "known failure cannot hide an additional failure"
    ((applyExpected expected { infrastructure with status := "fail" } "known diagnostic\nunexpected failure").status == "fail")
  check "Rust zero-target success rejected"
    ((checkedRustTargets "[check] 0/0 passed\n" 0).toOption.isNone)
  check "Rust missing summary rejected" ((checkedRustTargets "success\n" 0).toOption.isNone)
  check "Rust inconsistent success rejected"
    ((checkedRustTargets "[check] 1/2 passed\n" 0).toOption.isNone)
  check "Rust real work accepted" ((checkedRustTargets "[check] 2/2 passed\n" 0).toOption == some 2)
  check "Lean zero-target success rejected"
    ((Tests.Ix.Compile.KernelReport.checkedLeanTargets "##check-lean## 1 0 0 0\n").toOption.isNone)
  check "Lean unmatched selection retained"
    (Tests.Ix.Compile.KernelReport.leanUnmatched "[check-lean] warning: --consts name matched nothing: AX.X.T\n" == #["AX.X.T"])
  IO.FS.withTempDir fun dir => do
    let case : Case := ⟨"missing", "missing", "test", "base", "AX.Missing", "missing-source.lean", #[], #[]⟩
    let progress := dir / "runs" / case.id / "on"
    IO.FS.createDirAll progress
    writeJson (progress / "progress.json")
      (#[⟨case.id, "on", "elaborate", "pass", "completed before injected infrastructure failure", ""⟩] : Array Verdict)
    let rows ← runCaseSafe { dir, phases := #["elaborate", "compile", "certified"] } #[] case
    check "infrastructure failure preserves completed phase"
      (rows.any fun r => r.phase == "elaborate" && r.status == "pass")
    check "infrastructure failure records every unrun requested phase"
      ((rows.filter (·.status == "not-run")).size == 2 && rows.size == phaseNames.size + 1)
    check "infrastructure failure remains a failure"
      (rows.any fun r => r.phase == "infrastructure" && failure r)
  let aggregateCase : Case := ⟨"Agg_test", "Agg_test", "aggregate-family", "aggregate", "AX", "aggregates/Agg_test.lean", #[], #[]⟩
  let ledger : Array Verdict := phaseNames.map fun phase =>
    ⟨aggregateCase.id, "off", phase, if #["elaborate", "compile"].contains phase then "pass" else "not-selected", "", ""⟩
  check "complete aggregate ledger accepted"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] ledger).toOption.isSome)
  check "missing phase ledger rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] (ledger.extract 1 ledger.size)).toOption.isNone)
  check "duplicate phase ledger rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] (ledger ++ ledger)).toOption.isNone)
  check "wrong executed case manifest rejected"
    ((checkLedger #[{ aggregateCase with id := "different" }] #["off"] #["elaborate", "compile"] ledger).toOption.isNone)
  check "empty ledger rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] #[]).toOption.isNone)
  check "unknown ledger phase selection rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile", "unknown"] ledger).toOption.isNone)
  IO.println s!"[corpus] curated {curated shapes |>.size} cases; smoke4; full{shapes.size}"
  return 0

/-- Development evidence against the read-only legacy catalog: exact declaration
and extra source equality, independent of order in JSON objects. No Python runs. -/
private def verifyLegacy (data path : System.FilePath) : IO UInt32 := do
  let shapes ← loadCatalog data
  let legacy : Array Json ← readJson path
  let mut count := 0
  let mut problems : Array String := #[]
  for row in legacy do
    let id ← IO.ofExcept (row.getObjValAs? String "id")
    let some shape := shapes.find? (·.id == id)
      | problems := problems.push s!"missing shape {id}"
        continue
    let decl ← IO.ofExcept (row.getObjValAs? String "decl")
    if shape.decl != decl then problems := problems.push s!"{id}: declaration differs"
    let extraNames ← IO.ofExcept (row.getObjValAs? (Array String) "extras")
    if extraNames.size != shape.extras.size then problems := problems.push s!"{id}: extra count differs"
    let texts ← IO.ofExcept (row.getObjVal? "extra_text")
    for name in extraNames do
      let text ← IO.ofExcept (texts.getObjValAs? String name)
      if shape.extras.toList.lookup name != some text then problems := problems.push s!"{id}/{name}: extra differs"
    count := count + 1
  for p in problems do IO.println s!"[corpus] FAIL {p}"
  IO.println s!"[corpus] compared {count} legacy declarations and extras; {problems.size} differences"
  return if count == 1325 && problems.isEmpty then 0 else 1

/-- Verify all 70 round2 bases byte-for-byte, and all 82 historical permutations
up to blank separator lines introduced by the generic member assembler. -/
private def verifyRound2 (data path : System.FilePath) : IO UInt32 := do
  let shapes ← loadCatalog data
  let mut count := 0
  let mut failures := 0
  let lines (text : String) := (text.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  for entry in ← path.readDir do
    if entry.path.extension != some "lean" then continue
    let id := entry.path.fileStem.getD ""
    let parts := id.splitOn "__p"
    let base := parts.head!
    let some shape := shapes.find? (·.id == base)
      | throw <| IO.userError s!"unknown round2 fixture {id}"
    let actual ← if parts.length == 1 then pure shape.source
      else do
        let some index := (parts[1]!).toNat? | throw <| IO.userError s!"bad permutation ID {id}"
        let orders := (permutations (List.range shape.members.size)).mergeSort (fun a b => compare a b != .gt)
        let some order := orders[index]? | throw <| IO.userError s!"missing permutation {id}"
        IO.ofExcept (shape.permuted order #[])
    let expected ← IO.FS.readFile entry.path
    let equal := if parts.length == 1 then actual == expected else lines actual == lines expected
    unless equal do
      IO.println s!"[corpus] FAIL round2 {id}"
      failures := failures + 1
    count := count + 1
  IO.println s!"[corpus] compared {count} round2 sources; {failures} differences"
  return if count == 152 && failures == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  try
    let some op := args.head? | IO.print usage; return 2
    if op == "--help" then IO.print usage; return 0
    let opts ← IO.ofExcept (options args.tail)
    let dir : System.FilePath := opts.getD "--dir" "out/aux-shape-sweep"
    let data : System.FilePath := opts.getD "--data" "Tests/Ix/Compile/Corpus/Data"
    let jobs ← natOption opts "--jobs" 4
    let timeout ← natOption opts "--timeout" 900
    let mode := opts.getD "--mode" "both"
    let modes := if mode == "both" then #["off", "on"] else #[mode]
    match op with
    | "inventory" =>
      let shapes ← loadCatalog data
      let families := (shapes.map (·.family)).toList.eraseDups.mergeSort (· ≤ ·)
      for family in families do
        IO.println s!"{family}\t{(shapes.filter (·.family == family)).size}"
      IO.println s!"total\t{shapes.size}\ncurated\t{curated shapes |>.size}"
      return 0
    | "generate" =>
      generate (← IO.ofExcept <| select (← loadCatalog data) (opts.getD "--select" "curated")) dir
      return 0
    | "filter" => elaborate dir jobs timeout
    | "assemble" => assemble dir; return 0
    | "aggregate" => aggregate dir (← natOption opts "--size" 45); return 0
    | "run" =>
      let cases : Array Case ← readJson (dir / opts.getD "--cases" "cases.json")
      let expected : Array Expected ← match opts["--expected"]? with
        | none => pure #[]
        | some path => readJson path
      run
        { dir, jobs, timeout, workers := ← natOption opts "--workers" 1,
          ix := opts.getD "--ix" ".lake/build/bin/ix", cert := opts.getD "--cert" ".lake/build/bin/kernel-check-ixe",
          localScope := opts.contains "--local", keepEnvs := opts.contains "--keep-envs",
          phases := ((opts.getD "--phases" (String.intercalate "," phaseNames.toList)).splitOn ",").toArray }
        cases expected modes (opts.getD "--revision" "")
    | "compare" => compareVariants dir modes
    | "matrix" => matrix dir
    | "self-check" => selfCheck data
    | "verify-legacy" =>
      let some path := opts["--legacy"]? | throw <| IO.userError "verify-legacy requires --legacy"
      verifyLegacy data path
    | "verify-round2" =>
      let some path := opts["--legacy"]? | throw <| IO.userError "verify-round2 requires --legacy directory"
      verifyRound2 data path
    | _ => IO.eprintln usage; throw <| IO.userError s!"unknown command {op}"
  catch e =>
    IO.eprintln s!"[corpus] ERROR {e}"
    return 2
