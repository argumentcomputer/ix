import Tests.Ix.Compile.Corpus.Run

namespace Tests.Ix.Compile.Corpus

open Lean

def failure (row : Verdict) : Bool :=
  #["fail", "infrastructure-error", "not-run"].contains row.status

def verdictStatuses : Array String := #["pass", "known-unsupported", "documented-decline",
  "fail", "infrastructure-error", "not-run", "not-selected", "not-applicable"]

/-- Reporting requires exactly one row for every case/mode/phase, even when a
phase was not selected or could not run. Optional infrastructure rows add context;
they never replace the required phase rows. -/
def checkLedger (cases : Array Case) (modes phases : Array String) (rows : Array Verdict) :
    Except String Unit := do
  if cases.isEmpty || modes.isEmpty || rows.isEmpty then throw "empty corpus execution ledger"
  unless modes.all (#["off", "on"].contains ·) && modes.toList.eraseDups.length == modes.size do
    throw "invalid or duplicate ledger modes"
  unless phases.all (phaseNames.contains ·) && phases.toList.eraseDups.length == phases.size &&
      phases.contains "elaborate" && phases.contains "compile" do
    throw "invalid requested ledger phases"
  if (cases.map (·.id)).toList.eraseDups.length != cases.size then throw "duplicate ledger case"
  let mut seen : Std.HashSet (String × String × String) := {}
  for row in rows do
    unless cases.any (·.id == row.caseId) && modes.contains row.mode do
      throw s!"unknown ledger case/mode {row.caseId}/{row.mode}"
    unless verdictStatuses.contains row.status do throw s!"unknown verdict status {row.status}"
    unless phaseNames.contains row.phase || row.phase == "infrastructure" do
      throw s!"unknown verdict phase {row.phase}"
    let key := (row.caseId, row.mode, row.phase)
    if seen.contains key then throw s!"duplicate verdict {row.caseId}/{row.mode}/{row.phase}"
    seen := seen.insert key
    if row.phase == "infrastructure" then
      unless row.status == "infrastructure-error" do throw "invalid infrastructure verdict"
    else if !phases.contains row.phase then
      unless row.status == "not-selected" do throw s!"unselected phase has a result: {row.phase}"
    else if row.status == "not-selected" then throw s!"requested phase marked not-selected: {row.phase}"
    if row.status == "not-applicable" && !(row.phase == "parity" && row.mode == "on") then
      throw s!"invalid not-applicable phase {row.phase}/{row.mode}"
  for case in cases do
    for mode in modes do
      for phase in phaseNames do
        unless seen.contains (case.id, mode, phase) do
          throw s!"missing verdict {case.id}/{mode}/{phase}"

def validateExpected (cases : Array Case) (expected : Array Expected) : Except String Unit := do
  let mut seen : Std.HashSet (String × String × String) := {}
  for e in expected do
    if seen.contains (e.caseId, e.mode, e.phase) then throw s!"duplicate expectation {e.caseId}/{e.mode}/{e.phase}"
    seen := seen.insert (e.caseId, e.mode, e.phase)
    unless cases.any (·.id == e.caseId) do throw s!"expectation names absent case {e.caseId}"
    unless #["off", "on"].contains e.mode && phaseNames.contains e.phase do
      throw s!"invalid expected mode/phase {e.mode}/{e.phase}"
    if e.diagnostic.isEmpty || e.cause.isEmpty then throw "expected unsupported case lacks diagnostic or cause"

def run (cfg : RunConfig) (cases : Array Case) (expected : Array Expected)
    (modes : Array String) (revision : String) : IO UInt32 := do
  if cfg.jobs == 0 || cfg.workers == 0 || cfg.timeout == 0 then
    throw <| IO.userError "jobs, workers and timeout must be positive"
  if revision.isEmpty then throw <| IO.userError "--revision is required for run provenance"
  if cases.isEmpty || modes.isEmpty then throw <| IO.userError "run requires nonempty cases and modes"
  if modes.toList.eraseDups.length != modes.size then throw <| IO.userError "duplicate switch mode"
  let mut caseIds : Std.HashSet String := {}
  for case in cases do
    if caseIds.contains case.id then throw <| IO.userError s!"duplicate case {case.id}"
    if case.id.isEmpty || case.ns.isEmpty then throw <| IO.userError "empty case ID or namespace"
    caseIds := caseIds.insert case.id
  for mode in modes do
    unless #["off", "on"].contains mode do throw <| IO.userError s!"invalid switch mode {mode}"
  for phase in cfg.phases do
    unless phaseNames.contains phase do throw <| IO.userError s!"unknown phase {phase}"
  unless cfg.phases.contains "elaborate" && cfg.phases.contains "compile" do
    throw <| IO.userError "run must include elaborate and compile; use filter for elaboration only"
  if (cfg.phases.contains "closure" || cfg.phases.contains "parity") && !cfg.phases.contains "rust" then
    throw <| IO.userError "closure/parity requires the explicit Rust baseline phase"
  IO.ofExcept (validateExpected cases expected)
  for e in expected do
    unless modes.contains e.mode && cfg.phases.contains e.phase do
      throw <| IO.userError s!"expectation is outside selected execution: {e.caseId}/{e.mode}/{e.phase}"
  if ← (cfg.dir / "run-config.json").pathExists then
    throw <| IO.userError "run provenance already exists; use a fresh generated directory"
  let setup ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "--version"], cwd := cfg.dir }
  IO.FS.writeFile (cfg.dir / "lake-setup.log") (setup.stdout ++ setup.stderr)
  unless setup.exitCode == 0 do throw <| IO.userError "generated Lake project setup failed; see lake-setup.log"
  let version ← IO.Process.output { cmd := "lean", args := #["--version"] }
  let digests ← IO.Process.output { cmd := "sha256sum", args := #[cfg.ix.toString, cfg.cert.toString] }
  unless digests.exitCode == 0 do throw <| IO.userError s!"cannot fingerprint compiler/checker executables: {digests.stderr}"
  writeJson (cfg.dir / "run-config.json") <| Json.mkObj [
    ("revision", toJson revision), ("lean", toJson version.stdout),
    ("binaryDigests", toJson digests.stdout),
    ("modes", toJson modes), ("phases", toJson cfg.phases),
    ("scope", toJson (if cfg.localScope then "local" else "whole")),
    ("jobs", toJson cfg.jobs), ("workersPerCase", toJson cfg.workers),
    ("timeoutSeconds", toJson cfg.timeout), ("cases", toJson (cases.map (·.id))),
    ("closureBackend", toJson "rust --consts"), ("expected", toJson expected)]
  writeJson (cfg.dir / "run-cases.json") cases
  -- compile-lean always invokes Lake. Build each selected module once before
  -- parallel off/on cases; their later Lake calls then only verify cached inputs.
  let modules ← cases.mapM fun case => do
    unless case.file.endsWith ".lean" do throw <| IO.userError s!"non-Lean case source {case.file}"
    pure ((case.file.dropEnd 5).toString.replace "/" ".")
  let prepared ← IO.Process.output
    { cmd := "lake", args := #["build"] ++ modules, cwd := cfg.dir }
  IO.FS.writeFile (cfg.dir / "prepare.log") (prepared.stdout ++ prepared.stderr)
  writeJson (cfg.dir / "preparation.json") <| Json.mkObj [
    ("modules", toJson modules), ("exitCode", toJson prepared.exitCode.toNat),
    ("status", toJson (if prepared.exitCode == 0 then "pass" else "fail"))]
  if prepared.exitCode != 0 then
    let mut rows : Array Verdict := #[]
    for case in cases do
      for mode in modes do
        for phase in phaseNames do
          rows := rows.push ⟨case.id, mode, phase,
            if cfg.phases.contains phase then "not-run" else "not-selected",
            "shared source preparation failed", "prepare.log"⟩
    writeJson (cfg.dir / "verdicts.json") rows
    IO.eprintln "[corpus] source preparation failed; see prepare.log and preparation.json"
    return 1
  let mut pending : Array (Task (Except IO.Error (Array Verdict))) := #[]
  let mut rows := #[]
  for case in cases do
    for mode in modes do
      if pending.size ≥ cfg.jobs then
        if let some task := pending[0]? then rows := rows ++ (← IO.ofExcept task.get)
        pending := pending.extract 1 pending.size
        writeJson (cfg.dir / "run-progress.json") rows
      pending := pending.push (← IO.asTask (runCaseSafe { cfg with mode } expected case))
  for task in pending do rows := rows ++ (← IO.ofExcept (← IO.wait task))
  writeJson (cfg.dir / "verdicts.json") rows
  IO.ofExcept (checkLedger cases modes cfg.phases rows)
  let failures := rows.filter failure
  let unsupported := rows.filter fun row => #["known-unsupported", "documented-decline"].contains row.status
  IO.println s!"[corpus] {cases.size} cases × {modes.size} modes; {rows.size} phase rows; {unsupported.size} unsupported/declined, {failures.size} failures or unrun required phases"
  return if failures.isEmpty then 0 else 1

/-- Component-wise inverse renaming, unlike the old substring substitution. -/
def unrename (name : String) : String :=
  String.intercalate "." ((name.splitOn ".").map fun part =>
    if part == "AY" then "AX" else
      ([ ("Zq", "T"), ("Kq", "A"), ("Lq", "B"), ("Mq", "C"), ("Nq", "D") ].lookup part).getD part)

structure Comparison where
  caseId : String
  base : String
  mode : String
  kind : String
  status : String
  differing : Array String
  onlyBase : Array String
  onlyVariant : Array String
  addressMultisetEqual : Bool
  deriving ToJson, FromJson

def compareNamed (base variant : Array (String × String)) (rename : Bool) :
    Array String × Array String × Array String × Bool := Id.run do
  let variant := variant.map fun (n, a) => (if rename then unrename n else n, a)
  let bm := Std.HashMap.ofList base.toList
  let vm := Std.HashMap.ofList variant.toList
  let differing := base.filterMap fun (n, a) =>
    if let some b := vm[n]? then if a != b then some n else none else none
  let onlyBase := base.filterMap fun (n, _) => if vm.contains n then none else some n
  let onlyVariant := variant.filterMap fun (n, _) => if bm.contains n then none else some n
  let ba := (base.map (·.2)).qsort (· < ·)
  let va := (variant.map (·.2)).qsort (· < ·)
  return (differing.qsort (· < ·), onlyBase.qsort (· < ·), onlyVariant.qsort (· < ·), ba == va)

/-- No `_N` or Repr regex exclusions: all differences are retained for exact
non-canonical cause accounting. Missing base/variant artifacts fail closed. -/
def compareVariants (dir : System.FilePath) (modes : Array String) : IO UInt32 := do
  let cases : Array Case ← readJson (dir / "cases.json")
  let mut rows : Array Comparison := #[]
  for case in cases do
    if case.kind == "base" || case.kind == "aggregate" then continue
    for mode in modes do
      let bp := dir / "runs" / case.shape / mode / "compile-names.json"
      let vp := dir / "runs" / case.id / mode / "compile-names.json"
      if !(← bp.pathExists) || !(← vp.pathExists) then
        rows := rows.push ⟨case.id, case.shape, mode, case.kind, "missing", #[], #[], #[], false⟩
        continue
      let base : Array (String × String) ← readJson bp
      let variant : Array (String × String) ← readJson vp
      let (diff, onlyBase, onlyVariant, equal) := compareNamed base variant (case.kind == "rename")
      let ok := !base.isEmpty && !variant.isEmpty && diff.isEmpty && onlyBase.isEmpty && onlyVariant.isEmpty && equal
      rows := rows.push ⟨case.id, case.shape, mode, case.kind, if ok then "pass" else "difference",
        diff, onlyBase, onlyVariant, equal⟩
  writeJson (dir / "comparisons.json") rows
  let failures := rows.filter (·.status != "pass")
  IO.println s!"[corpus] {rows.size} variant comparisons, {failures.size} differences/missing; no blanket exclusions"
  return if failures.isEmpty then 0 else 1

def matrix (dir : System.FilePath) : IO UInt32 := do
  let config : Json ← readJson (dir / "run-config.json")
  let ids ← IO.ofExcept (config.getObjValAs? (Array String) "cases")
  let modes ← IO.ofExcept (config.getObjValAs? (Array String) "modes")
  let phases ← IO.ofExcept (config.getObjValAs? (Array String) "phases")
  let cases : Array Case ← readJson (dir / (if ← (dir / "run-cases.json").pathExists then "run-cases.json" else "cases.json"))
  unless (cases.map (·.id)).qsort (· < ·) == ids.qsort (· < ·) do
    throw <| IO.userError "case manifest does not match the executed cases"
  let rows : Array Verdict ← readJson (dir / "verdicts.json")
  IO.ofExcept (checkLedger cases modes phases rows)
  let family := fun id => ((cases.find? (·.id == id)).map (·.family)).getD "unknown"
  let families := (cases.map (·.family)).toList.eraseDups.mergeSort (· ≤ ·)
  let statuses := verdictStatuses
  let mut lines := #["| family | phase | mode | " ++ String.intercalate " | " statuses.toList ++ " |",
    "|---|---|---|" ++ String.join (statuses.toList.map fun _ => "---|")]
  for f in families do
    for phase in phaseNames.push "infrastructure" do
      for mode in #["off", "on"] do
        let selected := rows.filter fun r => family r.caseId == f && r.phase == phase && r.mode == mode
        unless selected.isEmpty do
          let counts := statuses.map fun status => toString (selected.filter (·.status == status)).size
          lines := lines.push s!"| {f} | {phase} | {mode} | {String.intercalate " | " counts.toList} |"
  let output := String.intercalate "\n" lines.toList ++ "\n"
  IO.FS.writeFile (dir / "matrix.md") output
  IO.print output
  return if rows.any failure then 1 else 0

def aggregate (dir : System.FilePath) (size : Nat := 45) : IO Unit := do
  if size == 0 then throw <| IO.userError "aggregate size must be positive"
  let cases : Array Case ← readJson (dir / "cases.json")
  IO.FS.createDirAll (dir / "aggregates")
  let bases := cases.filter (·.kind == "base")
  let families := (bases.map (·.family)).toList.eraseDups.mergeSort (· ≤ ·)
  let mut aggregates : Array Case := #[]
  let mut manifest : Array (String × Array String) := #[]
  for family in families do
    let selected := bases.filter (·.family == family)
    for index in [: (selected.size + size - 1) / size] do
      let part := selected.extract (index * size) ((index + 1) * size)
      let id := s!"Agg_{family.replace "-" "_"}_{index}"
      let file := s!"aggregates/{id}.lean"
      let mut source := ""
      for case in part do source := source ++ (← IO.FS.readFile (dir / case.file))
      IO.FS.writeFile (dir / file) source
      aggregates := aggregates.push { id, shape := id, family, kind := "aggregate", ns := "AX", file }
      manifest := manifest.push (id, part.map (·.id))
  writeJson (dir / "aggregates.json") aggregates
  writeJson (dir / "aggregate-members.json") manifest
  IO.println s!"[corpus] {aggregates.size} aggregates covering {bases.size} bases"

end Tests.Ix.Compile.Corpus
