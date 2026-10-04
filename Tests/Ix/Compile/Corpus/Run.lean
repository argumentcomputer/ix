import Tests.Ix.Compile.Corpus.Generate
import Ix.Ixon
import Tests.Ix.Compile.AuxCert
import Tests.Ix.Compile.KernelReport

namespace Tests.Ix.Compile.Corpus

open Lean

def phaseNames : Array String := #["elaborate", "compile", "rust", "determinism", "parity",
  "check-rs", "check-rs-anon", "check-lean", "certified", "closure", "pack", "validate", "validate-lean"]

structure RunConfig where
  dir : System.FilePath
  ix : System.FilePath := ".lake/build/bin/ix"
  cert : System.FilePath := ".lake/build/bin/kernel-check-ixe"
  phases : Array String := phaseNames
  mode : String := "on"
  jobs : Nat := 4
  workers : Nat := 1
  timeout : Nat := 900
  localScope : Bool := false
  keepEnvs : Bool := false

structure Verdict where
  caseId : String
  mode : String
  phase : String
  status : String
  detail : String
  log : String := ""
  deriving FromJson, ToJson

/-- Known unsupported cases need a reviewed exact identity and a diagnostic.
No wildcard shape/family/name matching is permitted. -/
structure Expected where
  caseId : String
  mode : String
  phase : String
  diagnostic : String
  cause : String
  deriving FromJson, ToJson

def applyExpected (expected : Array Expected) (row : Verdict) (diagnostic : String) : Verdict :=
  match expected.find? (fun e => e.caseId == row.caseId && e.mode == row.mode && e.phase == row.phase) with
  | none => row
  | some e =>
    if e.cause.isEmpty || e.diagnostic.isEmpty then
      { row with status := "fail", detail := "empty expected-failure cause or diagnostic" }
    else if row.status == "pass" then
      { row with status := "fail", detail := s!"stale expected failure: {e.cause}" }
    else if row.status == "fail" && (diagnostic.splitOn e.diagnostic).length > 1 then
      { row with status := "known-unsupported", detail := e.cause }
    else row

def envFor (cfg : RunConfig) : Array (String × Option String) := #[
  ("IX_PASS3", if cfg.mode == "on" then some "images" else none),
  ("LEAN_NUM_THREADS", some (toString cfg.workers)),
  ("RAYON_NUM_THREADS", some (toString cfg.workers)),
  ("IX_VALIDATE_AUXTABLE", none), ("LD_LIBRARY_PATH", none), ("CHECK_IXE_ROOTS", none)]

/-- Rust's stable summary must attest to nonempty work; absence and a successful
0/0 report are protocol errors, never an expected unsupported source case. -/
def checkedRustTargets (content : String) (exitCode : UInt32) : Except String Nat := do
  let summaries := (content.splitOn "\n").filter fun line =>
    line.startsWith "[check] " && line.endsWith " passed"
  let [line] := summaries | throw "check-rs did not emit exactly one work summary"
  let counts := ((line.drop 8).toString.dropEnd 7).toString.splitOn "/"
  let [passed, total] := counts | throw "malformed check-rs work summary"
  let (some p, some n) := (passed.toNat?, total.toNat?)
    | throw "nonnumeric check-rs work summary"
  if n == 0 || p > n then throw "check-rs reported zero or inconsistent targets"
  if exitCode == 0 && p != n then throw "check-rs success disagrees with its work summary"
  return n

def command (cfg : RunConfig) (dir : System.FilePath) (phase : String)
    (exe : String) (args : Array String)
    (extraEnv : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let out ← IO.Process.output
    { cmd := "timeout", args := #[toString cfg.timeout, exe] ++ args,
      env := (envFor cfg).filter (fun entry => !extraEnv.any (fun extra => extra.1 == entry.1)) ++ extraEnv }
  IO.FS.writeFile (dir / s!"{phase}.log") (out.stdout ++ out.stderr)
  let diagnostic := out.stdout ++ out.stderr
  let panic := #["PANIC", "panicked at", "Stack overflow", "out of memory"].any fun s =>
    (diagnostic.splitOn s).length > 1
  let checker := args[0]? == some "check-rs" || args[0]? == some "check-lean"
  if panic || (out.exitCode != 0 && out.exitCode != 1 && out.exitCode != 3) ||
      (checker && out.exitCode == 1) then
    throw <| IO.userError s!"{phase}: process infrastructure error, exit {out.exitCode}; see {dir}/{phase}.log"
  if args[0]? == some "check-rs" then
    discard <| IO.ofExcept (checkedRustTargets diagnostic out.exitCode)
    if (diagnostic.splitOn "exact name(s) not in env:").length > 1 then
      throw <| IO.userError s!"{phase}: requested Rust checker names were unmatched"
  if args[0]? == some "check-lean" then
    discard <| IO.ofExcept (KernelReport.checkedLeanTargets out.stdout)
    unless (KernelReport.leanUnmatched diagnostic).isEmpty do
      throw <| IO.userError s!"{phase}: requested Lean checker names were unmatched"
  return out

def resultRow (cfg : RunConfig) (case : Case) (phase : String) (out : IO.Process.Output) : Verdict :=
  { caseId := case.id, mode := cfg.mode, phase,
    status := if out.exitCode == 0 then "pass" else if out.exitCode == 1 || out.exitCode == 3 then "fail" else "infrastructure-error",
    detail := s!"exit {out.exitCode}", log := s!"{case.id}/{cfg.mode}/{phase}.log" }

def loadEnv (path : System.FilePath) : IO Ixon.Env := do
  IO.ofExcept <| Ixon.rsDeEnv (← IO.FS.readBinFile path)

def mine (env : Ixon.Env) (ns : String) : Array (Ix.Name × Ixon.Named) :=
  (env.named.toArray.filter fun (name, _) => name.pretty.startsWith (ns ++ ".")).qsort
    (fun a b => a.1.pretty < b.1.pretty)

def namesText (names : Array (Ix.Name × Ixon.Named)) : String :=
  String.join (names.toList.map fun (name, _) => name.pretty ++ "\n")

def namedManifest (names : Array (Ix.Name × Ixon.Named)) : Json :=
  toJson (names.map fun (name, value) => (name.pretty, toString value.addr))

/-- Compare complete Named records, including metadata/original/hints; missing
roots and closure-only invented names are failures, not absent comparisons. -/
def closureDifferences (whole closed : Ixon.Env) (root : String) : Array String := Id.run do
  let mut differences := #[]
  unless closed.named.toArray.any (fun (n, _) => n.pretty == root) do
    differences := differences.push s!"missing requested root {root}"
  for (n, nd) in closed.named do
    if whole.named.get? n != some nd then differences := differences.push n.pretty
  return differences.qsort (· < ·)

def withCheckedFile (cfg : RunConfig) (dir : System.FilePath) (label : String)
    (path : System.FilePath) : IO (Array String) := do
  let mut problems := #[]
  for (leg, args) in #[
      ("rs", #["check-rs", path.toString]),
      ("lean", #["check-lean", path.toString, "--workers", toString cfg.workers])] do
    let out ← command cfg dir s!"{label}-{leg}" cfg.ix.toString args
    if out.exitCode != 0 then problems := problems.push s!"{label}/{leg}: exit {out.exitCode}"
  return problems

/-- Legacy --consts closure probe, explicitly using Rust whole/closure outputs.
The Lean CLI lacks a --consts producer; its per-root closure gate belongs to the
separate in-process schedule/closure suite. Never compare an on-mode Lean image
against a legacy Rust closure and label the mismatch nondeterminism. -/
def closureLeg (cfg : RunConfig) (case : Case) (dir : System.FilePath)
    (src : System.FilePath) (whole : Ixon.Env) : IO (Array String) := do
  let mut problems := #[]
  let mut rows : Array Json := #[]
  IO.FS.createDirAll (dir / "closure")
  for ((name, _), i) in (mine whole case.ns).toList.zipIdx do
    let path := dir / "closure" / s!"{i}.ixe"
    let label := s!"closure/{i}"
    let out ← command { cfg with mode := "off" } dir label cfg.ix.toString
      #["compile", src.toString, "--no-build", "--consts", name.pretty, "--out", path.toString]
    let mut issues := #[]
    if out.exitCode != 0 || !(← path.pathExists) then
      issues := issues.push s!"{name.pretty}: closure compile exit {out.exitCode} or missing output"
    else
      let closed ← loadEnv path
      issues := closureDifferences whole closed name.pretty
      issues := issues ++ (← withCheckedFile cfg dir label path)
    rows := rows.push <| Json.mkObj [("root", toJson name.pretty), ("backend", toJson "rust"),
      ("problems", toJson issues), ("exitCode", toJson out.exitCode.toNat)]
    problems := problems ++ issues
    if !cfg.keepEnvs && (← path.pathExists) then IO.FS.removeFile path
  writeJson (dir / "closure.json") rows
  return problems

/-- Pack every fixture-owned name, a superset of the legacy auxiliary-only
selection; keep an explicit record for each root, including failed ones. -/
def packLeg (cfg : RunConfig) (case : Case) (dir path : System.FilePath)
    (env : Ixon.Env) : IO (Array String) := do
  let mut problems := #[]
  let mut rows : Array Json := #[]
  IO.FS.createDirAll (dir / "pack")
  for ((name, _), i) in (mine env case.ns).toList.zipIdx do
    let packed := dir / "pack" / s!"{i}.ixe"
    let label := s!"pack/{i}"
    let out ← command cfg dir label cfg.ix.toString #["pack", path.toString, name.pretty, "--out", packed.toString]
    let issues ← if out.exitCode != 0 || !(← packed.pathExists) then
        pure #[s!"{name.pretty}: pack exit {out.exitCode} or missing output"]
      else withCheckedFile cfg dir label packed
    rows := rows.push <| Json.mkObj [("root", toJson name.pretty), ("problems", toJson issues)]
    problems := problems ++ issues
    if !cfg.keepEnvs && (← packed.pathExists) then IO.FS.removeFile packed
  writeJson (dir / "pack.json") rows
  return problems

/-- Address coverage comes from the output environment, including aliases that
the checker's capped display-name array omitted. Protocol/process errors cannot
be reclassified by a known-failure entry. -/
def certifiedLeg (cfg : RunConfig) (case : Case) (dir path : System.FilePath)
    (env : Ixon.Env) : IO Verdict := do
  let reportPath := dir / "certified.jsonl"
  let out ← command cfg dir "certified" cfg.cert.toString
    #[path.toString, reportPath.toString, "--jobs", toString cfg.workers]
    #[("CHECK_IXE_ROOTS", some (String.intercalate "," ((mine env case.ns).map (·.1.pretty)).toList))]
  let fail (message : String) : Verdict :=
    { caseId := case.id, mode := cfg.mode,
      phase := "certified", status := "infrastructure-error", detail := message,
      log := s!"{case.id}/{cfg.mode}/certified.log" }
  unless ← reportPath.pathExists do return fail "certified checker wrote no report"
  let report ← match KernelReport.parse (← IO.FS.readFile reportPath) out.exitCode with
    | .ok report => pure report
    | .error e => return fail e
  let expected := (mine env case.ns).map fun (n, nd) =>
    (n.pretty, toString (AuxCert.recordOf env nd.addr))
  if let .error e := KernelReport.checkCoverage report expected then return fail e
  let mut counts : Std.HashMap String Nat := {}
  let mut problems : Array String := #[]
  let mut rows : Array Json := #[]
  for (name, address) in expected do
    let some verdict := report[address]? | return fail s!"missing {name}@{address}"
    counts := counts.insert verdict.outcome (counts.getD verdict.outcome 0 + 1)
    let documented := verdict.outcome == "decline" && AuxCert.documentedDecline verdict.reason
    if verdict.outcome != "accept" && !documented then
      problems := problems.push s!"{name}: {verdict.outcome}: {verdict.reason}"
    rows := rows.push <| Json.mkObj [("name", toJson name), ("address", toJson address),
      ("outcome", toJson verdict.outcome), ("reason", toJson verdict.reason),
      ("documentedDecline", toJson documented)]
  writeJson (dir / "certified-names.json") rows
  return { caseId := case.id, mode := cfg.mode, phase := "certified",
           status := if problems.isEmpty then (if counts.getD "decline" 0 == 0 then "pass" else "documented-decline") else "fail",
           detail := s!"accept={counts.getD "accept" 0} decline={counts.getD "decline" 0} reject={counts.getD "reject" 0} blocked={counts.getD "blocked" 0}; " ++
             String.intercalate "\n" problems.toList, log := s!"{case.id}/{cfg.mode}/certified.log" }

def runCase (cfg : RunConfig) (expected : Array Expected) (case : Case) : IO (Array Verdict) := do
  let dir := cfg.dir / "runs" / case.id / cfg.mode
  IO.FS.createDirAll dir
  if ← (dir / "verdicts.json").pathExists then
    throw <| IO.userError s!"results already exist for {case.id}/{cfg.mode}; use a fresh generated directory"
  let src ← IO.FS.realPath (cfg.dir / case.file)
  let leanPath := dir / "lean.ixe"
  let rustPath := dir / "rust.ixe"
  let scope := if cfg.localScope then #["--local"] else #[]
  let mut leanEnv : Option Ixon.Env := none
  let mut rustEnv : Option Ixon.Env := none
  let mut rows : Array Verdict := #[]
  let mut sourceOk := false
  for phase in phaseNames do
    let base : Verdict :=
      { caseId := case.id, mode := cfg.mode, phase,
        status := "not-selected", detail := "outside explicit phase selection" }
    if !cfg.phases.contains phase then
      rows := rows.push base
      continue
    let row ← match phase with
      | "elaborate" => do
        let out ← command cfg dir phase "lean" #[src.toString]
        sourceOk := out.exitCode == 0
        pure <| if sourceOk then resultRow cfg case phase out
          else { (resultRow cfg case phase out) with detail := "assembled source rejected; see elaboration log" }
      | "compile" | "rust" => do
        if !sourceOk then pure { base with status := "not-run", detail := "source elaboration did not pass" }
        else
          let isRust := phase == "rust"
          let path := if isRust then rustPath else leanPath
          let args := if isRust then #["compile", src.toString, "--no-build", "--out", path.toString] ++ scope
            else #["compile-lean", src.toString, "--workers", toString cfg.workers, "--out", path.toString] ++ scope
          let out ← command (if isRust then { cfg with mode := "off" } else cfg) dir phase cfg.ix.toString args
          let mut row := resultRow cfg case phase out
          if out.exitCode == 0 then
            if !(← path.pathExists) then row := { row with status := "infrastructure-error", detail := "successful compiler wrote no output" }
            else
              let env ← loadEnv path
              let names := mine env case.ns
              if names.isEmpty then row := { row with status := "infrastructure-error", detail := "compiled output has no fixture-owned names" }
              else
                writeJson (dir / s!"{phase}-names.json") (namedManifest names)
                IO.FS.writeFile (dir / s!"{phase}-names.txt") (namesText names)
                if isRust then rustEnv := some env else leanEnv := some env
          pure <| applyExpected expected row (out.stdout ++ out.stderr)
      | _ => do
        let some env := leanEnv
          | pure { base with status := "not-run", detail := "Lean compilation did not produce checked input" }
        if phase == "parity" && cfg.mode == "on" then
          pure { base with status := "not-applicable", detail := "Rust retains legacy surgery; parity is required only with Pass 3 off" }
        else if phase == "determinism" then
          let path := dir / "repeat.ixe"
          let out ← command cfg dir phase cfg.ix.toString
            (#["compile-lean", src.toString, "--workers", toString cfg.workers, "--out", path.toString] ++ scope)
          let equal ← if out.exitCode == 0 && (← path.pathExists) then
              pure <| (← IO.FS.readBinFile leanPath) == (← IO.FS.readBinFile path)
            else pure false
          if !cfg.keepEnvs && (← path.pathExists) then IO.FS.removeFile path
          pure { base with status := if equal then "pass" else "fail", detail := "repeated Lean output bytes", log := s!"{case.id}/{cfg.mode}/{phase}.log" }
        else if phase == "parity" then
          let equal ← if rustEnv.isSome then
              pure <| (← IO.FS.readBinFile leanPath) == (← IO.FS.readBinFile rustPath)
            else pure false
          pure { base with status := if equal then "pass" else "fail", detail := "switch-off Rust/Lean byte equality" }
        else if phase == "certified" then
          let row ← certifiedLeg cfg case dir leanPath env
          pure <| applyExpected expected row row.detail
        else if phase == "closure" || phase == "pack" then
          let issues ← if phase == "pack" then packLeg cfg case dir leanPath env
            else match rustEnv with
              | none => pure #["Rust whole output missing for closure baseline"]
              | some whole => closureLeg cfg case dir src whole
          let row :=
            { base with
              status := if issues.isEmpty then "pass" else "fail",
              detail := String.intercalate "\n" issues.toList }
          pure <| applyExpected expected row row.detail
        else
          let namesFile := dir / "compile-names.txt"
          let args := match phase with
            | "check-rs" => #["check-rs", leanPath.toString, "--consts-file", namesFile.toString]
            | "check-rs-anon" => #["check-rs", leanPath.toString, "--anon", "--consts-file", namesFile.toString]
            | "check-lean" => #["check-lean", leanPath.toString, "--consts-file", namesFile.toString, "--workers", toString cfg.workers]
            | "validate" => #["validate", src.toString, "--no-build", "--ns", case.ns, "--report", (dir / "validate.json").toString]
            | _ => #["validate-lean", src.toString, "--ns", case.ns, "--workers", toString cfg.workers, "--report", (dir / "validate-lean.json").toString]
          let out ← command cfg dir phase cfg.ix.toString args
          pure <| applyExpected expected (resultRow cfg case phase out) (out.stdout ++ out.stderr)
    rows := rows.push row
    -- Incremental, explicit evidence survives a later oracle/process failure.
    writeJson (dir / "progress.json") rows
  writeJson (dir / "verdicts.json") rows
  if !cfg.keepEnvs then
    for path in #[leanPath, rustPath] do
      if ← path.pathExists then IO.FS.removeFile path
  return rows

def runCaseSafe (cfg : RunConfig) (expected : Array Expected) (case : Case) : IO (Array Verdict) := do
  try runCase cfg expected case
  catch e =>
    let rows := #[
      { caseId := case.id, mode := cfg.mode, phase := "infrastructure",
        status := "infrastructure-error", detail := e.toString : Verdict }]
    let dir := cfg.dir / "runs" / case.id / cfg.mode
    IO.FS.createDirAll dir
    writeJson (dir / "failure.json") rows
    return rows

end Tests.Ix.Compile.Corpus
