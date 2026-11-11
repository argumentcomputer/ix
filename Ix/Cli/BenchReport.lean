/-
  `ix bench` reporting subcommands — everything between the results rows
  JSON (`Ix.Benchmark.Results`) and a human or bencher.dev:

    compare     two rows files → a Markdown base-vs-PR table. With no
                explicit inputs, compares the parameter combination's local baseline against
                its previous run (`.lake/benches/<params>.json` vs `.prev.json`), so
                a bare local rerun reports its own delta.
    report      per-cell results → one Markdown report, one table per backend
                (the PR comment)
    bmf         rows JSON → Bencher Metric Format (status ≠ ok rows dropped)
    fetch-main  base SHA + params → rows JSON pulled from bencher.dev (curl)
    ci …        CI adapters: parse (!benchmark comment → job matrix) and
                matrix (registry → workflow job matrices)

  CI and local runs share this surface: the PR comment table and the local
  terminal table are the same renderer.
-/
module
public import Cli
public import Lean.Data.Json
public import Ix.Benchmark.Results
public import Ix.Cli.BenchCmd
public import Ix.Cli.BenchPlots

public section

open Lean (Json)
open Ix.Benchmark.Results

namespace Ix.Cli.BenchReport

/-! ## Metric formatting -/

/-- Per-metric formatting kind. Metric names are the results-JSON keys the
    tools emit (see the registry in Ix.Cli.BenchCmd). Unknown metrics fall
    through to a generic decimal rendering. -/
def metricKind (metric : String) : String :=
  if metric == "file-size" || metric.endsWith "peak-rss" || metric.endsWith "proof-size"
  then "bytes"
  -- Every wall-clock measure is named `<what>-time`.
  else if metric.endsWith "-time" then "seconds"
  else if ["fft-cost", "cycles", "steps", "max-shard-cycles"].contains metric
    || metric.endsWith "throughput" then "count"
  else if ["constants", "shards"].contains metric || metric.endsWith "-shards" then "int"
  else "auto"

/-- Display label for a metric column. Keys stay the bencher measure slugs
    (renaming one would orphan its threshold/history); only the table
    rendering differs. `file-size` is the serialized `.ixe` env — bencher
    plots it as "Environment Size"; `peak-rss` reads better as plain RAM;
    `shards` names the env partition, apart from a proof's `trace-shards`;
    `throughput` carries its unit here because the runs print bare
    magnitudes (matching `unitsFor`'s "constants / second" on bencher). -/
def metricLabel (metric : String) : String :=
  if metric == "file-size" then "env-size"
  else if metric.endsWith "throughput" then s!"{metric} (const/s)"
  else if metric == "shards" then "env-shards"
  else metric.replace "peak-rss" "peak-ram"

/-- Group a digit string by thousands: `"105492"` → `"105,492"`. -/
private def commafy (s : String) : String := Id.run do
  let (sign, digits) :=
    if s.startsWith "-" then ("-", (s.drop 1).toString) else ("", s)
  let n := digits.length
  let mut out := sign
  let mut i := 0
  for c in digits.toList do
    if i != 0 && (n - i) % 3 == 0 then
      out := out.push ','
    out := out.push c
    i := i + 1
  return out

private def fmtF (f : Float) (decimals : Nat) : String :=
  let scale := (10.0 : Float) ^ decimals.toFloat
  let n := (f * scale).round / scale
  let s := toString n
  -- `toString 3.0 = "3.000000"`; trim to the requested precision.
  match s.splitOn "." with
  | [i, frac] => if decimals == 0 then i else i ++ "." ++ frac.take decimals
  | _ => s

def humanBytes (v : Float) : String := Id.run do
  let mut v := v
  for unit in ["B", "KiB", "MiB", "GiB"] do
    if v.abs < 1024.0 then
      return if unit == "B" then s!"{fmtF v 0} B" else s!"{fmtF v 2} {unit}"
    v := v / 1024.0
  return s!"{fmtF v 2} TiB"

def humanSeconds (v : Float) : String :=
  if v.abs < 0.001 then s!"{fmtF (v * 1e6) 1} µs"
  else if v.abs < 1.0 then s!"{fmtF (v * 1e3) 1} ms"
  else if v.abs < 60.0 then s!"{fmtF v 3} s"
  else s!"{fmtF (v / 60.0).floor 0}m {fmtF (v - 60.0 * (v / 60.0).floor) 1}s"

def humanCount (v : Float) : String := Id.run do
  if v.abs < 1000.0 then
    return if v == v.round then fmtF v 0 else fmtF v 3
  let mut v := v
  for unit in ["K", "M", "B"] do
    v := v / 1000.0
    if v.abs < 1000.0 then return s!"{fmtF v 2}{unit}"
  return s!"{fmtF (v / 1000.0) 2}T"

def human (v : Option Float) (metric : String) : String :=
  match v with
  | none => "n/a"
  | some v =>
    match metricKind metric with
    | "bytes" => humanBytes v
    | "seconds" => humanSeconds v
    | "count" => humanCount v
    | "int" => commafy (fmtF v 0)
    | _ => if v == v.round then commafy (fmtF v 0) else fmtF v 3

/-- Metrics where a LARGER value is the improvement; everything else is
    lower-is-better (times, RAM, cycles, sizes). `throughput` means
    constants checked per second on EVERY backend. -/
def higherIsBetter (metric : String) : Bool :=
  metric.endsWith "throughput"

/-! ## Row access -/

def rowNum (rows : Json) (name metric : String) : Option Float := do
  let row ← (rows.getObjVal? name).toOption
  match (row.getObjVal? metric).toOption with
  | some (.num n) => some n.toFloat
  | _ => none

def rowStatus (rows : Json) (name : String) : String :=
  ((rows.getObjVal? name).toOption.bind
    fun r => (r.getObjVal? "status").toOption.bind (·.getStr?.toOption))
    |>.getD "ok"

def rowNames (rows : Json) : Array String :=
  match rows with
  | .obj kvs => kvs.toArray.map (·.1)
  | _ => #[]

/-! ## compare -/

/-- Signed regression magnitude: positive ⇒ the PR side got worse. -/
def badness (deltaPct : Float) (metric : String) : Float :=
  if higherIsBetter metric then -deltaPct else deltaPct

/-- `(factor ≥ 1, direction word)` for the ratio annotation; wording follows
    the metric kind ("1.15× slower" is meaningless for a byte metric). -/
def ratio (mainV prV : Float) (metric : String) : Option (Float × String) :=
  if mainV <= 0.0 || prV <= 0.0 then none else
  let grew := prV >= mainV
  let factor := if grew then prV / mainV else mainV / prV
  if higherIsBetter metric then
    some (factor, if grew then "faster" else "slower")
  else
    let words := match metricKind metric with
      | "seconds" => ("slower", "faster")
      | "bytes" => ("larger", "smaller")
      | _ => ("more", "fewer")
    some (factor, if grew then words.1 else words.2)

/-- One side of a metric cell: the value, or the row's failure for a
    metric the failure prevented. `none` when the side has no such row or
    no value. A kill can leave real partial measurements, which still
    render. An OOM is a capacity kill; any other kill is a failure of the
    tool. -/
def sideText (rows : Json) (name metric : String) : Option String :=
  if !(rowNames rows).contains name then none else
  let status := rowStatus rows name
  if status == "rejected" then some "❌" else
  match rowNum rows name metric with
  | some v => some (human (some v) metric)
  | none =>
    if status == "oom" then some "❌ OOM"
    else if status == "crash" then some "❌ failed"
    else none

/-- A metric's three cells, `base | PR | Δ%`, the Δ% marked ⚠️
    (regression) or 🟢 (improvement) when its badness-signed value passes
    `threshold`, and with the change as a factor (`1.10× slower`) from 1.05×
    on; with the flags (regressed, improved). All three are empty
    when neither side has the metric, and Δ% is `n/a` when only one does. -/
def metricCells (base pr : Json) (name metric : String) (threshold : Float) :
    Array String × Bool × Bool :=
  let b := sideText base name metric
  let p := sideText pr name metric
  if b.isNone && p.isNone then (#["", "", ""], false, false) else
  let sides := #[b.getD "—", p.getD "—"]
  match rowNum base name metric, rowNum pr name metric with
  | some bv, some pv =>
    if bv == 0.0 then (sides.push "n/a", false, false) else
    let dp := (pv - bv) / bv * 100.0
    let bad := badness dp metric
    let mark := if bad > threshold then " ⚠️" else if bad < -threshold then " 🟢" else ""
    -- The ratio only when it adds signal beyond the percentage.
    let factor := match ratio bv pv metric with
      | some (f, word) => if f >= 1.05 then s!" ({fmtF f 2}× {word})" else ""
      | none => ""
    (sides.push s!"{if dp >= 0.0 then "+" else ""}{fmtF dp 1}%{factor}{mark}",
      bad > threshold, bad < -threshold)
  | _, _ => (sides.push "n/a", false, false)

/-- One measured cell, (backend, env): both sides' rows, where the base
    side came from, and the hosts that measured each side. -/
structure Cell where
  backend : String
  env : String
  base : Json := Json.mkObj []
  pr : Json := Json.mkObj []
  baseSource : String := ""
  baseHardware : String := ""
  prHardware : String := ""

/-- The rows of a cell in display order: the env row, then its constants
    (shared constants in registry order, then any others by name). The
    flag marks the env row, present only when measured. -/
def Cell.rows (c : Cell) : Array (String × Bool) := Id.run do
  let names := (rowNames c.base ++ rowNames c.pr).foldl
    (fun acc n => if acc.contains n then acc else acc.push n) #[]
  let shared := Ix.BenchConstants.benchConstants.map (·.name)
  let constants := (shared.filter fun n => names.contains n && n != c.env)
    ++ ((names.filter fun n => n != c.env && !shared.contains n).qsort (· < ·))
  let envRow := if names.contains c.env then #[(c.env, true)] else #[]
  return envRow ++ constants.map ((·, false))

/-- The columns of one row kind's table: the kind's measures that some of
    `rows` has a value for, in registry order. -/
def columnsOf (metrics : List String) (rows : Array (Cell × String)) : List String :=
  metrics.filter fun m => rows.any fun (c, name) =>
    (rowNum c.base name m).isSome || (rowNum c.pr name m).isSome

/-- One backend's tables over its cells, one per row kind: the env rows,
    then the constant rows, then one table per proving stage the constant
    rows ran. Each metric a table's rows carry is a `base`, `PR` and `Δ%`
    column. -/
def renderBackend (spec : Ix.Cli.BenchCmd.BackendSpec) (cells : Array Cell)
    (threshold : Float) (baseLabel : String) : IO String := do
  let order := Ix.Cli.BenchCmd.envSpecs.map (·.name)
  let cells := cells.qsort fun a b => order.idxOf a.env < order.idxOf b.env
  let envRows := (cells.filter fun c => (c.rows.find? (·.2)).isSome).map fun c => (c, c.env)
  let constantRows := cells.flatMap fun c =>
    (c.rows.filter (!·.2)).map fun (name, _) => (c, name)
  -- A stage table names its stage on its time and throughput columns
  -- (`prove-time`, `prove-throughput`); its other measures drop the prefix
  -- (`peak-ram`, not `prove-peak-ram`).
  let table := fun (rows : Array (Cell × String)) (head : String) (label : String → String)
      (metrics : List String) (stage : String) => Id.run do
    let shown := fun (m : String) =>
      let rest := (m.drop (stage.length + 1)).toString
      metricLabel (if stage.isEmpty || !m.startsWith (stage ++ "-")
          || rest == "time" || rest == "throughput"
        then m else rest)
    let header := #[head] ++ (metrics.toArray.map fun m =>
      #[s!"{shown m} ({baseLabel})", s!"{shown m} (PR)", "Δ%"]).flatten
    let mut lines := #[
      "| " ++ " | ".intercalate header.toList ++ " |",
      "|" ++ "|".intercalate (header.toList.map fun _ => "---") ++ "|"]
    for (c, name) in rows do
      let cols := (metrics.toArray.map fun m => (metricCells c.base c.pr name m threshold).1).flatten
      lines := lines.push ("| " ++ " | ".intercalate (label name :: cols.toList) ++ " |")
    return lines
  let kind := fun (rows : Array (Cell × String)) (head : String) (label : String → String)
      (metrics : List String) => table rows head label (columnsOf metrics rows) ""
  let mut rows := 0
  let mut regressed := 0
  let mut improved := 0
  let mut failures : Array String := #[]
  for c in cells do
    for (name, isEnv) in c.rows do
      if !(rowNames c.base ++ rowNames c.pr).contains name then continue
      rows := rows + 1
      let metrics := if isEnv then spec.envMetrics
        else spec.constantMetrics ++ (spec.stages.map (·.2)).flatten
      let flags := metrics.map fun m => (metricCells c.base c.pr name m threshold).2
      if flags.any (·.1) then regressed := regressed + 1
      if flags.any (·.2) then improved := improved + 1
      if rowStatus c.base name == "rejected" then
        failures := failures.push s!"❌ **`{name}` FAILED TO TYPECHECK on the {baseLabel} side** — the kernel rejected it; see the logs."
      if rowStatus c.pr name == "rejected" then
        failures := failures.push s!"❌ **`{name}` FAILED TO TYPECHECK on the PR side** — the kernel rejected it; see the logs."
  let mut out := #[s!"### `{spec.name}`", ""]
  if rows == 0 then
    return "\n".intercalate (out.push "_No results were produced (every row failed, \
      timed out, or was dropped). See the workflow logs._").toList
  out := out ++ failures
  if !failures.isEmpty then out := out.push ""
  let plural := fun (n : Nat) (noun : String) => s!"{n} {noun}{if n == 1 then "" else "s"}"
  out := out.push s!"_{plural rows "row"} · {regressed} with regressions · \
    {improved} with improvements (|Δ| > {fmtF threshold 1}% on any metric)._"
  -- One side empty while the other measured is almost always a broken side
  -- (e.g. a base binary that predates a flag), not a real comparison.
  if cells.all (fun c => (rowNames c.base).isEmpty) then
    out := out.push "" |>.push
      s!"_⚠️ no {baseLabel}-side results (base run failed — see the workflow logs)._"
  else if cells.all (fun c => (rowNames c.pr).isEmpty) then
    out := out.push "" |>.push "_⚠️ no PR-side results (see the workflow logs)._"
  if !envRows.isEmpty then
    out := out ++ #["", s!"#### `{spec.name}` · envs", ""]
      ++ kind envRows "env" id spec.envMetrics
  if !constantRows.isEmpty then
    out := out ++ #["", s!"#### `{spec.name}` · constants", ""]
      ++ kind constantRows "constant" (s!"`{·}`") spec.constantMetrics
  for (stage, metrics) in spec.stages do
    let ran := constantRows.filter fun (c, name) =>
      metrics.any fun m => (rowNum c.base name m).isSome || (rowNum c.pr name m).isSome
    if !ran.isEmpty then
      out := out ++ #["", s!"#### `{spec.name}` · {stage}", ""]
        ++ table ran "constant" (s!"`{·}`") (columnsOf metrics ran) stage
  return "\n".intercalate out.toList

def runCompareCmd (p : Cli.Parsed) : IO UInt32 := do
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let env := (p.flag? "env").map (·.as! String) |>.getD "InitStd"
  let params := s!"{backend}-{env}"
  -- Explicit paths win; otherwise the local baseline pair, so a bare
  -- `ix bench compare --backend …` after two runs reports the local delta.
  let benchDir ← Ix.Cli.BenchCmd.benchOutputDir
  let mainPath := (p.flag? "base").map (·.as! String)
    |>.getD s!"{benchDir}/{params}.prev.json"
  let prPath := (p.flag? "pr").map (·.as! String)
    |>.getD s!"{benchDir}/{params}.json"
  let some spec := Ix.Cli.BenchCmd.findBackend backend
    | p.printError s!"error: unknown backend '{backend}' (see backendSpecs)"
      return exitUsage
  let threshold := (p.flag? "threshold").map (fun f => (f.as! Nat).toFloat)
    |>.getD 3.0
  let mainSrc := (p.flag? "base-source").map (·.as! String) |>.getD mainPath
  let baseLabel := (p.flag? "base-label").map (·.as! String) |>.getD "main"
  let cell : Cell := {
    backend, env, base := ← readRows mainPath, pr := ← readRows prPath }
  let table := s!"{baseLabel} from: {mainSrc}\n\n" ++
    (← renderBackend spec #[cell] threshold baseLabel)
  match p.flag? "out" with
  | some f => IO.FS.writeFile (f.as! String) (table ++ "\n")
  | none => IO.println table
  return 0

/-! ## report -/

/-- A cell directory as the PR workflow writes it: `base.json`, `pr.json`
    (either may be missing) and `meta.json` with `backend`, `env`, `base-source`, `base-hardware` and
    `pr-hardware`. -/
def readCell (dir : System.FilePath) : IO (Option Cell) := do
  let metaJson ← readRows (dir / "meta.json").toString
  let str := fun (k : String) =>
    ((metaJson.getObjVal? k).toOption.bind (·.getStr?.toOption)).getD ""
  if str "backend" == "" then return none
  let basePath := (dir / "base.json").toString
  let prPath := (dir / "pr.json").toString
  return some {
    backend := str "backend", env := str "env"
    base := ← readRows basePath, pr := ← readRows prPath
    baseSource := str "base-source", baseHardware := str "base-hardware"
    prHardware := str "pr-hardware" }

/-- The distinct non-empty values, in first-seen order. -/
def distinct (xs : Array String) : Array String :=
  xs.foldl (fun acc x => if x.isEmpty || acc.contains x then acc else acc.push x) #[]

/-- Assemble the per-cell results (`<dir>/<cell>/`, see `readCell`) into
    one Markdown report, the PR comment: one header line (base ← PR, the
    machine, where the base side came from, the run's selection), the
    measuring hardware once, then one table per backend in registry order.
    The link flags are optional garnish: with `--head`/`--base-sha`/
    `--repo-url`/`--run-id` the header links both commits and a logs
    footer is appended. -/
def runReportCmd (p : Cli.Parsed) : IO UInt32 := do
  let cellsDir := (p.flag? "cells").map (·.as! String) |>.getD "cells"
  let head := (p.flag? "head").map (·.as! String) |>.getD ""
  let baseSha := (p.flag? "base-sha").map (·.as! String) |>.getD ""
  let repoUrl := (p.flag? "repo-url").map (·.as! String) |>.getD ""
  let runId := (p.flag? "run-id").map (·.as! String) |>.getD ""
  let summary := (p.flag? "summary").map (·.as! String) |>.getD ""
  let baseLabel := (p.flag? "base-label").map (·.as! String) |>.getD "main"
  let threshold := (p.flag? "threshold").map (fun f => (f.as! Nat).toFloat)
    |>.getD 3.0
  let commit := fun (sha : String) =>
    if sha.isEmpty then "" else if repoUrl.isEmpty then s!"`{sha.take 7}`"
    else s!"[`{sha.take 7}`]({repoUrl}/commit/{sha})"
  let base := if baseSha.isEmpty then baseLabel else s!"{baseLabel} {commit baseSha}"
  let mut cells : Array Cell := #[]
  if ← System.FilePath.pathExists cellsDir then
    for entry in ← System.FilePath.readDir cellsDir do
      if let some c ← readCell entry.path then cells := cells.push c
  let header := s!"## `!benchmark` — {base} ← PR {commit head}"
  let machine ← Ix.Cli.BenchCmd.benchmarkMachine
  let sources := distinct (cells.map (·.baseSource))
  let mut line := #[s!"machine `{machine}`"]
  if !sources.isEmpty then line := line.push s!"base: {", ".intercalate sources.toList}"
  if !summary.isEmpty then line := line.push summary
  let mut parts := #[header, "", " · ".intercalate line.toList, ""]
  let baseHw := distinct (cells.map (·.baseHardware))
  let prHw := distinct (cells.map (·.prHardware))
  let hardware :=
    if baseHw == prHw && baseHw.size ≤ 1 then baseHw.toList.map (fun hw => s!"Hardware: {hw}")
    else [s!"Hardware: base {"; ".intercalate baseHw.toList} · PR {"; ".intercalate prHw.toList}"]
  for hw in hardware do parts := parts ++ #[hw, ""]
  if cells.isEmpty then
    parts := parts ++ #["_No results were produced — see the run logs._", ""]
  for spec in Ix.Cli.BenchCmd.backendSpecs do
    let mine := cells.filter (·.backend == spec.name)
    if mine.isEmpty then continue
    parts := parts ++ #[← renderBackend spec mine threshold baseLabel, ""]
  if !repoUrl.isEmpty && !runId.isEmpty then
    parts := parts.push s!"[Workflow logs]({repoUrl}/actions/runs/{runId})"
  let body := "\n".intercalate parts.toList ++ "\n"
  match p.flag? "out" with
  | some f => IO.FS.writeFile (f.as! String) body; IO.println body
  | none => IO.println body
  return 0

/-! ## bmf -/

/-- Measure slug for a per-shard breakdown key: the shard rows share the
    parent row's measure vocabulary (`shard-cycles` → `cycles`,
    `shard-time` → `execute-time`, `shard-peak-rss` → `peak-rss`). -/
def shardMeasure (k : String) : String :=
  if k == "shard-time" then "execute-time"
  else if k.startsWith "shard-" then (k.drop 6).toString
  else k

/-- Rows JSON → Bencher Metric Format. Rows with `status ≠ ok` are dropped
    whole — a rejected, OOM'd, partial or conditional run must never become
    a bencher data point. Numeric fields pass through as measures. Nested per-shard objects (`shard-cycles: {"0": …}`)
    become per-shard BENCHMARKS (`<name>/shard-0`) sharing the parent's
    measure slugs — multiplicity belongs in bencher's benchmark dimension,
    not as one measure per shard index. -/
def toBmf (rows : Json) : Json := Id.run do
  let mut out : Array (String × Json) := #[]
  for name in rowNames rows do
    -- A conditional row is a complete check whose verdict lists user axioms.
    if !["ok", "conditional"].contains (rowStatus rows name) then continue
    let some row := (rows.getObjVal? name).toOption | continue
    let mut measures : Array (String × Json) := #[]
    let mut shardRows : Array (String × Array (String × Json)) := #[]
    match row with
    | .obj kvs =>
      for (k, v) in kvs.toArray do
        if k == "status" then continue
        match v with
        | .num _ => measures := measures.push (k, Json.mkObj [("value", v)])
        | .obj sub =>
          for (subK, subV) in sub.toArray do
            if let .num _ := subV then
              let bench := s!"{name}/shard-{subK}"
              let m := (shardMeasure k, Json.mkObj [("value", subV)])
              shardRows := match shardRows.findIdx? (·.1 == bench) with
                | some i => shardRows.modify i fun (b, ms) => (b, ms.push m)
                | none => shardRows.push (bench, #[m])
        | _ => pure ()
    | _ => pure ()
    if !measures.isEmpty then
      out := out.push (name, Json.mkObj measures.toList)
    for (bench, ms) in shardRows do
      out := out.push (bench, Json.mkObj ms.toList)
  return Json.mkObj out.toList

def runBmfCmd (p : Cli.Parsed) : IO UInt32 := do
  let inPath := (p.flag? "in").map (·.as! String) |>.getD "bench.json"
  let outPath := (p.flag? "out").map (·.as! String) |>.getD "bmf.json"
  let bmf := toBmf (← readRows inPath)
  IO.FS.writeFile outPath bmf.pretty
  IO.println s!"bmf: {(rowNames bmf).size} benchmark(s) → {outPath}"
  -- Zero survivors (missing input, or every row OOM'd/rejected) is not an
  -- uploadable result — exit nonzero so the caller skips the upload
  -- instead of sending bencher an empty report it will reject.
  if (rowNames bmf).isEmpty then
    IO.eprintln "bmf: no ok rows — nothing to upload"
    return 1
  return 0

/-! ## fetch-main -/

def curlJson (url : String) : IO (Except String Json) := do
  let r ← IO.Process.output {
    cmd := "curl"
    args := #["-sf", "--retry", "3", "--retry-delay", "2",
              "--max-time", "30", url]
  }
  if r.exitCode != 0 then
    return .error s!"curl exit {r.exitCode}: {r.stderr.take 300}"
  return Lean.Json.parse r.stdout

/-- Pull the base SHA's rows JSON from bencher.dev. Exit codes are
    load-bearing for the workflow: 3 = transient (no report at that hash
    yet, or the API failed) — the caller falls back to running main
    locally; 2 = config error (unknown backend) — the caller fails
    the run loudly instead of paying the fallback forever. A PARTIAL miss
    still exits 0: `--missing-out` lists the uncovered names so the caller
    measures just those against the base checkout and merges. -/
def runFetchMainCmd (p : Cli.Parsed) : IO UInt32 := do
  let sha := (p.flag? "sha").map (·.as! String) |>.getD ""
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let out := (p.flag? "out").map (·.as! String) |>.getD "main.json"
  let some testbed := (Ix.Cli.BenchCmd.findBackend backend).map (·.testbed)
    | IO.println s!"fetch-main: no testbed for {backend}"
      return exitUsage
  let testbed := Ix.Cli.BenchCmd.testbedOnMachine testbed
    (← Ix.Cli.BenchCmd.benchmarkMachine)
  let wanted : Option (Array String) ← do
    let names ← Ix.Cli.ConstsFile.gather p "rows" "names"
    if (p.flag? "rows").isNone && (p.flag? "names").isNone then pure none
    else pure (some names)

  -- Page newest-first until the SHA's reports are found; aggregate across
  -- reports (matrix envs upload separately to one testbed), NEWEST report
  -- winning on a name collision (a re-run at the same commit supersedes).
  let reportHash := fun (r : Json) =>
    (r.getObjVal? "branch").toOption.bind fun b =>
    (b.getObjVal? "head").toOption.bind fun h =>
    (h.getObjVal? "version").toOption.bind fun v =>
    (v.getObjVal? "hash").toOption.bind (·.getStr?.toOption)
  let mut atSha : Array Json := #[]
  let mut page := 1
  while page <= 8 do
    let url := s!"https://api.bencher.dev/v0/projects/ix/reports?branch=main&testbed={testbed}&per_page=255&page={page}"
    match ← curlJson url with
    | .error e =>
      IO.println s!"fetch-main: bencher API error: {e}"
      return exitRejected
    | .ok j =>
      let reports := j.getArr?.toOption.getD #[]
      let hits := reports.filter fun r => reportHash r == some sha
      if !atSha.isEmpty && hits.isEmpty then break
      atSha := atSha ++ hits
      if reports.size < 255 then break
      page := page + 1
  if atSha.isEmpty then
    IO.println s!"fetch-main: no reports for {backend} @ {sha.take 8}"
    return exitRejected

  -- The LIST endpoint stopped inlining each report's `results` (it now
  -- carries only a `counts` summary), which read here as "report found,
  -- zero rows" and sent every caller down the full base-rerun fallback.
  -- Fetch each matched report by uuid — the single-report GET still
  -- returns full results; the inline array is used when a future API
  -- (or cached response) populates it again.
  let mut detailed : Array Json := #[]
  for r in atSha do
    let inline := (r.getObjVal? "results").toOption.bind (·.getArr?.toOption)
      |>.getD #[]
    if !inline.isEmpty then
      detailed := detailed.push r
    else
      let some uuid := (r.getObjVal? "uuid").toOption.bind (·.getStr?.toOption)
        | continue
      match ← curlJson s!"https://api.bencher.dev/v0/projects/ix/reports/{uuid}" with
      | .error e =>
        IO.println s!"fetch-main: bencher API error (report {uuid}): {e}"
        return exitRejected
      | .ok full => detailed := detailed.push full

  let mut rows : Array (String × Json) := #[]
  let mut seen : Array String := #[]
  for r in detailed do
    let iterations := (r.getObjVal? "results").toOption.bind (·.getArr?.toOption)
      |>.getD #[]
    for iteration in iterations do
      for bench in iteration.getArr?.toOption.getD #[] do
        let some name := (bench.getObjVal? "benchmark").toOption.bind fun b =>
            (b.getObjVal? "name").toOption.bind (·.getStr?.toOption) | continue
        if seen.contains name then continue
        if let some w := wanted then
          if !w.contains name then continue
        let mut metrics : Array (String × Json) := #[("status", Json.str "ok")]
        let ms := (bench.getObjVal? "measures").toOption.bind (·.getArr?.toOption)
          |>.getD #[]
        for m in ms do
          -- The SLUG is the source of truth: row keys are born
          -- slug-shaped (see the registry metric lists), uploads attach
          -- to measures by it, and
          -- the console-editable display name is never consulted.
          let mSlug := (m.getObjVal? "measure").toOption.bind fun x =>
            (x.getObjVal? "slug").toOption.bind (·.getStr?.toOption)
          let mVal := (m.getObjVal? "metric").toOption.bind fun x =>
            (x.getObjVal? "value").toOption
          if let (some ms, some mv) := (mSlug, mVal) then
            metrics := metrics.push (ms, mv)
        if metrics.size > 1 then
          seen := seen.push name
          rows := rows.push (name, Json.mkObj metrics.toList)
  if rows.isEmpty then
    IO.println "fetch-main: reports found but no matching benchmarks in --names"
    return exitRejected
  if let some missingOut := (p.flag? "missing-out").map (·.as! String) then
    let nameSet ← Ix.Cli.ConstsFile.gather p "rows" "names"
    let missing := nameSet.filter fun n => !seen.contains n
    IO.FS.writeFile missingOut
      ("\n".intercalate missing.toList ++ (if missing.isEmpty then "" else "\n"))
    if !missing.isEmpty then
      IO.println s!"fetch-main: {missing.size} name(s) not on bencher @ \
        {sha.take 8} (base run will measure): {", ".intercalate missing.toList}"
  IO.FS.writeFile out (Json.mkObj rows.toList).compress
  IO.println s!"fetch-main: {rows.size} row(s) from bencher for {backend}"
  return 0

/-! ## matrix -/

/-- Emit the benchmark matrix from the registry, so workflow matrices are
    generated instead of hand-copied: each enabled backend fanned over every
    registry env, each cell running all its rows (the env's shared constants
    and its env row) — the one fan-out every workflow
    matrix and gate derives from (any projection, like an env list, is a
    jq away). Each entry carries the metadata its job needs verbatim, the
    display label and the bencher testbed, so the workflow hardcodes none
    of it. -/
def runMatrixCmd (_ : Cli.Parsed) : IO UInt32 := do
  let machine ← Ix.Cli.BenchCmd.benchmarkMachine
  let mut entries : Array Json := #[]
  for b in Ix.Cli.BenchCmd.backendSpecs do
    if b.disabled.isSome then continue
    for env in Ix.Cli.BenchCmd.envSpecs.map (·.name) do
      entries := entries.push <| Json.mkObj
        [("backend", Json.str b.name), ("env", Json.str env),
         ("label", Json.str s!"{b.name}-{env}"),
         ("testbed", Json.str (Ix.Cli.BenchCmd.testbedOnMachine b.testbed machine))]
  IO.println (Json.arr entries).compress
  return 0

/-! ## parse -/

/-- Reject the `!benchmark` command: stderr for the log, and a
    `parse-error` step output so the workflow's failure comment can quote
    the reason instead of pointing at the run log. Exit 2 (usage). -/
def parseError (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  if let some outPath := ← IO.getEnv "GITHUB_OUTPUT" then
    let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
    h.putStr s!"parse-error={msg}\n"
    h.flush
  return 2

structure ParsedCommand where
  matrix : Array Json
  envs : Array String
  summary : String
  passthrough : Array String
  fresh : Bool

/-- Parse a `!benchmark` command into the runs it schedules — locally a
    dry-run preview (`ix bench ci parse --comment "!benchmark ixvm-ooc"` prints
    the summary and run list), in CI the matrix generator. The text comes
    from `--comment`, else the `COMMENT_BODY` env var (how the PR workflow
    passes the comment without inline shell interpolation). When
    `$GITHUB_OUTPUT` is set, the machine outputs (matrix, flags, summary,
    passthrough env) are appended there in Actions format.

    Grammar (an unknown command-line token, or an unknown env in
    BENCH_ENVS, rejects the command — exit 2 and a `parse-error` output):

      !benchmark ([ixvm [execute|prove|compress]] [ixvm-ooc] [compile] [decompile] | all)
                 [fresh] [KEY=VALUE …]
      (at least one backend or `all` is required)
      BENCH_CONSTANTS=all|none|a,b (constant rows; default all. A shared
                                    constant runs in its own env; any other
                                    name needs a single-env BENCH_ENVS
                                    naming where it lives.)
      BENCH_ENVS=all|none|a,b      (env rows: case-insensitive registry
                                    envs; default InitStd)
      Setting either key selects exactly what it names: the other key then
      defaults to `none`, and the defaults above apply only when neither
      is set. With neither set, `ixvm prove` and `ixvm compress` select
      only `Nat.add_comm`.
      RUST_LOG=… / RUSTFLAGS=… / IX_COMPILE_DEMOTE=…
                                    (passthrough; IX_COMPILE_DEMOTE reaches
                                    the measured `ix compile`, but emits the
                                    same `.ixe`; caches are SHA-keyed, so
                                    `fresh` remeasures a knob on one SHA)

    The ixvm subcommand defaults to execute. Prove adds proving and root
    verification to constant rows; compress also adds KZG compression and
    verification with development parameters. Env rows stay execution-only.

    Each scheduled cell is (backend, env) for an env with a selected
    constant row (on a backend with constant rows) or a selected env row;
    the cell runs exactly those rows.

    The KEY=VALUE config may sit on its own lines below the command (the
    comment form) or inline on the command line, whitespace-separated
    (the single-line form — a workflow_dispatch input box can't hold
    newlines). Inline keys parse strictly: an unknown key rejects the
    command, like a typo'd backend.

    The comparison prints in the comment only; PR runs never upload to
    bencher, so the canonical baseline is untouched. `fresh` bypasses
    stored benchmark products and baseline results while retaining
    dependency caches. -/
def parseCommand (body : String) : Except String ParsedCommand := do
  let lines := (body.splitOn "\n").map (·.replace "\r" "")
  let isCmd := fun (l : String) => (l.splitOn "!benchmark").length > 1
  let cmd := (lines.find? isCmd).getD ""
  let toks := if isCmd cmd
    then (((cmd.splitOn "!benchmark")[1]!).splitOn " ").filter (· ≠ "")
    else []
  -- `KEY=VALUE` tokens on the command line itself are the single-line
  -- form of the config lines — the manual workflow_dispatch path, whose
  -- input box can't hold newlines. Split them out here; they parse with
  -- the config lines below (strictly — like any command-line token).
  let (cfgToks, toks) := toks.partition (fun t => (t.splitOn "=").length > 1)

  let mut backends : Array Ix.Cli.BenchCmd.BackendSpec := #[]
  let mut skipped : Array Ix.Cli.BenchCmd.BackendSpec := #[]
  let mut ixvmMode : Ix.Cli.BenchCmd.IxvmMode := .execute
  let mut modeSet := false
  let mut afterIxvm := false
  let mut fresh := false
  for t in toks.map (·.toLower) do
    if t == "fresh" then
      fresh := true
      continue
    if let some mode := Ix.Cli.BenchCmd.IxvmMode.parse? t then
      if !afterIxvm then
        throw s!"`{t}` must follow `ixvm`: !benchmark ixvm {t}"
      if modeSet then
        throw "select only one ixvm subcommand: execute, prove, or compress"
      ixvmMode := mode
      modeSet := true
      afterIxvm := false
      continue
    afterIxvm := t == "ixvm"
    let requested := if t == "all"
      then Ix.Cli.BenchCmd.backendSpecs.filter (·.disabled.isNone)
      else (Ix.Cli.BenchCmd.findBackend t).toList
    -- Everything after `!benchmark` on the command line must parse: a
    -- typo'd backend silently running the default would report numbers
    -- the commenter never asked for.
    if requested.isEmpty then
      throw s!"unknown token `{t}` in the benchmark command \
        (expected a backend — \
        {", ".intercalate ((Ix.Cli.BenchCmd.backendSpecs.filter
          (·.disabled.isNone)).map (·.name))} — \
        or `all` / `fresh`; ixvm accepts execute, prove, or compress)"
    for b in requested do
      if b.disabled.isSome then
        if skipped.all (·.name != b.name) then skipped := skipped.push b
      else if backends.all (·.name != b.name) then
        backends := backends.push b
  if backends.isEmpty then
    if !skipped.isEmpty then
      let reasons := ", ".intercalate <| skipped.toList.map fun b =>
        s!"{b.name} ({b.disabled.getD "disabled in CI"})"
      throw s!"no requested benchmark backend is enabled in CI: {reasons}"
    throw s!"`!benchmark` needs a backend: one or more of \
      {", ".intercalate ((Ix.Cli.BenchCmd.backendSpecs.filter
        (·.disabled.isNone)).map (·.name))}, or `all`"

  -- KEY=VALUE config: the inline command-line tokens (strict — an
  -- unknown key rejects, same as a typo'd backend), then the lines below
  -- the command (lenient — comments contain prose, and prose contains
  -- `=`, so only recognized keys are consulted there).
  let mut envsVal : Option String := none
  let mut constantsVal : Option String := none
  let mut passthrough : Array String := #[]
  let mut cfgEntries : Array (String × Bool) :=
    (cfgToks.map ((·, true))).toArray
  let mut seenCmd := false
  for ln in lines do
    if !seenCmd then
      seenCmd := isCmd ln
      continue
    cfgEntries := cfgEntries.push (ln, false)
  for (entry, strict) in cfgEntries do
    let s := entry.trimAscii.toString
    match s.splitOn "=" with
    | key :: rest =>
      if rest.isEmpty then continue
      let val := "=".intercalate rest |>.trimAscii.toString
      match key.trimAscii.toString with
      | "BENCH_ENVS" => envsVal := some val
      | "BENCH_CONSTANTS" => constantsVal := some val
      | "BENCH_PROVE" | "BENCH_COMPRESS" =>
        throw "use `!benchmark ixvm execute|prove|compress` to select stages"
      | k =>
        if ["RUST_LOG", "RUSTFLAGS", "IX_COMPILE_DEMOTE"].contains k then
          passthrough := passthrough.push s!"{k}={val}"
        else if strict then
          throw s!"unknown config key `{k}` in the \
            benchmark command (expected BENCH_ENVS / BENCH_CONSTANTS, \
            or passthrough: RUST_LOG, RUSTFLAGS, IX_COMPILE_DEMOTE)"
    | [] => continue

  -- With neither key set, the default selection is every shared constant
  -- and the InitStd env row, or only `Nat.add_comm` when ixvm proves: CPU
  -- proving of the larger constants outlasts the job timeout. Setting one
  -- key selects only what it names.
  let neither := envsVal.isNone && constantsVal.isNone
  let proving := ixvmMode != .execute
  let envsSel := envsVal.getD (if neither && !proving then "InitStd" else "none")
  let constantsSel := constantsVal.getD
    (if !neither then "none" else if proving then "Nat.add_comm" else "all")

  -- BENCH_ENVS selects env rows: `all`, `none`, or registry env names
  -- (case-insensitive).
  let registryEnvs := Ix.Cli.BenchCmd.envSpecs.map (·.name)
  let mut envRows : Array String := #[]
  match envsSel.toLower with
  | "all" => envRows := registryEnvs.toArray
  | "none" => pure ()
  | _ =>
    for tok in envsSel.splitOn "," do
      let tok := tok.trimAscii.toString
      match Ix.Cli.BenchCmd.findEnv tok with
      | some e =>
        if !envRows.contains e.name then envRows := envRows.push e.name
      | none =>
        throw s!"unknown env `{tok}` in BENCH_ENVS \
          (expected all, none, or a registry env: {", ".intercalate registryEnvs})"

  -- BENCH_CONSTANTS selects constant rows: `all` (the default), `none`,
  -- or names. A shared constant runs in its own env; any other name needs
  -- BENCH_ENVS to name exactly one env, where it then runs.
  let mut constantRows : Array (String × String) := #[]
  match constantsSel.toLower with
  | "all" => constantRows := Ix.BenchConstants.benchConstants.map fun c => (c.name, c.env)
  | "none" => pure ()
  | _ =>
    for n in Ix.Cli.ConstsFile.parseCommaList constantsSel do
      match Ix.BenchConstants.benchConstants.find? (·.name == n) with
      | some c => constantRows := constantRows.push (n, c.env)
      | none =>
        if envRows.size != 1 then
          throw s!"BENCH_CONSTANTS: `{n}` is not a shared \
            benchmark constant; name the env it lives in with a single-env \
            BENCH_ENVS"
        constantRows := constantRows.push (n, envRows[0]!)

  if ixvmMode != .execute && constantRows.isEmpty then
    throw s!"ixvm {ixvmMode.name} requires at least one constant row; env rows are execution-only"

  -- One cell per (backend, env) with anything selected: the env's
  -- constant rows (on a backend with constant rows) and its env row.
  let mut entries : Array Json := #[]
  let mut allEnvs : Array String := #[]
  for b in backends do
    for e in registryEnvs do
      let cs := if b.hasConstants
        then (constantRows.filter (·.2 == e)).map (·.1) else #[]
      let envRow := envRows.contains e
      if cs.isEmpty && !envRow then continue
      if !allEnvs.contains e then allEnvs := allEnvs.push e
      entries := entries.push <| Json.mkObj
        [("backend", Json.str b.name), ("env", Json.str e),
         ("mode", Json.str (if b.name == "ixvm" && !cs.isEmpty then ixvmMode.name else "execute")),
         ("constants", Json.str (if cs.isEmpty then "none" else ",".intercalate cs.toList)),
         ("env-row", Json.str (if envRow then "1" else "0")),
         ("label", Json.str s!"{b.name}-{e}")]
  if entries.isEmpty then
    throw "the command selects no rows: BENCH_CONSTANTS and \
      BENCH_ENVS select nothing the requested backends measure"
  -- Registry order for the compile stage's matrix.
  allEnvs := registryEnvs.toArray.filter allEnvs.contains

  let names := " ".intercalate (backends.map (·.name)).toList
  let mut summary := s!"backends `{names}` · constants `{constantsSel}` · \
    env rows `{if envRows.isEmpty then "none" else ",".intercalate envRows.toList}`"
  for b in skipped do
    summary := summary ++
      s!" · skipped `{b.name}` ({b.disabled.getD "disabled in the registry"})"
  if backends.any (·.name == "ixvm") then
    summary := summary ++ s!" · ixvm `{ixvmMode.name}`"
  if ixvmMode == .compress then summary := summary ++ " · stages `execute+prove+compress`"
  else if ixvmMode == .prove then summary := summary ++ " · stages `execute+prove`"
  if fresh then
    summary := summary ++ " · baseline `fresh` (benchmark products rebuilt, bencher bypassed)"
  if !passthrough.isEmpty then
    summary := summary ++ " · env: `" ++ " ".intercalate passthrough.toList ++ "`"

  return { matrix := entries, envs := allEnvs, summary, passthrough, fresh }

def runParseCmd (p : Cli.Parsed) : IO UInt32 := do
  let body ← match p.flag? "comment" with
    | some f => pure (f.as! String)
    | none => pure ((← IO.getEnv "COMMENT_BODY").getD "")
  let parsed ← match parseCommand body with
    | .ok parsed => pure parsed
    | .error message => return ← parseError message
  -- `envs` drives the workflow's compile stage: every requested env is
  -- compiled exactly once — the `.ixe` artifact the prover runs restore,
  -- AND the measured row the compile run reuses as its PR side instead
  -- of compiling a second time.
  if let some outPath := ← IO.getEnv "GITHUB_OUTPUT" then
    let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
    h.putStr <| s!"matrix={(Json.arr parsed.matrix).compress}\n"
      ++ s!"envs={(Json.arr (parsed.envs.map Json.str)).compress}\n"
      ++ s!"fresh={if parsed.fresh then 1 else 0}\n"
      ++ s!"config-summary={parsed.summary}\n"
      ++ "passthrough-env<<PTENV\n"
      ++ "\n".intercalate parsed.passthrough.toList
      ++ (if parsed.passthrough.isEmpty then "" else "\n") ++ "PTENV\n"
    h.flush
  IO.println parsed.summary
  IO.println (Json.arr parsed.matrix).pretty
  return 0

end Ix.Cli.BenchReport

open Ix.Cli.BenchReport in
def benchCompareCmd : Cli.Cmd := `[Cli|
  "compare" VIA runCompareCmd;
  "Render a Markdown base-vs-PR table from two results rows files. Defaults to the parameter combination's local baseline pair (<BENCH_OUTPUT_DIR or .lake/benches>/<params>{.prev,}.json), so a bare rerun compares against the previous local run."

  FLAGS:
    backend       : String; "Run backend (table columns come from the registry)"
    env           : String; "Run env (default: InitStd)"
    base          : String; "Base-side rows JSON (default: the run baseline .prev.json)"
    pr            : String; "PR-side rows JSON (default: the run baseline .json)"
    threshold     : Nat;    "Flag |Δ| above this percentage (default: 3)"
    "base-source" : String; "Where the base side came from, for the title"
    "base-label"  : String; "Name the base side in headers (default: main)"
    out           : String; "Write the table here instead of stdout"
]

open Ix.Cli.BenchReport in
def benchReportCmd : Cli.Cmd := `[Cli|
  "report" VIA runReportCmd;
  "Assemble per-cell results (<dir>/<cell>/{base,pr,meta}.json) into one Markdown report with one table per backend. The link flags are optional: the PR workflow passes them to make the report a linkable comment body."

  FLAGS:
    cells      : String; "Directory of cell result directories (default: cells)"
    summary    : String; "The run's selection, for the header line"
    head       : String; "PR head commit SHA"
    "base-sha" : String; "Base commit SHA"
    threshold  : Nat;    "Mark |Δ| above this percentage (default: 3)"
    "base-label" : String; "Name the base side in the header (default: main)"
    "repo-url" : String; "Repository URL, enabling commit/logs links"
    "run-id"   : String; "Workflow run id for the logs link"
    out        : String; "Also write the report here (always printed)"
]

open Ix.Cli.BenchReport in
def benchBmfCmd : Cli.Cmd := `[Cli|
  "bmf" VIA runBmfCmd;
  "Convert benchmark results JSON to Bencher Metric Format (rows with status ≠ ok are dropped whole)"

  FLAGS:
    "in" : String; "Benchmark results JSON (default: bench.json)"
    out  : String; "BMF output path (default: bmf.json)"
]

open Ix.Cli.BenchReport in
def benchFetchMainCmd : Cli.Cmd := `[Cli|
  "fetch-main" VIA runFetchMainCmd;
  "Pull a base SHA's rows from bencher.dev. Exits 3 when bencher has no usable data yet (caller falls back to a local base run), 2 on registry drift."

  FLAGS:
    sha           : String; "Base commit SHA to fetch reports for"
    backend       : String; "Run backend (testbed from the registry)"
    rows          : String; "Only fetch these comma-separated row names (constants and envs)"
    names         : String; "Additionally read row names from a file (one per line); unions with --rows"
    "missing-out" : String; "Write the --names entries bencher lacked (the caller measures just these on the base checkout)"
    out           : String; "Rows JSON output (default: main.json)"
]

open Ix.Cli.BenchReport in
def benchCiMatrixCmd : Cli.Cmd := `[Cli|
  "matrix" VIA runMatrixCmd;
  "Emit the benchmark matrix from the registry: each enabled backend × its env set, with per-entry label and testbed"
]

open Ix.Cli.BenchReport in
def benchCiParseCmd : Cli.Cmd := `[Cli|
  "parse" VIA runParseCmd;
  "Parse a !benchmark command into the runs it schedules and write the job matrix to $GITHUB_OUTPUT (when set). Unknown tokens fall off the allowlist; --comment doubles as a local pre-flight of a comment before posting it."

  FLAGS:
    comment : String; "The command text (default: the COMMENT_BODY env var)"
]

def benchCiCmd : Cli.Cmd := `[Cli|
  ci NOOP;
  "CI adapters: the workflows' matrix and !benchmark-comment plumbing (safe to run by hand, rarely needed)"

  SUBCOMMANDS:
    benchCiParseCmd;
    benchCiMatrixCmd
]

def benchCmd : Cli.Cmd := `[Cli|
  bench NOOP;
  "Benchmark runs: run, compare, and publish locally exactly what CI runs"

  SUBCOMMANDS:
    benchRunCmd;
    benchCompareCmd;
    benchReportCmd;
    benchBmfCmd;
    benchFetchMainCmd;
    benchPlotsCmd;
    benchCiCmd
]
