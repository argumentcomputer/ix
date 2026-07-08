/-
  `ix bench` reporting subcommands — everything between the results rows
  JSON (`Ix.Benchmark.Results`) and a human or bencher.dev:

    compare     two rows files → a Markdown main-vs-PR table. With no
                explicit inputs, compares the cell's local baseline against
                its previous run (`.bench/<cell>.json` vs `.prev.json`), so
                a bare local rerun reports its own delta.
    comment     per-cell table files → the final PR comment body
    bmf         rows JSON → Bencher Metric Format (status ≠ ok rows dropped)
    fetch-main  base SHA + cell → rows JSON pulled from bencher.dev (curl)
    matrix      bench-config.json → GitHub Actions job-matrix JSON

  CI and local runs share this surface: the PR comment table and the local
  terminal table are the same renderer.
-/
module
public import Cli
public import Lean.Data.Json
public import Ix.Benchmark.Results
public import Ix.Cli.BenchCmd

public section

open Lean (Json)
open Ix.Benchmark.Results

namespace Ix.Cli.BenchReport

/-! ## Metric formatting -/

/-- Per-metric formatting kind. Metric names are the results-JSON keys the
    tools emit (see bench-config.json). Unknown metrics fall through to a
    generic decimal rendering. -/
def metricKind (metric : String) : String :=
  if ["peak-rss", "file-size", "proof-size"].contains metric
  then "bytes"
  else if metric.startsWith "phase:" then "seconds"
  else if ["execute-time", "prove-time", "verify-time", "check-time",
           "compile-time"].contains metric then "seconds"
  else if ["fft-cost", "cycles", "steps", "max-shard-cycles",
           "throughput"].contains metric then "count"
  else if ["constants", "shards"].contains metric then "int"
  else "auto"

/-- Display label for a metric column. Keys stay the bencher measure slugs
    (renaming one would orphan its threshold/history); only the table
    rendering differs. `file-size` is the serialized `.ixe` env — bencher
    plots it as "Environment Size"; `peak-rss` reads better as plain RAM. -/
def metricLabel (metric : String) : String :=
  if metric == "file-size" then "env-size"
  else if metric == "peak-rss" then "peak-ram"
  else metric

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
    lower-is-better (times, RAM, cycles, sizes). `throughput` is reused
    across backends with different units (consts/s on most; cycles/s on the
    zkVM hosts) — testbeds keep the series separate, and within any one
    table the unit is uniform. -/
def higherIsBetter (metric : String) : Bool := metric == "throughput"

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

/-- The `phase:<span>` field names of one row (flat keys — same shape on
    the PR side, in local baselines, and coming back from bencher). -/
def rowPhaseKeys (rows : Json) (name : String) : Array String :=
  match (rows.getObjVal? name).toOption with
  | some (.obj kvs) => kvs.toArray.map (·.1) |>.filter (·.startsWith "phase:")
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

structure CompareArgs where
  mainRows : Json
  prRows : Json
  metrics : Array String
  threshold : Float
  title : String

def renderCompare (a : CompareArgs) : String := Id.run do
  let names := (rowNames a.mainRows ++ rowNames a.prRows).foldl
    (fun acc n => if acc.contains n then acc else acc.push n) #[]
  if names.isEmpty then
    return a.title ++ "\n\n_No results were produced (every constant failed, \
      timed out, or was dropped). See the workflow logs._"
  -- Sort by the primary metric, largest first (n/a rows last).
  let primary := a.metrics[0]?.getD ""
  let key := fun n => (rowNum a.prRows n primary).orElse
    fun _ => rowNum a.mainRows n primary
  let names := names.qsort fun x y =>
    match key x, key y with
    | some vx, some vy => vx > vy
    | some _, none => true
    | none, some _ => false
    | none, none => x < y

  let mut head := #["constant"]
  for m in a.metrics do
    head := head ++ #[s!"{metricLabel m} (main)", s!"{metricLabel m} (PR)", "Δ%"]
  let mut lines := #[
    "| " ++ " | ".intercalate head.toList ++ " |",
    "|" ++ "|".intercalate (head.toList.map fun _ => "---") ++ "|"]

  let mut failures : Array (String × String) := #[]
  let mut regressed := 0
  let mut improved := 0
  for n in names do
    let mainStatus := rowStatus a.mainRows n
    let prStatus := rowStatus a.prRows n
    if mainStatus == "rejected" then failures := failures.push (n, "main")
    if prStatus == "rejected" then failures := failures.push (n, "PR")
    let mut rowRegressed := false
    let mut rowImproved := false
    let mut cells := #[s!"`{n}`"]
    for m in a.metrics do
      let mv := rowNum a.mainRows n m
      let pv := rowNum a.prRows n m
      -- An OOM row may still carry real partial measurements; render those,
      -- and OOM only for the metrics the kill prevented. A REJECTED row is
      -- spelled out — the constant was rejected, not benchmarked.
      let renderSide := fun (status : String) (v : Option Float) =>
        if status == "rejected" then "❌ failed typecheck"
        else if status == "oom" && v.isNone then "OOM"
        else human v m
      let mut delta := "n/a"
      if let (some mvv, some pvv) := (mv, pv) then
        if mvv != 0.0 then
          let dp := (pvv - mvv) / mvv * 100.0
          delta := (if dp >= 0.0 then "+" else "") ++ fmtF dp 1 ++ "%"
          -- Ratio only when it adds signal beyond the percentage.
          if let some (f, word) := ratio mvv pvv m then
            if f >= 1.05 then delta := delta ++ s!" ({fmtF f 2}× {word})"
          let bad := badness dp m
          if bad > a.threshold then
            delta := delta ++ " ⚠️"; rowRegressed := true
          else if bad < -a.threshold then
            delta := delta ++ " 🟢"; rowImproved := true
      cells := cells ++ #[renderSide mainStatus mv, renderSide prStatus pv, delta]
    if rowRegressed then regressed := regressed + 1
    else if rowImproved then improved := improved + 1
    lines := lines.push ("| " ++ " | ".intercalate cells.toList ++ " |")

  let mut out := #[a.title, ""] ++ lines ++ #[""]
  -- Typecheck failures first and loud — a constant the kernel REJECTS is a
  -- correctness signal, not a benchmark blip.
  for (n, side) in failures do
    out := out.push s!"❌ **`{n}` FAILED TO TYPECHECK on the {side} side** — \
      the kernel rejected it; see the logs."
  if !failures.isEmpty then out := out.push ""
  out := out.push s!"_{names.size} constants · {regressed} regressed · \
    {improved} improved (|Δ| > {fmtF a.threshold 1}% on any metric)._"
  -- One side empty while the other measured is almost always a broken side
  -- (e.g. the base-run fallback hit a base binary that predates a flag),
  -- not a real all-regressed/all-new comparison — flag it briefly instead
  -- of leaving a silent all-n/a column; the workflow logs carry the why.
  if (rowNames a.mainRows).isEmpty then
    out := out.push "" |>.push
      "_⚠️ no main-side results (base run failed — see the workflow logs)._"
  else if (rowNames a.prRows).isEmpty then
    out := out.push "" |>.push
      "_⚠️ no PR-side results (see the workflow logs)._"
  -- Per-phase drill-down: the main table above carries every constant's
  -- high-level row; below it, each constant with `phase:<span>` fields
  -- (aiur witness/commit/quotient breakdowns, zkVM coarse phases) gets its
  -- own collapsed mini-table (`phase | main | PR | Δ%`), opened as
  -- desired.
  let mut detail : Array String := #[]
  for n in names do
    let keys := (rowPhaseKeys a.mainRows n ++ rowPhaseKeys a.prRows n).foldl
      (fun acc k => if acc.contains k then acc else acc.push k) #[]
    if keys.isEmpty then continue
    detail := detail.push "" |>.push "<details>"
      |>.push s!"<summary><code>{n}</code></summary>" |>.push ""
      |>.push "| phase | main | PR | Δ% |" |>.push "|---|---|---|---|"
    for k in keys.qsort (· < ·) do
      let mv := rowNum a.mainRows n k
      let pv := rowNum a.prRows n k
      let delta := match mv, pv with
        | some m, some p =>
          if m != 0.0 then
            let dp := (p - m) / m * 100.0
            (if dp >= 0.0 then "+" else "") ++ fmtF dp 1 ++ "%"
          else "n/a"
        | _, _ => "n/a"
      detail := detail.push
        s!"| `{k.drop 6}` | {human mv k} | {human pv k} | {delta} |"
    detail := detail.push "" |>.push "</details>"
  if !detail.isEmpty then
    out := (out.push "" |>.push "**per-phase drill-down**") ++ detail
  return "\n".intercalate out.toList

def metricsFor (cfg : Json) (backend mode : String) : Array String :=
  ((cfg.getObjVal? "backends").toOption.bind fun bs =>
    (bs.getObjVal? backend).toOption.bind fun b =>
    (b.getObjVal? "metrics").toOption.bind fun ms =>
    (ms.getObjVal? mode).toOption.bind fun arr =>
      arr.getArr?.toOption.map fun a =>
        a.filterMap (·.getStr?.toOption))
  |>.getD #[]

def runCompareCmd (p : Cli.Parsed) : IO UInt32 := do
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let env := (p.flag? "env").map (·.as! String) |>.getD "InitStd"
  let cfg ← Ix.Cli.BenchCmd.loadConfig <| (p.flag? "config").map (·.as! String)
    |>.getD "Benchmarks/bench-config.json"
  let mode := (p.flag? "mode").map (·.as! String) |>.getD <|
    ((cfg.getObjVal? "backends").toOption.bind fun bs =>
      (bs.getObjVal? backend).toOption.bind fun b =>
      (b.getObjVal? "default_mode").toOption.bind (·.getStr?.toOption))
    |>.getD "execute"
  let cell := s!"{backend}-{env}-{mode}"
  -- Explicit paths win; otherwise the local baseline pair, so a bare
  -- `ix bench compare --backend …` after two runs reports the local delta.
  let mainPath := (p.flag? "main").map (·.as! String)
    |>.getD s!".bench/{cell}.prev.json"
  let prPath := (p.flag? "pr").map (·.as! String)
    |>.getD s!".bench/{cell}.json"
  let metrics :=
    let flagged := (p.flag? "metric").map (·.as! (Array String)) |>.getD #[]
    if flagged.isEmpty then metricsFor cfg backend mode else flagged
  if metrics.isEmpty then
    p.printError s!"error: no metrics for {backend}/{mode}; pass --metric or fix bench-config"
    return exitUsage
  let threshold := (p.flag? "threshold").map (fun f => (f.as! Nat).toFloat)
    |>.getD 3.0
  let mainSrc := (p.flag? "main-source").map (·.as! String) |>.getD mainPath
  let title := (p.flag? "title").map (·.as! String)
    |>.getD s!"### `{backend}` · `{env}` · `{mode}` — main from: {mainSrc}"
  let table := renderCompare {
    mainRows := ← readRows mainPath
    prRows := ← readRows prPath
    metrics, threshold, title
  }
  match p.flag? "out" with
  | some f => IO.FS.writeFile (f.as! String) (table ++ "\n")
  | none => IO.println table
  return 0

/-! ## comment -/

def runCommentCmd (p : Cli.Parsed) : IO UInt32 := do
  let tablesDir := (p.flag? "tables").map (·.as! String) |>.getD "tables"
  let head := (p.flag? "head").map (·.as! String) |>.getD ""
  let repoUrl := (p.flag? "repo-url").map (·.as! String) |>.getD ""
  let runId := (p.flag? "run-id").map (·.as! String) |>.getD ""
  let summary := (p.flag? "summary").map (·.as! String) |>.getD ""
  let out := (p.flag? "out").map (·.as! String) |>.getD "comment-body.md"
  let commit := s!"[`{head.take 7}`]({repoUrl}/commit/{head})"
  let mut parts := #[s!"## `!benchmark` — main vs {commit}", "", summary, ""]
  let entries := (← System.FilePath.readDir tablesDir).map (·.path.toString)
  let tables := (entries.filter fun p =>
    (p.splitOn "/").getLast!.startsWith "table-" && p.endsWith ".md").qsort (· < ·)
  if tables.isEmpty then
    parts := parts ++ #["_No result tables were produced — see the workflow logs._", ""]
  else
    for t in tables do
      parts := parts ++ #[(← IO.FS.readFile t).trimAscii.toString, ""]
  parts := parts.push s!"[Workflow logs]({repoUrl}/actions/runs/{runId})"
  IO.FS.writeFile out ("\n".intercalate parts.toList ++ "\n")
  IO.println (← IO.FS.readFile out)
  return 0

/-! ## bmf -/

/-- Rows JSON → Bencher Metric Format. Rows with `status ≠ ok` are dropped
    whole — a rejected or OOM'd constant must never become a bencher data
    point. Nested objects (`phases`, `shard-cycles`, …) flatten to
    `<prefix>:<sub>` measures; `phases` uses the `phase:` prefix. -/
def toBmf (rows : Json) : Json := Id.run do
  let mut out : Array (String × Json) := #[]
  for name in rowNames rows do
    if rowStatus rows name != "ok" then continue
    let some row := (rows.getObjVal? name).toOption | continue
    let mut measures : Array (String × Json) := #[]
    match row with
    | .obj kvs =>
      for (k, v) in kvs.toArray do
        if k == "status" then continue
        match v with
        | .num _ => measures := measures.push (k, Json.mkObj [("value", v)])
        | .obj sub =>
          let prefixKey := if k == "phases" then "phase" else k
          for (subK, subV) in sub.toArray do
            if let .num _ := subV then
              measures := measures.push
                (s!"{prefixKey}:{subK}", Json.mkObj [("value", subV)])
        | _ => pure ()
    | _ => pure ()
    if !measures.isEmpty then
      out := out.push (name, Json.mkObj measures.toList)
  return Json.mkObj out.toList

def runBmfCmd (p : Cli.Parsed) : IO UInt32 := do
  let inPath := (p.flag? "in").map (·.as! String) |>.getD "bench.json"
  let outPath := (p.flag? "out").map (·.as! String) |>.getD "bmf.json"
  let bmf := toBmf (← readRows inPath)
  IO.FS.writeFile outPath bmf.pretty
  IO.println s!"bmf: {(rowNames bmf).size} benchmark(s) → {outPath}"
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
    locally; 2 = config error (unknown backend/mode) — the caller fails
    the cell loudly instead of paying the fallback forever. A PARTIAL miss
    still exits 0: `--missing-out` lists the uncovered names so the caller
    measures just those against the base checkout and merges. -/
def runFetchMainCmd (p : Cli.Parsed) : IO UInt32 := do
  let sha := (p.flag? "sha").map (·.as! String) |>.getD ""
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let cfg ← Ix.Cli.BenchCmd.loadConfig <| (p.flag? "config").map (·.as! String)
    |>.getD "Benchmarks/bench-config.json"
  let mode := (p.flag? "mode").map (·.as! String) |>.getD ""
  let out := (p.flag? "out").map (·.as! String) |>.getD "main.json"
  -- `testbed` is a string, or an object keyed by mode when a backend runs
  -- one bench-main cell per mode (aiur): shared measure names like
  -- `peak-rss` mean different phases per mode, so each mode stores on its
  -- own testbed.
  let testbed :=
    ((cfg.getObjVal? "backends").toOption.bind fun bs =>
      (bs.getObjVal? backend).toOption.bind fun b =>
        if (metricsFor cfg backend mode).isEmpty then none
        else match (b.getObjVal? "testbed").toOption with
          | some (.str s) => some s
          | some t@(.obj _) =>
            (t.getObjVal? mode).toOption.bind (·.getStr?.toOption)
          | _ => none)
  let some testbed := testbed
    | IO.println s!"fetch-main: no testbed for {backend}/{mode}"
      return exitUsage
  let wanted : Option (Array String) ← match p.flag? "names" with
    | some f => do
      let names ← Ix.Cli.ConstsFile.read (f.as! String)
      -- The env-keyed row (ooc whole-env, compile) isn't a Vectors.csv
      -- constant; admit it past the names filter explicitly.
      match (p.flag? "env").map (·.as! String) with
      | some env => pure (some (names.push env))
      | none => pure (some names)
    | none => pure none

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
    IO.println s!"fetch-main: no reports for {backend}/{mode} @ {sha.take 8}"
    return exitRejected

  let mut rows : Array (String × Json) := #[]
  let mut seen : Array String := #[]
  for r in atSha do
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
          let mName := (m.getObjVal? "measure").toOption.bind fun x =>
            (x.getObjVal? "name").toOption.bind (·.getStr?.toOption)
          let mVal := (m.getObjVal? "metric").toOption.bind fun x =>
            (x.getObjVal? "value").toOption
          if let (some mn, some mv) := (mName, mVal) then
            metrics := metrics.push (mn, mv)
        if metrics.size > 1 then
          seen := seen.push name
          rows := rows.push (name, Json.mkObj metrics.toList)
  if rows.isEmpty then
    IO.println "fetch-main: reports found but no matching benchmarks in --names"
    return exitRejected
  if let some missingOut := (p.flag? "missing-out").map (·.as! String) then
    -- Computed against the names file verbatim: the env-keyed row is an
    -- admit-filter, not a per-constant expectation.
    let nameSet ← match p.flag? "names" with
      | some f => Ix.Cli.ConstsFile.read (f.as! String)
      | none => pure #[]
    let missing := nameSet.filter fun n => !seen.contains n
    IO.FS.writeFile missingOut
      ("\n".intercalate missing.toList ++ (if missing.isEmpty then "" else "\n"))
    if !missing.isEmpty then
      IO.println s!"fetch-main: {missing.size} name(s) not on bencher @ \
        {sha.take 8} (base run will measure): {", ".intercalate missing.toList}"
  IO.FS.writeFile out (Json.mkObj rows.toList).compress
  IO.println s!"fetch-main: {rows.size} constant(s) from bencher for {backend}/{mode}"
  return 0

/-! ## matrix -/

/-- Emit GitHub Actions matrix JSON from the registry, so workflow matrices
    are generated instead of hand-copied. `--kind envs` lists the benched
    env names; `--kind cells` fans enabled backends × benched envs. -/
def runMatrixCmd (p : Cli.Parsed) : IO UInt32 := do
  let cfg ← Ix.Cli.BenchCmd.loadConfig <| (p.flag? "config").map (·.as! String)
    |>.getD "Benchmarks/bench-config.json"
  let kind := (p.flag? "kind").map (·.as! String) |>.getD "envs"
  let envs := (cfg.getObjVal? "envs").toOption.getD (Json.mkObj [])
  let benched : Array String := Id.run do
    let mut out := #[]
    for key in rowNames envs do
      let e := (envs.getObjVal? key).toOption.getD (Json.mkObj [])
      if (e.getObjVal? "benched").toOption == some (Json.bool true) then
        out := out.push key
    return out
  match kind with
  | "envs" =>
    IO.println (Json.arr (benched.map Json.str)).compress
  | "cells" =>
    let backends := (cfg.getObjVal? "backends").toOption.getD (Json.mkObj [])
    let mut cells : Array Json := #[]
    for b in rowNames backends do
      let bc := (backends.getObjVal? b).toOption.getD (Json.mkObj [])
      if (bc.getObjVal? "enabled").toOption != some (Json.bool true) then
        continue
      let mode := (bc.getObjVal? "default_mode").toOption.bind (·.getStr?.toOption)
        |>.getD "execute"
      for env in benched do
        cells := cells.push <| Json.mkObj
          [("backend", Json.str b), ("env", Json.str env),
           ("mode", Json.str mode)]
    IO.println (Json.arr cells).compress
  | other =>
    p.printError s!"error: unknown --kind '{other}' (envs | cells)"
    return exitUsage
  return 0

end Ix.Cli.BenchReport

open Ix.Cli.BenchReport in
def benchCompareCmd : Cli.Cmd := `[Cli|
  "compare" VIA runCompareCmd;
  "Render a Markdown main-vs-PR table from two results rows files. Defaults to the cell's local baseline pair (.bench/<cell>{.prev,}.json), so a bare rerun compares against the previous local run."

  FLAGS:
    backend       : String; "Cell backend (metrics come from bench-config.json)"
    env           : String; "Cell env (default: InitStd)"
    mode          : String; "Cell mode (default: the backend's default_mode)"
    main          : String; "Main-side rows JSON (default: .bench/<cell>.prev.json)"
    pr            : String; "PR-side rows JSON (default: .bench/<cell>.json)"
    metric        : Array String; "Metric column(s), overriding bench-config"
    threshold     : Nat;    "Flag |Δ| above this percentage (default: 3)"
    title         : String; "Table title (default: derived from the cell)"
    "main-source" : String; "Where the main side came from, for the title"
    out           : String; "Write the table here instead of stdout"
    config        : String; "Registry path (default: Benchmarks/bench-config.json)"
]

open Ix.Cli.BenchReport in
def benchCommentCmd : Cli.Cmd := `[Cli|
  "comment" VIA runCommentCmd;
  "Assemble per-cell table files (tables/table-*.md) into the final PR comment body"

  FLAGS:
    tables     : String; "Directory of table-*.md files (default: tables)"
    summary    : String; "Config summary line for the header"
    head       : String; "PR head SHA"
    "repo-url" : String; "Repository URL for links"
    "run-id"   : String; "Workflow run id for the logs link"
    out        : String; "Output path (default: comment-body.md)"
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
    backend       : String; "Cell backend (testbed from bench-config.json)"
    env           : String; "Cell env — admits the env-keyed row past --names"
    mode          : String; "Cell mode"
    names         : String; "Only fetch benchmarks named in this file"
    "missing-out" : String; "Write the --names entries bencher lacked (the caller measures just these on the base checkout)"
    out           : String; "Rows JSON output (default: main.json)"
    config        : String; "Registry path (default: Benchmarks/bench-config.json)"
]

open Ix.Cli.BenchReport in
def benchMatrixCmd : Cli.Cmd := `[Cli|
  "matrix" VIA runMatrixCmd;
  "Emit GitHub Actions matrix JSON from bench-config.json (--kind envs | cells)"

  FLAGS:
    kind   : String; "envs = benched env names; cells = enabled backends × benched envs"
    config : String; "Registry path (default: Benchmarks/bench-config.json)"
]

def benchCmd : Cli.Cmd := `[Cli|
  bench NOOP;
  "Benchmark cells: run, compare, and publish locally exactly what CI runs"

  SUBCOMMANDS:
    benchRunCmd;
    benchShardCmd;
    benchCompareCmd;
    benchCommentCmd;
    benchBmfCmd;
    benchFetchMainCmd;
    benchMatrixCmd
]
