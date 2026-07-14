/-
  `ix bench` reporting subcommands — everything between the results rows
  JSON (`Ix.Benchmark.Results`) and a human or bencher.dev:

    compare     two rows files → a Markdown main-vs-PR table. With no
                explicit inputs, compares the cell's local baseline against
                its previous run (`.lake/benches/<cell>.json` vs `.prev.json`), so
                a bare local rerun reports its own delta.
    report      per-cell table files → one Markdown report (the PR comment)
    bmf         rows JSON → Bencher Metric Format (status ≠ ok rows dropped)
    fetch-main  base SHA + cell → rows JSON pulled from bencher.dev (curl)
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
    tools emit (see the registry in Ix.Cli.BenchCmd). A `recursive-` metric
    formats like its inner counterpart (`recursive-peak-rss` like
    `peak-rss`, …). Unknown metrics fall through to a generic decimal
    rendering. -/
def metricKind (metric : String) : String :=
  let metric := if metric.startsWith "recursive-"
    then (metric.drop "recursive-".length).toString else metric
  if ["peak-rss", "file-size", "proof-size"].contains metric
  then "bytes"
  else if metric.startsWith "phase-" then "seconds"
  else if ["execute-time", "prove-time", "verify-time", "check-time",
           "compile-time"].contains metric then "seconds"
  else if ["fft-cost", "cycles", "steps", "max-shard-cycles",
           "throughput"].contains metric then "count"
  else if ["constants", "shards"].contains metric then "int"
  else "auto"

/-- Display label for a metric column. Keys stay the bencher measure slugs
    (renaming one would orphan its threshold/history); only the table
    rendering differs. `file-size` is the serialized `.ixe` env — bencher
    plots it as "Environment Size"; `peak-rss` reads better as plain RAM,
    in every slug that embeds it (`recursive-peak-rss` → …-peak-ram);
    `throughput` carries its unit here because the cells print bare
    magnitudes (matching `unitsFor`'s "constants / second" on bencher). -/
def metricLabel (metric : String) : String :=
  if metric == "file-size" then "env-size"
  else if metric == "throughput" then "throughput (const/s)"
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
    constants checked per second on EVERY backend (`ix_bench::throughput`
    is the one calculator; a zkVM's cycle rate stays derivable from its
    cycles / execute-time fields). -/
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

/-- The `phase-<span>` field names of one row (flat keys — same shape on
    the PR side, in local baselines, and coming back from bencher). -/
def rowPhaseKeys (rows : Json) (name : String) : Array String :=
  match (rows.getObjVal? name).toOption with
  | some (.obj kvs) => kvs.toArray.map (·.1) |>.filter (·.startsWith "phase-")
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
  /-- Render the per-constant `phase-<span>` drill-downs (opt-in:
      `BENCH_PHASES=1`) — the spans are noisy and dynamically named, so
      the default table stays at the headline measures. -/
  phases : Bool := false
  /-- What one table row is, for the header and summary: `constant` on
      the per-constant backends, `env` on compile (whose rows are
      env-keyed), `env/constant` on ooc (which mixes an env row with
      per-constant rows). -/
  rowNoun : String := "constant"

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

  let mut head := #[a.rowNoun]
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
    -- Independent tallies: a row can regress on one metric and improve
    -- on another (compile-time up, peak-ram down), and the summary must
    -- not hide either side.
    if rowRegressed then regressed := regressed + 1
    if rowImproved then improved := improved + 1
    lines := lines.push ("| " ++ " | ".intercalate cells.toList ++ " |")

  let mut out := #[a.title, ""] ++ lines ++ #[""]
  -- Typecheck failures first and loud — a constant the kernel REJECTS is a
  -- correctness signal, not a benchmark blip.
  for (n, side) in failures do
    out := out.push s!"❌ **`{n}` FAILED TO TYPECHECK on the {side} side** — \
      the kernel rejected it; see the logs."
  if !failures.isEmpty then out := out.push ""
  let plural := fun (n : Nat) (noun : String) =>
    s!"{n} {noun}{if n == 1 then "" else "s"}"
  out := out.push s!"_{plural names.size a.rowNoun} · {regressed} with \
    regressions · {improved} with improvements \
    (|Δ| > {fmtF a.threshold 1}% on any metric)._"
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
  -- Per-phase drill-down (only under `a.phases`): the main table above
  -- carries every constant's high-level row; below it, each constant with
  -- `phase-<span>` fields (aiur witness/commit/quotient breakdowns, zkVM
  -- coarse phases) gets its own collapsed mini-table
  -- (`phase | main | PR | Δ%`), opened as desired.
  let mut detail : Array String := #[]
  if a.phases then
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

def runCompareCmd (p : Cli.Parsed) : IO UInt32 := do
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let env := (p.flag? "env").map (·.as! String) |>.getD "InitStd"
  let mode := (p.flag? "mode").map (·.as! String)
    |>.getD (((Ix.Cli.BenchCmd.findBackend backend).map (·.defaultMode)).getD "execute")
  let cell := s!"{backend}-{env}-{mode}"
  -- Explicit paths win; otherwise the local baseline pair, so a bare
  -- `ix bench compare --backend …` after two runs reports the local delta.
  let benchDir ← Ix.Cli.BenchCmd.benchOutputDir
  let mainPath := (p.flag? "main").map (·.as! String)
    |>.getD s!"{benchDir}/{cell}.prev.json"
  let prPath := (p.flag? "pr").map (·.as! String)
    |>.getD s!"{benchDir}/{cell}.json"
  let metrics :=
    let flagged := (p.flag? "metric").map (·.as! (Array String)) |>.getD #[]
    if flagged.isEmpty then
      (((Ix.Cli.BenchCmd.findBackend backend).map
        (·.metricsFor mode)).getD []).toArray
    else flagged
  if metrics.isEmpty then
    p.printError s!"error: no metrics for {backend}/{mode}; pass --metric or fix backendSpecs"
    return exitUsage
  let threshold := (p.flag? "threshold").map (fun f => (f.as! Nat).toFloat)
    |>.getD 3.0
  let mainSrc := (p.flag? "main-source").map (·.as! String) |>.getD mainPath
  -- Name the mode only where a mode choice exists (aiur); a single-mode
  -- backend's `· execute` is registry plumbing, not information.
  let cellName :=
    if ((Ix.Cli.BenchCmd.findBackend backend).map (·.testbeds.length)).getD 0 > 1
    then s!"`{backend}` · `{env}` · `{mode}`"
    else s!"`{backend}` · `{env}`"
  let title := (p.flag? "title").map (·.as! String)
    |>.getD s!"### {cellName} — main from: {mainSrc}"
  let table := renderCompare {
    mainRows := ← readRows mainPath
    prRows := ← readRows prPath
    metrics, threshold, title
    phases := ((← IO.getEnv "BENCH_PHASES").getD "0") == "1"
    rowNoun :=
      if backend == "compile" then "env"
      else if backend == "ooc" then "env/constant"
      else if backend == "aiur-recursive" then "proof"
      else "constant"
  }
  match p.flag? "out" with
  | some f => IO.FS.writeFile (f.as! String) (table ++ "\n")
  | none => IO.println table
  return 0

/-! ## report -/

/-- Assemble per-cell compare tables (`<dir>/table-*.md`) into one Markdown
    report — run several cells locally, `--out table-<cell>.md` each, and
    read them as a single document. The link flags are optional garnish:
    with `--head`/`--repo-url`/`--run-id` (the PR workflow passes them) the
    header links the commit and a logs footer is appended. -/
def runReportCmd (p : Cli.Parsed) : IO UInt32 := do
  let tablesDir := (p.flag? "tables").map (·.as! String) |>.getD "tables"
  let head := (p.flag? "head").map (·.as! String) |>.getD ""
  let repoUrl := (p.flag? "repo-url").map (·.as! String) |>.getD ""
  let runId := (p.flag? "run-id").map (·.as! String) |>.getD ""
  let summary := (p.flag? "summary").map (·.as! String) |>.getD ""
  let commit := if head.isEmpty then ""
    else if repoUrl.isEmpty then s!" — main vs `{head.take 7}`"
    else s!" — main vs [`{head.take 7}`]({repoUrl}/commit/{head})"
  let mut parts := #[s!"## `!benchmark`{commit}", "", summary, ""]
  let entries := (← System.FilePath.readDir tablesDir).map (·.path.toString)
  let tables := (entries.filter fun p =>
    (p.splitOn "/").getLast!.startsWith "table-" && p.endsWith ".md").qsort (· < ·)
  if tables.isEmpty then
    parts := parts ++ #["_No result tables were produced — see the run logs._", ""]
  else
    for t in tables do
      parts := parts ++ #[(← IO.FS.readFile t).trimAscii.toString, ""]
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
    whole — a rejected or OOM'd constant must never become a bencher data
    point. Numeric fields (`phase-<span>` included) pass through as
    measures. Nested per-shard objects (`shard-cycles: {"0": …}`) become
    per-shard BENCHMARKS (`<name>/shard-0`) sharing the parent's measure
    slugs — multiplicity belongs in bencher's benchmark dimension, not as
    one measure per shard index. -/
def toBmf (rows : Json) : Json := Id.run do
  let mut out : Array (String × Json) := #[]
  for name in rowNames rows do
    if rowStatus rows name != "ok" then continue
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
    locally; 2 = config error (unknown backend/mode) — the caller fails
    the cell loudly instead of paying the fallback forever. A PARTIAL miss
    still exits 0: `--missing-out` lists the uncovered names so the caller
    measures just those against the base checkout and merges. -/
def runFetchMainCmd (p : Cli.Parsed) : IO UInt32 := do
  let sha := (p.flag? "sha").map (·.as! String) |>.getD ""
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let mode := (p.flag? "mode").map (·.as! String) |>.getD ""
  let out := (p.flag? "out").map (·.as! String) |>.getD "main.json"
  let some testbed := (Ix.Cli.BenchCmd.findBackend backend).bind
      (·.testbedFor mode)
    | IO.println s!"fetch-main: no testbed for {backend}/{mode}"
      return exitUsage
  let wanted : Option (Array String) ← do
    let names ← Ix.Cli.ConstsFile.gather p "consts" "names"
    if (p.flag? "consts").isNone && (p.flag? "names").isNone then pure none
    else
      -- The env-keyed row (ooc whole-env, compile) isn't a Vectors.csv
      -- constant; admit it past the names filter explicitly.
      match (p.flag? "env").map (·.as! String) with
      | some env => pure (some (names.push env))
      | none => pure (some names)

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
          -- The SLUG is the source of truth: row keys are born
          -- slug-shaped (see the registry metric lists and
          -- `BenchCmd.slugify`), uploads attach to measures by it, and
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
    -- Computed against the listed names verbatim: the env-keyed row is an
    -- admit-filter, not a per-constant expectation.
    let nameSet ← Ix.Cli.ConstsFile.gather p "consts" "names"
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
  let kind := (p.flag? "kind").map (·.as! String) |>.getD "envs"
  let benched := (Ix.Cli.BenchCmd.envSpecs.filter (·.benched)).map (·.name)
  match kind with
  | "envs" =>
    IO.println (Json.arr (benched.map Json.str).toArray).compress
  | "cells" =>
    let mut cells : Array Json := #[]
    for b in Ix.Cli.BenchCmd.backendSpecs do
      if b.disabled.isSome then continue
      -- The aiur-recursive backend is env-independent (fixed toy
      -- statements, no `.ixe`): one cell, not one per env.
      let envsFor := if b.name == "aiur-recursive" then benched.take 1 else benched
      for env in envsFor do
        cells := cells.push <| Json.mkObj
          [("backend", Json.str b.name), ("env", Json.str env),
           ("mode", Json.str b.defaultMode)]
    IO.println (Json.arr cells).compress
  | other =>
    p.printError s!"error: unknown --kind '{other}' (envs | cells)"
    return exitUsage
  return 0

/-! ## parse -/

/-- The runner every CI benchmark cell measures on — a `runs-on` field for
    the workflows' job matrices, meaningless locally. -/
def ciRunner : String := "warp-ubuntu-latest-x64-32x"

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

/-- Parse a `!benchmark` command into the cells it schedules — locally a
    dry-run preview (`ix bench ci parse --comment "!benchmark aiur"` prints
    the summary and cell list), in CI the matrix generator. The text comes
    from `--comment`, else the `COMMENT_BODY` env var (how the PR workflow
    passes the comment without inline shell interpolation). When
    `$GITHUB_OUTPUT` is set, the machine outputs (matrix, flags, summary,
    passthrough env) are appended there in Actions format.

    Grammar (an unknown command-line token, or an unknown/unbenched env in
    BENCH_ENVS, rejects the command — exit 2 and a `parse-error` output):

      !benchmark ([aiur] [zisk] [sp1] [ooc] [compile] [aiur-recursive] | all)
                 [execute] [KEY=VALUE …]
      BENCH_ENVS=InitStd,Mathlib   (case-insensitive; default InitStd;
                                    compile-only requests may name any
                                    registry env, e.g. Lean or FLT)
      BENCH_FULL=1                 (full curated set, not just primary)
      BENCH_SHARD=1                (only the multi-shard target constants)
      BENCH_PHASES=1 / RUST_LOG=… / WITHOUT_VK_VERIFICATION=… /
      RUSTFLAGS=… / IX_COMPILE_EAGER=… / IX_COMPILE_DEMOTE=… /
      IX_COMPILE_WORKERS=…         (passthrough; BENCH_PHASES=1 adds the
                                    per-constant phase drill-downs to the
                                    comment; the IX_COMPILE_* knobs reach
                                    the measured `ix compile` and key its
                                    caches, so knob runs don't reuse a
                                    default run's published row)

    The KEY=VALUE config may sit on its own lines below the command (the
    comment form) or inline on the command line, whitespace-separated
    (the single-line form — a workflow_dispatch input box can't hold
    newlines). Inline keys parse strictly: an unknown key rejects the
    command, like a typo'd backend.

    The bare `execute` token flips a backend with an execute metrics entry
    to execute-only — a real switch only for aiur, whose two modes store on
    separate testbeds, so either kind of cell finds a cached baseline. -/
def runParseCmd (p : Cli.Parsed) : IO UInt32 := do
  let body ← match p.flag? "comment" with
    | some f => pure (f.as! String)
    | none => pure ((← IO.getEnv "COMMENT_BODY").getD "")
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
  let mut executeFlag := false
  for t in toks.map (·.toLower) do
    if t == "execute" then
      executeFlag := true
      continue
    let requested := if t == "all"
      then Ix.Cli.BenchCmd.backendSpecs
      else (Ix.Cli.BenchCmd.findBackend t).toList
    -- Everything after `!benchmark` on the command line must parse: a
    -- typo'd backend silently running the default would report numbers
    -- the commenter never asked for.
    if requested.isEmpty then
      return ← parseError s!"unknown token `{t}` in the benchmark command \
        (expected a backend — \
        {", ".intercalate (Ix.Cli.BenchCmd.backendSpecs.map (·.name))} — \
        or `all` / `execute`)"
    for b in requested do
      if b.disabled.isSome then
        if skipped.all (·.name != b.name) then skipped := skipped.push b
      else if backends.all (·.name != b.name) then
        backends := backends.push b
  if backends.isEmpty then
    backends := (Ix.Cli.BenchCmd.findBackend "aiur").toList.toArray

  -- KEY=VALUE config: the inline command-line tokens (strict — an
  -- unknown key rejects, same as a typo'd backend), then the lines below
  -- the command (lenient — comments contain prose, and prose contains
  -- `=`, so only recognized keys are consulted there).
  let benchedEnvNames :=
    (Ix.Cli.BenchCmd.envSpecs.filter (·.benched)).map (·.name)
  let mut envs : Array String := #[]
  let mut shard := "0"
  let mut full := "0"
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
      | "BENCH_ENVS" =>
        -- A recognized key makes intent unambiguous, so its VALUE must
        -- parse fully too (unknown bare keys stay ignored — comments
        -- contain prose, and prose contains `=`).
        for tok in val.splitOn "," do
          let tok := tok.trimAscii.toString
          match Ix.Cli.BenchCmd.findEnv tok with
          | some e =>
            -- `compile` measures any registry env (its row is env-keyed;
            -- no curated constants involved). Every other backend selects
            -- constants from Vectors.csv, which only covers the benched
            -- envs — so an unbenched env needs a compile-only request.
            if !e.benched && backends.any (·.name != "compile") then
              return ← parseError s!"env `{e.name}` is only available for a \
                compile-only `!benchmark compile` (the other backends need \
                curated constants; benched: \
                {", ".intercalate benchedEnvNames})"
            if !envs.contains e.name then envs := envs.push e.name
          | none =>
            return ← parseError s!"unknown env `{tok}` in BENCH_ENVS \
              (registry: \
              {", ".intercalate (Ix.Cli.BenchCmd.envSpecs.map (·.name))})"
      | "BENCH_SHARD" => if val == "1" then shard := "1"
      | "BENCH_FULL" => if val == "1" then full := "1"
      | k =>
        if ["BENCH_PHASES", "RUST_LOG", "WITHOUT_VK_VERIFICATION",
            "RUSTFLAGS", "IX_COMPILE_EAGER", "IX_COMPILE_DEMOTE",
            "IX_COMPILE_WORKERS"].contains k then
          passthrough := passthrough.push s!"{k}={val}"
        else if strict then
          return ← parseError s!"unknown config key `{k}` in the \
            benchmark command (expected BENCH_ENVS / BENCH_FULL / \
            BENCH_SHARD, or passthrough: BENCH_PHASES, RUST_LOG, \
            WITHOUT_VK_VERIFICATION, RUSTFLAGS, IX_COMPILE_EAGER, \
            IX_COMPILE_DEMOTE, IX_COMPILE_WORKERS)"
    | [] => continue
  if envs.isEmpty then envs := #["InitStd"]

  let modeFor := fun (b : Ix.Cli.BenchCmd.BackendSpec) =>
    if executeFlag && !(b.metricsFor "execute").isEmpty then "execute"
    else b.defaultMode
  let mut cells : Array Json := #[]
  for b in backends do
    -- The aiur-recursive backend is env-independent (fixed toy
    -- statements, no `.ixe`): one cell no matter how many envs BENCH_ENVS
    -- lists. The env kept is the first requested one, so the cell's `.ixe`
    -- restore (an unconditional workflow step) still finds a compiled
    -- artifact.
    let cellEnvs := if b.name == "aiur-recursive" then envs.take 1 else envs
    for e in cellEnvs do
      cells := cells.push <| Json.mkObj
        [("backend", Json.str b.name), ("env", Json.str e),
         ("mode", Json.str (modeFor b)),
         ("runner", Json.str ciRunner),
         ("label", Json.str s!"{b.name}-{e}-{modeFor b}")]

  -- Annotate the mode only where a mode CHOICE exists (aiur's
  -- execute/prove); `ooc=execute` for a single-mode backend is noise.
  let modes := " ".intercalate
    (backends.map (fun b =>
      if b.testbeds.length > 1 then s!"{b.name}={modeFor b}" else b.name)).toList
  let mut summary := s!"backends: `{modes}` · envs: `{",".intercalate envs.toList}` · \
    set: `{if full == "1" then "full" else "primary"}` · shard: `{shard}`"
  for b in skipped do
    summary := summary ++
      s!" · skipped `{b.name}` ({b.disabled.getD "disabled in the registry"})"
  if !passthrough.isEmpty then
    summary := summary ++ " · env: `" ++ " ".intercalate passthrough.toList ++ "`"

  -- `envs` drives the workflow's compile stage: every requested env is
  -- compiled exactly once — the `.ixe` artifact the prover cells restore,
  -- AND the measured row the compile cell reuses as its PR side instead
  -- of compiling a second time.
  if let some outPath := ← IO.getEnv "GITHUB_OUTPUT" then
    let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
    h.putStr <| s!"matrix={(Json.arr cells).compress}\n"
      ++ s!"envs={(Json.arr (envs.map Json.str)).compress}\n"
      ++ s!"shard={shard}\nfull={full}\n"
      ++ s!"config-summary={summary}\n"
      ++ "passthrough-env<<PTENV\n"
      ++ "\n".intercalate passthrough.toList
      ++ (if passthrough.isEmpty then "" else "\n") ++ "PTENV\n"
    h.flush
  IO.println summary
  IO.println (Json.arr cells).pretty
  return 0

end Ix.Cli.BenchReport

open Ix.Cli.BenchReport in
def benchCompareCmd : Cli.Cmd := `[Cli|
  "compare" VIA runCompareCmd;
  "Render a Markdown main-vs-PR table from two results rows files. Defaults to the cell's local baseline pair (<BENCH_OUTPUT_DIR or .lake/benches>/<cell>{.prev,}.json), so a bare rerun compares against the previous local run."

  FLAGS:
    backend       : String; "Cell backend (metrics come from the registry)"
    env           : String; "Cell env (default: InitStd)"
    mode          : String; "Cell mode (default: the backend's default_mode)"
    main          : String; "Main-side rows JSON (default: the cell baseline .prev.json)"
    pr            : String; "PR-side rows JSON (default: the cell baseline .json)"
    metric        : Array String; "Metric column(s), overriding the registry"
    threshold     : Nat;    "Flag |Δ| above this percentage (default: 3)"
    title         : String; "Table title (default: derived from the cell)"
    "main-source" : String; "Where the main side came from, for the title"
    out           : String; "Write the table here instead of stdout"
]

open Ix.Cli.BenchReport in
def benchReportCmd : Cli.Cmd := `[Cli|
  "report" VIA runReportCmd;
  "Assemble per-cell compare tables (<dir>/table-*.md) into one Markdown report. The link flags are optional: the PR workflow passes them to make the report a linkable comment body."

  FLAGS:
    tables     : String; "Directory of table-*.md files (default: tables)"
    summary    : String; "Summary line for the header"
    head       : String; "Commit SHA to title the report with"
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
    backend       : String; "Cell backend (testbed from the registry)"
    env           : String; "Cell env — admits the env-keyed row past --names"
    mode          : String; "Cell mode"
    consts        : String; "Only fetch these comma-separated benchmark names"
    names         : String; "Additionally read names from a file (one per line); unions with --consts"
    "missing-out" : String; "Write the --names entries bencher lacked (the caller measures just these on the base checkout)"
    out           : String; "Rows JSON output (default: main.json)"
]

open Ix.Cli.BenchReport in
def benchCiMatrixCmd : Cli.Cmd := `[Cli|
  "matrix" VIA runMatrixCmd;
  "Emit GitHub Actions matrix JSON from the registry (--kind envs | cells)"

  FLAGS:
    kind   : String; "envs = benched env names; cells = enabled backends × benched envs"
]

open Ix.Cli.BenchReport in
def benchCiParseCmd : Cli.Cmd := `[Cli|
  "parse" VIA runParseCmd;
  "Parse a !benchmark command into the cells it schedules and write the job matrix to $GITHUB_OUTPUT (when set). Unknown tokens fall off the allowlist; --comment doubles as a local pre-flight of a comment before posting it."

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
  "Benchmark cells: run, compare, and publish locally exactly what CI runs"

  SUBCOMMANDS:
    benchRunCmd;
    benchShardCmd;
    benchCompareCmd;
    benchReportCmd;
    benchBmfCmd;
    benchFetchMainCmd;
    benchPlotsCmd;
    benchCiCmd
]
