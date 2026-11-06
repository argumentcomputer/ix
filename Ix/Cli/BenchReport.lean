/-
  `ix bench` reporting subcommands — everything between the results rows
  JSON (`Ix.Benchmark.Results`) and a human or bencher.dev:

    compare     two rows files → a Markdown base-vs-PR table. With no
                explicit inputs, compares the parameter combination's local baseline against
                its previous run (`.lake/benches/<params>.json` vs `.prev.json`), so
                a bare local rerun reports its own delta.
    report      per-combination table files → one Markdown report (the PR comment)
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
  if ["peak-rss", "file-size", "proof-size"].contains metric
  then "bytes"
  else if metric.startsWith "phase-" then "seconds"
  -- Every wall-clock measure is named `<what>-time`.
  else if metric.endsWith "-time" then "seconds"
  else if ["fft-cost", "cycles", "steps", "max-shard-cycles",
           "throughput"].contains metric then "count"
  else if ["constants", "shards"].contains metric then "int"
  else "auto"

/-- Display label for a metric column. Keys stay the bencher measure slugs
    (renaming one would orphan its threshold/history); only the table
    rendering differs. `file-size` is the serialized `.ixe` env — bencher
    plots it as "Environment Size"; `peak-rss` reads better as plain RAM;
    `throughput` carries its unit here because the runs print bare
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
    constants checked per second on EVERY backend. -/
def higherIsBetter (metric : String) : Bool :=
  metric == "throughput"

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
  /-- The table's columns, in order; the head is the row sort key. -/
  metrics : Array String
  threshold : Float
  title : String
  /-- Render the per-constant `phase-<span>` drill-downs (opt-in:
      `BENCH_PHASES=1`) — the spans are noisy and dynamically named, so
      the default table stays at the headline measures. -/
  phases : Bool := false
  /-- What one table row is, for the header and summary: `constant` or
      `env`. -/
  rowNoun : String := "constant"
  /-- What to call the base side in headers and notes. `!benchmark`
      compares against the PR's own base branch, which is only `main` for
      an unstacked PR; a manual dispatch can name any two SHAs. -/
  baseLabel : String := "main"

def renderCompare (a : CompareArgs) : String := Id.run do
  let names := (rowNames a.mainRows ++ rowNames a.prRows).foldl
    (fun acc n => if acc.contains n then acc else acc.push n) #[]
  if names.isEmpty then
    return a.title ++ "\n\n_No results were produced (every constant failed, \
      timed out, or was dropped). See the workflow logs._"
  -- Sort by the primary metric, largest first (n/a rows last).
  let primary := (a.metrics[0]?).getD ""
  let key := fun n => (rowNum a.prRows n primary).orElse
    fun _ => rowNum a.mainRows n primary
  let names := names.qsort fun x y =>
    match key x, key y with
    | some vx, some vy => vx > vy
    | some _, none => true
    | none, some _ => false
    | none, none => x < y

  let mut failures : Array (String × String) := #[]
  for n in names do
    if rowStatus a.mainRows n == "rejected" then
      failures := failures.push (n, a.baseLabel)
    if rowStatus a.prRows n == "rejected" then failures := failures.push (n, "PR")

  let mut head := #[a.rowNoun]
  for m in a.metrics do
    head := head ++ #[s!"{metricLabel m} ({a.baseLabel})", s!"{metricLabel m} (PR)", "Δ%"]
  let mut lines := #[
    "| " ++ " | ".intercalate head.toList ++ " |",
    "|" ++ "|".intercalate (head.toList.map fun _ => "---") ++ "|"]
  let mut regressed := 0
  let mut improved := 0
  for n in names do
    let mainStatus := rowStatus a.mainRows n
    let prStatus := rowStatus a.prRows n
    let mut rowRegressed := false
    let mut rowImproved := false
    let mut cols := #[s!"`{n}`"]
    for m in a.metrics do
      let mv := rowNum a.mainRows n m
      let pv := rowNum a.prRows n m
      -- An OOM/CRASH row may still carry real partial measurements; render
      -- those, and the status only for the metrics the kill prevented. OOM
      -- is a capacity kill; CRASH is a fault in the tool (e.g. a segfault)
      -- and needs a bug hunt, not a bigger box. A REJECTED row is
      -- spelled out — the constant was rejected, not benchmarked.
      let renderSide := fun (status : String) (v : Option Float) =>
        if status == "rejected" then "❌ failed typecheck"
        else if status == "oom" && v.isNone then "OOM"
        else if status == "crash" && v.isNone then "💥 CRASH"
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
      cols := cols ++ #[renderSide mainStatus mv, renderSide prStatus pv, delta]
    -- Independent tallies: a row can regress on one metric and improve
    -- on another (compile-time up, peak-ram down), and the summary must
    -- not hide either side.
    if rowRegressed then regressed := regressed + 1
    if rowImproved then improved := improved + 1
    lines := lines.push ("| " ++ " | ".intercalate cols.toList ++ " |")

  -- Assembly order puts the scannable verdict FIRST and collapses long
  -- tables: a multi-cell PR comment reads as one verdict line per cell,
  -- with each table one click away. Typecheck failures and empty-side
  -- warnings stay visible unconditionally — a constant the kernel REJECTS
  -- is a correctness signal, not a benchmark blip.
  let mut out := #[a.title, ""]
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
      s!"_⚠️ no {a.baseLabel}-side results (base run failed — see the workflow logs)._"
  else if (rowNames a.prRows).isEmpty then
    out := out.push "" |>.push
      "_⚠️ no PR-side results (see the workflow logs)._"
  if names.size > 5 then
    out := out ++ #["",
      s!"<details><summary>comparison table ({plural names.size a.rowNoun})</summary>", ""]
      ++ lines ++ #["", "</details>"]
  else
    out := out ++ #[""] ++ lines
  -- Per-phase drill-down (only under `a.phases`): the tables above
  -- carry every constant's high-level row; below it, each constant with
  -- `phase-<span>` fields
  -- gets its own collapsed mini-table
  -- (`phase | base | PR | Δ%`), opened as desired.
  let mut detail : Array String := #[]
  if a.phases then
    for n in names do
      let keys := (rowPhaseKeys a.mainRows n ++ rowPhaseKeys a.prRows n).foldl
        (fun acc k => if acc.contains k then acc else acc.push k) #[]
      if keys.isEmpty then continue
      detail := detail.push "" |>.push "<details>"
        |>.push s!"<summary><code>{n}</code></summary>" |>.push ""
        |>.push s!"| phase | {a.baseLabel} | PR | Δ% |"
        |>.push "|---|---|---|---|"
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

/-! ## Per-constant drill-down (ixvm-ooc `--per-const` attribution CSVs) -/

/-- One entry of a `--per-const` attribution CSV: the
    aggregated measurements of one constant's (or Muts block's) check. -/
structure PerConstEntry where
  nanos : Float := 0
  cost : Float := 0
  subst : Float := 0
  whnf : Float := 0
  defEq : Float := 0
  natArith : Float := 0
  intern : Float := 0

/-- Split one CSV line whose FIRST field may be minimally quoted (names
    like `«term_,_»`); the remaining fields are plain numerics. -/
private def splitPerConstLine (line : String) : Option (String × Array String) :=
  if line.startsWith "\"" then
    -- Scan for the closing quote, un-escaping doubled quotes.
    let chars := line.toList.drop 1
    let rec go (cs : List Char) (acc : String) : Option (String × String) :=
      match cs with
      | '"' :: '"' :: rest => go rest (acc.push '"')
      | '"' :: ',' :: rest => some (acc, String.ofList rest)
      | '"' :: [] => some (acc, "")
      | c :: rest => go rest (acc.push c)
      | [] => none
    match go chars "" with
    | some (name, rest) => some (name, (rest.splitOn ",").toArray)
    | none => none
  else
    match line.splitOn "," with
    | name :: rest => some (name, rest.toArray)
    | [] => none

/-- Parse an attribution CSV into name → summed entry (structurally
    equivalent constants can share a first-registered name; summing keeps
    the join total-preserving). Column order comes from the Rust writer:
    `name,addr,consts,nanos,heartbeats,subst,whnf,def_eq,nat_arith,intern,cost`. -/
def readPerConstCsv (path : String) : IO (Std.HashMap String PerConstEntry) := do
  let mut out : Std.HashMap String PerConstEntry := {}
  let content ← IO.FS.readFile path
  for rawLine in content.splitOn "\n" do
    -- CRLF tolerance: a trailing '\r' would silently zero the last field.
    let line :=
      if rawLine.endsWith "\r" then (rawLine.dropEnd 1).toString
      else rawLine
    if line.isEmpty || line.startsWith "name," then continue
    let some (name, fs) := splitPerConstLine line | continue
    if fs.size < 10 then continue
    let num := fun (i : Nat) => (fs[i]!.toNat?.getD 0).toFloat
    let row : PerConstEntry := {
      nanos := num 2, subst := num 4, whnf := num 5, defEq := num 6
      natArith := num 7, intern := num 8, cost := num 9 }
    let acc := out.get? name |>.getD {}
    out := out.insert name {
      nanos := acc.nanos + row.nanos, cost := acc.cost + row.cost
      subst := acc.subst + row.subst, whnf := acc.whnf + row.whnf
      defEq := acc.defEq + row.defEq, natArith := acc.natArith + row.natArith
      intern := acc.intern + row.intern }
  return out

/-- One delta cell in the drill-down tables, styled like the main compare
    table: signed percent, a `(N.NN× word)` ratio annotation past 1.05×,
    and ⚠️ / 🟢 past `threshold` percent (badness-signed, so 🟢 marks
    improvements). `metric` picks the ratio wording via `metricKind`. -/
private def fmtDeltaCell (mainV prV : Float) (metric : String)
    (threshold : Float := 3.0) : String :=
  if mainV <= 0 then "n/a" else Id.run do
    let dp := (prV - mainV) / mainV * 100.0
    let mut s := (if dp >= 0 then "+" else "") ++ fmtF dp 1 ++ "%"
    if let some (f, word) := ratio mainV prV metric then
      if f >= 1.05 then s := s ++ s!" ({fmtF f 2}× {word})"
    let bad := badness dp metric
    if bad > threshold then s := s ++ " ⚠️"
    else if bad < -threshold then s := s ++ " 🟢"
    return s

private def fmtMs (nanos : Float) : String :=
  let ms := nanos / 1e6
  if ms >= 1000 then s!"{fmtF (ms / 1000) 2}s"
  else if ms >= 10 then s!"{fmtF ms 0}ms"
  else s!"{fmtF ms 1}ms"

private def fmtPct (x : Float) : String :=
  (if x >= 0 then "+" else "") ++ fmtF (x * 100) 1 ++ "%"

/-- The counter whose relative change best explains a mover — model-free
    "why" hint next to the wall-time delta. Counters with tiny volumes on
    both sides (< 20 events) are skipped as ratio noise, and a best delta
    under 5% is not worth naming. -/
private def moverDriver (m pr : PerConstEntry) : String :=
  let cands := #[
    ("subst", m.subst, pr.subst), ("whnf", m.whnf, pr.whnf),
    ("def_eq", m.defEq, pr.defEq), ("nat_arith", m.natArith, pr.natArith),
    ("intern", m.intern, pr.intern)]
  let scored := cands.filterMap fun (n, a, b) =>
    if a < 20 && b < 20 then none
    else
      let base := if a < 1 then 1.0 else a
      some (n, (b - base) / base)
  let best := scored.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some y => if x.2.abs > y.2.abs then some x else acc
  match best with
  | some (n, d) => if d.abs < 0.05 then "—" else s!"{n} {fmtPct d}"
  | none => "—"

/-- Render the top-movers drill-down from two per-constant attribution
    CSVs (`--per-const`).

    **Entry scope.** An entry is one constant's (or Muts block's) OWN
    check inside the whole-env run: dependencies are lazily ingressed and
    trusted — each checked in its own entry — but the ingress of the
    closure slice the check consults is charged to the entry (the env is
    cleared per item). Entries therefore sum to the whole-env totals with
    no double counting, and a change to a shared dependency surfaces in
    every consumer entry it affects. This is NOT the full-closure scope of
    the headline table's curated `--consts` measurements (which re-check
    the whole closure) — the same name can be
    seconds there and milliseconds here.

    Movers split into two classes with different evidence quality:

    - **cost movers** — the predicted cost moved: |Δcost| ≥ `costFloorRel`
      of the constant's base-side cost, OR ≥ `costFloorAbs` outright (so a
      big constant moving a lot of real cost at a small percentage still
      enters). Ranked by percent change — pathologies first. The op
      counters are far more stable than wall time but NOT bit-deterministic
      under parallel checking: worker→item assignment varies uids, and
      uid-keyed hash iteration order perturbs a few order-sensitive kernel
      paths. A Mathlib A/A run measured drift on 0.7% of constants,
      envelope ≈ 13% relative and 0.27e9 absolute — hence the 15% / 1e9
      defaults. (`--workers 1` runs are exactly reproducible when
      precision matters.)
    - **time-only movers** — wall time moved (≥ `floorMs` and `floorRel`)
      but cost did not. On an A/A run this is pure scheduling/cache noise;
      on an A/B it can also be allocator or locality effects a counter
      can't see. Reported second, clearly labeled. -/
def renderPerConstMovers (mainCsv prCsv : String) (baseLabel : String := "main")
    (topN : Nat := 10)
    (floorMs : Float := 10.0) (floorRel : Float := 0.03)
    (costFloorRel : Float := 0.15) (costFloorAbs : Float := 1e9) :
    IO String := do
  let main ← readPerConstCsv mainCsv
  let pr ← readPerConstCsv prCsv
  let mut behavior : Array (String × PerConstEntry × PerConstEntry × Float) := #[]
  let mut timeOnly : Array (String × PerConstEntry × PerConstEntry × Float) := #[]
  let mut sumMain := 0.0
  let mut sumPr := 0.0
  let mut sumCostMain := 0.0
  let mut sumCostPr := 0.0
  let mut removed := 0
  let mut removedNs := 0.0
  for (name, m) in main do
    sumMain := sumMain + m.nanos
    sumCostMain := sumCostMain + m.cost
    match pr.get? name with
    | some p =>
      let dc := p.cost - m.cost
      let d := p.nanos - m.nanos
      if dc.abs >= 5e7
        && (dc.abs >= costFloorRel * m.cost || dc.abs >= costFloorAbs)
      then
        -- Store the RELATIVE deltas: sections rank by percent change.
        behavior := behavior.push (name, m, p, dc / max m.cost 1.0)
      else if d.abs >= floorMs * 1e6 && d.abs >= floorRel * m.nanos then
        timeOnly := timeOnly.push (name, m, p, d / max m.nanos 1.0)
    | none => removed := removed + 1; removedNs := removedNs + m.nanos
  let mut added := 0
  let mut addedNs := 0.0
  for (name, p) in pr do
    sumPr := sumPr + p.nanos
    sumCostPr := sumCostPr + p.cost
    if !main.contains name then
      added := added + 1; addedNs := addedNs + p.nanos
  let totalDelta :=
    if sumMain > 0 then fmtPct ((sumPr - sumMain) / sumMain) else "n/a"
  let totalCostDelta :=
    if sumCostMain > 0
    then fmtPct ((sumCostPr - sumCostMain) / sumCostMain) else "n/a"
  let mut out := s!"<details><summary>per-constant drill-down — \
    Σ check {fmtMs sumMain} → {fmtMs sumPr} ({totalDelta}), \
    Σ cost {totalCostDelta}; \
    {behavior.size} cost mover(s), {timeOnly.size} time-only mover(s)"
  if added > 0 || removed > 0 then
    out := out ++ s!"; {added} added ({fmtMs addedNs}), \
      {removed} removed ({fmtMs removedNs})"
  out := out ++ "</summary>\n\n"
  out := out ++ "_Each entry is one constant's own check within the \
    whole-env run (deps ingress lazily; each dep is checked in its own \
    entry; entries sum to the env) — not the full-closure scope of the \
    headline `--consts` measurements._\n\n"
  let section_ := fun (title : String)
      (rows : Array (String × PerConstEntry × PerConstEntry × Float)) =>
    if rows.isEmpty then ""
    else Id.run do
      let mut s := s!"**{title}**\n\n\
        | constant | {baseLabel} | PR | Δtime | Δcost | driver |\n\
        |---|---|---|---|---|---|\n"
      for (name, m, p, _) in rows do
        let dcost := fmtDeltaCell m.cost p.cost "cycles"
        let dtime := fmtDeltaCell m.nanos p.nanos "check-time"
        s := s ++ s!"| `{name}` | {fmtMs m.nanos} | {fmtMs p.nanos} \
          | {dtime} | {dcost} | {moverDriver m p} |\n"
      s ++ "\n"
  let bSorted := behavior.qsort (fun a b => a.2.2.2.abs > b.2.2.2.abs)
  out := out ++ section_ "Cost regressions (counter-backed)"
    (bSorted.filter (fun a => a.2.2.2 > 0) |>.extract 0 topN)
  out := out ++ section_ "Cost improvements (counter-backed)"
    (bSorted.filter (fun a => a.2.2.2 < 0) |>.extract 0 topN)
  let tSorted := timeOnly.qsort (fun a b => a.2.2.2.abs > b.2.2.2.abs)
  out := out ++ section_
    "Time-only movers (cost flat — scheduling/locality noise)"
    (tSorted.extract 0 (min topN 5))
  return out ++ "</details>"

/-- `rows` restricted to the names `keep` admits. -/
def filterRows (rows : Json) (keep : String → Bool) : Json :=
  match rows with
  | .obj kvs => Json.mkObj (kvs.toArray.filter (keep ·.1)).toList
  | other => other

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
  let mainRows ← readRows mainPath
  let prRows ← readRows prPath
  let threshold := (p.flag? "threshold").map (fun f => (f.as! Nat).toFloat)
    |>.getD 3.0
  let mainSrc := (p.flag? "base-source").map (·.as! String) |>.getD mainPath
  let baseLabel := (p.flag? "base-label").map (·.as! String) |>.getD "main"
  let title := (p.flag? "title").map (·.as! String)
    |>.getD s!"### `{backend}` · `{env}` — {baseLabel} from: {mainSrc}"
  let phases := ((← IO.getEnv "BENCH_PHASES").getD "0") == "1"
  -- The env row and the constant rows measure different things, so each
  -- kind gets its own table with its own columns. Either side having a
  -- row of a kind renders that kind's table.
  let isEnvRow := (· == env)
  let has := fun (keep : String → Bool) =>
    (rowNames mainRows ++ rowNames prRows).any keep
  let mut tables : Array String := #[]
  if has isEnvRow then
    tables := tables.push <| renderCompare {
      mainRows := filterRows mainRows isEnvRow, prRows := filterRows prRows isEnvRow
      metrics := spec.envMetrics.toArray, threshold, title, baseLabel, phases
      rowNoun := "env" }
  if spec.hasConstants && has (!isEnvRow ·) then
    tables := tables.push <| renderCompare {
      mainRows := filterRows mainRows (!isEnvRow ·)
      prRows := filterRows prRows (!isEnvRow ·)
      metrics := spec.constantMetrics.toArray, threshold, baseLabel, phases
      title := if tables.isEmpty then title else "#### constants"
      rowNoun := "constant" }
  let mut table := if tables.isEmpty
    then renderCompare { mainRows, prRows, metrics := #[], threshold, title, baseLabel }
    else "\n\n".intercalate tables.toList
  -- Per-constant attribution drill-down: rendered whenever an
  -- attribution CSV (`--per-const`, written by the ixvm-ooc env row)
  -- sits next to BOTH results files.
  let mainAttrib := mainPath ++ ".perconst.csv"
  let prAttrib := prPath ++ ".perconst.csv"
  if (← System.FilePath.pathExists ⟨mainAttrib⟩)
    && (← System.FilePath.pathExists ⟨prAttrib⟩)
  then
    table := table ++ "\n\n" ++ (← renderPerConstMovers mainAttrib prAttrib baseLabel)
  match p.flag? "out" with
  | some f => IO.FS.writeFile (f.as! String) (table ++ "\n")
  | none => IO.println table
  return 0

/-! ## report -/

/-- Assemble per-run compare tables (`<dir>/table-*.md`) into one Markdown
    report — run several parameter combinations locally, `--out table-<params>.md` each, and
    read them as a single document. The link flags are optional garnish:
    with `--head`/`--repo-url`/`--run-id` (the PR workflow passes them) the
    header links the commit and a logs footer is appended. -/
def runReportCmd (p : Cli.Parsed) : IO UInt32 := do
  let tablesDir := (p.flag? "tables").map (·.as! String) |>.getD "tables"
  let head := (p.flag? "head").map (·.as! String) |>.getD ""
  let repoUrl := (p.flag? "repo-url").map (·.as! String) |>.getD ""
  let runId := (p.flag? "run-id").map (·.as! String) |>.getD ""
  let summary := (p.flag? "summary").map (·.as! String) |>.getD ""
  let baseLabel := (p.flag? "base-label").map (·.as! String) |>.getD "main"
  let commit := if head.isEmpty then ""
    else if repoUrl.isEmpty then s!" — {baseLabel} vs `{head.take 7}`"
    else s!" — {baseLabel} vs [`{head.take 7}`]({repoUrl}/commit/{head})"
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
    whole — a rejected, OOM'd, partial or conditional run must never become
    a bencher data point. Numeric fields (`phase-<span>` included) pass
    through as measures. Nested per-shard objects (`shard-cycles: {"0": …}`)
    become per-shard BENCHMARKS (`<name>/shard-0`) sharing the parent's
    measure slugs — multiplicity belongs in bencher's benchmark dimension,
    not as one measure per shard index. -/
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

/-- Parse a `!benchmark` command into the runs it schedules — locally a
    dry-run preview (`ix bench ci parse --comment "!benchmark ixvm-ooc"` prints
    the summary and run list), in CI the matrix generator. The text comes
    from `--comment`, else the `COMMENT_BODY` env var (how the PR workflow
    passes the comment without inline shell interpolation). When
    `$GITHUB_OUTPUT` is set, the machine outputs (matrix, flags, summary,
    passthrough env) are appended there in Actions format.

    Grammar (an unknown command-line token, or an unknown env in
    BENCH_ENVS, rejects the command — exit 2 and a `parse-error` output):

      !benchmark ([ixvm] [ixvm-ooc] [compile] [decompile] | all)
                 [fresh] [KEY=VALUE …]
      (at least one backend or `all` is required)
      BENCH_CONSTANTS=all|none|a,b (constant rows; default all. A shared
                                    constant runs in its own env; any other
                                    name needs a single-env BENCH_ENVS
                                    naming where it lives.)
      BENCH_ENVS=all|none|a,b      (env rows: case-insensitive registry
                                    envs; default InitStd)
      BENCH_PHASES=1 / RUST_LOG=… /
      RUSTFLAGS=… / IX_COMPILE_EAGER=… / IX_COMPILE_DEMOTE=… /
      IX_COMPILE_WORKERS=… / IX_DECOMPILE_KENV_CLEAR_ENTRIES=…
                                    (passthrough; BENCH_PHASES=1 adds the
                                    per-constant phase drill-downs to the
                                    comment; the IX_COMPILE_* knobs reach
                                    the measured `ix compile`, but emit the
                                    same `.ixe`; caches are SHA-keyed, so add
                                    `fresh` to remeasure a knob on one SHA)

    Each scheduled cell is (backend, env) for an env with a selected
    constant row (on a backend with constant rows) or a selected env row;
    the cell runs exactly those rows.

    The KEY=VALUE config may sit on its own lines below the command (the
    comment form) or inline on the command line, whitespace-separated
    (the single-line form — a workflow_dispatch input box can't hold
    newlines). Inline keys parse strictly: an unknown key rejects the
    command, like a typo'd backend.

    The bare `fresh` token makes every run bypass its bencher baseline and
    keeps persistent cached benchmark binaries, compiled `.ixe` files, and
    compile rows out of measured jobs. A cached head `ix` may bootstrap this
    canonical parser, but the workflow replaces the full binary bundle before
    publishing it. Both measured source trees are rebuilt, and run-scoped
    artifacts carry their products between jobs. Dependency caches remain
    enabled. The comparison prints in the comment only; PR runs never upload
    to bencher, so the canonical baseline is untouched. -/
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
  let mut freshFlag := false
  for t in toks.map (·.toLower) do
    if t == "fresh" then
      freshFlag := true
      continue
    let requested := if t == "all"
      then Ix.Cli.BenchCmd.backendSpecs.filter (·.disabled.isNone)
      else (Ix.Cli.BenchCmd.findBackend t).toList
    -- Everything after `!benchmark` on the command line must parse: a
    -- typo'd backend silently running the default would report numbers
    -- the commenter never asked for.
    if requested.isEmpty then
      return ← parseError s!"unknown token `{t}` in the benchmark command \
        (expected a backend — \
        {", ".intercalate ((Ix.Cli.BenchCmd.backendSpecs.filter
          (·.disabled.isNone)).map (·.name))} — \
        or `all` / `fresh`)"
    for b in requested do
      if b.disabled.isSome then
        if skipped.all (·.name != b.name) then skipped := skipped.push b
      else if backends.all (·.name != b.name) then
        backends := backends.push b
  if backends.isEmpty then
    if !skipped.isEmpty then
      let reasons := ", ".intercalate <| skipped.toList.map fun b =>
        s!"{b.name} ({b.disabled.getD "disabled in CI"})"
      return ← parseError s!"no requested benchmark backend is enabled in CI: {reasons}"
    return ← parseError s!"`!benchmark` needs a backend: one or more of \
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
      | k =>
        if ["BENCH_PHASES", "RUST_LOG",
            "RUSTFLAGS", "IX_COMPILE_EAGER", "IX_COMPILE_DEMOTE",
            "IX_COMPILE_WORKERS", "BENCH_TRACE_SHARDS",
            "IX_DECOMPILE_KENV_CLEAR_ENTRIES"].contains k then
          passthrough := passthrough.push s!"{k}={val}"
        else if strict then
          return ← parseError s!"unknown config key `{k}` in the \
            benchmark command (expected BENCH_ENVS / BENCH_CONSTANTS, \
            or passthrough: BENCH_PHASES, \
            RUST_LOG, RUSTFLAGS, \
            IX_COMPILE_EAGER, IX_COMPILE_DEMOTE, IX_COMPILE_WORKERS, \
            BENCH_TRACE_SHARDS, IX_DECOMPILE_KENV_CLEAR_ENTRIES)"
    | [] => continue

  -- BENCH_ENVS selects env rows: `all`, `none`, or registry env names
  -- (case-insensitive). Default: InitStd.
  let registryEnvs := Ix.Cli.BenchCmd.envSpecs.map (·.name)
  let mut envRows : Array String := #[]
  match (envsVal.getD "InitStd").toLower with
  | "all" => envRows := registryEnvs.toArray
  | "none" => pure ()
  | _ =>
    for tok in (envsVal.getD "InitStd").splitOn "," do
      let tok := tok.trimAscii.toString
      match Ix.Cli.BenchCmd.findEnv tok with
      | some e =>
        if !envRows.contains e.name then envRows := envRows.push e.name
      | none =>
        return ← parseError s!"unknown env `{tok}` in BENCH_ENVS \
          (expected all, none, or a registry env: {", ".intercalate registryEnvs})"

  -- BENCH_CONSTANTS selects constant rows: `all` (the default), `none`,
  -- or names. A shared constant runs in its own env; any other name needs
  -- BENCH_ENVS to name exactly one env, where it then runs.
  let mut constantRows : Array (String × String) := #[]
  match (constantsVal.getD "all").toLower with
  | "all" => constantRows := Ix.BenchConstants.benchConstants.map fun c => (c.name, c.env)
  | "none" => pure ()
  | _ =>
    for n in Ix.Cli.ConstsFile.parseCommaList (constantsVal.getD "") do
      match Ix.BenchConstants.benchConstants.find? (·.name == n) with
      | some c => constantRows := constantRows.push (n, c.env)
      | none =>
        if envRows.size != 1 then
          return ← parseError s!"BENCH_CONSTANTS: `{n}` is not a shared \
            benchmark constant; name the env it lives in with a single-env \
            BENCH_ENVS"
        constantRows := constantRows.push (n, envRows[0]!)

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
         ("constants", Json.str (if cs.isEmpty then "none" else ",".intercalate cs.toList)),
         ("env-row", Json.str (if envRow then "1" else "0")),
         ("label", Json.str s!"{b.name}-{e}")]
  if entries.isEmpty then
    return ← parseError "the command selects no rows: BENCH_CONSTANTS and \
      BENCH_ENVS select nothing the requested backends measure"
  -- Registry order for the compile stage's matrix.
  allEnvs := registryEnvs.toArray.filter allEnvs.contains

  let names := " ".intercalate (backends.map (·.name)).toList
  let mut summary := s!"backends: `{names}` · envs: `{",".intercalate allEnvs.toList}`"
  summary := summary ++ s!" · env rows: `{if envRows.isEmpty then "none" else ",".intercalate envRows.toList}`"
  summary := summary ++ s!" · constants: `{constantsVal.getD "all"}`"
  summary := summary ++ s!" · machine: `{← Ix.Cli.BenchCmd.benchmarkMachine}`"
  if freshFlag then
    summary := summary ++
      " · baseline: `fresh` (benchmark products rebuilt, base-SHA run, bencher bypassed)"
  for b in skipped do
    summary := summary ++
      s!" · skipped `{b.name}` ({b.disabled.getD "disabled in the registry"})"
  if !passthrough.isEmpty then
    summary := summary ++ " · env: `" ++ " ".intercalate passthrough.toList ++ "`"

  -- `envs` drives the workflow's compile stage: every requested env is
  -- compiled exactly once — the `.ixe` artifact the prover runs restore,
  -- AND the measured row the compile run reuses as its PR side instead
  -- of compiling a second time.
  if let some outPath := ← IO.getEnv "GITHUB_OUTPUT" then
    let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
    h.putStr <| s!"matrix={(Json.arr entries).compress}\n"
      ++ s!"envs={(Json.arr (allEnvs.map Json.str)).compress}\n"
      ++ s!"fresh={if freshFlag then 1 else 0}\n"
      ++ s!"config-summary={summary}\n"
      ++ "passthrough-env<<PTENV\n"
      ++ "\n".intercalate passthrough.toList
      ++ (if passthrough.isEmpty then "" else "\n") ++ "PTENV\n"
    h.flush
  IO.println summary
  IO.println (Json.arr entries).pretty
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
    title         : String; "Table title (default: derived from the run)"
    "base-source" : String; "Where the base side came from, for the title"
    "base-label"  : String; "Name the base side in headers (default: main)"
    out           : String; "Write the table here instead of stdout"
]

open Ix.Cli.BenchReport in
def benchReportCmd : Cli.Cmd := `[Cli|
  "report" VIA runReportCmd;
  "Assemble per-run compare tables (<dir>/table-*.md) into one Markdown report. The link flags are optional: the PR workflow passes them to make the report a linkable comment body."

  FLAGS:
    tables     : String; "Directory of table-*.md files (default: tables)"
    summary    : String; "Summary line for the header"
    head       : String; "Commit SHA to title the report with"
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
