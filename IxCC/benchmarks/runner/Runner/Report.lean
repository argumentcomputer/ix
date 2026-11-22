import Runner.Measure

/-! Summaries of both profiles.

**Process** (`report.md`, `report.json`): per fixture and row, the median
whole-process time over blocks; per fixture, the ratio of each row to
`lean-clang` with a percentile-bootstrap interval over paired blocks; per
rung, the geometric mean of those ratios.

**Entry** (`entry-report.md`, `entry-report.json`, when `entry-samples.json`
exists): per fixture and row, the median time per call; the ratio of each row
to `lean-clang`, `clang-O2`, `clang-O3` and the diagnostic `clang-tagged`
row, paired per block, with 95% percentile-bootstrap intervals; the `perf`
counters per call (instructions, cycles, IPC, branches, branch misses) and
the bytes the row allocated per call where it reports them; then per rung
the geometric mean of each row's ratios to each baseline over the fixtures
where both exist, with a hierarchical bootstrap interval (blocks resampled
within each fixture), the largest per-fixture ratio, and the fixtures used
and missing. A ratio above 1 means the row is slower than the baseline. -/

namespace Runner

open Lean System

/-! ## Process profile -/

def reportProcess (manifest : Manifest) (out : FilePath) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (out / "samples.json")))
  let samples ← IO.ofExcept do
    (← (← json.getObjVal? "samples").getArr?).mapM fun s => do
      return (← (← s.getObjVal? "fixture").getStr?, ← (← s.getObjVal? "row").getStr?,
        ← (← s.getObjVal? "block").getNat?, ← (← s.getObjVal? "ns").getNat?)
  let env := json.getObjValD "environment"
  let rows := Row.process.filter fun r => samples.any (·.2.1 == r.name)
  let others := rows.filter (· != .leanClang)
  let mut lines : Array String := #[
    "# Local benchmark report: process profile", "",
    s!"Host: {env.getObjValD "cpu_model" |>.compress}, worker CPU {env.getObjValD "worker_cpu" |>.compress}, governor {env.getObjValD "governor" |>.compress}, load {env.getObjValD "loadavg" |>.compress}.",
    s!"Blocks per fixture: {json.getObjValD "blocks" |>.compress}. Whole-process wall time (startup included); ratio = row / lean-clang (above 1 is slower); 95% percentile-bootstrap intervals over paired blocks.", "",
    "| Fixture | Rung | " ++ " | ".intercalate (rows.map (s!"{·.name} ms")) ++ " | " ++
      " | ".intercalate (others.map (s!"{·.name} / lean-clang")) ++ " |",
    "| --- | --- | " ++ " | ".intercalate ((rows ++ others).map fun _ => "---:") ++ " |"]
  let mut rungRatios : Array (String × String × Float) := #[]
  let mut rowsJson : Array Json := #[]
  for fixture in manifest.fixtures do
    let of (row : String) := samples.filter fun (f, r, _, _) => f == fixture.name && r == row
    let base := of "lean-clang"
    if base.isEmpty then continue
    let ms (row : String) := median ((of row).map fun (_, _, _, ns) => ns.toFloat / 1e6)
    let paired (row : String) : Array Float := (of row).filterMap fun (_, _, block, ns) =>
      (base.find? fun (_, _, b, _) => b == block).map fun (_, _, _, baseNs) => ns.toFloat / baseNs.toFloat
    let cell (row : String) : String :=
      let ratios := paired row
      if ratios.isEmpty then "-" else
      let (low, high) := bootstrap ratios
      fmtInterval (median ratios) low high
    for row in others do
      unless (paired row.name).isEmpty do
        rungRatios := rungRatios.push (fixture.rung, row.name, median (paired row.name))
    lines := lines.push (s!"| {fixture.name} | {fixture.rung} | " ++
      " | ".intercalate (rows.map fun r => if (of r.name).isEmpty then "-" else fmt (ms r.name) 1) ++ " | " ++
      " | ".intercalate (others.map (cell ·.name)) ++ " |")
    rowsJson := rowsJson.push (Json.mkObj [("fixture", Json.str fixture.name), ("rung", Json.str fixture.rung),
      ("median_ms", Json.mkObj (rows.filterMap fun r =>
        if (of r.name).isEmpty then none else some (r.name, toJson (ms r.name)))),
      ("ratio_to_lean_clang", Json.mkObj (others.filterMap fun r =>
        if (paired r.name).isEmpty then none else some (r.name, toJson (median (paired r.name)))))])
  lines := lines ++ #["", "| Rung | Row | Geomean ratio to lean-clang | Fixtures |", "| --- | --- | ---: | ---: |"]
  for rung in ["K1", "K2", "K3"] do
    for row in others do
      let values := rungRatios.filterMap fun (r, w, v) => if r == rung && w == row.name && v > 0 then some v else none
      unless values.isEmpty do
        lines := lines.push s!"| {rung} | {row.name} | {fmt (geomean values)} | {values.size} |"
  IO.FS.writeFile (out / "report.md") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out / "report.json") ((Json.mkObj [("environment", env), ("fixtures", Json.arr rowsJson)]).pretty ++ "\n")
  IO.println s!"wrote {out / "report.md"}"

/-! ## Entry profile -/

/-- The paired per-block ratios of one row to one baseline on one fixture. -/
structure RatioSet where
  rung : String
  fixture : String
  row : String
  base : String
  ratios : Array Float

/-- Baselines of the entry report's ratio columns. -/
def entryBaselines : List Row := [.leanClang, .clangO2, .clangO3, .clangTagged]

/-- Rows whose geometric means the entry report gives. -/
def geomeanRows : List Row := [.ixcc, .lirKernel, .clangTagged, .leanClang]

def fmtNs (ns : Float) : String :=
  if ns ≥ 1e6 then s!"{fmt (ns / 1e6) 3} ms" else if ns ≥ 1e3 then s!"{fmt (ns / 1e3) 3} µs"
  else s!"{fmt ns 1} ns"

def fmtCount (value : Float) : String :=
  if value.abs ≥ 1e9 then s!"{fmt (value / 1e9) 3} G" else if value.abs ≥ 1e6 then s!"{fmt (value / 1e6) 3} M"
  else if value.abs ≥ 1e4 then s!"{fmt (value / 1e3) 1} k" else fmt value 1

def reportEntry (manifest : Manifest) (out : FilePath) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (out / "entry-samples.json")))
  let all ← IO.ofExcept ((json.getObjValD "samples").getArr?)
  let isValid (s : Json) : Bool := (s.getObjValD "valid").getBool?.toOption.getD true
  let samples ← IO.ofExcept do
    (all.filter isValid).mapM fun s => do
      return (← (← s.getObjVal? "fixture").getStr?, ← (← s.getObjVal? "row").getStr?,
        ← (← s.getObjVal? "block").getNat?, (← (← s.getObjVal? "ns_per_call").getNum?).toFloat,
        (s.getObjValD "heap_bytes").getNat?.toOption, ← (← s.getObjVal? "reps").getNat?,
        ← (← s.getObjVal? "warmup").getNat?)
  -- the gate's record: invalid attempts, accepted blocks that were not quiet, waits
  let blockKey (s : Json) := (s.getObjValD "fixture").compress ++ "/" ++ (s.getObjValD "block").compress ++
    "/" ++ (s.getObjValD "attempt").compress
  let firstOfBlock := all.foldl (fun (seen : List String × Array Json) s =>
    if seen.1.contains (blockKey s) then seen else (blockKey s :: seen.1, seen.2.push s)) ([], #[]) |>.2
  let invalidAttempts := (firstOfBlock.filter (!isValid ·)).size
  let loud := (firstOfBlock.filter fun s => isValid s &&
    (s.getObjValD "quiet").getBool?.toOption == some false).size
  let waited := firstOfBlock.foldl (fun acc s => acc + ((s.getObjValD "waited_s").getNat?.toOption.getD 0)) 0
  let gated := !(json.getObjValD "gate").isNull
  let env := json.getObjValD "environment"
  let envEnd := json.getObjValD "environment_end"
  let perf ← try some <$> IO.ofExcept (Json.parse (← IO.FS.readFile (out / "entry-perf.json"))) catch _ => pure none
  let build ← try some <$> IO.ofExcept (Json.parse (← IO.FS.readFile (out / "build.json"))) catch _ => pure none
  let reps ← try some <$> IO.ofExcept (Json.parse (← IO.FS.readFile (repsFile out))) catch _ => pure none
  let counter (fixture row event : String) : Option Float := do
    let p ← perf
    let entry ← (p.getArr?.toOption.getD #[]).find? fun e =>
      e.getObjValD "fixture" == Json.str fixture && e.getObjValD "row" == Json.str row
    (entry.getObjValD event).getNum?.toOption.map (·.toFloat)
  let str (j : Json) (k : String) : String := (j.getObjValD k).getStr?.toOption.getD "unavailable"
  let mut lines : Array String := #[
    "# Local benchmark report: entry profile", "",
    s!"Host: {str env "cpu_model"}, worker CPU {env.getObjValD "worker_cpu" |>.compress} (SMT siblings {str env "worker_siblings"}, max {str env "worker_max_khz"} kHz), governor {str env "governor"}, energy preference {str env "energy_preference"}, boost {str env "boost"}, kernel {str env "kernel"}.",
    s!"Load average at the start: {str env "loadavg"}; at the end: {str envEnd "loadavg"}. Mains power online: {str env "ac_online"} at the start, {str envEnd "ac_online"} at the end; platform profile {str env "platform_profile"}; worker frequency {str env "worker_cur_khz"} kHz at the start, {str envEnd "worker_cur_khz"} kHz at the end (snapshots).",
    s!"Blocks per fixture: {json.getObjValD "blocks" |>.compress}; each block runs every row once in a shuffled order, a fresh pinned process each. Target chunk: {(reps.map (·.getObjValD "target_ms" |>.compress)).getD "?"} ms.",
    if gated then s!"Quiet gate {(json.getObjValD "gate").compress}: {invalidAttempts} block attempts were disturbed (kept in the samples as invalid and run again), {loud} accepted blocks were not quiet (out of attempts), {waited} s spent waiting for quiet."
    else "No quiet gate: blocks ran whatever else the machine was doing (see the load averages).",
    "Time per call of the fixture's `entry`, in process (the entry profile: startup and runtime initialisation excluded, the entry's guards and result handoff included); medians over blocks. Ratios are row / baseline (above 1 is slower), paired per block, with 95% percentile-bootstrap intervals (2000 rounds). Counters are user-space `perf` events per call (a run with the repetitions minus one without; median of the runs). `clang-tagged` and `lir-kernel` are diagnostic rows that attribute a gap; they are never real-program results.", ""]
  if let some b := build then
    lines := lines.push s!"Toolchains: {(b.getObjValD "versions").compress}."
    lines := lines.push ""
  let mut ratioSets : Array RatioSet := #[]
  let mut rowsJson : Array Json := #[]
  -- variant rows (A/B and what-if objects), in name order
  let variants : List Row := (samples.map (·.2.1)).toList.eraseDups.mergeSort (· ≤ ·) |>.filterMap fun n =>
    match Row.ofName? n with | some (.variant v) => some (Row.variant v) | _ => none
  let baselinesAll := if variants.isEmpty then entryBaselines else .ixcc :: entryBaselines
  for fixture in manifest.fixtures do
    let of (row : String) := samples.filter fun (f, r, _) => f == fixture.name && r == row
    let rows := (Row.entry ++ variants).filter fun r => !(of r.name).isEmpty
    if rows.isEmpty then continue
    let ns (row : String) := median ((of row).map (·.2.2.2.1))
    let paired (row base : String) : Array Float := (of row).filterMap fun (_, _, block, t, _) =>
      ((of base).find? fun (_, _, b, _) => b == block).map fun (_, _, _, bt, _) => t / bt
    let baselines := baselinesAll.filter rows.contains
    lines := lines ++ #[s!"## {fixture.name} ({fixture.rung}): entry {" ".intercalate fixture.benchArgs} = {(fixture.benchExpected.map trimmed).getD "?"}", "",
      "| Row | time/call | " ++ " | ".intercalate (baselines.map (s!"/ {·.name}")) ++
        " | instructions/call | cycles/call | IPC | branches/call | branch misses/call | heap B/call | reps |",
      "| --- | ---: | " ++ " | ".intercalate (baselines.map fun _ => "---:") ++ " | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for row in rows do
      let cells := baselines.map fun base =>
        if base == row then "1" else
        let ratios := paired row.name base.name
        if ratios.isEmpty then "-" else
        let (low, high) := bootstrap ratios
        s!"{fmtRatio (median ratios)} [{fmtRatio low}, {fmtRatio high}]"
      for base in baselines do
        if base != row then
          ratioSets := ratioSets.push
            { rung := fixture.rung, fixture := fixture.name, row := row.name,
              base := base.name, ratios := paired row.name base.name }
      let c (e : String) := (counter fixture.name row.name e).map fmtCount |>.getD "-"
      let ipc := match counter fixture.name row.name "instructions", counter fixture.name row.name "cycles" with
        | some i, some cy => if cy > 0 then fmt (i / cy) 2 else "-"
        | _, _ => "-"
      let heaps := (of row.name).filterMap fun (_, _, _, _, h, r, w) => h.map fun h => h.toFloat / (r + w).toFloat
      let heap := if heaps.isEmpty then "-" else fmt (median heaps) 1
      let repsCell := match (of row.name)[0]? with | some (_, _, _, _, _, r, _) => toString r | none => "-"
      lines := lines.push (s!"| {row.name} | {fmtNs (ns row.name)} | " ++ " | ".intercalate cells ++
        s!" | {c "instructions"} | {c "cycles"} | {ipc} | {c "branches"} | {c "branch-misses"} | {heap} | {repsCell} |")
      rowsJson := rowsJson.push (Json.mkObj [("fixture", Json.str fixture.name), ("row", Json.str row.name),
        ("median_ns_per_call", toJson (ns row.name)),
        ("ratios", Json.mkObj (baselines.filterMap fun base =>
          let ratios := paired row.name base.name
          if base == row || ratios.isEmpty then none else
          let (low, high) := bootstrap ratios
          some (base.name, Json.mkObj [("median", toJson (median ratios)), ("low", toJson low), ("high", toJson high)])))])
    lines := lines.push ""
  -- geometric means per rung
  lines := lines ++ #["## Geometric means", "",
    "Over the fixtures of the rung where both rows exist: the geometric mean of the per-fixture median paired ratios, with a 95% hierarchical-bootstrap interval (blocks resampled within each fixture); the largest per-fixture ratio; and the geometric mean without that fixture, which shows whether one fixture drives the mean (for example a twin that clang folds to a closed form).", "",
    "| Rung | Row | Baseline | Geomean [95%] | Largest (fixture) | Without the largest [95%] | Fixtures | Missing |",
    "| --- | --- | --- | ---: | ---: | ---: | --- | --- |"]
  let mut geoJson : Array Json := #[]
  for rung in ["K1", "K2", "K3"] do
    let rungFixtures := manifest.fixtures.filter (·.rung == rung) |>.map (·.name)
    for row in geomeanRows ++ variants do
      for base in baselinesAll do
        if row == base then continue
        let groups := ratioSets.filter fun s =>
          s.rung == rung && s.row == row.name && s.base == base.name && !s.ratios.isEmpty
        if groups.isEmpty then continue
        let (point, low, high) := geomeanBootstrap (groups.map (·.ratios))
        let (worst, worstFixture) := groups.foldl (fun (m, n) s =>
          let v := median s.ratios
          if v > m then (v, s.fixture) else (m, n)) (0.0, "")
        let rest := groups.filter (·.fixture != worstFixture)
        let (restPoint, restLow, restHigh) := geomeanBootstrap (rest.map (·.ratios))
        let restCell := if rest.isEmpty then "-" else s!"{fmtRatio restPoint} [{fmtRatio restLow}, {fmtRatio restHigh}]"
        let used := groups.map (·.fixture)
        let missing := rungFixtures.filter (!used.contains ·)
        lines := lines.push s!"| {rung} | {row.name} | {base.name} | {fmtRatio point} [{fmtRatio low}, {fmtRatio high}] | {fmtRatio worst} ({worstFixture}) | {restCell} | {", ".intercalate used.toList} | {if missing.isEmpty then "-" else ", ".intercalate missing.toList} |"
        geoJson := geoJson.push (Json.mkObj [("rung", Json.str rung), ("row", Json.str row.name),
          ("baseline", Json.str base.name), ("geomean", toJson point), ("low", toJson low), ("high", toJson high),
          ("largest", toJson worst), ("largest_fixture", Json.str worstFixture),
          ("without_largest", if rest.isEmpty then Json.null else Json.mkObj [("geomean", toJson restPoint),
            ("low", toJson restLow), ("high", toJson restHigh)]),
          ("fixtures", toJson used), ("missing", toJson missing)])
  -- compile times
  if let some b := build then
    let compiles := (b.getObjValD "ixcc_compiles").getArr?.toOption.getD #[]
    unless compiles.isEmpty do
      lines := lines ++ #["", "## ixcc compiles", "",
        "`ixcc compile … --no-typecheck` per closure: wall time of the process, and its `--stats` lines.", "",
        "| Fixture | Wall ms | Stats |", "| --- | ---: | --- |"]
      for c in compiles do
        let stats := ((c.getObjValD "stats").getStr?.toOption.getD "").splitOn "\n" |>.filter (!·.isEmpty)
        lines := lines.push s!"| {str c "fixture"} | {fmt ((c.getObjValD "wall_ms").getNum?.toOption.map (·.toFloat) |>.getD 0) 1} | {"; ".intercalate stats} |"
    let statuses := ((b.getObjValD "statuses").getArr?.toOption.getD #[]).filter fun s =>
      (s.getObjValD "status").getStr?.toOption != some "built"
    unless statuses.isEmpty do
      lines := lines ++ #["", "Rows not built:", ""]
      for s in statuses do
        lines := lines.push s!"- {str s "row"}/{str s "fixture"}: {str s "status"}: {str s "detail"}"
  IO.FS.writeFile (out / "entry-report.md") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out / "entry-report.json") ((Json.mkObj [("environment", env), ("environment_end", envEnd),
    ("rows", Json.arr rowsJson), ("geomeans", Json.arr geoJson)]).pretty ++ "\n")
  IO.println s!"wrote {out / "entry-report.md"}"

def report (manifest : Manifest) (out : FilePath) : IO Unit := do
  if ← (out / "samples.json").pathExists then reportProcess manifest out
  if ← (out / "entry-samples.json").pathExists then reportEntry manifest out

end Runner
