/-
  `ix bench plots`: sync the bencher.dev dashboard plots to the benchmark
  registry — one plot per (workload, measure) that bench-main.yml tracks,
  with one line per benchmark row (a constant or env name) on the current
  machine's testbed, plus the cross-cutting shared input-constants trend. The spec derives from the registry
  (`Ix.Cli.BenchCmd`) + the shared constant set (`Ix.BenchConstants`), so
  nothing is hand-listed, and
  every join is on the bencher SLUG (the row-key identity uploads use;
  display names are console-editable and never consulted).

  Idempotent, keyed by title (the display names in `plotTitle`): a plot
  whose dimensions already match is left alone (only its dashboard index
  is re-asserted); a stale one is deleted and recreated (the plot PATCH
  endpoint only takes index/title/window, not dimensions). The registry
  owns the dashboard: every plot whose title is not in the desired set is
  deleted, so each sync converges to exactly the registry's plots — a
  hand-created plot does not survive a sync. A registry benchmark,
  measure, or whole testbed bencher hasn't seen yet (first upload still
  pending) is skipped with a warning and picked up on the next sync.

  The sync also asserts every measure's canonical units (`unitsFor`) —
  bencher auto-creates measures with placeholder units on first upload,
  and plots would render unitless otherwise.

  All bencher.dev traffic goes through the bencher CLI (`bencher <dim>
  list` / `plot create|update|delete` / `measure update`), which reads
  BENCHER_API_KEY from the environment itself; the list endpoints are
  public, so `--dry-run` needs no key.
-/
module
public import Cli
public import Lean.Data.Json
public import Ix.Cli.BenchCmd

public section

open Lean (Json)

namespace Ix.Cli.BenchPlots

/-- The registry's workload key (testbed minus hardware suffix) — what
    the titles, skips, and ordering here are written against. -/
def workloadOf (testbed : String) : String :=
  BenchCmd.workloadOf testbed

/-- Dashboard display title per (workload, measure). Presentation only —
    measurement identity stays the slugs — which is why it lives here and
    not in the registry. Titles key the sync's keep/replace decisions:
    keep them unique. An unmapped pair falls back to
    `<workload>: <measure>`, which stays unique and flags itself for a
    nicer name here. -/
def plotTitle (workload measure : String) : String :=
  match workload, measure with
  | "ix-compile-certified", "compile-time" => "Certified Compile Time"
  | "ix-compile-certified", "throughput"   => "Certified Compile Throughput"
  | "ix-compile-certified", "peak-rss"     => "Certified Compile Peak RAM Usage"
  | "ix-compile-certified", "file-size"    => "Certified Compile Env Size"
  | "ix-compile-certified", "constants"    => "Certified Compile Input Constants"
  | "ix-decompile-lean", "decompile-time"     => "Ix Decompile Time"
  | "ix-decompile-lean", "throughput"         => "Ix Decompile Throughput"
  | "ix-decompile-lean", "peak-rss"           => "Ix Decompile Peak RAM Usage"
  | "ixvm", "execute-time"     => "IxVM Execute Time"
  | "ixvm", "check-time"       => "IxVM Check Time"
  | "ixvm", "peak-rss"         => "IxVM Check Peak RAM Usage"
  | "ixvm", "shards"           => "IxVM Env Shards"
  | "ixvm-ooc", "check-time"   => "IxVM OOC (IxC) Check Time"
  | "ixvm-ooc", "throughput"   => "IxVM OOC (IxC) Check Throughput"
  | "ixvm-ooc", "peak-rss"     => "IxVM OOC (IxC) Check Peak RAM Usage"
  | w, m => s!"{w}: {m}"

/-- Tracked but not plotted solo. `ix-decompile-lean` reuses the compile run's `.ixe`, so its `file-size` /
    `constants` duplicate "Certified Compile Env Size" / "Certified Compile Input Constants"
    exactly — the decompile run tracks only its own decompile-time /
    throughput / peak-rss trends. -/
def plotSkips : List (String × String) :=
  [("ix-decompile-lean", "file-size"), ("ix-decompile-lean", "constants")]

/-- Canonical units per measure slug, asserted on every sync: bencher
    auto-creates a measure with placeholder units ("Measure (units)") on
    its first upload, leaving plots unitless — and a console edit would
    drift from this list, so the sync re-asserts it. Phase spans are
    wall-clock seconds. -/
def unitsFor (slug : String) : Option String :=
  if slug.startsWith "phase-" then some "seconds (s)" else
  [("compile-time", "seconds (s)"),
   ("decompile-time", "seconds (s)"),
   ("execute-time", "seconds (s)"),
   ("check-time", "seconds (s)"),
   ("peak-rss", "bytes (B)"),
   ("file-size", "bytes (B)"),
   ("constants", "constants"),
   ("shards", "shards"),
   ("throughput", "constants / second")].lookup slug

/-- Dashboard group order (compile first, then decompile, IxVM execution,
    IxVM out-of-circuit checks); unranked workloads (a future backend) sort last. -/
def workloadOrder : List String :=
  ["ix-compile-certified", "ix-decompile-lean", "ixvm", "ixvm-ooc"]

structure PlotSpec where
  testbed : String
  /-- Each plotted measure with the benchmark rows that carry it. -/
  measures : List (String × Array String)

/-- One spec per bench-main workload: its measure slugs and the benchmark row
    names that carry each measure, both from the registry
    (`BackendSpec.benchmarkNames`): the shared constants for a constant-row
    measure, the envs for an env-row measure, both lines on one plot when
    both kinds carry it. Dynamic sub-rows (`<name>/shard-N`) are left out: their
    multiplicity shifts with the shard manifest, and the parent row carries
    the headline trend. -/
def plotSpecs : Array PlotSpec := Id.run do
  let mut specs : Array PlotSpec := #[]
  for b in BenchCmd.backendSpecs do
    if b.disabled.isSome then continue
    specs := specs.push
      { testbed := b.testbed,
        measures := b.metrics.map fun m => (m, b.benchmarkNames m) }
  return specs.qsort fun a b =>
    workloadOrder.idxOf (workloadOf a.testbed)
      < workloadOrder.idxOf (workloadOf b.testbed)

/-! ## bencher CLI plumbing -/

/-- Spawn env for the bencher CLI: drop LD_LIBRARY_PATH. `lake exe`
    prepends the Lean toolchain's lib dirs there (for libleanshared), and
    the loader consults LD_LIBRARY_PATH before a binary's own RUNPATH — so
    bencher would resolve the toolchain's bundled, older `libgcc_s.so.1`
    and die on a missing GCC symbol version. bencher is self-contained;
    it needs nothing from the Lean runtime. -/
def bencherEnv : Array (String × Option String) :=
  #[("LD_LIBRARY_PATH", none)]

/-- Run the bencher CLI and parse its JSON stdout. -/
def bencherJson (args : Array String) : IO Json := do
  let r ← IO.Process.output { cmd := "bencher", args, env := bencherEnv }
  if r.exitCode != 0 then
    throw <| IO.userError
      s!"bencher {" ".intercalate args.toList} failed (exit {r.exitCode}):\n{r.stderr}"
  match Json.parse r.stdout with
  | .ok j => return j
  | .error e => do
    throw <| IO.userError
      s!"bencher {" ".intercalate args.toList}: unparseable JSON: {e}"

/-- Run a bencher write call (create/update/delete), output discarded. -/
def bencherRun (args : Array String) : IO Unit := do
  let r ← IO.Process.output { cmd := "bencher", args, env := bencherEnv }
  if r.exitCode != 0 then
    throw <| IO.userError
      s!"bencher {" ".intercalate args.toList} failed (exit {r.exitCode}):\n{r.stderr}"

/-- One dimension's full list (paginated; the read endpoints are public). -/
def fetchAll (project dim : String) : IO (Array Json) := do
  let mut out : Array Json := #[]
  for page in [1:65] do
    let chunk ← bencherJson
      #[dim, "list", project, "--per-page", "255", "--page", toString page]
    let arr := chunk.getArr?.toOption.getD #[]
    out := out ++ arr
    if arr.size < 255 then break
  return out

def objStr (j : Json) (k : String) : Option String :=
  (j.getObjVal? k).toOption.bind (·.getStr?.toOption)

def objStrArr (j : Json) (k : String) : Array String :=
  ((j.getObjVal? k).toOption.bind (·.getArr?.toOption)).getD #[]
    |>.filterMap (·.getStr?.toOption)

/-- The uuid of the item whose `key` field equals `val`. -/
def findUuid (items : Array Json) (key val : String) : Option String :=
  items.findSome? fun it =>
    if objStr it key == some val then objStr it "uuid" else none

/-- The workload's testbeds on the benchmark machines: only the current
    implementation's series, never a retired testbed. -/
def testbedsForPlot (testbeds : Array Json) (workload : String) : Array String :=
  (BenchCmd.benchmarkMachines.toArray.map (BenchCmd.testbedOnMachine workload)).filterMap
    (findUuid testbeds "slug" ·)

/-! ## Sync -/

/-- A plot as the sync wants it: everything already resolved to UUIDs. -/
structure DesiredPlot where
  title : String
  testbeds : Array String
  benchmarks : Array String
  measure : String
  window : Nat

inductive Outcome | created | replaced | kept

/-- Create/keep/replace one plot. An existing plot matches by title; same
    dimensions (order-insensitively), window, and axis → keep, re-asserting
    only the dashboard index (the list JSON carries no index field, so it
    can't be diffed). Anything else is deleted and recreated. -/
def syncPlot (project : String) (dryRun : Bool)
    (xAxis branchUuid : String) (plots : Array Json) (idx : Nat)
    (d : DesiredPlot) : IO Outcome := do
  let sorted := fun (a : Array String) => a.qsort (· < ·)
  let existing := plots.find? fun pl => objStr pl "title" == some d.title
  if let some pl := existing then
    let same :=
      objStrArr pl "branches" == #[branchUuid]
      && sorted (objStrArr pl "testbeds") == sorted d.testbeds
      && sorted (objStrArr pl "benchmarks") == sorted d.benchmarks
      && objStrArr pl "measures" == #[d.measure]
      && ((pl.getObjVal? "window").toOption.bind (·.getNat?.toOption))
           == some d.window
      && objStr pl "x_axis" == some xAxis
    if same then
      IO.println s!"keep:    {d.title}"
      unless dryRun do
        bencherRun #["plot", "update", project, (objStr pl "uuid").getD "",
          "--index", toString idx]
      return .kept
    IO.println s!"replace: {d.title}"
    unless dryRun do
      bencherRun #["plot", "delete", project, (objStr pl "uuid").getD ""]
  else
    IO.println s!"create:  {d.title}"
  unless dryRun do
    let mut args := #["plot", "create", project,
      "--title", d.title, "--index", toString idx,
      "--x-axis", xAxis, "--window", toString d.window,
      "--branches", branchUuid, "--measures", d.measure]
    for t in d.testbeds do args := args ++ #["--testbeds", t]
    for b in d.benchmarks do args := args ++ #["--benchmarks", b]
    bencherRun args
  return if existing.isSome then .replaced else .created

def runPlotsCmd (p : Cli.Parsed) : IO UInt32 := do
  let project := (p.flag? "project").map (·.as! String) |>.getD "ix"
  let branch := (p.flag? "branch").map (·.as! String) |>.getD "main"
  let window := (p.flag? "window").map (·.as! Nat) |>.getD 7257600
  let xAxis := (p.flag? "x-axis").map (·.as! String) |>.getD "version"
  let dryRun := p.hasFlag "dry-run"
  if !dryRun && (← IO.getEnv "BENCHER_API_KEY").isNone then
    p.printError "error: set BENCHER_API_KEY (or pass --dry-run)"
    return 2
  let specs := plotSpecs

  let branches ← fetchAll project "branch"
  let testbeds ← fetchAll project "testbed"
  let measures ← fetchAll project "measure"
  let benchmarks ← fetchAll project "benchmark"
  let plots ← fetchAll project "plot"

  -- Units first, so even a plotless measure (phase spans, PR-column-only
  -- counters) renders with its unit everywhere bencher shows it.
  for m in measures do
    if let (some slug, some uuid) := (objStr m "slug", objStr m "uuid") then
      if let some want := unitsFor slug then
        let cur := (objStr m "units").getD ""
        if cur != want then
          IO.println s!"units:   {slug}: \"{cur}\" → \"{want}\""
          unless dryRun do
            bencherRun #["measure", "update", project, uuid, "--units", want]

  let some branchUuid := findUuid branches "name" branch
    | p.printError s!"error: no branch named '{branch}'"; return 1

  let mut created := 0
  let mut replaced := 0
  let mut kept := 0
  let mut idx := 0
  let mut desired : Array DesiredPlot := #[]
  for spec in specs do
    let workload := workloadOf spec.testbed
    -- A registry testbed bencher hasn't seen yet (first upload still
    -- pending after a rename or a new backend) has no plots to sync:
    -- warn and skip it, like a not-yet-uploaded benchmark, instead of
    -- failing the whole run. Picked up on a later sync once data lands.
    let testbedUuids := testbedsForPlot testbeds workload
    if testbedUuids.isEmpty then
      IO.eprintln s!"warn: no testbeds for '{spec.testbed}' on bencher yet — skipped"
      continue
    for (measure, names) in spec.measures do
      if plotSkips.contains (workload, measure) then continue
      -- Benchmark names → UUIDs, dropping the not-yet-uploaded ones loudly.
      let mut benchUuids : Array String := #[]
      for n in names do
        match findUuid benchmarks "name" n with
        | some u => benchUuids := benchUuids.push u
        | none => do
          IO.eprintln
            s!"warn: {spec.testbed}: benchmark '{n}' not on bencher yet — skipped"
      -- A measure bencher hasn't seen yet (first upload after a rename or
      -- a new tracked measure still pending) has no series to plot: warn
      -- and skip, like a not-yet-uploaded benchmark or testbed. Its
      -- existing plot (if any) is removed below and recreated by a later
      -- sync once data lands.
      let some measureUuid := findUuid measures "slug" measure
        | IO.eprintln s!"warn: measure '{measure}' not on bencher yet — skipped"; continue
      let title := plotTitle workload measure
      desired := desired.push
        { title, testbeds := testbedUuids, benchmarks := benchUuids,
          measure := measureUuid, window }

  -- The native checker supplies closure counts independently of proving
  -- capacity. Select only the shared constants, excluding whole-env rows.
  let overlay : Option DesiredPlot := do
    let oocTb ← BenchCmd.benchmarkMachines.findSome? fun machine =>
      findUuid testbeds "slug" (BenchCmd.testbedOnMachine "ixvm-ooc" machine)
    let consts ← findUuid measures "slug" "constants"
    let names := Ix.BenchConstants.benchConstants.filterMap fun c =>
      findUuid benchmarks "name" c.name
    return { title := "IxVM OOC (IxC) Input Constants",
             testbeds := #[oocTb], benchmarks := names,
             measure := consts, window }
  match overlay with
  | some d => desired := desired.push d
  | none => do
    IO.eprintln
      "warn: input-constants plot skipped (missing testbed or measure)"

  -- The registry owns the dashboard: delete every plot whose title isn't
  -- in the desired set, so each sync converges to exactly the registry's
  -- plots (a renamed or de-listed plot goes away instead of lingering
  -- beside its replacement).
  let desiredTitles := desired.map (·.title)
  let mut removed := 0
  for pl in plots do
    if let some title := objStr pl "title" then
      if !desiredTitles.contains title then
        IO.println s!"remove:  {title}"
        unless dryRun do
          bencherRun #["plot", "delete", project, (objStr pl "uuid").getD ""]
        removed := removed + 1

  for d in desired do
    match ← syncPlot project dryRun xAxis branchUuid plots idx d with
    | .created => created := created + 1
    | .replaced => replaced := replaced + 1
    | .kept => kept := kept + 1
    idx := idx + 1

  IO.println s!"plots: {created} created, {replaced} replaced, {removed} removed, {kept} kept \
    → https://bencher.dev/console/projects/{project}/plots"
  return 0

end Ix.Cli.BenchPlots

open Ix.Cli.BenchPlots in
def benchPlotsCmd : Cli.Cmd := `[Cli|
  plots VIA runPlotsCmd;
  "Sync the bencher.dev dashboard plots to the registry: one plot per tracked (workload, measure) on the current machine's testbed, plus the shared input-constants plot. Needs the bencher CLI; writes need BENCHER_API_KEY (plot create/delete permission)."

  FLAGS:
    "dry-run";         "Print the create/replace/keep decisions without writing (no key needed)"
    project : String;  "Bencher project slug (default: ix)"
    branch  : String;  "Branch whose series the plots track (default: main)"
    window  : Nat;     "Seconds of history per plot (default: 7257600 = 12 weeks)"
    "x-axis" : String; "date_time | version (default: version)"
]
