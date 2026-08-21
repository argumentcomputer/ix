/-
  `ix bench plots`: sync the bencher.dev dashboard plots to the benchmark
  registry — one plot per (testbed, measure) that bench-main.yml tracks,
  with one line per benchmark row uploaded there, plus the cross-cutting
  shared input-constants trend. The spec derives from the registry
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

/-- The registry's workload key (testbed minus runner-arch suffix) — what
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
  | "ix-compile", "compile-time"         => "Ix Compile Time"
  | "ix-compile", "throughput"           => "Ix Compile Throughput"
  | "ix-compile", "peak-rss"             => "Ix Compile Peak RAM Usage"
  | "ix-compile", "file-size"            => "Ix Environment Size"
  | "ix-compile", "constants"            => "Ix Input Constants"
  | "ix-decompile", "decompile-time"     => "Ix Decompile Time"
  | "ix-decompile", "throughput"         => "Ix Decompile Throughput"
  | "ix-decompile", "peak-rss"           => "Ix Decompile Peak RAM Usage"
  | "aiur", "total-time"             => "Aiur Total Time"
  | "aiur", "pipeline-throughput"    => "Aiur Total Throughput"
  | "aiur", "pipeline-peak-rss"      => "Aiur Total Peak RAM Usage"
  | "aiur", "ixvm-prove-time"          => "Aiur IxVM Time"
  | "aiur", "fri-verifier-prove-time"  => "Aiur FRI Verifier Time"
  | "aiur", "ixvm-fft-cost"            => "Aiur IxVM FFT Cost"
  | "aiur", "fri-verifier-fft-cost"    => "Aiur FRI Verifier FFT Cost"
  | "aiur", "fri-verifier-verify-time" => "Aiur FRI Verifier Verify Time"
  | "aiur", "fri-verifier-peak-rss"    => "Aiur FRI Verifier Peak RAM Usage"
  | "aiur", "ixvm-proof-size"          => "Aiur IxVM Proof Size"
  | "aiur", "fri-verifier-proof-size"  => "Aiur FRI Verifier Proof Size"
  | "zisk-check-execute", "execute-time" => "Zisk Execute Time"
  | "zisk-check-execute", "throughput"   => "Zisk Execute Throughput"
  | "zisk-check-execute", "peak-rss"     => "Zisk Execute Peak RAM Usage"
  | "zisk-check-execute", "cycles"       => "Zisk Cycles"
  | "zisk-check-execute", "shards"       => "Zisk Shards"
  | "ooc-check", "check-time"            => "OOC Check Time"
  | "ooc-check", "throughput"            => "OOC Check Throughput"
  | "ooc-check", "peak-rss"              => "OOC Check Peak RAM Usage"
  | w, m => s!"{w}: {m}"

/-- Tracked but not plotted solo. Zisk
    `constants` charts on the input-constants plot below instead of alone.
    `ix-decompile` reuses the compile run's `.ixe`, so its `file-size` /
    `constants` duplicate "Ix Environment Size" / "Ix Input Constants"
    exactly — the decompile run tracks only its own decompile-time /
    throughput / peak-rss trends. The aiur run's per-stage headline is
    that stage's `prove-time` — a prove runs its own witness execution,
    so it is the whole cost of producing the stage's proof, and the
    standalone `execute-time` beside it is a second, instrumentation-only
    run. The ixvm stage's peak-rss / verify-time are tracked for the
    compare table but not plotted: their cost is inside `ixvm-prove-time`
    and the deterministic `ixvm-fft-cost` trend, and that stage's proof
    is an intermediate artifact consumed by the next stage. Its
    `ixvm-proof-size` IS plotted: it sizes the next stage's in-circuit
    verification workload. The whole-run `pipeline-peak-rss` too: which stage
    sets the run's RAM ceiling can shift as pipeline stages are added,
    so no per-stage peak plot stands in for it. The per-stage
    throughputs are table columns only — over the exactly-pinned
    `constants` they are the plotted stage times inverted — while the
    end-to-end `pipeline-throughput` gets the backend's one throughput
    plot, comparable with the other backends'. -/
def plotSkips : List (String × String) :=
  [("zisk-check-execute", "constants"),
   ("ix-decompile", "file-size"), ("ix-decompile", "constants"),
   ("aiur", "ixvm-peak-rss"), ("aiur", "ixvm-verify-time"),
   ("aiur", "ixvm-execute-time"), ("aiur", "fri-verifier-execute-time"),
   ("aiur", "ixvm-throughput"), ("aiur", "fri-verifier-throughput")]

/-- Canonical units per measure slug, asserted on every sync: bencher
    auto-creates a measure with placeholder units ("Measure (units)") on
    its first upload, leaving plots unitless — and a console edit would
    drift from this list, so the sync re-asserts it. Phase spans are
    wall-clock seconds. A stage-qualified slug (`ixvm-prove-time`,
    `pipeline-peak-rss`) carries its base measure's units, so only base
    names are listed. -/
def unitsFor (slug : String) : Option String :=
  if slug.startsWith "phase-" then some "seconds (s)" else
  [("execute-peak-rss", "bytes (B)"),
   ("compile-time", "seconds (s)"),
   ("decompile-time", "seconds (s)"),
   ("execute-time", "seconds (s)"),
   ("prove-time", "seconds (s)"),
   ("verify-time", "seconds (s)"),
   ("check-time", "seconds (s)"),
   ("total-time", "seconds (s)"),
   ("peak-rss", "bytes (B)"),
   ("file-size", "bytes (B)"),
   ("proof-size", "bytes (B)"),
   ("constants", "constants"),
   ("cycles", "cycles"),
   ("max-shard-cycles", "cycles"),
   ("shards", "shards"),
   ("fft-cost", "FFTs"),
   ("throughput", "constants / second")].lookup
     (BenchCmd.dropStagePrefix slug)

/-- Dashboard group order (compile first, then the aiur pipeline, zisk,
    ooc); unranked workloads (a future backend) sort last. -/
def workloadOrder : List String :=
  ["ix-compile", "ix-decompile", "aiur", "zisk-check-execute", "ooc-check"]

structure PlotSpec where
  testbed : String
  measures : List String
  benchmarks : Array String

/-- One spec per bench-main testbed: its measure slugs and the benchmark row
    names uploaded there, both from the registry (`BackendSpec.benchmarkNames`,
    keyed off `inputs`) — env-keyed backends (compile, decompile) key one row
    per compiled env, the per-constant backends one row per primary, and ooc
    adds a whole-env row. Dynamic
    sub-rows (`<name>/shard-N`) are left out: their multiplicity shifts with the
    shard manifest, and the parent row carries the headline trend. -/
def plotSpecs : Array PlotSpec := Id.run do
  let mut specs : Array PlotSpec := #[]
  for b in BenchCmd.backendSpecs do
    if b.disabled.isSome then continue
    for (mode, testbed) in b.testbeds do
      -- On-demand modes (e.g. aiur `execute`) upload nothing, so there's
      -- nothing to plot — the registry marks them explicitly.
      if b.unscheduled.contains mode then continue
      specs := specs.push
        { testbed, measures := b.metricsFor mode,
          benchmarks := b.benchmarkNames mode }
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

/-! ## Sync -/

/-- History window (seconds) for a plot, overriding the global `--window`
    default by display title. A listed title renders a tighter rolling span so
    its recent trend isn't compressed by older history; every other title uses
    the default. Keyed by title — the same identity the sync keeps/replaces
    on. -/
def windowFor (title : String) (dflt : Nat) : Nat :=
  match title with
  | "Zisk Execute Throughput" => 4 * 7 * 24 * 3600  -- 4 weeks
  | _ => dflt

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
    let some testbedUuid := findUuid testbeds "slug" spec.testbed
      | IO.eprintln s!"warn: testbed '{spec.testbed}' not on bencher yet — skipped"; continue
    -- Benchmark names → UUIDs, dropping the not-yet-uploaded ones loudly.
    let mut benchUuids : Array String := #[]
    for n in spec.benchmarks do
      match findUuid benchmarks "name" n with
      | some u => benchUuids := benchUuids.push u
      | none => do
        IO.eprintln
          s!"warn: {spec.testbed}: benchmark '{n}' not on bencher yet — skipped"
    for measure in spec.measures do
      if plotSkips.contains (workload, measure) then continue
      -- A measure bencher hasn't seen yet (first upload after a rename or
      -- a new tracked measure still pending) has no series to plot: warn
      -- and skip, like a not-yet-uploaded benchmark or testbed. Its
      -- existing plot (if any) is removed below and recreated by a later
      -- sync once data lands.
      let some measureUuid := findUuid measures "slug" measure
        | IO.eprintln s!"warn: measure '{measure}' not on bencher yet — skipped"; continue
      let title := plotTitle workload measure
      desired := desired.push
        { title, testbeds := #[testbedUuid], benchmarks := benchUuids,
          measure := measureUuid, window := windowFor title window }

  -- Input-constants trend over the shared constant set. The kernel
  -- backends (aiur, zisk, ooc) report the SAME named-constant count for
  -- each checked closure (the pre-shard input set, unaffected by
  -- anon-work dedup or shard partitioning), so the count is shared:
  -- sourcing it from more than one testbed would draw every constant
  -- multiple times. The zisk run is the single source: its sharded
  -- execution keeps every closure feasible, so its rows (and their
  -- `constants`) upload even where the aiur prove OOMs and the row is
  -- dropped; only zisk's excluded names lack a line, and those have no
  -- completed upload from any backend.
  let overlay : Option DesiredPlot := do
    let ziskTb ← findUuid testbeds "slug" "zisk-check-execute-x64-32x"
    let consts ← findUuid measures "slug" "constants"
    let names ← (specs.find? (·.testbed == "zisk-check-execute-x64-32x")).map
      (·.benchmarks.filterMap (findUuid benchmarks "name" ·))
    return { title := "Kernel Input Constants",
             testbeds := #[ziskTb], benchmarks := names,
             measure := consts, window := windowFor "Kernel Input Constants" window }
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
  "Sync the bencher.dev dashboard plots to the registry: one plot per tracked (testbed, measure) plus the shared input-constants plot. Needs the bencher CLI; writes need BENCHER_API_KEY (plot create/delete permission)."

  FLAGS:
    "dry-run";         "Print the create/replace/keep decisions without writing (no key needed)"
    project : String;  "Bencher project slug (default: ix)"
    branch  : String;  "Branch whose series the plots track (default: main)"
    window  : Nat;     "Seconds of history per plot (default: 7257600 = 12 weeks)"
    "x-axis" : String; "date_time | version (default: version)"
]
