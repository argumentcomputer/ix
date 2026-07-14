/-
  `ix bench plots`: sync the bencher.dev dashboard plots to the benchmark
  registry — one plot per (testbed, measure) that bench-main.yml tracks,
  with one line per benchmark row uploaded there, plus the cross-kernel
  input-constants overlay. The spec derives from the registry
  (`Ix.Cli.BenchCmd`) + `Vectors.csv`, so nothing is hand-listed, and
  every join is on the bencher SLUG (the row-key identity uploads use;
  display names are console-editable and never consulted).

  Idempotent, keyed by title (the display names in `plotTitle`): a plot
  whose dimensions already match is left alone (only its dashboard index
  is re-asserted); a stale one is deleted and recreated (the plot PATCH
  endpoint only takes index/title/window, not dimensions). Unrecognized
  titles are untouched, so hand-pinned plots survive. A registry benchmark
  bencher hasn't seen yet (first upload still pending) is skipped with a
  warning and picked up on the next sync.

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

/-- A testbed minus its runner-arch suffix — the workload key the titles,
    skips, and ordering are written against. -/
def workloadOf (testbed : String) : String :=
  if testbed.endsWith "-x64-32x" then (testbed.dropEnd 8).toString
  else testbed

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
  | "aiur-check-prove", "prove-time"     => "Aiur Prove Time"
  | "aiur-check-prove", "throughput"     => "Aiur Prove Throughput"
  | "aiur-check-prove", "peak-rss"       => "Aiur Prove Peak RAM Usage"
  | "aiur-check-prove", "verify-time"    => "Aiur Verify Time"
  | "aiur-check-prove", "proof-size"     => "Aiur Proof Size"
  | "aiur-check-prove", "fft-cost"       => "Aiur FFT Cost"
  | "aiur-check-execute", "execute-time" => "Aiur Execute Time"
  | "aiur-check-execute", "throughput"   => "Aiur Execute Throughput"
  | "aiur-check-execute", "peak-rss"     => "Aiur Execute Peak RAM Usage"
  | "zisk-check-execute", "execute-time" => "Zisk Execute Time"
  | "zisk-check-execute", "throughput"   => "Zisk Execute Throughput"
  | "zisk-check-execute", "peak-rss"     => "Zisk Execute Peak RAM Usage"
  | "zisk-check-execute", "cycles"       => "Zisk Cycles"
  | "ooc-check", "check-time"            => "OOC Check Time"
  | "ooc-check", "throughput"            => "OOC Check Throughput"
  | "ooc-check", "peak-rss"              => "OOC Check Peak RAM Usage"
  | w, m => s!"{w}: {m}"

/-- Tracked but not plotted solo. The two aiur cells re-measure each
    other's deterministic Phase-1 numbers as a redundancy check — one
    trend line each is enough ("Aiur Execute Time" from the execute cell,
    "Aiur FFT Cost" from the prove cell). Zisk `shards` is a PR-comment
    column only ("Zisk Cycles" / max-shard-cycles carry the sharding
    trend), and zisk `constants` charts on the cross-kernel overlay below
    instead of alone. `ix-decompile` reuses the compile cell's `.ixe`, so
    its `file-size` / `constants` duplicate "Ix Environment Size" / "Ix
    Input Constants" exactly — the decompile cell tracks only its own
    decompile-time / throughput / peak-rss trends. -/
def plotSkips : List (String × String) :=
  [("aiur-check-prove", "execute-time"), ("aiur-check-execute", "fft-cost"),
   ("zisk-check-execute", "shards"), ("zisk-check-execute", "constants"),
   ("ix-decompile", "file-size"), ("ix-decompile", "constants")]

/-- Canonical units per measure slug, asserted on every sync: bencher
    auto-creates a measure with placeholder units ("Measure (units)") on
    its first upload, leaving plots unitless — and a console edit would
    drift from this list, so the sync re-asserts it. Phase spans are
    wall-clock seconds. -/
def unitsFor (slug : String) : Option String :=
  if slug.startsWith "phase-" then some "seconds (s)" else
  [("execute-peak-rss", "bytes (B)"),
   ("compile-time", "seconds (s)"),
   ("decompile-time", "seconds (s)"),
   ("execute-time", "seconds (s)"),
   ("prove-time", "seconds (s)"),
   ("verify-time", "seconds (s)"),
   ("check-time", "seconds (s)"),
   ("peak-rss", "bytes (B)"),
   ("file-size", "bytes (B)"),
   ("proof-size", "bytes (B)"),
   ("constants", "constants"),
   ("cycles", "cycles"),
   ("max-shard-cycles", "cycles"),
   ("shards", "shards"),
   ("fft-cost", "FFTs"),
   ("recursive-execute-time", "seconds (s)"),
   ("recursive-prove-time", "seconds (s)"),
   ("recursive-verify-time", "seconds (s)"),
   ("recursive-peak-rss", "bytes (B)"),
   ("recursive-proof-size", "bytes (B)"),
   ("recursive-fft-cost", "FFTs"),
   ("throughput", "constants / second")].lookup slug

/-- Dashboard group order (compile first, then aiur prove/execute, zisk,
    ooc); unranked workloads (a future backend) sort last. -/
def workloadOrder : List String :=
  ["ix-compile", "ix-decompile", "aiur-check-prove", "aiur-check-execute",
   "aiur-check-recursive", "aiur-recursive", "zisk-check-execute",
   "ooc-check"]

structure PlotSpec where
  testbed : String
  measures : List String
  benchmarks : Array String

/-- One spec per bench-main testbed: its measure slugs and the benchmark
    row names uploaded there, mirroring the row emitters — compile keys
    one row per env (benched or not: the compile matrix is deliberately
    wider), decompile one row per benched env (a `.ixe` consumer), ooc one
    whole-env row plus one full-closure row per primary,
    the per-constant backends one row per primary. Dynamic sub-rows
    (`<name>/shard-N`) are left out: their multiplicity shifts with the
    shard manifest, and the parent row carries the headline trend. -/
def plotSpecs (rows : Array BenchCmd.VectorRow) : Array PlotSpec := Id.run do
  let benched := (BenchCmd.envSpecs.filter (·.benched)).map (·.name)
  let mut specs : Array PlotSpec := #[]
  for b in BenchCmd.backendSpecs do
    if b.disabled.isSome then continue
    for (mode, testbed) in b.testbeds do
      let names : Array String := Id.run do
        if b.name == "compile" then
          return (BenchCmd.envSpecs.map (·.name)).toArray
        if b.name == "aiur-recursive" then
          return (BenchCmd.recursiveConfigs.map (·.1)).toArray
        -- decompile is env-keyed like compile but a `.ixe` consumer: one row
        -- per benched env (it runs only where a benched `.ixe` exists).
        if b.name == "decompile" then
          return benched.toArray
        let mut ns : Array String := #[]
        for env in benched do
          if b.name == "ooc" then ns := ns.push env
          ns := ns ++ (BenchCmd.selectNames rows env mode
            (full := false) (tier := "") (shardOnly := false)).map (·.name)
        return ns
      specs := specs.push
        { testbed, measures := b.metricsFor mode, benchmarks := names }
  return specs.qsort fun a b =>
    workloadOrder.idxOf (workloadOf a.testbed)
      < workloadOrder.idxOf (workloadOf b.testbed)

/-! ## bencher CLI plumbing -/

/-- Run the bencher CLI and parse its JSON stdout. -/
def bencherJson (args : Array String) : IO Json := do
  let r ← IO.Process.output { cmd := "bencher", args }
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
  let r ← IO.Process.output { cmd := "bencher", args }
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

/-- A plot as the sync wants it: everything already resolved to UUIDs. -/
structure DesiredPlot where
  title : String
  testbeds : Array String
  benchmarks : Array String
  measure : String

inductive Outcome | created | replaced | kept

/-- Create/keep/replace one plot. An existing plot matches by title; same
    dimensions (order-insensitively), window, and axis → keep, re-asserting
    only the dashboard index (the list JSON carries no index field, so it
    can't be diffed). Anything else is deleted and recreated. -/
def syncPlot (project : String) (dryRun : Bool) (window : Nat)
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
           == some window
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
      "--x-axis", xAxis, "--window", toString window,
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
  let csv := (p.flag? "csv").map (·.as! String)
    |>.getD "Benchmarks/Vectors.csv"
  let dryRun := p.hasFlag "dry-run"
  if !dryRun && (← IO.getEnv "BENCHER_API_KEY").isNone then
    p.printError "error: set BENCHER_API_KEY (or pass --dry-run)"
    return 2
  let specs := plotSpecs (BenchCmd.parseVectorsCsv (← IO.FS.readFile csv))

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
    let some testbedUuid := findUuid testbeds "slug" spec.testbed
      | p.printError s!"error: no testbed slug '{spec.testbed}'"; return 1
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
      let some measureUuid := findUuid measures "slug" measure
        | p.printError s!"error: no measure slug '{measure}'"; return 1
      desired := desired.push
        { title := plotTitle workload measure, testbeds := #[testbedUuid],
          benchmarks := benchUuids, measure := measureUuid }

  -- Cross-kernel input-constants overlay: aiur and zisk both report the
  -- named constants of the checked closure — the pre-shard input set,
  -- unaffected by anon-work dedup or shard partitioning — so the paired
  -- lines must coincide. Separation on this chart means the kernels'
  -- counts drifted apart (a coverage bug tripwire), on top of the count
  -- trend itself. Zisk lines render once its host uploads `constants`.
  let overlay : Option DesiredPlot := do
    let aiurTb ← findUuid testbeds "slug" "aiur-check-prove-x64-32x"
    let ziskTb ← findUuid testbeds "slug" "zisk-check-execute-x64-32x"
    let consts ← findUuid measures "slug" "constants"
    let primaries ← (specs.find? (·.testbed == "aiur-check-prove-x64-32x")).map
      (·.benchmarks.filterMap (findUuid benchmarks "name" ·))
    return { title := "Aiur/Zisk Input Constants",
             testbeds := #[aiurTb, ziskTb], benchmarks := primaries,
             measure := consts }
  match overlay with
  | some d => desired := desired.push d
  | none => do
    IO.eprintln
      "warn: input-constants overlay skipped (missing testbed or measure)"

  for d in desired do
    match ← syncPlot project dryRun window xAxis branchUuid plots idx d with
    | .created => created := created + 1
    | .replaced => replaced := replaced + 1
    | .kept => kept := kept + 1
    idx := idx + 1

  IO.println s!"plots: {created} created, {replaced} replaced, {kept} kept \
    → https://bencher.dev/console/projects/{project}/plots"
  return 0

end Ix.Cli.BenchPlots

open Ix.Cli.BenchPlots in
def benchPlotsCmd : Cli.Cmd := `[Cli|
  plots VIA runPlotsCmd;
  "Sync the bencher.dev dashboard plots to the registry: one plot per tracked (testbed, measure) plus the cross-kernel input-constants overlay. Needs the bencher CLI; writes need BENCHER_API_KEY (plot create/delete permission)."

  FLAGS:
    "dry-run";         "Print the create/replace/keep decisions without writing (no key needed)"
    project : String;  "Bencher project slug (default: ix)"
    branch  : String;  "Branch whose series the plots track (default: main)"
    window  : Nat;     "Seconds of history per plot (default: 7257600 = 12 weeks)"
    "x-axis" : String; "date_time | version (default: version)"
    csv     : String;  "Vectors path (default: Benchmarks/Vectors.csv)"
]
