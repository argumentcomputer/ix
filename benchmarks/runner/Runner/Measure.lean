import Runner.Build
import Runner.Stats

/-! Paired, randomized block measurement on one pinned core, in two profiles.

**Process profile** (`measure --profile process`, the default). Each block
runs every built row of a fixture once, in a shuffled order, at the
fixture's benchmark arguments. The worker process is pinned with `taskset`.
Within a block, every row must print the same output, which is a correctness
guard at benchmark size. Timing is whole-process wall time, so it includes
process and runtime startup.

**Entry profile** (`calibrate`, then `measure --profile entry`). Each block
runs every built entry row of a fixture once, in a shuffled order, as a
fresh pinned process that initialises the row once (Lean's runtime, the
compilatrix region and `cx_init`), makes `warmup` untimed calls and times
`reps` calls of the entry in one interval. `calibrate` chooses `reps` per
row and fixture in a pilot so that each timed chunk lasts about the target
(default 250 ms), and `warmup` as a tenth of it; startup is excluded, so
`tak` and `gcd` are no longer startup-dominated. Every result must equal
`bench_expected`. `perf` counts user-space instructions, cycles, branches
and branch misses per call: a run with `reps` calls minus a run with none
(the same setup and warm-up), the median of `--runs` such pairs. -/

namespace Runner

open Lean System

structure Sample where
  fixture : String
  row : String
  block : Nat
  nanos : Nat

def Sample.json (s : Sample) : Json :=
  Json.mkObj [("fixture", Json.str s.fixture), ("row", Json.str s.row),
    ("block", toJson s.block), ("ns", toJson s.nanos)]

/-- Deterministic shuffle (xorshift over the block and fixture index). -/
def shuffle (seed : Nat) (items : List α) : List α := Id.run do
  let mut state : UInt64 := 0x9e3779b97f4a7c15 ^^^ seed.toUInt64
  let mut array := items.toArray
  for i in [:array.size] do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 7)
    state := state ^^^ (state <<< 17)
    let j := i + (state.toNat % (array.size - i))
    array := array.swapIfInBounds i j
  return array.toList

def readProc (path : String) : IO String := do
  try return (← IO.FS.readFile path).trimAscii.toString catch _ => return "unavailable"

/-- Whether mains power is online (`1`, `0`), from the power-supply class. -/
def acOnline : IO String := do
  let root : FilePath := "/sys/class/power_supply"
  try
    for entry in ← root.readDir do
      if (← readProc (entry.path / "type").toString) == "Mains" then
        return ← readProc (entry.path / "online").toString
    return "no mains supply listed"
  catch _ => return "unavailable"

/-- Host observations recorded with every session. -/
def environment (cpu : Nat) : IO Json := do
  let model := ((← readProc "/proc/cpuinfo").splitOn "\n").find? (·.startsWith "model name") |>.getD ""
  let uname ← IO.Process.output { cmd := "uname", args := #["-srvm"] }
  return Json.mkObj [
    ("cpu_model", Json.str ((model.splitOn ":").getD 1 "").trimAscii.toString),
    ("worker_cpu", toJson cpu),
    ("worker_max_khz", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/cpuinfo_max_freq")),
    ("worker_cur_khz", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_cur_freq")),
    ("worker_siblings", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list")),
    ("governor", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor")),
    ("energy_preference", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/energy_performance_preference")),
    ("platform_profile", Json.str (← readProc "/sys/firmware/acpi/platform_profile")),
    ("ac_online", Json.str (← acOnline)),
    ("boost", Json.str (← readProc "/sys/devices/system/cpu/cpufreq/boost")),
    ("loadavg", Json.str (← readProc "/proc/loadavg")),
    ("kernel", Json.str uname.stdout.trimAscii.toString)]

/-- `--rows`: row names, or a prefix ending in `*` (`compilatrix@*`). -/
def rowSelected (spec : Option (List String)) (row : Row) : Bool :=
  spec.all fun names => names.any fun s =>
    s == row.name || (s.endsWith "*" && row.name.startsWith (s.dropEnd 1).toString)

def measureProcess (manifest : Manifest) (out : FilePath) (cpu blocks : Nat)
    (only : Option (List String)) : IO Unit := do
  let fixtures := manifest.fixtures.filter fun f => only.all (·.contains f.name)
  let env ← environment cpu
  let mut samples : Array Sample := #[]
  for (fixture, index) in fixtures.toList.zipIdx do
    let rows ← builtRows out false fixture
    if rows.isEmpty then continue
    -- One untimed warm-up run per row (page cache, binary loading).
    for row in rows do
      let _ ← run "taskset" (["-c", toString cpu, (binary out row fixture).toString] ++ fixture.benchArgs)
    for block in [:blocks] do
      let mut outputs : List String := []
      for row in shuffle (block * 1000 + index) rows do
        let start ← IO.monoNanosNow
        let output ← run "taskset" (["-c", toString cpu, (binary out row fixture).toString] ++ fixture.benchArgs)
        let stop ← IO.monoNanosNow
        outputs := output.stdout :: outputs
        samples := samples.push { fixture := fixture.name, row := row.name, block, nanos := stop - start }
      unless outputs.all (· == outputs.headD "") do
        throw (IO.userError s!"{fixture.name}: rows disagree at benchmark size in block {block}")
    IO.println s!"measured {fixture.name}: {blocks} blocks"
  IO.FS.writeFile (out / "samples.json") ((Json.mkObj [
    ("format", Json.str "compilatrix/benchmark-samples/1"),
    ("environment", env), ("environment_end", ← environment cpu), ("blocks", toJson blocks),
    ("samples", Json.arr (samples.map Sample.json))]).pretty ++ "\n")

/-! ## Entry profile -/

/-- One timed run of an entry binary: `(result, ns per call, heap bytes)`. -/
def runEntry (out : FilePath) (cpu : Option Nat) (row : Row) (fixture : Fixture) (reps warmup : Nat) :
    IO (String × Float × Option Nat) := do
  let exe := (entryBinary out row fixture).toString
  let args := [toString reps, toString warmup] ++ fixture.benchArgs
  let output ← match cpu with
    | some c => run "taskset" (["-c", toString c, exe] ++ args)
    | none => run exe args
  match (trimmed output.stdout).splitOn " " with
  | [_, result, ns, _, heap] =>
    match (Json.parse ns).toOption.bind (·.getNum?.toOption) with
    | some t =>
      let heap := heap.toNat?.bind fun h => if h == 18446744073709551615 then none else some h
      return (result, t.toFloat, heap)
    | none => throw (IO.userError s!"{row.name}/{fixture.name}: malformed output {output.stdout}")
  | _ => throw (IO.userError s!"{row.name}/{fixture.name}: malformed output {output.stdout}")

structure Plan where
  reps : Nat
  warmup : Nat
  pilotNs : Float

def repsFile (out : FilePath) : FilePath := out / "entry-reps.json"

def loadPlans (out : FilePath) : IO (List (String × String × Plan)) := do
  unless ← (repsFile out).pathExists do return []
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (repsFile out)))
  let plans ← IO.ofExcept ((json.getObjValD "plans").getArr?)
  plans.toList.mapM fun p => IO.ofExcept do
    return (← (p.getObjValD "fixture").getStr?, ← (p.getObjValD "row").getStr?,
      { reps := ← (p.getObjValD "reps").getNat?, warmup := ← (p.getObjValD "warmup").getNat?,
        pilotNs := (← (p.getObjValD "pilot_ns_per_call").getNum?).toFloat })

def fmtPilot (ns : Float) : String :=
  if ns ≥ 1e6 then s!"{(ns / 1e4).round / 100} ms" else if ns ≥ 1e3 then s!"{(ns / 10).round / 100} µs"
  else s!"{(ns * 100).round / 100} ns"

/-- Choose repetitions per row and fixture: the pilot grows `reps` tenfold
until a chunk lasts 20 ms, then scales it to `targetMs`. Plans for rows
outside the selection are kept. -/
def calibrate (manifest : Manifest) (out : FilePath) (cpu targetMs : Nat) (only rows : Option (List String)) :
    IO Unit := do
  let mut plans := (← loadPlans out).toArray
  for fixture in manifest.fixtures.filter fun f => only.all (·.contains f.name) do
    for row in (← builtRows out true fixture).filter (rowSelected rows) do
      let mut reps := 1
      let mut per := 0.0
      repeat
        let mut best := 0.0
        for i in [:3] do
          let (_, ns, _) ← runEntry out (some cpu) row fixture reps 1
          if i == 0 || ns < best then best := ns
        per := best
        if per * reps.toFloat ≥ 2e7 || reps ≥ 1000000000 then break
        reps := reps * 10
      let chosen := max 1 ((targetMs.toFloat * 1e6 / per).ceil.toUInt64.toNat)
      plans := (plans.filter fun (f, r, _) => !(f == fixture.name && r == row.name)).push
        (fixture.name, row.name, { reps := chosen, warmup := max 1 (chosen / 10), pilotNs := per })
      IO.println s!"{fixture.name} {row.name}: {fmtPilot per} per call, reps {chosen}"
  let json := plans.map fun (f, r, p) => Json.mkObj [("fixture", Json.str f), ("row", Json.str r),
    ("reps", toJson p.reps), ("warmup", toJson p.warmup), ("pilot_ns_per_call", toJson p.pilotNs)]
  IO.FS.writeFile (repsFile out) ((Json.mkObj [("format", Json.str "compilatrix/benchmark-entry-reps/1"),
    ("target_ms", toJson targetMs), ("worker_cpu", toJson cpu), ("plans", Json.arr json)]).pretty ++ "\n")

def planFor (plans : List (String × String × Plan)) (fixture : Fixture) (row : Row) : Option Plan :=
  (plans.find? fun (f, r, _) => f == fixture.name && r == row.name).map (·.2.2)

/-- The selected rows of a fixture with a binary and a plan. -/
def plannedRows (out : FilePath) (plans : List (String × String × Plan)) (rows : Option (List String))
    (fixture : Fixture) : IO (List (Row × Plan)) := do
  return ((← builtRows out true fixture).filter (rowSelected rows)).filterMap fun row =>
    (planFor plans fixture row).map (row, ·)

/-! ## Quiet blocks

A shared development machine runs builds next to a session. Busy time per
CPU comes from `/proc/stat`: a block is *quiet* when, over its whole
duration, the worker's SMT siblings were busy at most 10% of the time and at
most `maxBusy` other CPUs were busy more than half the time. With a gate,
`measure` waits (polling every 10 s, up to `maxWaitS` per block) for a quiet
second before a block, and a block that was not quiet is kept with its
reason, marked invalid, and run again (up to `attempts` times). -/

structure Gate where
  maxBusy : Nat := 1
  maxWaitS : Nat := 1800
  attempts : Nat := 5

/-- Per-CPU `(busy, total)` jiffies from `/proc/stat`. -/
def cpuTimes : IO (List (Nat × Nat × Nat)) := do
  let text ← readProc "/proc/stat"
  return (text.splitOn "\n").filterMap fun line =>
    match (line.splitOn " ").filter (!·.isEmpty) with
    | name :: fields =>
      if name.startsWith "cpu" && name.length > 3 then
        match (name.drop 3).toString.toNat?, fields.mapM String.toNat? with
        | some n, some vs =>
          let total := vs.take 8 |>.foldl (· + ·) 0
          let idle := vs.getD 3 0 + vs.getD 4 0
          some (n, total - idle, total)
        | _, _ => none
      else none
    | [] => none

/-- The worker's SMT siblings (`2,14` or `2-3`), without the worker. -/
def siblings (cpu : Nat) : IO (List Nat) := do
  let text ← readProc s!"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list"
  let parts := text.splitOn ","
  let cpus := parts.flatMap fun p => match p.splitOn "-" with
    | [a, b] => match a.toNat?, b.toNat? with
      | some x, some y => List.range (y + 1 - x) |>.map (· + x)
      | _, _ => []
    | [a] => a.toNat?.toList
    | _ => []
  return cpus.filter (· != cpu)

/-- Busy fractions between two snapshots: the siblings' largest, and how many
other CPUs (not the worker, its siblings or `controller`) were over half busy. -/
def busyBetween (worker : Nat) (sibs : List Nat) (controller : Option Nat)
    (before after : List (Nat × Nat × Nat)) : Float × Nat :=
  let fracs := after.filterMap fun (n, b1, t1) =>
    (before.find? (·.1 == n)).map fun (_, b0, t0) =>
      (n, if t1 > t0 then (b1 - b0).toFloat / (t1 - t0).toFloat else 0.0)
  let sib := (fracs.filter fun (n, _) => sibs.contains n).foldl (fun m (_, f) => max m f) 0.0
  let others := (fracs.filter fun (n, f) => n != worker && !sibs.contains n && controller != some n && f > 0.5).length
  (sib, others)

def Gate.quiet (g : Gate) (sibling : Float) (others : Nat) : Bool := sibling ≤ 0.10 && others ≤ g.maxBusy

/-- The controller's own CPU, when it is pinned to one. -/
def controllerCpu : IO (Option Nat) := do
  let status ← readProc "/proc/self/status"
  let line := (status.splitOn "\n").find? (·.startsWith "Cpus_allowed_list:") |>.getD ""
  return ((line.splitOn ":").getD 1 "").trimAscii.toString.toNat?

/-- Wait for a quiet second; the seconds waited. -/
def waitQuiet (g : Gate) (cpu : Nat) (sibs : List Nat) (controller : Option Nat) : IO Nat := do
  let mut waited := 0
  repeat
    let t0 ← cpuTimes
    IO.sleep 1000
    let t1 ← cpuTimes
    let (sib, others) := busyBetween cpu sibs controller t0 t1
    if g.quiet sib others || waited ≥ g.maxWaitS then break
    IO.sleep 9000
    waited := waited + 10
  return waited

def measureEntry (manifest : Manifest) (out : FilePath) (cpu blocks : Nat) (only rows : Option (List String))
    (gate : Option Gate := none) : IO Unit := do
  let plans ← loadPlans out
  let env ← environment cpu
  let sibs ← siblings cpu
  let controller ← controllerCpu
  let mut samples : Array Json := #[]
  let mut invalid := 0
  for (fixture, index) in (manifest.fixtures.filter fun f => only.all (·.contains f.name)).toList.zipIdx do
    let rows ← plannedRows out plans rows fixture
    if rows.isEmpty then continue
    let some want := fixture.benchExpected.map trimmed
      | throw (IO.userError s!"{fixture.name}: no bench_expected")
    -- one untimed process per row (page cache, binary loading)
    for (row, plan) in rows do
      let _ ← runEntry out (some cpu) row fixture 1 (min plan.warmup 1)
    for block in [:blocks] do
      let mut attempt := 0
      repeat
        let waited ← match gate with
          | some g => waitQuiet g cpu sibs controller
          | none => pure 0
        let load ← readProc "/proc/loadavg"
        let t0 ← cpuTimes
        let mut results : Array (Row × Plan × Float × Option Nat) := #[]
        for (row, plan) in shuffle (block * 1000 + index) rows do
          let (result, ns, heap) ← runEntry out (some cpu) row fixture plan.reps plan.warmup
          unless result == want do
            throw (IO.userError s!"{row.name}/{fixture.name}: {result} differs from {want} in block {block}")
          results := results.push (row, plan, ns, heap)
        let (sib, others) := busyBetween cpu sibs controller t0 (← cpuTimes)
        let quiet := (gate.getD {}).quiet sib others
        let valid := gate.isNone || quiet || attempt + 1 ≥ (gate.getD {}).attempts
        let reason := if quiet then "" else
          s!"siblings busy {(sib * 1000).round / 10}%, {others} other CPUs over half busy"
        for (row, plan, ns, heap) in results do
          samples := samples.push (Json.mkObj [("fixture", Json.str fixture.name), ("row", Json.str row.name),
            ("block", toJson block), ("attempt", toJson attempt), ("reps", toJson plan.reps),
            ("warmup", toJson plan.warmup), ("ns_per_call", toJson ns),
            ("heap_bytes", match heap with | some h => toJson h | none => Json.null),
            ("loadavg", Json.str load), ("waited_s", toJson waited),
            ("sibling_busy", toJson sib), ("other_busy_cpus", toJson others), ("quiet", toJson quiet),
            ("valid", toJson valid), ("reason", Json.str reason)])
        -- an invalid attempt is kept, and the block runs again
        if valid then break
        invalid := invalid + 1
        attempt := attempt + 1
    IO.println s!"measured {fixture.name}: {blocks} blocks × {rows.length} rows"
  IO.FS.writeFile (out / "entry-samples.json") ((Json.mkObj [
    ("format", Json.str "compilatrix/benchmark-entry-samples/2"),
    ("environment", env), ("environment_end", ← environment cpu), ("blocks", toJson blocks),
    ("gate", match gate with
      | some g => Json.mkObj [("max_busy", toJson g.maxBusy), ("max_wait_s", toJson g.maxWaitS),
          ("attempts", toJson g.attempts), ("sibling_max", toJson 0.10)]
      | none => Json.null),
    ("invalid_attempts", toJson invalid),
    ("samples", Json.arr samples)]).pretty ++ "\n")
  IO.println s!"invalid block attempts: {invalid}"

/-! ## Counters -/

/-- `perf stat -x,` lines: `value,unit,event,...`; a counter perf could not
read is `none`. -/
def counters (text : String) : List (String × Option Nat) :=
  (text.splitOn "\n").filterMap fun line =>
    match line.splitOn "," with
    | value :: _ :: event :: _ =>
        if event.isEmpty then none
        else some ((event.splitOn ":").headD event, value.toNat?)
    | _ => none

def events : List String := ["instructions", "cycles", "branches", "branch-misses"]

def perfStat (perf : String) (out : FilePath) (cpu : Nat) (row : Row) (fixture : Fixture) (reps warmup : Nat) :
    IO (List (String × Option Nat)) := do
  let output ← run perf (["stat", "-x,", "-e", ",".intercalate (events.map (· ++ ":u")), "--",
    "taskset", "-c", toString cpu, (entryBinary out row fixture).toString, toString reps, toString warmup] ++
    fixture.benchArgs)
  return counters output.stderr

def perfAll (manifest : Manifest) (out : FilePath) (cpu : Nat) (perf : String) (runs : Nat)
    (only rows : Option (List String)) (gate : Option Gate := none) : IO Unit := do
  let plans ← loadPlans out
  let sibs ← siblings cpu
  let controller ← controllerCpu
  let mut rowsJson : Array Json := #[]
  for fixture in manifest.fixtures.filter fun f => only.all (·.contains f.name) do
    let planned ← plannedRows out plans rows fixture
    if planned.isEmpty then continue
    for (row, plan) in planned do
      let mut perRun : Array (List (String × Option Float)) := #[]
      for _ in [:runs] do
        if let some g := gate then
          let _ ← waitQuiet g cpu sibs controller
        let full ← perfStat perf out cpu row fixture plan.reps plan.warmup
        let none' ← perfStat perf out cpu row fixture 0 plan.warmup
        perRun := perRun.push (events.map fun event =>
          let value := (full.find? (·.1 == event)).bind (·.2)
          let base := (none'.find? (·.1 == event)).bind (·.2)
          (event, match value, base with
            | some v, some b => some ((v.toFloat - b.toFloat) / plan.reps.toFloat)
            | _, _ => none))
      let fields := events.map fun event =>
        let values := perRun.filterMap fun r => (r.find? (·.1 == event)).bind (·.2)
        (event, if values.size == perRun.size && !values.isEmpty then toJson (median values)
          else Json.str "unavailable")
      rowsJson := rowsJson.push (Json.mkObj ([("fixture", Json.str fixture.name), ("row", Json.str row.name),
        ("reps", toJson plan.reps), ("runs", toJson runs)] ++ fields))
    IO.println s!"counted {fixture.name}"
  IO.FS.writeFile (out / "entry-perf.json") ((Json.arr rowsJson).pretty ++ "\n")

end Runner
