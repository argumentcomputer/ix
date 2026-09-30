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

/-- Host observations recorded with every session. -/
def environment (cpu : Nat) : IO Json := do
  let model := ((← readProc "/proc/cpuinfo").splitOn "\n").find? (·.startsWith "model name") |>.getD ""
  let uname ← IO.Process.output { cmd := "uname", args := #["-srvm"] }
  return Json.mkObj [
    ("cpu_model", Json.str ((model.splitOn ":").getD 1 "").trimAscii.toString),
    ("worker_cpu", toJson cpu),
    ("worker_max_khz", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/cpuinfo_max_freq")),
    ("worker_siblings", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list")),
    ("governor", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor")),
    ("energy_preference", Json.str (← readProc s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/energy_performance_preference")),
    ("boost", Json.str (← readProc "/sys/devices/system/cpu/cpufreq/boost")),
    ("loadavg", Json.str (← readProc "/proc/loadavg")),
    ("kernel", Json.str uname.stdout.trimAscii.toString)]

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

/-- Choose repetitions per row and fixture: the pilot grows `reps` tenfold
until a chunk lasts 20 ms, then scales it to `targetMs`. -/
def calibrate (manifest : Manifest) (out : FilePath) (cpu targetMs : Nat) (only : Option (List String)) :
    IO Unit := do
  let mut plans : Array Json := #[]
  for fixture in manifest.fixtures.filter fun f => only.all (·.contains f.name) do
    for row in ← builtRows out true fixture do
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
      let warmup := max 1 (chosen / 10)
      plans := plans.push (Json.mkObj [("fixture", Json.str fixture.name), ("row", Json.str row.name),
        ("reps", toJson chosen), ("warmup", toJson warmup), ("pilot_ns_per_call", toJson per)])
      IO.println s!"{fixture.name} {row.name}: {fmtNs per} per call, reps {chosen}"
  IO.FS.writeFile (repsFile out) ((Json.mkObj [("format", Json.str "compilatrix/benchmark-entry-reps/1"),
    ("target_ms", toJson targetMs), ("worker_cpu", toJson cpu), ("plans", Json.arr plans)]).pretty ++ "\n")
where
  fmtNs (ns : Float) : String :=
    if ns ≥ 1e6 then s!"{(ns / 1e4).round / 100} ms" else if ns ≥ 1e3 then s!"{(ns / 10).round / 100} µs"
    else s!"{(ns * 100).round / 100} ns"

def loadPlans (out : FilePath) : IO (List (String × String × Plan)) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (repsFile out)))
  let plans ← IO.ofExcept ((json.getObjValD "plans").getArr?)
  plans.toList.mapM fun p => IO.ofExcept do
    return (← (p.getObjValD "fixture").getStr?, ← (p.getObjValD "row").getStr?,
      { reps := ← (p.getObjValD "reps").getNat?, warmup := ← (p.getObjValD "warmup").getNat?,
        pilotNs := (← (p.getObjValD "pilot_ns_per_call").getNum?).toFloat })

def planFor (plans : List (String × String × Plan)) (fixture : Fixture) (row : Row) : Option Plan :=
  (plans.find? fun (f, r, _) => f == fixture.name && r == row.name).map (·.2.2)

/-- The rows of a fixture with a binary and a plan. -/
def plannedRows (out : FilePath) (plans : List (String × String × Plan)) (fixture : Fixture) :
    IO (List (Row × Plan)) := do
  return (← builtRows out true fixture).filterMap fun row => (planFor plans fixture row).map (row, ·)

def measureEntry (manifest : Manifest) (out : FilePath) (cpu blocks : Nat) (only : Option (List String)) :
    IO Unit := do
  let plans ← loadPlans out
  let env ← environment cpu
  let mut samples : Array Json := #[]
  for (fixture, index) in (manifest.fixtures.filter fun f => only.all (·.contains f.name)).toList.zipIdx do
    let rows ← plannedRows out plans fixture
    if rows.isEmpty then continue
    let some want := fixture.benchExpected.map trimmed
      | throw (IO.userError s!"{fixture.name}: no bench_expected")
    -- one untimed process per row (page cache, binary loading)
    for (row, plan) in rows do
      let _ ← runEntry out (some cpu) row fixture 1 (min plan.warmup 1)
    for block in [:blocks] do
      let load ← readProc "/proc/loadavg"
      for (row, plan) in shuffle (block * 1000 + index) rows do
        let (result, ns, heap) ← runEntry out (some cpu) row fixture plan.reps plan.warmup
        unless result == want do
          throw (IO.userError s!"{row.name}/{fixture.name}: {result} differs from {want} in block {block}")
        samples := samples.push (Json.mkObj [("fixture", Json.str fixture.name), ("row", Json.str row.name),
          ("block", toJson block), ("reps", toJson plan.reps), ("warmup", toJson plan.warmup),
          ("ns_per_call", toJson ns), ("heap_bytes", match heap with | some h => toJson h | none => Json.null),
          ("loadavg", Json.str load)])
    IO.println s!"measured {fixture.name}: {blocks} blocks × {rows.length} rows"
  IO.FS.writeFile (out / "entry-samples.json") ((Json.mkObj [
    ("format", Json.str "compilatrix/benchmark-entry-samples/1"),
    ("environment", env), ("environment_end", ← environment cpu), ("blocks", toJson blocks),
    ("samples", Json.arr samples)]).pretty ++ "\n")

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
    (only : Option (List String)) : IO Unit := do
  let plans ← loadPlans out
  let mut rowsJson : Array Json := #[]
  for fixture in manifest.fixtures.filter fun f => only.all (·.contains f.name) do
    for (row, plan) in ← plannedRows out plans fixture do
      let mut perRun : Array (List (String × Option Float)) := #[]
      for _ in [:runs] do
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
