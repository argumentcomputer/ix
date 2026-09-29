import Runner.Build

/-! Paired, randomized block measurement on one pinned core.

Each block runs every row of a fixture once, in a shuffled order, at the
fixture's benchmark arguments. The worker process is pinned with `taskset`.
Within a block, every row must print the same output, which is a correctness
guard at benchmark size. Timing is whole-process wall time, so it includes
process and runtime startup; the benchmark arguments are sized for runs of
at least tens of milliseconds, and startup is part of every row alike. -/

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

/-- Host observations recorded with every session. -/
def environment (cpu : Nat) : IO Json := do
  let read (path : String) : IO String := do
    try return (← IO.FS.readFile path).trimAscii.toString catch _ => return "unavailable"
  let model := ((← read "/proc/cpuinfo").splitOn "\n").find? (·.startsWith "model name") |>.getD ""
  let uname ← IO.Process.output { cmd := "uname", args := #["-srvm"] }
  return Json.mkObj [
    ("cpu_model", Json.str ((model.splitOn ":").getD 1 "").trimAscii.toString),
    ("worker_cpu", toJson cpu),
    ("worker_max_khz", Json.str (← read s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/cpuinfo_max_freq")),
    ("governor", Json.str (← read s!"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor")),
    ("boost", Json.str (← read "/sys/devices/system/cpu/cpufreq/boost")),
    ("loadavg", Json.str (← read "/proc/loadavg")),
    ("kernel", Json.str uname.stdout.trimAscii.toString)]

def measure (manifest : Manifest) (out : FilePath) (cpu blocks : Nat)
    (only : Option (List String)) : IO Unit := do
  let fixtures := manifest.fixtures.filter fun f => only.all (·.contains f.name)
  let env ← environment cpu
  let mut samples : Array Sample := #[]
  for (fixture, index) in fixtures.toList.zipIdx do
    -- One untimed warm-up run per row (page cache, binary loading).
    for row in Row.all do
      let _ ← run "taskset" (["-c", toString cpu, (binary out row fixture).toString] ++ fixture.benchArgs)
    for block in [:blocks] do
      let mut outputs : List String := []
      for row in shuffle (block * 1000 + index) Row.all do
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
    ("environment", env), ("blocks", toJson blocks),
    ("samples", Json.arr (samples.map Sample.json))]).pretty ++ "\n")

end Runner
