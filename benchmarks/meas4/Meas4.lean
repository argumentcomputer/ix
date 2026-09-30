import Lean.Data.Json

/-!
# MEAS-4 early probe (roadmap MEAS-4, note 05 §12, Phase 1 item M1.B6)

Measures the synthetic Lir kernels `fib`, `sum-loop` and `gcd`, compiled
natively by Compilatr.ix, against C twins and Lean's own compiler. These
are backend probes, never real-program results (roadmap §9).

| Row | Build |
| --- | --- |
| `compilatrix-probe` | `backend-probe`'s objects (`Backend.compile` of `CompilatrixTests/Lir/Kernels.lean`), called through their SysV export wrappers |
| `clang-twin` | `twins.c`'s tagged twins (the kernels' representation and overflow checks) at `-O2` |
| `lean-clang` | `K1Probe.lean` (the K1 definitions of the fixtures) through `lean -c` and `leanc -O3 -DNDEBUG` |
| `clang-natural` | the fixtures' untagged algorithms at `-O2`, for reference (`sum-loop` folds to a closed form) |

Every row links the same timing driver (`driver.c`) and an adapter
(`row_*.c`); timing is in-process (the benchmark design's entry profile),
so process and runtime startup are excluded.

Run from the repository root in `nix develop`, after `lake build backend-probe`:

```sh
lean --run benchmarks/meas4/Meas4.lean build OUT
lean --run benchmarks/meas4/Meas4.lean check OUT
taskset -c 5 lean --run benchmarks/meas4/Meas4.lean measure OUT --cpu 2 --blocks 20
lean --run benchmarks/meas4/Meas4.lean perf OUT --cpu 2 --perf PERF   # optional
lean --run benchmarks/meas4/Meas4.lean report OUT
```

`build` takes `--probe PATH` (default `.lake/build/bin/backend-probe`) and
uses `cc` for C, `lean` and `leanc` for the Lean row, and `objdump` and `nm`
for code size and static counts. `measure` runs one untimed warm-up per row
and kernel, then blocks; each block runs every row once in a shuffled order,
pinned with `taskset`, and fails if the rows' results differ. `perf` counts
user-space instructions, cycles, branches and branch misses per operation
(a run with the repetitions minus a run with none); an unavailable counter
is recorded as unavailable, not as zero. `report` gives per kernel the
median ns/op, the ratio of each row to `clang-twin` and to `lean-clang`
with a 95% percentile-bootstrap interval over paired blocks (as the runner
does), the counters, code size and static counts, and compile times.
-/

open Lean System

namespace Meas4

/-! ## Rows and kernels -/

def rows : List String := ["compilatrix-probe", "clang-twin", "lean-clang", "clang-natural"]

structure Kernel where
  name : String
  /-- The Lir kernel's name, and the symbols of the twins and of Lean's code. -/
  lir : String
  twin : String
  natural : String
  lean : List String
  args : List Nat
  reps : Nat
  expected : Nat
  /-- What one operation is, for the report. -/
  op : String

def fibNat (n : Nat) : Nat := Id.run do
  let mut (a, b) := (0, 1)
  for _ in [:n] do (a, b) := (b, a + b)
  return a

def kernels : List Kernel := [
  { name := "fib", lir := "fib", twin := "twin_fib", natural := "natural_fib", lean := ["K1_fib"],
    args := [30], reps := 100, expected := fibNat 30,
    op := s!"fib 30 ({2 * fibNat 31 - 1} calls)" },
  { name := "sum_loop", lir := "sumLoop", twin := "twin_sum_loop", natural := "natural_sum_loop",
    lean := ["K1_sumLoop"], args := [10000000], reps := 40, expected := 10000000 * 9999999 / 2,
    op := "sum-loop 10^7 (10^7 iterations)" },
  { name := "gcd", lir := "gcd", twin := "twin_gcd", natural := "natural_gcd", lean := ["K1_gcd"],
    args := [fibNat 92, fibNat 91], reps := 100000, expected := 1,
    op := "gcd (F 92) (F 91) (91 divisions)" }]

/-! ## Processes -/

def run (cmd : String) (args : List String) (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let output ← IO.Process.output { cmd, args := args.toArray, cwd, env }
  if output.exitCode != 0 then
    throw (IO.userError s!"{cmd} {" ".intercalate args} exited {output.exitCode}:\n{output.stdout}{output.stderr}")
  return output

/-- How C is compiled: clang at `-O2`, with the nixpkgs cc wrapper's
hardening off (`NIX_HARDENING_ENABLE` empty) and its frame pointers
overridden. -/
def ccFlags : List String :=
  ["-O2", "-fomit-frame-pointer", "-momit-leaf-frame-pointer", "-Wall", "-Wextra", "-Werror"]
def ccEnv : Array (String × Option String) := #[("NIX_HARDENING_ENABLE", some "")]

def firstLine (cmd : String) (args : List String) : IO String := do
  let output ← IO.Process.output { cmd, args := args.toArray }
  return ((output.stdout ++ output.stderr).splitOn "\n").headD "" |>.trimAscii.toString

def binary (out : FilePath) (row : String) : FilePath := out / "bin" / row

/-- Run a row on a kernel: `(result, ns per operation)`. -/
def runRow (out : FilePath) (cpu : Option Nat) (row : String) (k : Kernel) (reps : Nat) : IO (Nat × Float) := do
  let exe := (binary out row).toString
  let args := [k.name, toString reps] ++ k.args.map toString
  let output ← match cpu with
    | some c => run "taskset" (["-c", toString c, exe] ++ args)
    | none => run exe args
  match (output.stdout.trimAscii.toString.splitOn " ") with
  | [_, _, result, ns, _] =>
      match result.toNat?, (Json.parse ns).toOption.bind (·.getNum?.toOption) with
      | some r, some t => return (r, t.toFloat)
      | _, _ => throw (IO.userError s!"{row} {k.name}: malformed output {output.stdout}")
  | _ => throw (IO.userError s!"{row} {k.name}: malformed output {output.stdout}")

/-! ## Build -/

/-- Instructions of `symbol` in an Intel-syntax `objdump -d` listing. -/
def functionLines (dump symbol : String) : List String :=
  let lines := dump.splitOn "\n"
  let body := (lines.dropWhile (fun l => !l.endsWith s!"<{symbol}>:")).drop 1
  (body.takeWhile (fun l => !l.trimAscii.isEmpty)).filter (·.contains "\t")

def instruction (line : String) : String := ((line.splitOn "\t").getLast?.getD "").trimAscii.toString

def isReg (operand : String) : Bool :=
  let o := operand.trimAscii.toString
  !o.contains '[' && !o.startsWith "0x" && !(o.toList.all Char.isDigit) && !o.isEmpty

/-- Static counts: instructions, register moves, `rsp`-relative stores and
loads, pushes and pops. -/
def staticCounts (lines : List String) : Json :=
  let insns := lines.map instruction
  let count (p : String → Bool) := (insns.filter p).length
  let operands (i : String) : List String :=
    ((i.splitOn " ").drop 1 |> " ".intercalate |>.splitOn ",").map (·.trimAscii.toString)
  let mnemonic (i : String) : String := (i.splitOn " ").headD ""
  Json.mkObj [
    ("instructions", toJson insns.length),
    ("reg_moves", toJson (count fun i => mnemonic i == "mov" && (operands i).all isReg)),
    ("stack_stores", toJson (count fun i => mnemonic i == "mov" && ((operands i).headD "").contains "[rsp")),
    ("stack_loads", toJson (count fun i => mnemonic i == "mov" && ((operands i).getD 1 "").contains "[rsp")),
    ("push_pop", toJson (count fun i => mnemonic i == "push" || mnemonic i == "pop"))]

/-- `nm -S` sizes of defined text symbols. -/
def symbolSizes (nm : String) : List (String × Nat) :=
  (nm.splitOn "\n").filterMap fun line =>
    match line.splitOn " " with
    | [_, size, kind, name] =>
        if kind == "T" || kind == "t" then
          some (name, size.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat
            else c.toLower.toNat - 'a'.toNat + 10)) 0)
        else none
    | _ => none

def build (out probe : FilePath) : IO Unit := do
  let here : FilePath := "benchmarks/meas4"
  IO.FS.createDirAll out
  let out ← IO.FS.realPath out
  let obj := out / "obj"
  IO.FS.createDirAll obj
  IO.FS.createDirAll (out / "bin")
  IO.FS.createDirAll (out / "asm")
  -- the Compilatrix objects and their static counts and compile times
  let probed ← run probe.toString [obj.toString, "--reps", "50"]
  IO.FS.writeFile (out / "probe.jsonl") probed.stdout
  -- Plain clang -O2: without the nixpkgs wrapper's hardening (zeroing
  -- call-used registers, stack protectors, fortify) and frame pointers,
  -- which upstream clang does not add at -O2 either.
  let cc (args : List String) := run "cc" (ccFlags ++ args) (env := ccEnv)
  let _ ← cc ["-c", (here / "driver.c").toString, "-o", (obj / "driver.o").toString]
  let _ ← cc ["-c", (here / "twins.c").toString, "-o", (obj / "twins.o").toString]
  let _ ← cc ["-c", (here / "row_twin.c").toString, "-o", (obj / "row_twin.o").toString]
  let _ ← cc ["-DNATURAL", "-c", (here / "row_twin.c").toString, "-o", (obj / "row_natural.o").toString]
  let _ ← cc ["-c", (here / "row_compilatrix.c").toString, "-o", (obj / "row_compilatrix.o").toString]
  let lirs := kernels.map fun k => (obj / s!"lir_{k.lir}.o").toString
  let _ ← cc (["-o", (binary out "compilatrix-probe").toString, (obj / "driver.o").toString,
    (obj / "row_compilatrix.o").toString] ++ lirs)
  let _ ← cc ["-o", (binary out "clang-twin").toString, (obj / "driver.o").toString,
    (obj / "row_twin.o").toString, (obj / "twins.o").toString]
  let _ ← cc ["-o", (binary out "clang-natural").toString, (obj / "driver.o").toString,
    (obj / "row_natural.o").toString, (obj / "twins.o").toString]
  -- the Lean row, as the runner builds lean-clang
  let _ ← run "lean" ["-c", (obj / "K1Probe.c").toString, "K1Probe.lean"] (cwd := some here)
  let _ ← run "leanc" ["-O3", "-DNDEBUG", "-c", (obj / "K1Probe.c").toString, "-o", (obj / "K1Probe.o").toString]
  let _ ← run "leanc" ["-O2", "-c", (here / "row_lean.c").toString, "-o", (obj / "row_lean.o").toString]
  let _ ← run "leanc" ["-o", (binary out "lean-clang").toString, (obj / "driver.o").toString,
    (obj / "row_lean.o").toString, (obj / "K1Probe.o").toString]
  -- disassembly, sizes and static counts of each row's kernel code
  let dump (o : String) : IO String := do
    let text := (← run "objdump" ["-d", "-M", "intel", "--no-show-raw-insn", (obj / o).toString]).stdout
    IO.FS.writeFile (out / "asm" / (o ++ ".txt")) text
    return text
  let nm (o : String) : IO (List (String × Nat)) := do
    return symbolSizes (← run "nm" ["-S", (obj / o).toString]).stdout
  let twinDump ← dump "twins.o"
  let twinSizes ← nm "twins.o"
  let leanDump ← dump "K1Probe.o"
  let leanSizes ← nm "K1Probe.o"
  let mut code : Array Json := #[]
  for k in kernels do
    let lirDump ← dump s!"lir_{k.lir}.o"
    let sized (sizes : List (String × Nat)) (names : List String) : Nat :=
      (sizes.filter fun (n, _) => names.contains n).foldl (· + ·.2) 0
    -- Lean's code: the exported entry's callees are specialised helpers
    -- named after the definition.
    let leanNames := leanSizes.filter (fun (n, _) => k.lean.any fun s => (n.splitOn s).length > 1) |>.map (·.1)
    code := code.push (Json.mkObj [("kernel", Json.str k.name),
      ("compilatrix-probe", Json.mkObj [("object_text", toJson ((symbolSizes (← run "nm" ["-S", (obj / s!"lir_{k.lir}.o").toString]).stdout).foldl (· + ·.2) 0)),
        ("static_object", staticCounts (functionLines lirDump s!"lir_{k.lir}"))]),
      ("clang-twin", Json.mkObj [("bytes", toJson (sized twinSizes [k.twin])),
        ("static", staticCounts (functionLines twinDump k.twin))]),
      ("clang-natural", Json.mkObj [("bytes", toJson (sized twinSizes [k.natural])),
        ("static", staticCounts (functionLines twinDump k.natural))]),
      ("lean-clang", Json.mkObj [("bytes", toJson (sized leanSizes leanNames)),
        ("symbols", toJson leanNames),
        ("static", staticCounts (leanNames.flatMap (functionLines leanDump ·)))])])
  IO.FS.writeFile (out / "code.json") ((Json.arr code).pretty ++ "\n")
  let versions := Json.mkObj [
    ("cc", Json.str (← firstLine "cc" ["--version"])),
    ("lean", Json.str (← firstLine "lean" ["--version"])),
    ("leanc", Json.str (← firstLine "leanc" ["--version"])),
    ("objdump", Json.str (← firstLine "objdump" ["--version"]))]
  IO.FS.writeFile (out / "build.json") ((Json.mkObj [("format", Json.str "compilatrix/meas4-build/1"),
    ("rows", toJson rows), ("versions", versions), ("cc_flags", toJson ccFlags),
    ("cc_env", Json.str "NIX_HARDENING_ENABLE="),
    ("lean_flags", Json.str "lean -c; leanc -O3 -DNDEBUG (K1Probe.c), leanc -O2 (row_lean.c)")]).pretty ++ "\n")
  IO.println s!"built {rows.length} rows into {out}"

/-! ## Check -/

def check (out : FilePath) : IO Unit := do
  for k in kernels do
    for row in rows do
      let (result, _) ← runRow out none row k 1
      unless result == k.expected do
        throw (IO.userError s!"{row} {k.name}: {result}, expected {k.expected}")
  IO.println s!"checked {kernels.length} kernels × {rows.length} rows"

/-! ## Measure (the runner's shuffle and host record) -/

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

def measure (out : FilePath) (cpu blocks : Nat) : IO Unit := do
  let env ← environment cpu
  let mut samples : Array Json := #[]
  for (k, index) in kernels.zipIdx do
    for row in rows do
      let _ ← runRow out (some cpu) row k k.reps
    for block in [:blocks] do
      for row in shuffle (block * 1000 + index) rows do
        let (result, ns) ← runRow out (some cpu) row k k.reps
        unless result == k.expected do
          throw (IO.userError s!"{row} {k.name}: {result} differs from {k.expected} in block {block}")
        samples := samples.push (Json.mkObj [("kernel", Json.str k.name), ("row", Json.str row),
          ("block", toJson block), ("reps", toJson k.reps), ("ns_per_op", toJson ns)])
    IO.println s!"measured {k.name}: {blocks} blocks"
  IO.FS.writeFile (out / "samples.json") ((Json.mkObj [
    ("format", Json.str "compilatrix/meas4-samples/1"), ("environment", env), ("blocks", toJson blocks),
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

def perfStat (perf : String) (out : FilePath) (cpu : Nat) (row : String) (k : Kernel) (reps : Nat) :
    IO (List (String × Option Nat)) := do
  let output ← run perf (["stat", "-x,", "-e", "instructions:u,cycles:u,branches:u,branch-misses:u", "--",
    "taskset", "-c", toString cpu, (binary out row).toString, k.name, toString reps] ++ k.args.map toString)
  return counters output.stderr

def perfAll (out : FilePath) (cpu : Nat) (perf : String) : IO Unit := do
  let mut rowsJson : Array Json := #[]
  for k in kernels do
    for row in rows do
      let full ← perfStat perf out cpu row k k.reps
      let none' ← perfStat perf out cpu row k 0
      let perOp := full.map fun (event, value) =>
        let base := (none'.find? (·.1 == event)).bind (·.2)
        (event, match value, base with
          | some v, some b => toJson ((v.toFloat - b.toFloat) / k.reps.toFloat)
          | _, _ => Json.str "unavailable")
      rowsJson := rowsJson.push (Json.mkObj ([("kernel", Json.str k.name), ("row", Json.str row)] ++ perOp))
  IO.FS.writeFile (out / "perf.json") ((Json.arr rowsJson).pretty ++ "\n")
  IO.println s!"counted {kernels.length} kernels × {rows.length} rows"

/-! ## Report (the runner's statistics) -/

def median (values : Array Float) : Float :=
  let sorted := values.qsort (· < ·)
  if sorted.isEmpty then 0
  else if sorted.size % 2 == 1 then sorted[sorted.size / 2]!
  else (sorted[sorted.size / 2 - 1]! + sorted[sorted.size / 2]!) / 2

/-- Percentile bootstrap of the median paired ratio (deterministic resampling). -/
def bootstrap (ratios : Array Float) (rounds : Nat := 2000) : Float × Float := Id.run do
  if ratios.isEmpty then return (0, 0)
  let mut state : UInt64 := 0x243f6a8885a308d3
  let mut estimates : Array Float := #[]
  for _ in [:rounds] do
    let mut resample : Array Float := #[]
    for _ in [:ratios.size] do
      state := state ^^^ (state <<< 13)
      state := state ^^^ (state >>> 7)
      state := state ^^^ (state <<< 17)
      resample := resample.push ratios[state.toNat % ratios.size]!
    estimates := estimates.push (median resample)
  let sorted := estimates.qsort (· < ·)
  return (sorted[rounds * 25 / 1000]!, sorted[rounds * 975 / 1000]!)

def fmt (value : Float) (digits : Nat := 3) : String :=
  let scaled := (value.abs * (10 : Float) ^ digits.toFloat).round.toUInt64.toNat
  let whole := scaled / 10 ^ digits
  let frac := toString (scaled % 10 ^ digits)
  let sign := if value < 0 then "-" else ""
  if digits == 0 then s!"{sign}{whole}"
  else s!"{sign}{whole}.{"".pushn '0' (digits - frac.length)}{frac}"

def readJson (path : FilePath) : IO Json := do IO.ofExcept (Json.parse (← IO.FS.readFile path))

def num (j : Json) (key : String) : Float :=
  match j.getObjValD key |>.getNum? with
  | .ok n => n.toFloat
  | .error _ => 0

def report (out : FilePath) : IO Unit := do
  let json ← readJson (out / "samples.json")
  let samples ← IO.ofExcept do
    (← (← json.getObjVal? "samples").getArr?).mapM fun s => do
      return (← (← s.getObjVal? "kernel").getStr?, ← (← s.getObjVal? "row").getStr?,
        ← (← s.getObjVal? "block").getNat?, (← (← s.getObjVal? "ns_per_op").getNum?).toFloat)
  let env := json.getObjValD "environment"
  let perf ← try some <$> readJson (out / "perf.json") catch _ => pure none
  let code ← readJson (out / "code.json")
  let probe ← (← IO.FS.readFile (out / "probe.jsonl")).splitOn "\n" |>.filter (!·.isEmpty) |>.mapM
    (fun line => IO.ofExcept (Json.parse line))
  let mut lines : Array String := #[
    "# MEAS-4 early probe: measured tables", "",
    s!"Host: {env.getObjValD "cpu_model" |>.compress}, worker CPU {env.getObjValD "worker_cpu" |>.compress}, governor {env.getObjValD "governor" |>.compress}, boost {env.getObjValD "boost" |>.compress}, load {env.getObjValD "loadavg" |>.compress}.",
    s!"Blocks per kernel: {json.getObjValD "blocks" |>.compress}. In-process time per operation (entry profile); medians over blocks; ratios are paired per block, with 95% percentile-bootstrap intervals (2000 rounds), as the runner reports them.", ""]
  let mut summary : Array Json := #[]
  for k in kernels do
    let of (row : String) := samples.filter fun (kn, r, _, _) => kn == k.name && r == row
    let ns (row : String) := median ((of row).map (·.2.2.2))
    let paired (row base : String) : Array Float := (of row).filterMap fun (_, _, block, t) =>
      ((of base).find? fun (_, _, b, _) => b == block).map fun (_, _, _, bt) => t / bt
    let cell (row base : String) : String :=
      if row == base then "1" else
        let ratios := paired row base
        let (low, high) := bootstrap ratios
        s!"{fmt (median ratios)} [{fmt low}, {fmt high}]"
    let perfOf (row event : String) : String :=
      match perf with
      | none => "not measured"
      | some p =>
          match (p.getArr?.toOption.getD #[]).find? (fun e =>
              e.getObjValD "kernel" == Json.str k.name && e.getObjValD "row" == Json.str row) with
          | none => "not measured"
          | some e =>
              match (e.getObjValD event).getNum? with
              | .ok n => fmt n.toFloat 1
              | .error _ => "unavailable"
    let ipc (row : String) : String :=
      match perfOf row "instructions", perfOf row "cycles" with
      | i, c => match (Json.parse i).toOption.bind (·.getNum?.toOption), (Json.parse c).toOption.bind (·.getNum?.toOption) with
        | some i, some c => if c.toFloat > 0 then fmt (i.toFloat / c.toFloat) 2 else "-"
        | _, _ => "-"
    lines := lines ++ #[s!"## {k.name}: {k.op}", "",
      "| Row | ns/op (median) | / clang-twin | / lean-clang | instructions/op | cycles/op | IPC | branch misses/op |",
      "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for row in rows do
      lines := lines.push s!"| {row} | {fmt (ns row) 1} | {cell row "clang-twin"} | {cell row "lean-clang"} | {perfOf row "instructions"} | {perfOf row "cycles"} | {ipc row} | {perfOf row "branch-misses"} |"
      summary := summary.push (Json.mkObj [("kernel", Json.str k.name), ("row", Json.str row),
        ("median_ns", toJson (ns row)),
        ("ratio_to_clang_twin", toJson (median (paired row "clang-twin"))),
        ("ratio_to_lean_clang", toJson (median (paired row "lean-clang")))])
    lines := lines.push ""
  -- code size and static counts
  lines := lines ++ #["## Code size and static counts", "",
    "Bytes of the kernel's own code (`nm -S`; for compilatrix-probe the function without its export wrapper and exit group, from `backend-probe`), and static counts over those instructions (`objdump`): register-to-register moves, `rsp`-relative stores and loads (spills, reloads and callee-saved saves), pushes and pops.", "",
    "| Kernel | Row | Bytes | Instructions | Reg moves | Stack stores | Stack loads | Push/pop |",
    "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
  for entry in code.getArr?.toOption.getD #[] do
    let kernel := (entry.getObjValD "kernel").getStr?.toOption.getD ""
    let p := probe.find? fun j => (j.getObjValD "kernel").getStr?.toOption.getD "" ==
      ((kernels.find? (·.name == kernel)).map (·.lir)).getD ""
    for row in rows do
      let r := entry.getObjValD row
      let n (o : Json) (key : String) := toString (num o key).toUInt64
      if row == "compilatrix-probe" then
        -- the function alone, from the typed program backend-probe laid out
        let f := (p.map (·.getObjValD "function_x86")).getD Json.null
        let bytes := (p.map fun j => num j "function").getD 0
        lines := lines.push s!"| {kernel} | {row} | {bytes.toUInt64} (object text {n r "object_text"}) | {n f "instructions"} | {n f "moves"} | {n f "stack_stores"} | {n f "stack_loads"} | 0 |"
      else
        let s := r.getObjValD "static"
        lines := lines.push s!"| {kernel} | {row} | {n r "bytes"} | {n s "instructions"} | {n s "reg_moves"} | {n s "stack_stores"} | {n s "stack_loads"} | {n s "push_pop"} |"
  lines := lines ++ #["", "## Compilatrix: allocation, loops and compile time", "",
    "From `backend-probe`: allocation's static edits in Xl, the laid-out x86 inside natural loops, prologue stack checks, and the median native time of each phase (`Backend.compile` = selection, allocation and emission).", "",
    "| Kernel | Allocation | Xl spills / reloads / moves | Loop blocks | Loop instructions | Loop moves / stack stores / loads | Stack checks | Select ms | Allocate ms | Emit ms | Compile ms |",
    "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
  for j in probe do
    let xl := j.getObjValD "xl"
    let loop := j.getObjValD "loop"
    let ms := j.getObjValD "compile_ms"
    let n (o : Json) (key : String) := toString (num o key).toUInt64
    lines := lines.push s!"| {(j.getObjValD "kernel").getStr?.toOption.getD ""} | {(j.getObjValD "allocation").getStr?.toOption.getD ""} | {n xl "spills"} / {n xl "reloads"} / {n xl "moves"} | {n loop "blocks"} | {n loop "instructions"} | {n loop "moves"} / {n loop "stack_stores"} / {n loop "stack_loads"} | {n j "stackChecks"} | {fmt (num ms "select")} | {fmt (num ms "allocate")} | {fmt (num ms "emit")} | {fmt (num ms "compile")} |"
  IO.FS.writeFile (out / "tables.md") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out / "summary.json") ((Json.mkObj [("environment", env), ("rows", Json.arr summary)]).pretty ++ "\n")
  IO.println s!"wrote {out / "tables.md"}"

end Meas4

open Meas4 in
def main (args : List String) : IO UInt32 := do
  let usage := "usage: Meas4.lean (build OUT [--probe PATH] | check OUT | measure OUT [--cpu N] [--blocks B] | perf OUT [--cpu N] [--perf PATH] | report OUT)"
  try
    match args with
    | ["build", out] => build out ".lake/build/bin/backend-probe"
    | ["build", out, "--probe", probe] => build out probe
    | ["check", out] => check out
    | "measure" :: out :: rest =>
        let rec options (cpu blocks : Nat) : List String → IO (Nat × Nat)
          | "--cpu" :: n :: more => options n.toNat! blocks more
          | "--blocks" :: n :: more => options cpu n.toNat! more
          | [] => pure (cpu, blocks)
          | _ => throw (IO.userError usage)
        let (cpu, blocks) ← options 2 10 rest
        measure out cpu blocks
    | "perf" :: out :: rest =>
        let rec perfOptions (cpu : Nat) (perf : String) : List String → IO (Nat × String)
          | "--cpu" :: n :: more => perfOptions n.toNat! perf more
          | "--perf" :: p :: more => perfOptions cpu p more
          | [] => pure (cpu, perf)
          | _ => throw (IO.userError usage)
        let (cpu, perf) ← perfOptions 2 "perf" rest
        perfAll out cpu perf
    | ["report", out] => report out
    | _ => throw (IO.userError usage)
    return 0
  catch error =>
    IO.eprintln s!"meas4: {error}"
    return 1
