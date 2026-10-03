import CompilatrixTests.Pipeline.Support
import Compilatrix.Tools.Check

/-! Deterministic x86 step counts (M3.2, MEAS-3): each bench-k1 program, as
the compiler makes it (`Recheck.compileInput`), runs `cx_init` and then its
root on the typed x86 machine (`X86.step` from the exported wrapper) and on
the byte machine (`ByteEval` over the object's own `.text`), as
`tests-pipeline`'s `x86` and `bytes` levels do. The step counts, the result
(`rax:rdx` and its readback) and the arguments must equal the reviewed
baseline [`fixtures/ixon-v4/bench-k1/steps.json`] exactly.

The counts are a property of the emitted code: they change when selection,
allocation, stacking, layout or the runtime lowering changes what runs, so
a baseline change is a reviewed, performance-relevant change. Regenerate
with `lake exe check-steps --write` and review the diff.

The arguments are the K1 test runs of the machine levels (`tests-pipeline`
runs the typed and byte machines at these sizes, about 40 µs per typed
step): fib 13, sum-loop 5000, ackermann 3 3, tak 12 12 8 4 and gcd at its
test size (1071 462); the four further bench-k1 programs at sizes of the
same cost. `--program NAME` restricts a check to the named programs. -/

namespace CompilatrixTests.Pipeline.Steps

open Compilatrix Compilatrix.Recheck CompilatrixTests.Src
open Lean (Json ToJson FromJson toJson fromJson?)
open System

def baseline : FilePath := "fixtures/ixon-v4/bench-k1/steps.json"
def formatName : String := "compilatrix/x86-steps/1"
def regenerate : String := "lake exe check-steps --write"

/-- The runs: each program and its arguments. -/
def runs : List (String × List Nat) :=
  [("fib", [13]), ("sum-loop", [5000]), ("ackermann", [3, 3]), ("tak", [12, 12, 8, 4]),
   ("gcd", [1071, 462]),
   ("collatz", [27]), ("prime-count", [100]), ("even-odd", [1001]), ("sfib", [1000])]

/-- One run's counts. `init*`: `cx_init`'s steps; `typed`/`bytes`: the
root's steps after it. -/
structure Row where
  name : String
  args : List Nat
  initTyped : Nat
  initBytes : Nat
  typed : Nat
  bytes : Nat
  status : Nat
  value : Nat
  obs : String
  deriving BEq, Repr, ToJson, FromJson

structure Baseline where
  format : String
  regenerate : String
  rows : List Row
  deriving ToJson, FromJson

def fuel : Nat := 1 <<< 34

/-- Compile `name`, then run `cx_init` and the root on `args` on both
machines (`Rt.Machine.runExport`, which requires their `rax:rdx` to agree
and the callee-saved registers and `rsp` restored). -/
def measure (name : String) (args : List Nat) : IO Row := do
  let (_, art) ← compileIn name (← benchInput name)
  let cc := compiledOf art
  let some root := art.roots.head? | throw (IO.userError s!"{name}: no root")
  let ms ← IO.ofExcept (CompilatrixTests.Rt.Machine.initMachines cc)
  let (e, ms') ← IO.ofExcept <| ← IO.lazyPure fun _ =>
    CompilatrixTests.Rt.Machine.runExport cc root.symbol (args.map UInt64.ofNat) ms fuel
  let obs := if e.status == 0 then readWord root ms'.typed.memory e.value else none
  pure { name, args, initTyped := ms.typedSteps, initBytes := ms.byteSteps
         typed := ms'.typedSteps - ms.typedSteps, bytes := ms'.byteSteps - ms.byteSteps
         status := e.status.toNat, value := e.value.toNat, obs := (obs.map Rt.renderObs).getD "-" }

/-- The baseline file: one row per line, fields in a fixed order (parsed
back by `FromJson`). -/
def Baseline.render (b : Baseline) : String :=
  let str (s : String) := (Json.str s).compress
  let row (r : Row) :=
    s!"    \{\"name\": {str r.name}, \"args\": {(toJson r.args).compress}, \"typed\": {r.typed}, \
      \"bytes\": {r.bytes}, \"initTyped\": {r.initTyped}, \"initBytes\": {r.initBytes}, \
      \"status\": {r.status}, \"value\": {r.value}, \"obs\": {str r.obs}}"
  s!"\{\n  \"format\": {str b.format},\n  \"regenerate\": {str b.regenerate},\n  \"rows\": [\n\
    {",\n".intercalate (b.rows.map row)}\n  ]\n}\n"

def Row.render (r : Row) : String :=
  s!"{r.name} {r.args}: typed {r.typed} (cx_init {r.initTyped}), bytes {r.bytes} (cx_init {r.initBytes}), \
    status {r.status}, value {r.value}, {r.obs}"

/-- Every field that differs, as `field: baseline → now`. -/
def Row.diff (old new : Row) : List String :=
  let f (label : String) (a b : String) := if a == b then [] else [s!"{label}: {a} → {b}"]
  f "args" (toString old.args) (toString new.args) ++
  f "typed steps" (toString old.typed) (toString new.typed) ++
  f "byte steps" (toString old.bytes) (toString new.bytes) ++
  f "cx_init typed steps" (toString old.initTyped) (toString new.initTyped) ++
  f "cx_init byte steps" (toString old.initBytes) (toString new.initBytes) ++
  f "status" (toString old.status) (toString new.status) ++
  f "value" (toString old.value) (toString new.value) ++
  f "readback" old.obs new.obs

def readBaseline : IO Baseline := do
  let text ← IO.FS.readFile baseline
  let json ← IO.ofExcept (Json.parse text)
  match fromJson? json with
  | .ok (b : Baseline) => pure b
  | .error e => throw (IO.userError s!"{baseline}: {e}")

def main (args : List String) : IO UInt32 := do
  let write := args.contains "--write"
  let rec only : List String → List String
    | "--program" :: n :: rest => n :: only rest
    | _ :: rest => only rest
    | [] => []
  let names := only args
  if args.contains "--test-size" then
    -- manual: every program at its benchmark test size, printed, not compared
    for (name, _) in runs do
      let (a, _) ← CompilatrixTests.Src.Bench.testCase name
      let (row, ms) ← timed (measure name a)
      IO.println s!"  {row.render} ({ms} ms)"
      (← IO.getStdout).flush
    return 0
  for n in names do
    unless runs.any (·.1 == n) do
      IO.eprintln s!"check-steps: unknown program {n}"
      return 2
  if write && !names.isEmpty then
    IO.eprintln "check-steps: --write regenerates every row; drop --program"
    return 2
  let selected := if names.isEmpty then runs else runs.filter (names.contains ·.1)
  let mut rows := #[]
  for (name, a) in selected do
    let (row, ms) ← timed (measure name a)
    IO.println s!"  {row.render} ({ms} ms)"
    (← IO.getStdout).flush
    rows := rows.push row
  if write then
    let b : Baseline := { format := formatName, regenerate, rows := rows.toList }
    IO.FS.writeFile baseline b.render
    IO.println s!"check-steps: wrote {rows.size} rows to {baseline}"
    return 0
  let b ← readBaseline
  let mut problems : Array String := #[]
  unless b.format == formatName do problems := problems.push s!"format {b.format}, expected {formatName}"
  if names.isEmpty then
    unless b.rows.map (·.name) == runs.map (·.1) do
      problems := problems.push s!"baseline programs {b.rows.map (·.name)}, runs {runs.map (·.1)}"
  for row in rows do
    match b.rows.find? (·.name == row.name) with
    | none => problems := problems.push s!"{row.name}: not in the baseline"
    | some old =>
      for d in old.diff row do problems := problems.push s!"{row.name}: {d}"
  if problems.isEmpty then
    IO.println s!"check-steps: {rows.size} runs equal {baseline} (typed and byte steps, cx_init, result)"
    return 0
  IO.eprintln s!"check-steps: {problems.size} differences from {baseline}:"
  for p in problems do IO.eprintln s!"  {p}"
  IO.eprintln s!"A change in step counts is a reviewed, performance-relevant change: \
    regenerate with `{regenerate}` and review the diff."
  return 1

end CompilatrixTests.Pipeline.Steps
