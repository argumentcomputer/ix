import CompilatrixTests.Src.Rules
import CompilatrixTests.Src.Table
import CompilatrixTests.Src.Runs
import CompilatrixTests.Src.Differential
import CompilatrixTests.Src.Pins
import CompilatrixTests.Src.Diagnostics
import CompilatrixTests.Src.Bench

/-! The `tests-src` suite (design note 01 §10): rules, the K1 table, K1 runs
on the eqn route, the native differential, pins, diagnostics, and the
bench-k1 entries. `tests-src-slow` adds `ack 3 10` and `fib 30` without
primitives. -/

namespace CompilatrixTests.Src.Run

open Compilatrix Compilatrix.Src CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--entry", name] =>
    IO.println (← Bench.runEntry name)
    return 0
  | _ => pure ()
  let a ← IO.mkRef 0
  try
    IO.println "tests-src"
    part a "rules and eval_mono" (Rules.run a)
    part a "table on K1" (Table.run a)
    part a "K1 on the eqn route" do
      for r in ← Runs.eqnRoute a do
        IO.println s!"    {r.label} = {r.expected} in {r.ms} ms (clock 16 × {r.calls} Lean calls)"
    part a "least clocks" do
      for line in ← Runs.clockRatios do IO.println s!"    {line}"
    part a "fallback route" do
      for line in ← Runs.fallback a do IO.println s!"    {line}"
    part a "differential against native Lean" (Differential.run a)
    part a "pins" (Pins.run a)
    part a "diagnostics" (Diagnostics.run a)
    part a "bench-k1 entries" do
      for line in ← Bench.run a (← IO.appPath) do IO.println s!"    {line}"
    IO.println s!"tests-src: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-src: FAILED after {← a.get} assertions: {e}"
    return 1

/-- Rows over the 60 s budget (01 §10 part 3), recorded as a coverage
change: `ack 3 10` on the eqn route and `fib 30` with no primitives. -/
def slow (_args : List String) : IO UInt32 := do
  let a ← IO.mkRef 0
  try
    let l ← loadK1
    let (v, calls) := Runs.ackCalls 3 10
    let row ← Runs.runRow a l "K1.ack" [3, 10] v calls
    IO.println s!"  {row.label} = {row.expected} in {row.ms} ms"
    let np ← loadK1 { typecheck := false, table := { prims := [] } }
    let row ← Runs.runRow a np "K1.fib" [30] 832040 (Runs.fibCalls 30) (budget := 1 <<< 40)
    IO.println s!"  noPrims {row.label} = {row.expected} in {row.ms} ms"
    IO.println s!"tests-src-slow: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-src-slow: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Src.Run
