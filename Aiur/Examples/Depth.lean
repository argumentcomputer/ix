import Aiur.Library.U32.Goldilocks
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

open Aiur Lean

/-- Recursion through the depth pass (Track A, H1), exported for the Rust
tests (`crates/aiur/tests/fixtures/depth.ixa`):

* `even`/`odd` and `owned`/`link`: mutual recursion through exact slots;
* `fib`: two co-firing self-calls, gap slots;
* `run` and `top`: external slots into recursive callees from another SCC;
* `loop`: the memo-cycle counterexample, whose self-call is an exact slot;
* `owned`: a unit-returning recursive function, deferred across records.

Every recursion here needs its depth word. The recursive functions double their argument toward
a target (`4096`, or `64` for `owned`), so the argument of a call is neither a proper part of a
parameter nor a parameter moved by a literal step, and `Depth.Structural` exempts no SCC:
doubling is not a measure on the field (`2` has multiplicative order `192` in Goldilocks, so
`x ↦ 2x` has cycles of `192` rows). `loop` passes its argument unchanged. On a power of two
`x = 2^(t - n)` below the target `2^t` the functions are the usual ones of `n`: `even`/`odd`
give the parity of `n`, `fib` the `n`-th Fibonacci number, and `owned` has height `2n`. -/
def depthExample : Modules.Program Nat := aiur_modules% "
module Depth {
  fn loop(x: Field) -> Field { loop(x) }
  fn even(x: Field) -> Field { match x { 4096 => 1, _ => odd(x * 2) } }
  fn odd(x: Field) -> Field { match x { 4096 => 0, _ => even(x * 2) } }
  fn fib(x: Field) -> Field { match x { 4096 => 0, 2048 => 1, _ => fib(x * 2) + fib(x * 4) } }
  fn run(x: Field) -> Field { even(x) + fib(x) }
  fn owned(x: Field) -> () { match x { 64 => (), _ => link(x * 2) } }
  fn link(x: Field) -> () { owned(x) }
  fn top(x: Field) -> Field { let _unit = owned(x); x + 1 }
}
"

def entries : List String := ["Depth::run", "Depth::fib", "Depth::loop", "Depth::top"]

def main (args : List String) : IO Unit := do
  let source := depthExample.toField Library.U32.Goldilocks.F
  let prepared ← IO.ofExcept (Modules.prepare source entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let artifact := compiled.circuit.artifact
  let physical ← IO.ofExcept (Optimized.Physical.prepare artifact)
  let (cfg, _) ← IO.ofExcept
    (Trace.depthConfig Library.U32.Goldilocks.modulus compiled.circuit.inlined.program physical)
  -- The fixture must exercise every slot kind and both limb tables.
  let kinds := cfg.plans.flatMap (·.2.slots)
  for kind in [Optimized.Depth.SlotKind.exact, .gap, .external] do
    unless kinds.contains kind do throw (IO.userError s!"depth fixture has no {reprStr kind} slot")
  unless cfg.limbs == [16, 8] do throw (IO.userError "depth fixture does not use k = 24")
  -- No SCC of the fixture is exempt: every recursive circuit carries a depth word.
  unless cfg.structural.isEmpty do
    throw (IO.userError s!"depth fixture has exempt circuits {cfg.structural}")
  for name in ["Depth::loop", "Depth::even", "Depth::odd", "Depth::fib", "Depth::owned"] do
    unless cfg.recursive (physical.representative name) do
      throw (IO.userError s!"depth fixture circuit {name} has no depth word")
  let (exported, trace) ← IO.ofExcept (Trace.exportPreparedPlan Library.U32.Goldilocks.modulus
    ZMod.val compiled.circuit.inlined.program artifact physical exported)
  let package ← IO.ofExcept (Artifact.package exported Library.U32.Goldilocks.modulus ZMod.val (some trace))
  let path := args.headD "/tmp/aiur-depth.ixa"
  if args.contains "--check" then
    let previous ← IO.FS.readBinFile path
    unless previous.data == package.data do throw (IO.userError "depth fixture is stale")
  else Artifact.write path package
