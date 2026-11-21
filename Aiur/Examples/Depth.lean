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
* `owned`: a unit-returning recursive function, deferred across records. -/
def depthExample : Modules.Program Nat := aiur_modules% "
module Depth {
  fn loop(x: Field) -> Field { loop(x) }
  fn even(n: Field) -> Field { match n { 0 => 1, _ => odd(n - 1) } }
  fn odd(n: Field) -> Field { match n { 0 => 0, _ => even(n - 1) } }
  fn fib(n: Field) -> Field { match n { 0 => 0, 1 => 1, _ => fib(n - 1) + fib(n - 2) } }
  fn run(n: Field) -> Field { even(n) + fib(n) }
  fn owned(n: Field) -> () { match n { 0 => (), _ => link(n - 1) } }
  fn link(n: Field) -> () { owned(n) }
  fn top(n: Field) -> Field { let _unit = owned(n); n + 1 }
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
  let cfg ← IO.ofExcept (Trace.depthConfig Library.U32.Goldilocks.modulus physical)
  -- The fixture must exercise every slot kind and both limb tables.
  let kinds := cfg.plans.flatMap (·.2.slots)
  for kind in [Optimized.Depth.SlotKind.exact, .gap, .external] do
    unless kinds.contains kind do throw (IO.userError s!"depth fixture has no {reprStr kind} slot")
  unless cfg.limbs == [16, 8] do throw (IO.userError "depth fixture does not use k = 24")
  let (exported, trace) ← IO.ofExcept (Trace.exportPreparedPlan Library.U32.Goldilocks.modulus
    ZMod.val compiled.circuit.inlined.program artifact physical exported)
  let package ← IO.ofExcept (Artifact.package exported Library.U32.Goldilocks.modulus ZMod.val (some trace))
  let path := args.headD "/tmp/aiur-depth.ixa"
  if args.contains "--check" then
    let previous ← IO.FS.readBinFile path
    unless previous.data == package.data do throw (IO.userError "depth fixture is stale")
  else Artifact.write path package
