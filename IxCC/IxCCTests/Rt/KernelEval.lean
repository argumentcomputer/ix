import IxCCTests.Rt.Kernel

/-!
# `Rt.lower` evaluated by the kernel

`Rt.lower` (with the Lir edge splitter) is on `Recheck.run`'s path in style
P (proved once, re-run), so Lean's kernel must evaluate it (D17). These examples re-run it with
`decide +kernel` (no native evaluation), composed with `Cfg.ofAnf`, on

* the pipeline's final Anf program of each bench-k1 entry
  (`IxCCTests.Fir.Artifacts`, checked against the live pipeline by
  `tests-rt` and `tests-fir`);
* hand-written Cfg programs with what K1 lacks: allocation, projection,
  mixed and cell switches and the `Nat` procedures; critical edges (split
  in the kernel); a literal without a word and a dead block (pruned),

so a change that stops the lowering reducing (a `HashMap`, well-founded
recursion, a native-only implementation) fails to elaborate here. The
expected summaries were computed natively (`Kernel.expected`,
`Kernel.expectedCfg`); `tests-rt` recomputes them natively from the same
tables. A wrong expectation is rejected (the `≠` examples).
-/

namespace IxCCTests.Rt.KernelEval

open IxCC IxCCTests.Rt.Kernel

set_option maxRecDepth 100000 in
example : summary Fir.Artifacts.fib = some (5, 37, 108, 2, 9) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Fir.Artifacts.sumLoop = some (5, 36, 104, 3, 9) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Fir.Artifacts.ackermann = some (5, 38, 106, 4, 9) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Fir.Artifacts.tak = some (5, 36, 116, 3, 8) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Fir.Artifacts.gcd = some (5, 32, 109, 3, 7) := by decide +kernel

set_option maxRecDepth 100000 in
example : cfgSummary (Cases.cfgOf Cases.values') = some (13, 77, 165, 5, 14) := by decide +kernel

set_option maxRecDepth 100000 in
example : cfgSummary Cases.critical = some (5, 37, 103, 2, 8) := by decide +kernel

set_option maxRecDepth 100000 in
example : cfgSummary Cases.bigEdge = some (4, 30, 103, 2, 8) := by decide +kernel

/-! Sanity: the kernel tells a wrong summary apart. -/

set_option maxRecDepth 100000 in
example : summary Fir.Artifacts.fib ≠ some (5, 37, 108, 3, 9) := by decide +kernel

set_option maxRecDepth 100000 in
example : cfgSummary Cases.critical ≠ some (5, 35, 103, 2, 8) := by decide +kernel

end IxCCTests.Rt.KernelEval
