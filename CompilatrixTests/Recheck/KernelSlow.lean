import CompilatrixTests.Recheck.Kernel.Ackermann
import CompilatrixTests.Recheck.Kernel.SumLoop

/-! # The recheck path on the large K1 artifacts (manual)

`Recheck.runTyped` on the ackermann and sum-loop bench-k1 artifacts, by
`decide +kernel`. Their artifacts (1,344 and 1,469 constants, shared) take
40–55 s to elaborate, so this aggregate is built by hand: `lake build
CompilatrixTests.Recheck.KernelSlow`. -/
