import CompilatrixTests.Recheck.Kernel.Ackermann
import CompilatrixTests.Recheck.Kernel.SumLoop
import CompilatrixTests.Recheck.KernelRun.Tak
import CompilatrixTests.Recheck.KernelRun.Gcd
import CompilatrixTests.Recheck.KernelRun.Ackermann
import CompilatrixTests.Recheck.KernelRun.SumLoop

/-! # The recheck path on K1 artifacts in the kernel: the slow part (manual)

`Recheck.runTyped` on the ackermann and sum-loop bench-k1 artifacts, and
the whole `Recheck.run` (the object's bytes) on tak, gcd, ackermann and
sum-loop, by `decide +kernel`. Each full run takes 15–35 s of kernel time,
and the ackermann and sum-loop artifacts (1,344 and 1,469 constants,
shared) take 40–55 s to elaborate, so this aggregate is built by hand:
`lake build CompilatrixTests.Recheck.KernelSlow`. fib's full run and the
typed programs of fib, tak and gcd are in the default build
(`CompilatrixTests.Recheck.Kernel`). -/
