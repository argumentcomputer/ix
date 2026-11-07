import IxCCTests.Recheck.Kernel.Ackermann
import IxCCTests.Recheck.Kernel.SumLoop
import IxCCTests.Recheck.KernelRun.Tak
import IxCCTests.Recheck.KernelRun.Gcd
import IxCCTests.Recheck.KernelRun.Ackermann
import IxCCTests.Recheck.KernelRun.SumLoop

/-! # The recheck path on K1 artifacts in the kernel: the slow part (manual)

`Recheck.runTyped` on the ackermann and sum-loop bench-k1 artifacts, and
the whole `Recheck.run` (the object's bytes) on tak, gcd, ackermann and
sum-loop, by `decide +kernel`. Each full run takes 15–35 s of kernel time,
and the ackermann and sum-loop artifacts (1,344 and 1,469 constants,
shared) take 40–55 s to elaborate, so this aggregate is built by hand:
`lake build IxCCTests.Recheck.KernelSlow`. fib's full run and the
typed programs of fib, tak and gcd are in the default build
(`IxCCTests.Recheck.Kernel`). -/
