import IxCCTests.Recheck.Kernel.EvenOdd
import IxCCTests.Recheck.Kernel.Sfib
import IxCCTests.Recheck.KernelRun.Tak
import IxCCTests.Recheck.KernelRun.Gcd
import IxCCTests.Recheck.KernelRun.EvenOdd
import IxCCTests.Recheck.KernelRun.Sfib

/-! # The recheck path on K1 artifacts in the kernel: the slow part (manual)

`Recheck.runTyped` on the even-odd and sfib bench-k1 artifacts, and the whole
`Recheck.run` (the object's bytes) on tak, gcd, even-odd and sfib, by
`decide +kernel`. Built by hand only (`lake build IxCCTests.Recheck.KernelSlow`;
no library imports it). fib's full run and the typed programs of fib, tak and
gcd are in the default build (`IxCCTests.Recheck.Kernel`).

The samples are small because the kernel-evaluated checks scale badly with the
closure: the role-bound sum-loop artifact (3,482 constants, from 1,469 in the
older unbound closure) did not finish `runTyped` in 30 minutes at 19 GB with no
heartbeat limit, where the older artifact elaborated in about a minute and
evaluated in about 20 s; ackermann and sum-loop were therefore replaced by
even-odd and sfib when the fixtures were regenerated role-bound. -/
