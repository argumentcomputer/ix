import IxCCTests.Lam.KernelK1.Fib
import IxCCTests.Lam.KernelK1.Tak
import IxCCTests.Lam.KernelK1.Gcd

/-! # The front end on K1 artifacts, evaluated by the kernel

`Src.Recheck.run` and erasure to Lam on the loaded fib, tak and gcd bench-k1
programs (`IxCCTests.Src.Artifacts`), checked by `decide +kernel`
(the kernel-recheck tests do the same for the whole of `Recheck.run`). `tests-lam` builds the
fib module; `lake build IxCCTests.Lam.KernelK1` builds all three
(about a minute, most of it elaborating the generated data). -/
