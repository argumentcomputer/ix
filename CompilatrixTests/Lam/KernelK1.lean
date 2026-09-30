import CompilatrixTests.Lam.KernelK1.Fib
import CompilatrixTests.Lam.KernelK1.Tak
import CompilatrixTests.Lam.KernelK1.Gcd

/-! # The front end on K1 artifacts, evaluated by the kernel

`Src.Recheck.run` and erasure to Lam on the loaded fib, tak and gcd bench-k1
programs (`CompilatrixTests.Src.Artifacts`), checked by `decide +kernel`
(M1.K1; M2.8 turns this into the kernel-recheck gate). `tests-lam` builds the
fib module; `lake build CompilatrixTests.Lam.KernelK1` builds all three
(about a minute, most of it elaborating the generated data). -/
