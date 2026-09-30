import CompilatrixTests.Recheck.Kernel.Fib
import CompilatrixTests.Recheck.Kernel.Tak
import CompilatrixTests.Recheck.Kernel.Gcd

/-! # The recheck path on K1 artifacts, evaluated by the kernel

`Recheck.runTyped` on the fib, tak and gcd bench-k1 artifacts
(`CompilatrixTests.Recheck.Artifacts`), checked by `decide +kernel` against
the natively computed typed programs (M1.K1; M2.8 makes this the
kernel-recheck gate). `tests-recheck` builds this module, so the programs
derivation of `nix flake check` evaluates it; ackermann and sum-loop are in
the manual `CompilatrixTests.Recheck.KernelSlow`. -/
