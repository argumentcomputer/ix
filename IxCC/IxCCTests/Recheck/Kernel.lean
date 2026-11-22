import IxCCTests.Recheck.Kernel.Fib
import IxCCTests.Recheck.Kernel.Tak
import IxCCTests.Recheck.Kernel.Gcd

/-! # The recheck path on K1 artifacts, evaluated by the kernel

On the bench-k1 artifacts (`IxCCTests.Recheck.Artifacts`),
`decide +kernel` checks against the native run:

* `Recheck.runTyped` (the laid-out typed x86 program) on fib, tak and gcd;
* the whole `Recheck.run` (the object's bytes) on fib, about 17 s.

`tests-recheck` builds this module, so the programs derivation of
`nix flake check` evaluates it. The rest (typed programs of even-odd and
sfib, whole runs of tak, gcd, even-odd and sfib) is the manual
`IxCCTests.Recheck.KernelSlow`, which no library imports. -/
