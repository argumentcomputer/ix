import CompilatrixTests.Recheck.Artifacts.Fib
import CompilatrixTests.Recheck.Kernel.Support

/-! The `fib` bench-k1 artifact through the recheck path in the kernel
(M1.K1): `Recheck.runTyped` on the program, configuration and certificate
of `CompilatrixTests.Recheck.Artifacts.Fib` gives, by `decide +kernel`, the
laid-out typed x86 program the native run computes (21 blocks, 165
instructions). -/

namespace CompilatrixTests.Recheck.Kernel.Fib

open Compilatrix CompilatrixTests.Recheck.Artifacts.Fib

set_option maxRecDepth 1000000

/-- The recheck path up to the laid-out typed program. -/
example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

/-- Sanity: the kernel tells a wrong program apart. -/
example : (Recheck.runTyped cfg program cert).map (·.program) ≠ .ok { typed with entry := 1 } := by
  decide +kernel

end CompilatrixTests.Recheck.Kernel.Fib
