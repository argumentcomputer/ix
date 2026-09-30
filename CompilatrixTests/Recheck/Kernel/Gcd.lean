import CompilatrixTests.Recheck.Artifacts.Gcd
import CompilatrixTests.Recheck.Kernel.Support

/-! The `gcd` bench-k1 artifact through the recheck path in the kernel
(M1.K1): `Recheck.runTyped` gives the natively computed typed program (16
blocks, 159 instructions). -/

namespace CompilatrixTests.Recheck.Kernel.Gcd

open Compilatrix CompilatrixTests.Recheck.Artifacts.Gcd

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end CompilatrixTests.Recheck.Kernel.Gcd
