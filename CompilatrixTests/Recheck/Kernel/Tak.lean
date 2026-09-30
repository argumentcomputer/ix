import CompilatrixTests.Recheck.Artifacts.Tak
import CompilatrixTests.Recheck.Kernel.Support

/-! The `tak` bench-k1 artifact through the recheck path in the kernel
(M1.K1): `Recheck.runTyped` gives the natively computed typed program (21
blocks, 205 instructions). -/

namespace CompilatrixTests.Recheck.Kernel.Tak

open Compilatrix CompilatrixTests.Recheck.Artifacts.Tak

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end CompilatrixTests.Recheck.Kernel.Tak
