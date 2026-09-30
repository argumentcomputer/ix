import CompilatrixTests.Recheck.Artifacts.Ackermann
import CompilatrixTests.Recheck.Kernel.Support

/-! The `ackermann` bench-k1 artifact through the recheck path in the
kernel (M1.K1): `Recheck.runTyped` gives the natively computed typed
program (22 blocks, 162 instructions). Manual (the artifact takes about 40 s
to elaborate): `lake build CompilatrixTests.Recheck.KernelSlow`. -/

namespace CompilatrixTests.Recheck.Kernel.Ackermann

open Compilatrix CompilatrixTests.Recheck.Artifacts.Ackermann

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end CompilatrixTests.Recheck.Kernel.Ackermann
