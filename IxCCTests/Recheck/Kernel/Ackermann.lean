import IxCCTests.Recheck.Artifacts.Ackermann
import IxCCTests.Recheck.Kernel.Support

/-! The `ackermann` bench-k1 artifact through the recheck path in the
kernel (M1.K1): `Recheck.runTyped` gives the natively computed typed
program (22 blocks, 162 instructions). Manual (the artifact takes about 40 s
to elaborate): `lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.Kernel.Ackermann

open IxCC IxCCTests.Recheck.Artifacts.Ackermann

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end IxCCTests.Recheck.Kernel.Ackermann
