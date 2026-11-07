import IxCCTests.Recheck.Artifacts.SumLoop
import IxCCTests.Recheck.Kernel.Support

/-! The `sum-loop` bench-k1 artifact through the recheck path in the
kernel (M1.K1): `Recheck.runTyped` gives the natively computed typed
program (19 blocks, 159 instructions). Manual (the artifact takes about a
minute to elaborate, the evaluation about 20 s): `lake build
IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.Kernel.SumLoop

open IxCC IxCCTests.Recheck.Artifacts.SumLoop

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end IxCCTests.Recheck.Kernel.SumLoop
