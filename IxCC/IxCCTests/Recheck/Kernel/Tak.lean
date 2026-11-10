import IxCCTests.Recheck.Artifacts.Tak
import IxCCTests.Recheck.Kernel.Support

/-! The `tak` bench-k1 artifact through the recheck path in the kernel:
`Recheck.runTyped` gives the natively computed typed program (21
blocks, 205 instructions). -/

namespace IxCCTests.Recheck.Kernel.Tak

open IxCC IxCCTests.Recheck.Artifacts.Tak

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end IxCCTests.Recheck.Kernel.Tak
