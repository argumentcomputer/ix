import IxCCTests.Recheck.Artifacts.Sfib
import IxCCTests.Recheck.Kernel.Support

/-! The `sfib` bench-k1 artifact through the recheck path in the kernel:
`Recheck.runTyped` gives the natively computed typed program. Manual:
`lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.Kernel.Sfib

open IxCC IxCCTests.Recheck.Artifacts.Sfib

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end IxCCTests.Recheck.Kernel.Sfib
