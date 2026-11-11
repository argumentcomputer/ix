import IxCCTests.Recheck.Artifacts.EvenOdd
import IxCCTests.Recheck.Kernel.Support

/-! The `even-odd` bench-k1 artifact through the recheck path in the kernel:
`Recheck.runTyped` gives the natively computed typed program. Manual:
`lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.Kernel.EvenOdd

open IxCC IxCCTests.Recheck.Artifacts.EvenOdd

set_option maxRecDepth 1000000

example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

end IxCCTests.Recheck.Kernel.EvenOdd
