import IxCCTests.Src.Artifacts.Tak
import IxCCTests.Lam.KernelK1.Front

/-! The `tak` bench-k1 artifact through the front end in the kernel. -/

namespace IxCCTests.Lam.KernelK1.Tak

open IxCCTests.Src.Artifacts.Tak

set_option maxRecDepth 1000000

/-- `tak`'s entry (constant 73) erases to 18 globals rooted at `const 73`. -/
example : facts program ann 18 73 = true := by decide +kernel

end IxCCTests.Lam.KernelK1.Tak
