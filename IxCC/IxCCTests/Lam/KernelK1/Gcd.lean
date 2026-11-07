import IxCCTests.Src.Artifacts.Gcd
import IxCCTests.Lam.KernelK1.Front

/-! The `gcd` bench-k1 artifact through the front end in the kernel. -/

namespace IxCCTests.Lam.KernelK1.Gcd

open IxCCTests.Src.Artifacts.Gcd

set_option maxRecDepth 1000000

/-- `gcd`'s entry (constant 127) erases to 13 globals rooted at `const 127`. -/
example : facts program ann 13 127 = true := by decide +kernel

end IxCCTests.Lam.KernelK1.Gcd
