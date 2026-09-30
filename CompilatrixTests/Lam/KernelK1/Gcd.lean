import CompilatrixTests.Src.Artifacts.Gcd
import CompilatrixTests.Lam.KernelK1.Front

/-! The `gcd` bench-k1 artifact through the front end in the kernel. -/

namespace CompilatrixTests.Lam.KernelK1.Gcd

open CompilatrixTests.Src.Artifacts.Gcd

set_option maxRecDepth 1000000

/-- `gcd`'s entry (constant 19) erases to 13 globals rooted at `const 19`. -/
example : facts program ann 13 19 = true := by decide +kernel

end CompilatrixTests.Lam.KernelK1.Gcd
