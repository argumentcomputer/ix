import CompilatrixTests.Src.Artifacts.Tak
import CompilatrixTests.Lam.KernelK1.Front

/-! The `tak` bench-k1 artifact through the front end in the kernel. -/

namespace CompilatrixTests.Lam.KernelK1.Tak

open CompilatrixTests.Src.Artifacts.Tak

set_option maxRecDepth 1000000

/-- `tak`'s entry (constant 41) erases to 18 globals rooted at `const 41`. -/
example : facts program ann 18 41 = true := by decide +kernel

end CompilatrixTests.Lam.KernelK1.Tak
