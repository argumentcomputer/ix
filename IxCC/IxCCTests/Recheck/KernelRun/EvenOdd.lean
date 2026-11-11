import IxCCTests.Recheck.Artifacts.EvenOdd
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on the `even-odd` bench-k1 artifact in the kernel:
`Recheck.run` gives the object's bytes the native run writes. Manual:
`lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.KernelRun.EvenOdd

open IxCC IxCCTests.Recheck.Artifacts.EvenOdd

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.KernelRun.EvenOdd
