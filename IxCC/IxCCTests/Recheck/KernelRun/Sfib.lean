import IxCCTests.Recheck.Artifacts.Sfib
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on the `sfib` bench-k1 artifact in the kernel:
`Recheck.run` gives the object's bytes the native run writes. Manual:
`lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.KernelRun.Sfib

open IxCC IxCCTests.Recheck.Artifacts.Sfib

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.KernelRun.Sfib
