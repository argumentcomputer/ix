import IxCCTests.Recheck.Artifacts.Tak
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on the `tak` bench-k1 artifact in the kernel:
`Recheck.run` gives the object's 2,192 bytes the native run
writes. Manual (about 20 s): `lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.KernelRun.Tak

open IxCC IxCCTests.Recheck.Artifacts.Tak

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.KernelRun.Tak
