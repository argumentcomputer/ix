import IxCCTests.Recheck.Artifacts.Ackermann
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on the `ackermann` bench-k1 artifact in the
kernel: `Recheck.run` gives the object's 2,040 bytes the native run
writes. Manual (about 20 s after a 40 s artifact): `lake build
IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.KernelRun.Ackermann

open IxCC IxCCTests.Recheck.Artifacts.Ackermann

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.KernelRun.Ackermann
