import IxCCTests.Recheck.Artifacts.Gcd
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on the `gcd` bench-k1 artifact in the kernel:
`Recheck.run` gives the object's 1,984 bytes the native run
writes. Manual (about 15 s): `lake build IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.KernelRun.Gcd

open IxCC IxCCTests.Recheck.Artifacts.Gcd

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.KernelRun.Gcd
