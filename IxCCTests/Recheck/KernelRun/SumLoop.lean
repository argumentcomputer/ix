import IxCCTests.Recheck.Artifacts.SumLoop
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on the `sum-loop` bench-k1 artifact in the kernel
(M1.K1): `Recheck.run` gives the object's 2,016 bytes the native run writes.
Manual (about 35 s and 8 GB after a one-minute artifact): `lake build
IxCCTests.Recheck.KernelSlow`. -/

namespace IxCCTests.Recheck.KernelRun.SumLoop

open IxCC IxCCTests.Recheck.Artifacts.SumLoop

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.KernelRun.SumLoop
