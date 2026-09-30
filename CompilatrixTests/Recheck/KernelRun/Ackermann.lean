import CompilatrixTests.Recheck.Artifacts.Ackermann
import CompilatrixTests.Recheck.Kernel.Support

/-! The whole recheck path on the `ackermann` bench-k1 artifact in the
kernel (M1.K1): `Recheck.run` gives the object's 2,040 bytes the native run
writes. Manual (about 20 s after a 40 s artifact): `lake build
CompilatrixTests.Recheck.KernelSlow`. -/

namespace CompilatrixTests.Recheck.KernelRun.Ackermann

open Compilatrix CompilatrixTests.Recheck.Artifacts.Ackermann

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end CompilatrixTests.Recheck.KernelRun.Ackermann
