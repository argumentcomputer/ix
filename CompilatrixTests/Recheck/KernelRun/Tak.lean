import CompilatrixTests.Recheck.Artifacts.Tak
import CompilatrixTests.Recheck.Kernel.Support

/-! The whole recheck path on the `tak` bench-k1 artifact in the kernel
(M1.K1): `Recheck.run` gives the object's 2,216 bytes the native run
writes. Manual (about 20 s): `lake build CompilatrixTests.Recheck.KernelSlow`. -/

namespace CompilatrixTests.Recheck.KernelRun.Tak

open Compilatrix CompilatrixTests.Recheck.Artifacts.Tak

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end CompilatrixTests.Recheck.KernelRun.Tak
