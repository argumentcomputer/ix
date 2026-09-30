import CompilatrixTests.Recheck.Artifacts.Gcd
import CompilatrixTests.Recheck.Kernel.Support

/-! The whole recheck path on the `gcd` bench-k1 artifact in the kernel
(M1.K1): `Recheck.run` gives the object's 1,984 bytes the native run
writes. Manual (about 15 s): `lake build CompilatrixTests.Recheck.KernelSlow`. -/

namespace CompilatrixTests.Recheck.KernelRun.Gcd

open Compilatrix CompilatrixTests.Recheck.Artifacts.Gcd

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end CompilatrixTests.Recheck.KernelRun.Gcd
