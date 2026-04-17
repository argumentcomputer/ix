/-
  Kernel ingress + egress roundtrip test.

  Exercises `Lean env → Ixon → kernel ingress → kernel egress → Lean env`
  on the full current environment and compares each constant (by content
  hash) against the original. This isolates ingress correctness from
  kernel-level typechecking: if `kernel-roundtrip` passes but
  `kernel-tutorial` fails, the bug is in the check side.
-/
import Ix.Common
import Ix.Meta
import LSpec

open LSpec

namespace Tests.Ix.Kernel.Roundtrip

/-- FFI: run the kernel roundtrip and collect per-constant diff messages.
    Empty array = roundtrip agrees with the original Lean env.

    Implemented in `src/ffi/kernel.rs::rs_kernel_roundtrip`. -/
@[extern "rs_kernel_roundtrip"]
opaque rsKernelRoundtripFFI :
    @& List (Lean.Name × Lean.ConstantInfo) → IO (Array String)

def testRoundtrip : TestSeq :=
  .individualIO "kernel ingress+egress roundtrip" none (do
    let leanEnv ← get_env!
    let errors ← rsKernelRoundtripFFI leanEnv.constants.toList
    if errors.isEmpty then
      return (true, 0, 0, none)
    else
      IO.println s!"[kernel-roundtrip] {errors.size} errors:"
      for msg in errors[:min 20 errors.size] do
        IO.println s!"  {msg}"
      return (false, 0, 0, some s!"{errors.size} roundtrip mismatches")
  ) .done

def suite : List TestSeq := [testRoundtrip]

end Tests.Ix.Kernel.Roundtrip
