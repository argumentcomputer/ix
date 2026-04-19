/-
  Kernel ixon roundtrip test.

  Exercises
  `Lean env → compile → ixon_ingress → kenv → ixon_egress → decompile → Lean`
  on the full current environment and compares each constant (by content
  hash) against the original. Passing through `ixon_egress + decompile_env`
  lets the validated decompile path regenerate aux_gen constants (brecOn,
  below, ...) from the kernel-canonicalized Ixon form, rather than a
  second ad-hoc `KEnv → Lean` decompiler.

  If `kernel-ixon-roundtrip` passes but `kernel-tutorial` fails, the bug
  is in the check side.
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
  .individualIO "kernel ixon roundtrip" none (do
    let leanEnv ← get_env!
    let errors ← rsKernelRoundtripFFI leanEnv.constants.toList
    if errors.isEmpty then
      return (true, 0, 0, none)
    else
      IO.println s!"[kernel-ixon-roundtrip] {errors.size} errors:"
      for msg in errors[:min 20 errors.size] do
        IO.println s!"  {msg}"
      return (false, 0, 0, some s!"{errors.size} roundtrip mismatches")
  ) .done

def suite : List TestSeq := [testRoundtrip]

end Tests.Ix.Kernel.Roundtrip
