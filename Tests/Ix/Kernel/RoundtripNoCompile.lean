/-
  Kernel lean roundtrip test (skips compile).

  Exercises `Lean env → lean_ingress → KEnv<Meta> → lean_egress → Lean env`
  on the full current environment and compares each constant (by content
  hash) against the original. Unlike `kernel-ixon-roundtrip`, this path
  skips `compile_env` and `ixon_ingress` entirely, so it isolates
  direct-from-Lean kernel ingress from any compile/Ixon bugs.

  Used as a bisecting diagnostic: if this test is clean but
  `kernel-ixon-roundtrip` has errors, the bug lives in the compile
  pipeline (most likely `aux_gen` regeneration). If both tests fail with
  the same errors, the bug is in the ingress/egress pipeline itself.
-/
import Ix.Common
import Ix.Meta
import LSpec

open LSpec

namespace Tests.Ix.Kernel.RoundtripNoCompile

/-- FFI: run the no-compile kernel roundtrip and collect per-constant diff
    messages. Empty array = roundtrip agrees with the original Lean env.

    Implemented in `src/ffi/kernel.rs::rs_kernel_roundtrip_no_compile`. -/
@[extern "rs_kernel_roundtrip_no_compile"]
opaque rsKernelRoundtripNoCompileFFI :
    @& List (Lean.Name × Lean.ConstantInfo) → IO (Array String)

def testRoundtripNoCompile : TestSeq :=
  .individualIO "kernel lean roundtrip" none (do
    let leanEnv ← get_env!
    let errors ← rsKernelRoundtripNoCompileFFI leanEnv.constants.toList
    if errors.isEmpty then
      return (true, 0, 0, none)
    else
      IO.println s!"[kernel-lean-roundtrip] {errors.size} errors:"
      for msg in errors[:min 20 errors.size] do
        IO.println s!"  {msg}"
      return (false, 0, 0, some s!"{errors.size} roundtrip mismatches")
  ) .done

def suite : List TestSeq := [testRoundtripNoCompile]

end Tests.Ix.Kernel.RoundtripNoCompile
