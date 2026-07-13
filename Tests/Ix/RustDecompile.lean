/-
  Rust decompile roundtrip test.

  Exercises `Lean env → compile → serialize → deserialize → decompile →
  Lean` — the `ix decompile` pipeline over the serialized `.ixe`
  boundary (demoted-at-parse metadata load, `Named.original` recovery
  for shape-divergent aux blocks, expression interning) — and
  hash-compares every constant against the original.
  `kernel-ixon-roundtrip` covers the kernel ingress/egress leg instead.
-/
import Ix.Common
import Ix.Meta
import LSpec

open LSpec

namespace Tests.RustDecompile

/-- FFI: run the serialized decompile roundtrip and collect per-constant
    diff messages. Empty array = decompile agrees with the original Lean
    env.

    Implemented in `crates/ffi/src/kernel.rs::rs_decompile_roundtrip`. -/
@[extern "rs_decompile_roundtrip"]
opaque rsDecompileRoundtripFFI :
    @& List (Lean.Name × Lean.ConstantInfo) → IO (Array String)

def testRoundtrip : TestSeq :=
  .individualIO "rust decompile roundtrip" none (do
    let leanEnv ← get_env!
    let errors ← rsDecompileRoundtripFFI leanEnv.constants.toList
    if errors.isEmpty then
      return (true, 0, 0, none)
    else
      IO.println s!"[rust-decompile] {errors.size} errors:"
      for msg in errors[:min 20 errors.size] do
        IO.println s!"  {msg}"
      return (false, 0, 0, some s!"{errors.size} roundtrip mismatches")
  ) .done

def rustDecompileSuiteIO : List TestSeq := [testRoundtrip]

end Tests.RustDecompile
