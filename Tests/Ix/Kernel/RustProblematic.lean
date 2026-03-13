/-
  Rust kernel tests for problematic constants.
  Constants that fail or are slow in the Rust kernel, isolated for debugging.
-/
import Ix.Kernel
import Ix.CompileM
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Consts
import LSpec

open LSpec

namespace Tests.Ix.Kernel.RustProblematic

/-- Run problematic constants through the Rust kernel with tracing. -/
def testProblematic : TestSeq :=
  .individualIO "rust-kernel-problematic" (do
    let leanEnv ← get_env!
    let problematicNames := Consts.rustProblematicConsts

    let rustStart ← IO.monoMsNow
    let results ← Ix.Kernel.rsCheckConsts leanEnv problematicNames
    let rustMs := (← IO.monoMsNow) - rustStart
    for (name, result) in results do
      match result with
      | none => IO.println s!"  ✓ {name} ({rustMs.formatMs})"
      | some err => IO.println s!"  ✗ {name} ({rustMs.formatMs}): {repr err}"

    return (true, none)
  ) .done

def suite : List TestSeq := [testProblematic]

end Tests.Ix.Kernel.RustProblematic
