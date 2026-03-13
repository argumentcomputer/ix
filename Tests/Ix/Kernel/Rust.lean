/-
  Rust kernel FFI integration tests.
  Exercises the Rust NbE kernel (via rs_check_consts2) against the
  shared regression constant list.
-/
import Ix.Kernel
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Consts
import LSpec

open LSpec

namespace Tests.Ix.Kernel.Rust

/-- Typecheck regression constants through the Rust FFI kernel. -/
def testConsts : TestSeq :=
  .individualIO "rust kernel const checks" (do
    let leanEnv ← get_env!
    let constNames := Consts.regressionConsts

    IO.println s!"[rust-kernel-consts] checking {constNames.size} constants via Rust FFI..."
    let start ← IO.monoMsNow
    let results ← Ix.Kernel.rsCheckConsts leanEnv constNames
    let elapsed := (← IO.monoMsNow) - start
    IO.println s!"[rust-kernel-consts] batch check completed in {elapsed.formatMs}"

    let mut passed := 0
    let mut failures : Array String := #[]
    for (name, result) in results do
      match result with
      | none =>
        IO.println s!"  ✓ {name}"
        passed := passed + 1
      | some err =>
        IO.println s!"  ✗ {name}: {repr err}"
        failures := failures.push s!"{name}: {repr err}"

    IO.println s!"[rust-kernel-consts] {passed}/{constNames.size} passed ({elapsed.formatMs})"
    if failures.isEmpty then
      return (true, none)
    else
      return (false, some s!"{failures.size} failure(s)")
  ) .done

/-- Test Rust kernel env conversion with structural verification. -/
def testConvertEnv : TestSeq :=
  .individualIO "rust kernel convert env" (do
    let leanEnv ← get_env!
    let leanCount := leanEnv.constants.toList.length
    IO.println s!"[rust-kernel-convert] Lean env: {leanCount} constants"
    let start ← IO.monoMsNow
    let result ← Ix.Kernel.rsConvertEnv leanEnv
    let elapsed := (← IO.monoMsNow) - start
    if result.size < 5 then
      let status := result.getD 0 "no result"
      IO.println s!"[rust-kernel-convert] FAILED: {status} in {elapsed.formatMs}"
      return (false, some status)
    else
      let status := result[0]!
      let kenvSize := result[1]!
      let primsFound := result[2]!
      let quotInit := result[3]!
      let mismatchCount := result[4]!
      IO.println s!"[rust-kernel-convert] kenv={kenvSize} prims={primsFound} quot={quotInit} mismatches={mismatchCount} in {elapsed.formatMs}"
      -- Report details (missing prims and mismatches)
      for i in [5:result.size] do
        IO.println s!"  {result[i]!}"
      if status == "ok" then
        return (true, none)
      else
        return (false, some s!"{status}: {mismatchCount} mismatches")
  ) .done

def constSuite : List TestSeq := [testConsts]
def convertSuite : List TestSeq := [testConvertEnv]

end Tests.Ix.Kernel.Rust
