/-
  Focused CompPoly regression checks through the serialized Rust-kernel path.

  `BF128Ghash.gcd_start_reduction` exposed a pathological equal-rank delta
  walk when its shared `Abbrev` head was excluded from same-head congruence.
  Keep the exact theorem here so the regression can be reproduced without a
  full CompPoly sweep.

  Requires `comppoly.ixe` at the repository root. Run with:

    lake exe ix compile Benchmarks/Compile/CompPoly.lean \
      --out comppoly.ixe --verbose
    lake test -- kernel-check-comppoly --ignored
-/
import Ix.KernelCheck
import LSpec

open LSpec
open Ix.KernelCheck (rsCheckIxonFFI)

namespace Tests.Ix.Kernel.CheckCompPoly

def ixePath : System.FilePath := "comppoly.ixe"

def focusConsts : Array Lean.Name := #[
  `BF128Ghash.gcd_start_reduction
]

private def filterFocusConsts (names : Array Lean.Name) : IO (Array Lean.Name) := do
  match (← IO.getEnv "IX_KERNEL_FOCUS_CONST") with
  | none => pure names
  | some filter =>
    let filtered := names.filter fun name => name.toString.contains filter
    IO.println s!"[check-comppoly] IX_KERNEL_FOCUS_CONST={filter} matched \
      {filtered.size}/{names.size}"
    pure filtered

def testRustCheckCompPoly : TestSeq :=
  .individualIO s!"kernel check {focusConsts.size} CompPoly focus const(s)" none (do
    unless (← ixePath.pathExists) do
      return (false, 0, focusConsts.size, some s!"{ixePath} missing — build it with \
        `lake exe ix compile Benchmarks/Compile/CompPoly.lean \
          --out comppoly.ixe --verbose`")
    let names ← filterFocusConsts focusConsts
    if names.isEmpty then
      return (false, 0, 0, some "IX_KERNEL_FOCUS_CONST matched no CompPoly canary")
    let start ← IO.monoMsNow
    let expected := names.map fun _ => true
    let results ← rsCheckIxonFFI ixePath.toString names expected false ""
    let elapsed := (← IO.monoMsNow) - start
    let mut failures : Array (Lean.Name × String) := #[]
    for i in [:names.size] do
      if let some err := results[i]! then
        failures := failures.push (names[i]!, err.message)
    IO.println s!"[check-comppoly] {names.size - failures.size}/{names.size} \
      passed in {elapsed}ms"
    for (name, msg) in failures do
      IO.println s!"  ✗ {name}: {msg}"
    if failures.isEmpty then
      return (true, names.size, names.size, none)
    return (false, names.size - failures.size, names.size,
      some s!"CompPoly focus check failed with {failures.size} failure(s)")
  ) .done

def suite : List TestSeq := [testRustCheckCompPoly]

end Tests.Ix.Kernel.CheckCompPoly
