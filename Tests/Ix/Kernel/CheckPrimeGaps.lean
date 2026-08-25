/-
  Focused PrimeGaps certificate reductions for both Ix kernels.

  Unlike the corpus checks, this suite is self-contained: the exact packed
  tables and reducer-facing theorem terms live in `PrimeGapsReduction`, and
  only their 393-constant transitive closure is compiled. No Palomar checkout
  or multi-gigabyte TruthMines artifact is required.

  Run with: `lake test -- kernel-check-primegaps --ignored`
-/
import Ix.KernelCheck
import Ix.Meta
import Tests.Ix.Kernel.FocusedLeanCheck
import Tests.Ix.Kernel.PrimeGapsReduction
import Tests.Ix.Kernel.TutorialMeta
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI)

namespace Tests.Ix.Kernel.CheckPrimeGaps

def focusConsts : Array Lean.Name := #[
  `Tests.Ix.Kernel.PrimeGapsReduction.dataOk,
  `Tests.Ix.Kernel.PrimeGapsReduction.encOk
]

private def filterFocusConsts (names : Array Lean.Name) : IO (Array Lean.Name) := do
  match (← IO.getEnv "IX_KERNEL_FOCUS_CONST") with
  | none => pure names
  | some filter =>
    let filtered := names.filter fun name => name.toString.contains filter
    IO.println s!"[check-primegaps] IX_KERNEL_FOCUS_CONST={filter} matched \
      {filtered.size}/{names.size}"
    pure filtered

def testRustCheckPrimeGaps : TestSeq :=
  .individualIO s!"kernel check {focusConsts.size} inlined PrimeGaps consts" none (do
    let names ← filterFocusConsts focusConsts
    if names.isEmpty then
      return (false, 0, 0, some "IX_KERNEL_FOCUS_CONST matched no PrimeGaps canary")

    let leanEnv ← get_env!
    let (_, closedConsts) :=
      Tests.Ix.Kernel.TutorialMeta.collectDepsWithExtras leanEnv {} names.toList
    IO.println s!"[check-primegaps] compiling {closedConsts.length}-constant \
      closure for {names.size} exact subject(s)"

    let expected := names.map fun _ => true
    let start ← IO.monoMsNow
    let results ← rsCheckConstsFFI closedConsts names expected false
    let elapsed := (← IO.monoMsNow) - start

    let mut failures : Array (Lean.Name × String) := #[]
    for i in [:names.size] do
      if let some err := results[i]! then
        let message := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError m => s!"compile: {m}"
        failures := failures.push (names[i]!, message)

    IO.println s!"[check-primegaps] {names.size - failures.size}/{names.size} \
      passed in {elapsed}ms"
    for (name, message) in failures do
      IO.println s!"  ✗ {name}: {message}"

    if failures.isEmpty then
      return (true, names.size, names.size, none)
    return (false, names.size - failures.size, names.size,
      some s!"PrimeGaps focus check failed with {failures.size} failure(s)")
  ) .done

def testLeanCheckPrimeGaps : TestSeq :=
  .individualIO s!"Ix.Tc check {focusConsts.size} inlined PrimeGaps consts" none (do
    let names ← filterFocusConsts focusConsts
    let leanEnv ← get_env!
    let (_, closedConsts) :=
      Tests.Ix.Kernel.TutorialMeta.collectDepsWithExtras leanEnv {} names.toList
    IO.println s!"[check-primegaps/lean] compiling \
      {closedConsts.length}-constant closure for {names.size} exact subject(s)"
    Tests.Ix.Kernel.FocusedLeanCheck.checkClosure "check-primegaps/lean"
      "primegaps-reduction" closedConsts names
  ) .done

def suite : List TestSeq := [testRustCheckPrimeGaps, testLeanCheckPrimeGaps]

end Tests.Ix.Kernel.CheckPrimeGaps
