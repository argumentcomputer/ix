/-
  Self-contained TauCeti Eq.rec / Rule-K regression suite.

  The exact TauCeti theorem closures remain useful corpus acceptance tests,
  but are about 158 MiB each.  This suite compiles the two reducer-facing
  constants in `TauCetiReduction` directly and therefore needs neither
  TauCeti nor Mathlib.

  Run with: `lake test -- kernel-check-tauceti-reduction --ignored`
-/
import Ix.KernelCheck
import Ix.Meta
import Tests.Ix.Kernel.FocusedLeanCheck
import Tests.Ix.Kernel.TauCetiReduction
import Tests.Ix.Kernel.TutorialMeta
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI)

namespace Tests.Ix.Kernel.CheckTauCetiReduction

def focusConsts : Array Lean.Name := #[
  `Tests.Ix.Kernel.TauCetiReduction.composedApply,
  `Tests.Ix.Kernel.TauCetiReduction.composedSymmApply
]

def testRustCheckTauCetiReduction : TestSeq :=
  .individualIO s!"kernel check {focusConsts.size} inlined TauCeti reductions" none (do
    let leanEnv ← get_env!
    let (_, closedConsts) :=
      Tests.Ix.Kernel.TutorialMeta.collectDepsWithExtras leanEnv {} focusConsts.toList
    IO.println s!"[check-tauceti-reduction] compiling {closedConsts.length}-constant \
      closure for {focusConsts.size} subject(s)"

    let expected := focusConsts.map fun _ => true
    let start ← IO.monoMsNow
    let results ← rsCheckConstsFFI closedConsts focusConsts expected false
    let elapsed := (← IO.monoMsNow) - start

    let mut failures : Array (Lean.Name × String) := #[]
    for i in [:focusConsts.size] do
      if let some err := results[i]! then
        let message := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError m => s!"compile: {m}"
        failures := failures.push (focusConsts[i]!, message)

    IO.println s!"[check-tauceti-reduction] \
      {focusConsts.size - failures.size}/{focusConsts.size} passed in {elapsed}ms"
    for (name, message) in failures do
      IO.println s!"  ✗ {name}: {message}"

    if failures.isEmpty then
      return (true, focusConsts.size, focusConsts.size, none)
    return (false, focusConsts.size - failures.size, focusConsts.size,
      some s!"TauCeti reduction check failed with {failures.size} failure(s)")
  ) .done

def testLeanCheckTauCetiReduction : TestSeq :=
  .individualIO s!"Ix.Tc check {focusConsts.size} inlined TauCeti reductions" none (do
    let leanEnv ← get_env!
    let (_, closedConsts) :=
      Tests.Ix.Kernel.TutorialMeta.collectDepsWithExtras leanEnv {} focusConsts.toList
    IO.println s!"[check-tauceti-reduction/lean] compiling \
      {closedConsts.length}-constant closure for {focusConsts.size} subject(s)"
    Tests.Ix.Kernel.FocusedLeanCheck.checkClosure
      "check-tauceti-reduction/lean" "tauceti-reduction" closedConsts focusConsts
  ) .done

def suite : List TestSeq := [
  testRustCheckTauCetiReduction,
  testLeanCheckTauCetiReduction
]

end Tests.Ix.Kernel.CheckTauCetiReduction
