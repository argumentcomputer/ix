/-
  Focused PrimeGaps certificate reductions for both Ix kernels.

  Unlike the corpus checks, this suite is self-contained: the exact packed
  tables and reducer-facing theorem terms live in `PrimeGapsReduction`, and
  only their 393-constant transitive closure is compiled. No Palomar checkout
  or multi-gigabyte TruthMines artifact is required.

  Run with: `lake test -- kernel-check-primegaps --ignored`
-/
import Ix.Meta
import Tests.Ix.Kernel.FocusedLeanCheck
import Tests.Ix.Kernel.PrimeGapsReduction
import Tests.Ix.Kernel.TutorialMeta
import LSpec

open LSpec

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

def testLeanCheckPrimeGaps : TestSeq :=
  .individualIO s!"IxC check {focusConsts.size} inlined PrimeGaps consts" none (do
    let names ← filterFocusConsts focusConsts
    let leanEnv ← get_env!
    IO.println s!"[check-primegaps/lean] compiling \
      selected IxC closure for {names.size} exact subject(s)"
    Tests.Ix.Kernel.FocusedLeanCheck.checkClosure "check-primegaps/lean"
      "primegaps-reduction" leanEnv names
  ) .done

def suite : List TestSeq := [testLeanCheckPrimeGaps]

end Tests.Ix.Kernel.CheckPrimeGaps
