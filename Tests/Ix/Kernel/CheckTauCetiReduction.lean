/-
  Self-contained TauCeti Eq.rec / Rule-K regression suite.

  The exact TauCeti theorem closures remain useful corpus acceptance tests,
  but are about 158 MiB each.  This suite compiles the two reducer-facing
  constants in `TauCetiReduction` directly and therefore needs neither
  TauCeti nor Mathlib.

  Run with: `lake test -- kernel-check-tauceti-reduction --ignored`
-/
import Ix.Meta
import Tests.Ix.Kernel.FocusedLeanCheck
import Tests.Ix.Kernel.TauCetiReduction
import Tests.Ix.Kernel.TutorialMeta
import LSpec

open LSpec

namespace Tests.Ix.Kernel.CheckTauCetiReduction

def focusConsts : Array Lean.Name := #[
  `Tests.Ix.Kernel.TauCetiReduction.composedApply,
  `Tests.Ix.Kernel.TauCetiReduction.composedSymmApply
]

def testLeanCheckTauCetiReduction : TestSeq :=
  .individualIO s!"IxC check {focusConsts.size} inlined TauCeti reductions" none (do
    let leanEnv ← get_env!
    IO.println s!"[check-tauceti-reduction/lean] compiling \
      selected IxC closure for {focusConsts.size} subject(s)"
    Tests.Ix.Kernel.FocusedLeanCheck.checkClosure
      "check-tauceti-reduction/lean" "tauceti-reduction" leanEnv focusConsts
  ) .done

def suite : List TestSeq := [
  testLeanCheckTauCetiReduction
]

end Tests.Ix.Kernel.CheckTauCetiReduction
