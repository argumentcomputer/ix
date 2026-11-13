import Tests.Ix.IxVM
import Tests.Ix.IxVM.FieldReductionDefs

/-! # Inductive types whose field or index types reduce

`Check` claims on the types and recursors of `Tests.Ix.IxVM.FieldReductionDefs`.
IxVM accepts non-recursive constructor field reduction (`KField`, `KField.rec`)
and former-telescope reduction (`KIndex`, `KIndex.rec`), and declines native
blocks whose constructor fields mention the block in a non-syntactic occurrence
(`ArrowTree`, `KTree`, `Phantom` and their recursors). -/

namespace Tests.Ix.IxVM.FieldReduction

open IxVM.ClaimHarness

/-- A fixture's name. -/
def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.FieldReductionDefs ++ n.toName

/-- Accepted constants: non-recursive field reduction and former reduction. -/
def acceptedNames : List String :=
  ["KField", "KField.rec", "KIndex", "KIndex.rec"]

/-- Declined constants: non-syntactic block occurrences in native constructor fields. -/
def declinedNames : List String :=
  ["ArrowTree", "ArrowTree.rec", "KTree", "KTree.rec", "Phantom", "Phantom.rec"]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let accepted := acceptedNames.map defs
  let declined := declinedNames.map defs
  let all := accepted ++ declined
  let missing := all.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-field-reduction] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv all.toArray leanEnv
  let acceptCases := accepted.map fun n => Tests.Ix.IxVM.kernelCheckCase env n true
  let declineCases : List Builder := declined.map fun n => fun u => do
    let c ← Tests.Ix.IxVM.kernelCheckCase env n true u
    return { c with accept := false, rejectsWith := some "strict positivity: non-syntactic" }
  runCases "ixvm-field-reduction" (acceptCases ++ declineCases).toArray

end Tests.Ix.IxVM.FieldReduction
