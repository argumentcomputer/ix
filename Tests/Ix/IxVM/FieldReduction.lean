import Tests.Ix.IxVM
import Tests.Ix.IxVM.FieldReductionDefs

/-! # Inductive types whose field or index types reduce

`Check` claims on the types and recursors of `Tests.Ix.IxVM.FieldReductionDefs`.
IxVM accepts non-recursive constructor field reduction (`KField`, `KField.rec`),
declines native blocks whose former telescope reduces beyond δβζ
(`KIndex`, `KIndex.rec`, whose index telescope reduces via `@Eq.rec`), and
declines native blocks whose constructor fields mention the block in a
non-syntactic occurrence (`ArrowTree`, `KTree`, `Phantom` and their recursors). -/

namespace Tests.Ix.IxVM.FieldReduction

open IxVM.ClaimHarness

/-- A fixture's name. -/
def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.FieldReductionDefs ++ n.toName

/-- Accepted constants: non-recursive constructor field reduction. -/
def acceptedNames : List String :=
  ["KField", "KField.rec"]

/-- Declined constants: former-telescope reduction beyond δβζ (K-like `@Eq.rec`). -/
def declinedFormerNames : List String :=
  ["KIndex", "KIndex.rec"]

/-- Declined constants: non-syntactic block occurrences in native constructor fields. -/
def declinedNames : List String :=
  ["ArrowTree", "ArrowTree.rec", "KTree", "KTree.rec", "Phantom", "Phantom.rec"]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let accepted := acceptedNames.map defs
  let declinedFormer := declinedFormerNames.map defs
  let declined := declinedNames.map defs
  let all := accepted ++ declinedFormer ++ declined
  let missing := all.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-field-reduction] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv all.toArray leanEnv
  let acceptCases := accepted.map fun n => Tests.Ix.IxVM.kernelCheckCase env n true
  let declineFormerCases : List Builder := declinedFormer.map fun n => fun u => do
    let c ← Tests.Ix.IxVM.kernelCheckCase env n true u
    return { c with accept := false, rejectsWith := some "KernelGuard::definition_value" }
  let declineCases : List Builder := declined.map fun n => fun u => do
    let c ← Tests.Ix.IxVM.kernelCheckCase env n true u
    return { c with accept := false, rejectsWith := some "strict positivity: non-syntactic" }
  runCases "ixvm-field-reduction" (acceptCases ++ declineFormerCases ++ declineCases).toArray

end Tests.Ix.IxVM.FieldReduction
