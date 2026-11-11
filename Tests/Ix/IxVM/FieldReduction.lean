import Tests.Ix.IxVM
import Tests.Ix.IxVM.FieldReductionDefs

/-! # Recursors of inductive types whose field or index types reduce

`Check` claims on the recursors of `Tests.Ix.IxVM.FieldReductionDefs`, each of
which Lean's kernel accepts. IxVM reconstructs the canonical recursor and
compares it with the stored one; the reconstruction head-normalizes field and
index types that mention earlier binders, so it must do so in their context. -/

namespace Tests.Ix.IxVM.FieldReduction

open IxVM.ClaimHarness

/-- A fixture's name. -/
def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.FieldReductionDefs ++ n.toName

/-- The checked constants: the types and their recursors. -/
def names : List String :=
  ["ArrowTree", "ArrowTree.rec", "KField", "KField.rec", "KTree", "KTree.rec",
   "KIndex", "KIndex.rec"]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let all := names.map defs
  let missing := all.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.println s!"[ixvm-field-reduction] not in the environment (Lean refused them): {missing}"
  let present := all.filter leanEnv.constants.contains
  let env ← loadSharedIxonEnv present.toArray leanEnv
  runCases "ixvm-field-reduction"
    (present.map fun n => Tests.Ix.IxVM.kernelCheckCase env n true).toArray

end Tests.Ix.IxVM.FieldReduction
