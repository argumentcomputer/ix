import Aiur.Optimized.AllocationCertificate
import Mathlib.Algebra.Field.Rat

namespace AiurCompilerIndexTests
open Aiur Aiur.Optimized

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def referenceControl (chip : ScopedChip Rat) : Bool :=
  @decide (Control.Certificate chip) (by
    unfold Control.Certificate Control.Choice.Checked
    infer_instance)

private def referenceAllocation (chip : ScopedChip Rat) (layout : ColumnLayout) : Bool :=
  @decide (Allocation.Certificate chip layout) (by
    unfold Allocation.Certificate
    infer_instance)

set_option synthInstance.maxSize 4096 in
private def referenceDegree (source target : ScopedChip Rat)
    (definitions : List (Degree.Definition Rat)) (values : Array (Polynomial Rat)) : Bool :=
  @decide (Degree.Certificate source target definitions values) (by
    unfold Degree.Certificate
    dsimp only
    infer_instance)

private def branches : ScopedChip Rat := {
  name := "indexed branches"
  inputs := [.field 0], output := .field 0
  roles := #[.input, .selector, .selector, .auxiliary 1, .auxiliary 2]
  aliases := #[none, none, none, none, none]
  scopes := #[⟨.const 1, []⟩, ⟨.var 1, [(0, 0)]⟩, ⟨.var 2, [(0, 1)]⟩]
  choices := #[⟨0, [1, 2]⟩]
  equations := #[⟨0, .sub (.add (.var 1) (.var 2)) (.const 1)⟩,
    ⟨0, .mul (.var 2) (.var 1)⟩,
    ⟨1, .sub (.var 3) (.var 0)⟩, ⟨2, .sub (.var 4) (.var 0)⟩]
  calls := #[], cells := #[] }

private def shared : ColumnLayout :=
  ⟨#[some 0, some 1, some 2, some 3, some 3], #[[0], [1], [2], [3, 4]]⟩

def run : IO Unit := do
  let missing := { branches with equations := branches.equations.extract 1 4 }
  let guarded := { branches with
    equations := branches.equations.modify 0 (fun eq => { eq with scope := 1 }) }
  -- Same index key, different field constant: indexing must not authorize it.
  let collision := { branches with
    equations := branches.equations.set! 0 ⟨0, .sub (.add (.var 1) (.var 2)) (.const 2)⟩ }
  let normalized := { branches with
    equations := branches.equations.map (fun eq => { eq with polynomial := .add (.const 0) eq.polynomial }) }
  for (chip, expected) in [(branches, true), (missing, false), (guarded, false),
      (collision, false), (normalized, true)] do
    ensure "indexed control certificate disagreed with exhaustive checking"
      (decide (Control.Certificate chip) == referenceControl chip)
    ensure "indexed control certificate lost or invented a global equation"
      (decide (Control.Certificate chip) == expected)
  let aliasedInput := { shared with columnOf := shared.columnOf.set! 3 (some 0) }
  let aliasedSelectors := { shared with columnOf := shared.columnOf.set! 2 (some 1) }
  let unallocated := { shared with columnOf := shared.columnOf.set! 3 none }
  for (layout, expected) in [(shared, true), (aliasedInput, false),
      (aliasedSelectors, false), (unallocated, false)] do
    ensure "indexed allocation certificate disagreed with all-pairs checking"
      (decide (Allocation.Certificate branches layout) == referenceAllocation branches layout)
    ensure "allocation certificate accepted simultaneous column occupants"
      (decide (Allocation.Certificate branches layout) == expected)
  let quartic := { branches with
    equations := branches.equations.push ⟨1,
      .sub (.var 3) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))⟩ }
  let state ← IO.ofExcept (Degree.boundState {} quartic)
  ensure "degree fixture did not allocate a product witness" (!state.cache.isEmpty)
  let values := Degree.expand state.chip.roles.size state.cache
  let missing := { state.chip with equations := #[] }
  let misplaced := { state.chip with
    equations := state.chip.equations.map fun eq => { eq with scope := 0 } }
  let wrongConstant := { state.chip with
    equations := state.chip.equations.map fun eq =>
      { eq with polynomial := .add eq.polynomial (.const 1) } }
  for (target, expected) in [(state.chip, true), (missing, false),
      (misplaced, false), (wrongConstant, false)] do
    let checked := decide (Degree.Certificate quartic target state.cache values)
    ensure "indexed degree certificate disagreed with exhaustive checking"
      (checked == referenceDegree quartic target state.cache values)
    ensure "degree certificate lost a defining equation or its scope" (checked == expected)
  IO.println "Passed compiler-index checks: normalization, collisions, global equations, degree definitions, and exclusive column sharing."

#print axioms Index.getD_build
#print axioms Control.zeroEquation_iff_indexed
#print axioms Allocation.sharing_iff_indexed
#print axioms EquationIndex.member_build

end AiurCompilerIndexTests
