import Compilatrix.Ixby.Inline.Optimize
import Compilatrix.Ixby.Lean

/-! Apply the checked pass after the typed frontend has finished building its
image. Keep the builder slots synchronized with the selected program so that
reporting or a later `finishProgram` cannot silently restore the original code.
This interface adds an Ixby-to-Ixby certificate, not a source certificate. -/

namespace Compilatrix.Ixby.Inline

open LeanFrontend

structure ImageOutcome (source : Image) (protectedPrefix : Nat) where
  selected : Outcome source.state.limits source.program protectedPrefix

def ImageOutcome.image {source protectedPrefix}
    (result : ImageOutcome source protectedPrefix) : Image := {
  source with
  program := result.selected.program
  state := { source.state with functions := source.state.functions.mapIdx fun index slot =>
    { slot with value := result.selected.program.functions[index]? } } }

/-- The policy explicitly identifies any protected runtime prefix. Callers
exporting runtime images additionally run their existing helper certificates
on the selected image, and recheck the binary after serialization. -/
def optimizeImage (source : Image) (policy : Policy) :
    Except String (ImageOutcome source policy.protectedPrefix) := do
  unless source.state.functions.size == source.program.functions.size do
    throw "inline image: builder function count differs"
  for (slot, index) in source.state.functions.zipIdx do
    unless slot.value == source.program.functions[index]? do
      throw s!"inline image: builder function body differs at {index}"
    unless (source.program.functions[index]?).map (·.arity) == some slot.arity do
      throw s!"inline image: builder function arity differs at {index}"
  unless source.state.constructors == source.program.constructors do
    throw "inline image: builder constructors differ"
  return ⟨← optimize source.state.limits source.program policy⟩

end Compilatrix.Ixby.Inline
