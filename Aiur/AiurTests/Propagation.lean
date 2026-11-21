import Aiur.Optimized.CheckedLayout
import Mathlib.Algebra.Field.Rat

namespace AiurPropagationTests

open Aiur Aiur.Optimized

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def optimize (chip : Circuit.Chip Rat) : IO (Circuit.Chip Rat) := do
  match Propagation.run chip with
  | .error error => throw (IO.userError error)
  | .ok result =>
      ensure "propagation produced an invalid layout" result.chip.wellFormed
      return result.chip

def copies : Circuit.Chip Rat := {
  name := "copies", inputs := [.field 0], output := .field (.var 3), numVars := 4
  constraints := [.sub (.var 1) (.var 0), .sub (.var 2) (.const 3),
    .sub (.var 3) (.add (.var 1) (.var 2))]
  sends := [], memory := [] }

def guarded : Circuit.Chip Rat := {
  name := "guarded", inputs := [.field 0], output := .field (.var 1), numVars := 2
  constraints := [.mul (.var 0) (.sub (.var 0) (.const 1)),
    .mul (.var 0) (.sub (.var 1) (.const 3))]
  sends := [], memory := [] }

/-- A linear-size circuit whose naive substitutions produce 2^depth copies of
the input in the output expression. Keep the optimized expression compact. -/
def doubling (depth : Nat) : Circuit.Chip Rat := {
  name := "doubling", inputs := [.field 0], output := .field (.var depth)
  numVars := depth + 1
  constraints := (List.range depth).map fun i =>
    .sub (.var (i + 1)) (.add (.var i) (.var i))
  sends := [], memory := [] }

def run : IO Unit := do
  ensure "scoped search stopped at a zero coefficient instead of trying the next variable"
    (ScopedPropagation.definition? (.add (.sub (.var 0) (.var 0)) (.var 1) : Polynomial Rat) ==
      some (1, .const 0))
  ensure "scoped search treated a nonlinear equation as an affine definition"
    (ScopedPropagation.definition? (.mul (.var 0) (.var 1) : Polynomial Rat)).isNone
  let copied ← optimize copies
  ensure "copy/constant chain retained columns or equations"
    (copied.numVars == 1 && copied.constraints.isEmpty &&
      copied.output == .field (.add (.var 0) (.const 3)))
  for x in ([-2, 0, 7] : List Rat) do
    ensure "provided affine expression changed"
      (copied.checkRow ⟨[]⟩ ⟨"copies", [x]⟩ ==
        .ok (⟨"copies", [.field x], .field (x + 3)⟩, []))
  let constant ← optimize {
    name := "constant", inputs := [], output := .field (.var 0), numVars := 1
    constraints := [.sub (.var 0) (.const 7)], sends := [], memory := [] }
  ensure "constant output requires a column"
    (constant.numVars == 0 && constant.output == .field (.const 7) && constant.constraints.isEmpty)
  ensure "zero-column row was rejected"
    (constant.checkRow ⟨[]⟩ ⟨"constant", []⟩ == .ok (⟨"constant", [], .field 7⟩, []))
  let branch ← optimize guarded
  ensure "guarded definition was substituted globally" (branch.numVars == 2)
  ensure "inactive branch constrained its unused value"
    (branch.checkRow ⟨[]⟩ ⟨"guarded", [0, 11]⟩ == .ok (⟨"guarded", [.field 0], .field 11⟩, []))
  ensure "active branch lost its equation" (branch.checkRow ⟨[]⟩ ⟨"guarded", [1, 11]⟩).toOption.isNone
  ensure "certificate accepted a guarded definition"
    (!decide (({ id := 1, value := .const 3 } : Propagation.Candidate Rat).Certificate guarded))
  ensure "certificate accepted a self-reference"
    (!decide (({ id := 1, value := .var 1 } : Propagation.Candidate Rat).Certificate copies))
  ensure "certificate invented an equality"
    (!decide (({ id := 1, value := .const 19 } : Propagation.Candidate Rat).Certificate copies))
  let proposal : Propagation.Proposal Rat := ⟨{id := 1, value := .var 0}, 0⟩
  ensure "indexed certificate rejected its defining equation" (proposal.check copies).isSome
  ensure "indexed certificate accepted an unrelated equation"
    (({proposal with equationIndex := 1}).check copies).isNone
  ensure "indexed certificate accepted an invalid equation index"
    (({proposal with equationIndex := 100}).check copies).isNone
  ensure "indexed certificate accepted a guarded definition"
    (({candidate := {id := 1, value := .const 3}, equationIndex := 1} :
      Propagation.Proposal Rat).check guarded).isNone
  let call : Circuit.Send Rat := ⟨"callee", [.field (.var 0)], .field 1, .const 1⟩
  let called ← optimize {
    name := "calls", inputs := [.field 0], output := .field (.var 2), numVars := 3
    constraints := [.sub (.var 2) (.var 1)], sends := [call, call], memory := [] }
  ensure "call output copy retained a column" (called.numVars == 2)
  ensure "repeated call requirements were merged"
    ((called.premises ⟨"calls", [2, 5]⟩) ==
      [⟨"callee", [.field 2], .field 5⟩, ⟨"callee", [.field 2], .field 5⟩])
  let memory ← optimize {
    name := "memory", inputs := [.field 0], output := ⟨.tuple [], []⟩, numVars := 2
    constraints := [.sub (.var 1) (.const 3)], sends := []
    memory := [⟨.var 0, .field (.var 1), .const 1⟩] }
  ensure "ROM constant retained a column" (memory.numVars == 1 && memory.memory.length == 1)
  ensure "ROM lookup changed after constant propagation"
    (memory.checkRow ⟨[(2, .field 3)]⟩ ⟨"memory", [2]⟩).toOption.isSome
  ensure "ROM membership was dropped"
    (memory.checkRow ⟨[(2, .field 4)]⟩ ⟨"memory", [2]⟩).toOption.isNone
  let nonlinear ← optimize {
    name := "square", inputs := [.field 0], output := .field (.var 1), numVars := 2
    constraints := [.sub (.var 1) (.mul (.var 0) (.var 0))], sends := [], memory := [] }
  ensure "nonlinear output bypassed the affine lookup bound"
    (nonlinear.numVars == 2 && nonlinear.stats.maxLookupDegree == 1)
  let cycle ← optimize {
    name := "cycle", inputs := [], output := .field (.var 0), numVars := 2
    constraints := [.sub (.var 0) (.var 1), .sub (.var 1) (.var 0)], sends := [], memory := [] }
  ensure "cyclic copies did not retain their free value" (cycle.numVars == 1 && cycle.constraints.isEmpty)
  let doubled ← optimize (doubling 30)
  ensure "linear substitutions expanded instead of collecting coefficients"
    (doubled.numVars == 1 && doubled.constraints.isEmpty &&
      doubled.output == .field (.mul (.const (2^30)) (.var 0)))
  ensure "normalized doubling chain changed the result"
    (doubled.checkRow ⟨[]⟩ ⟨"doubling", [3]⟩ ==
      .ok (⟨"doubling", [.field 3], .field (3 * 2^30)⟩, []))
  let nested : Polynomial Rat := .mul
    (.add (.var 0) (.sub (.var 1) (.var 0))) (.add (.var 0) (.var 0))
  ensure "linear parts of a nonlinear expression were not collected"
    (nested.normalizeLinear == .mul (.var 1) (.mul (.const 2) (.var 0)))
  IO.println "Passed propagation checks: expressions, constants, guards, ROM, repeated calls, degree bounds, and cyclic copies."

#print axioms Propagation.Candidate.equivalent
#print axioms Propagation.compact_equivalent
#print axioms Polynomial.denote_normalizeLinear
#print axioms Circuit.Chip.Equivalent.localRule

end AiurPropagationTests
