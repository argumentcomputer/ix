import Aiur.Scalar
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur.Scalar Aiur.Scalar.Circuit

namespace AiurCircuitTests

def division : Program Nat := scalar_aiur% "
fn square(x) { x * x }
fn main(x, y) { square(x / y) }
"

def matching : Program Nat := scalar_aiur% "
fn choose(x) { match x { 0 => 10, 2 => 20, _ => 30 } }
fn partial_match(x) { match x { 0 => 10 } }
fn discarded(x) { match x { _ => 11, 0 => discarded(x), 0 => 99 } }
"

def nested : Program Nat := scalar_aiur% "
fn guarded(x) {
  match x {
    0 => 7,
    _ => match x { 1 => 1 / 0, _ => looping(x) },
  }
}
fn looping(x) { looping(x) }
"

def recursion : Program Nat := scalar_aiur% "
fn even(n) { match n { 0 => 1, _ => odd(n - 1) } }
fn odd(n) { match n { 0 => 0, _ => even(n - 1) } }
"

def repeated : Program Nat := scalar_aiur% "
fn square(x) { x * x }
fn twice(x) { square(x) + square(x) }
"

def duplicates : Program Nat := scalar_aiur% "fn bad(x) { match x { 0 => 1, 0 => 2 } }"
def collisions : Program Nat := scalar_aiur% "fn bad(x) { match x { 0 => 1, 7 => 2, _ => 3 } }"

private def checkedCompile [Field F] [DecidableEq F] (program : Program F) : IO (System F) :=
  match compile program with
  | .ok system => pure system
  | .error error => throw (IO.userError s!"unexpected compilation failure: {error}")

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"circuit test failed: {label}")

private def expect (label : String) (actual expected : Except WitnessError Unit) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

private def rejects (label : String) (actual : Except WitnessError Unit) : IO Unit :=
  check label (match actual with | .error _ => true | .ok () => false)

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def run : IO Unit := do
  let arithmetic ← checkedCompile (division.toField Rat)
  let entry : Message Rat := ⟨"main", [6, 2], 9⟩
  -- main: x, y, output, inverse(y), call result. square: x, output.
  let divisionRow : Row Rat := ⟨"main", [6, 2, 9, 1 / 2, 9]⟩
  let calleeRow : Row Rat := ⟨"square", [3, 9]⟩
  let rows := [divisionRow, calleeRow]
  expect "division and call" (arithmetic.check entry rows) (.ok ())
  expect "row order" (arithmetic.check entry rows.reverse) (.ok ())
  let reordered : System Rat := { arithmetic with chips := arithmetic.chips.map fun (chip : Chip Rat) =>
    { chip with constraints := chip.constraints.reverse, sends := chip.sends.reverse } }
  expect "equation order" (reordered.check entry rows) (.ok ())
  expect "missing callee" (arithmetic.check entry [divisionRow]) (.error .unbalancedMessages)
  expect "forged return value"
    (arithmetic.check ⟨"main", [6, 2], 10⟩
      [⟨"main", [6, 2, 10, 1 / 2, 10]⟩, ⟨"square", [3, 9]⟩])
    (.error .unbalancedMessages)
  expect "wrong callee arguments"
    (arithmetic.check entry [divisionRow, ⟨"square", [4, 16]⟩]) (.error .unbalancedMessages)
  rejects "incorrect inverse"
    (arithmetic.check entry [⟨"main", [6, 2, 9, 1, 9]⟩, calleeRow])
  rejects "zero divided by zero"
    (arithmetic.check ⟨"main", [0, 0], 0⟩ [⟨"main", [0, 0, 0, 0, 0]⟩, ⟨"square", [0, 0]⟩])
  expect "wrong row length" (arithmetic.check entry [⟨"main", [6, 2, 9]⟩])
    (.error (.wrongRowSize "main" 5 3))
  expect "unknown row chip" (arithmetic.check entry [⟨"unknown", []⟩])
    (.error (.unknownChip "unknown"))

  let choices ← checkedCompile (matching.toField Rat)
  -- choose: x, output, match result, selectors for 0/2/default, default's two inverses.
  expect "first literal"
    (choices.check ⟨"choose", [0], 10⟩ [⟨"choose", [0, 10, 10, 1, 0, 0, 0, 0]⟩]) (.ok ())
  expect "second literal"
    (choices.check ⟨"choose", [2], 20⟩ [⟨"choose", [2, 20, 20, 0, 1, 0, 0, 0]⟩]) (.ok ())
  expect "default excludes every literal"
    (choices.check ⟨"choose", [3], 30⟩ [⟨"choose", [3, 30, 30, 0, 0, 1, 1 / 3, 1]⟩]) (.ok ())
  rejects "no branch selected"
    (choices.check ⟨"choose", [0], 10⟩ [⟨"choose", [0, 10, 10, 0, 0, 0, 0, 0]⟩])
  rejects "wrong literal selected"
    (choices.check ⟨"choose", [0], 20⟩ [⟨"choose", [0, 20, 20, 0, 1, 0, 0, 0]⟩])
  rejects "default cannot steal a literal case"
    (choices.check ⟨"choose", [0], 30⟩ [⟨"choose", [0, 30, 30, 0, 0, 1, 1, -(1 / 2)]⟩])
  rejects "multiple branches selected"
    (choices.check ⟨"choose", [0], 10⟩ [⟨"choose", [0, 10, 10, 1, 1, 0, 0, 0]⟩])
  rejects "fractional selector"
    (choices.check ⟨"choose", [3], 30⟩ [⟨"choose", [3, 30, 30, 0, 0, 1 / 2, 1 / 3, 1]⟩])
  rejects "uncovered match, no selector"
    (choices.check ⟨"partial_match", [1], 10⟩ [⟨"partial_match", [1, 10, 10, 0]⟩])
  rejects "uncovered match, forced selector"
    (choices.check ⟨"partial_match", [1], 10⟩ [⟨"partial_match", [1, 10, 10, 1]⟩])
  expect "arms after wildcard discarded"
    (choices.check ⟨"discarded", [0], 11⟩ [⟨"discarded", [0, 11, 11, 1]⟩]) (.ok ())
  check "discarded call has no send" ((choices.findChip? "discarded").any (·.sends.isEmpty))

  let guarded ← checkedCompile (nested.toField Rat)
  expect "inactive nested division and recursion"
    (guarded.check ⟨"guarded", [0], 7⟩
      [⟨"guarded", [0, 7, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩]) (.ok ())
  rejects "inactive nested match cannot select a branch"
    (guarded.check ⟨"guarded", [0], 7⟩
      [⟨"guarded", [0, 7, 7, 1, 0, 0, 0, 0, 0, 1, -1, 0]⟩])
  rejects "active nested division by zero"
    (guarded.check ⟨"guarded", [1], 0⟩
      [⟨"guarded", [1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0]⟩])
  expect "self-supporting recursive row is insufficient"
    (guarded.check ⟨"looping", [1], 5⟩ [⟨"looping", [1, 5, 5]⟩]) (.error .unbalancedMessages)

  let recursiveSystem ← checkedCompile (recursion.toField Rat)
  check "one chip per recursive function" (recursiveSystem.chips.length == 2)
  expect "mutual recursion witness"
    (recursiveSystem.check ⟨"even", [2], 1⟩
      [⟨"even", [0, 1, 1, 1, 0, 0, 0]⟩,
       ⟨"even", [2, 1, 1, 0, 1, 1 / 2, 1]⟩,
       ⟨"odd", [1, 1, 1, 0, 1, 1, 1]⟩]) (.ok ())

  let twice ← checkedCompile (repeated.toField Rat)
  let twiceEntry : Message Rat := ⟨"twice", [3], 18⟩
  let twiceRow : Row Rat := ⟨"twice", [3, 18, 9, 9]⟩
  let squareRow : Row Rat := ⟨"square", [3, 9]⟩
  expect "repeated messages count separately"
    (twice.check twiceEntry [twiceRow, squareRow, squareRow]) (.ok ())
  expect "one receive cannot discharge two calls"
    (twice.check twiceEntry [twiceRow, squareRow]) (.error .unbalancedMessages)
  check "each call result is fresh"
    ((twice.findChip? "twice").any fun chip =>
      chip.sends.length == 2 && decide ((chip.sends.map (·.result)).Nodup))

  check "duplicate patterns rejected"
    (match compile (duplicates.toField Rat) with
    | .error (.duplicatePattern "bad") => true
    | _ => false)
  check "patterns checked after field conversion"
    (match compile (collisions.toField (ZMod 7)) with
    | .error (.duplicatePattern "bad") => true
    | _ => false)
  let finite ← checkedCompile (division.toField (ZMod 7))
  expect "finite-field division and call"
    (finite.check ⟨"main", [6, 2], 2⟩
      [⟨"main", [6, 2, 2, 4, 2]⟩, ⟨"square", [3, 2]⟩]) (.ok ())
  let finiteChoices ← checkedCompile (matching.toField (ZMod 7))
  expect "finite-field default inverses"
    (finiteChoices.check ⟨"choose", [3], 2⟩
      [⟨"choose", [3, 2, 2, 0, 0, 1, 5, 1]⟩]) (.ok ())
  IO.println "Passed circuit compilation and witness checks."

end AiurCircuitTests
