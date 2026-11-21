import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur Aiur.Circuit

namespace AiurAccumulatorTests

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def source : Program Nat := aiur% "
table keys: () { (), }
table values: Field { 7, }
map known() -> Field = keys => values;
fn leaf() -> Field { 7 }
fn twice() -> Field { leaf() + leaf() }
fn loop() -> Field { loop() }
fn tables() -> Field { known() + known() }
fn memory(x: Field) -> Field { *&x }
"

def system (F : Type) [Field F] [DecidableEq F] : System F :=
  (compile (source.toField F)).toOption.getD { chips := [] }

def leaf : Row Rat := ⟨"leaf", [7]⟩
def twice : Row Rat := ⟨"twice", [14, 7, 7]⟩
def loop : Row Rat := ⟨"loop", [99, 99]⟩
def root : Message Rat := ⟨"twice", [], 14⟩
def loopClaim : Message Rat := ⟨"loop", [], 99⟩

private def unit (claim : Message Rat) (rows : List (Row Rat)) :=
  (system Rat).check ⟨[]⟩ claim rows

private def memo (claim : Message Rat) (rows : List (WeightedRow Rat)) :=
  (system Rat).checkMemo ⟨[]⟩ claim rows

def checks : List (String × Except WitnessError Unit × Except WitnessError Unit) := [
  ("unit requires duplicate rows", unit root [twice, leaf, leaf], .ok ()),
  ("unit cannot reuse one provide", unit root [twice, leaf], .error .unbalancedMessages),
  ("row order is irrelevant", unit root [leaf, twice, leaf], .ok ()),
  ("memo shares one leaf", memo root [⟨twice, 1⟩, ⟨leaf, 2⟩], .ok ()),
  ("memo row order is irrelevant", memo root [⟨leaf, 2⟩, ⟨twice, 1⟩], .ok ()),
  ("provide multiplicity must balance", memo root [⟨twice, 1⟩, ⟨leaf, 1⟩], .error .unbalancedMessages),
  ("requires are not multiplied", memo root [⟨twice, 2⟩, ⟨leaf, 4⟩], .error .unbalancedMessages),
  ("zero provide still requires premises", memo root [⟨twice, 1⟩, ⟨leaf, 2⟩, ⟨loop, 0⟩],
    .error .unbalancedMessages),
  ("signed provides cancel exactly", memo root [⟨twice, 1⟩, ⟨leaf, 3⟩, ⟨leaf, -1⟩], .ok ()),
  ("negative provide alone cannot prove root", memo ⟨"leaf", [], 7⟩ [⟨leaf, -1⟩],
    .error .unbalancedMessages),
  ("unit cycle cannot justify root", unit loopClaim [loop], .error .unbalancedMessages),
  ("memo cycle can justify root", memo loopClaim [⟨loop, 2⟩], .ok ()),
  ("unused balanced cycle is allowed", unit root [twice, leaf, loop, leaf], .ok ()),
  ("zero weight cannot bypass constraints", memo root
    [⟨twice, 1⟩, ⟨leaf, 2⟩, ⟨⟨"leaf", [8]⟩, 0⟩], .error (.constraintNotZero "leaf" 0)),
  ("zero weight cannot bypass row width", memo root
    [⟨twice, 1⟩, ⟨leaf, 2⟩, ⟨⟨"leaf", []⟩, 0⟩], .error (.wrongRowSize "leaf" 1 0)),
  ("unknown weighted row", memo root [⟨⟨"absent", []⟩, 0⟩], .error (.unknownChip "absent")),
  ("unit static root", unit ⟨"known", [], 7⟩ [], .ok ()),
  ("memo static root", memo ⟨"known", [], 7⟩ [], .ok ()),
  ("false static claim", memo ⟨"known", [], 8⟩ [], .error .unbalancedMessages),
  ("unit static leaves are reusable", unit ⟨"tables", [], 14⟩ [⟨"tables", [14, 7, 7]⟩], .ok ()),
  ("memo static leaves are reusable", memo ⟨"tables", [], 14⟩ [⟨⟨"tables", [14, 7, 7]⟩, 1⟩], .ok ()),
  ("memo ROM membership", (system Rat).checkMemo ⟨[(99, 7)]⟩ ⟨"memory", [7], 7⟩
    [⟨⟨"memory", [7, 7, 99, 7]⟩, 1⟩], .ok ()),
  ("memo missing ROM cell", memo ⟨"memory", [7], 7⟩ [⟨⟨"memory", [7, 7, 99, 7]⟩, 1⟩],
    .error (.missingCell "memory" 0)),
  ("memo rejects nonfunctional ROM", (system Rat).checkMemo ⟨[(99, 7), (99, 8)]⟩
    ⟨"memory", [7], 7⟩ [⟨⟨"memory", [7, 7, 99, 7]⟩, 1⟩], .error .invalidROM),
  ("memo rejects pointer arguments", memo ⟨"memory", [.ptr .field 99], 7⟩ [],
    .error .pointerEntryArgument),
  ("memo rejects malformed root", memo ⟨"leaf", [], ⟨.field, []⟩⟩ [], .error .malformedEntry)
]

-- Balance remains exact even when two requirements would vanish in the circuit field.
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example : (system (ZMod 2)).check ⟨[]⟩ ⟨"twice", [], 0⟩ [⟨"twice", [0, 1, 1]⟩] =
    .error .unbalancedMessages := by decide +kernel
example : (system (ZMod 2)).checkMemo ⟨[]⟩ ⟨"twice", [], 0⟩ [⟨⟨"twice", [0, 1, 1]⟩, 1⟩] =
    .error .unbalancedMessages := by decide +kernel
example : (system (ZMod 2)).checkMemo ⟨[]⟩ ⟨"twice", [], 0⟩
    [⟨⟨"twice", [0, 1, 1]⟩, 1⟩, ⟨⟨"leaf", [1]⟩, 2⟩] = .ok () := by decide +kernel

theorem tree : Derives (system Rat) ⟨[]⟩ root :=
  System.check_sound (by decide +kernel : unit root [twice, leaf, leaf] = .ok ())

theorem cyclic : MemoDerives (system Rat) ⟨[]⟩ loopClaim :=
  System.checkMemo_sound (by decide +kernel : memo loopClaim [⟨loop, 2⟩] = .ok ())

example : ∃ rows, (system Rat).check ⟨[]⟩ root rows = .ok () :=
  (System.check_derives_iff (by decide +kernel)).mpr tree

example : ∃ rows, (system Rat).checkMemo ⟨[]⟩ loopClaim rows = .ok () :=
  (System.checkMemo_derives_iff (by decide +kernel)).mpr cyclic

-- Theorems are checked by Lean's kernel; classical choice is permitted, admissions are not.
/-- info: 'Aiur.Circuit.System.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.System.check_sound
/-- info: 'Aiur.Circuit.Derivation.check_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.Derivation.check_complete
/-- info: 'Aiur.Circuit.System.checkMemo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.System.checkMemo_sound
/-- info: 'Aiur.Circuit.MemoDerivation.check_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.MemoDerivation.check_complete

def run : IO Unit := do
  for (label, actual, expected) in checks do
    unless actual = expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  IO.println s!"Passed {checks.length} integer accumulator checks."

end AiurAccumulatorTests
