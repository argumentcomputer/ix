/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Stages.Bytecode

/-! Logical output degrees and physical auxiliary allocation of one operation.
This projection retains the compiler's independent degree bookkeeping. -/

namespace Aiur.Bytecode

structure OpAllocation where
  degrees : Array Nat
  auxiliaries : Nat
  deriving DecidableEq, Repr

def OpAllocation.advice (size : Nat) : OpAllocation := ⟨Array.replicate size 1, size⟩

def selectedDegree (degrees : Array Nat) (indices : Array Nat) (initial : Nat) : Nat :=
  (indices.map fun index => degrees[index]?.getD 0).foldl Nat.max initial

theorem selectedDegree_initial (degrees : Array Nat) (indices : Array Nat) (initial : Nat) :
    selectedDegree degrees indices initial = max initial (selectedDegree degrees indices 0) := by
  simpa only [selectedDegree, Nat.max_zero] using
    (Array.foldl_assoc (op := Nat.max) (xs := indices.map fun index => degrees[index]?.getD 0)
      (a₁ := initial) (a₂ := 0))

theorem selectedDegree_append (degrees : Array Nat) (left right : Array Nat) (initial : Nat) :
    selectedDegree degrees (left ++ right) initial =
      max (selectedDegree degrees left initial) (selectedDegree degrees right 0) := by
  simp only [selectedDegree, Array.map_append, Array.foldl_append]
  exact selectedDegree_initial degrees right _

def Op.allocation (degrees : Array Nat) : Op → OpAllocation
  | .const _ => ⟨#[0], 0⟩
  | .add a b | .sub a b => ⟨#[max (degrees[a]?.getD 0) (degrees[b]?.getD 0)], 0⟩
  | .mul a b =>
    let degree := degrees[a]?.getD 0 + degrees[b]?.getD 0
    if degree < 2 then ⟨#[degree], 0⟩ else .advice 1
  | .eqZero a => if degrees[a]?.getD 0 = 0 then ⟨#[0], 0⟩ else ⟨#[1], 2⟩
  | .call _ _ size unconstrained =>
    ⟨Array.replicate size 1, size + (if unconstrained then 0 else 6)⟩
  | .store _ => .advice 1
  | .load size _ | .ioRead _ _ size => .advice size
  | .assertEq .. | .ioSetInfo .. | .ioWrite .. | .debug .. | .u8RangeCheck .. => ⟨#[], 0⟩
  | .ioGetInfo .. | .unconstrainedBigUintDivMod .. => .advice 2
  | .u8BitDecomposition .. | .unconstrainedGToBytes .. => .advice 8
  | .u8ShiftLeft .. | .u8ShiftRight .. | .u8Xor .. | .u8And .. | .u8Or .. | .u8LessThan ..
  | .unconstrainedGInverse .. => .advice 1
  | .u8Add a b | .u8Sub a b =>
    ⟨#[1, max (max (degrees[a]?.getD 0) (degrees[b]?.getD 0)) 1], 1⟩
  | .u8Mul .. | .u8XorSplit7 .. | .u8XorSplit4 .. => .advice 2
  | .u32LessThan .. => ⟨#[1], 12⟩
  | .unconstrainedU32Add a b => ⟨(Array.replicate 4 1).push (selectedDegree degrees (a ++ b) 1), 4⟩
  | .unconstrainedU32Add3 a b c => ⟨(Array.replicate 4 1).push (selectedDegree degrees (a ++ b ++ c) 1), 4⟩
  | .u32ToField indices => ⟨#[selectedDegree degrees indices 0], 0⟩

/-- Allocation for a selected component layout. The empty mode table retains
the generic ordered call allocation described by `Op.allocation`. -/
def Op.allocationFor (callRanks : Array CallRank) (degrees : Array Nat) : Op → OpAllocation
  | .call function _ size unconstrained =>
    let extra := if unconstrained then 0 else
      match callRanks[function]?.getD .ordered with
      | .zero => 0
      | .bound => 1
      | .ordered => 6
    ⟨Array.replicate size 1, size + extra⟩
  | op => op.allocation degrees

theorem Op.allocationFor_empty (op : Op) (degrees : Array Nat) :
    op.allocationFor #[] degrees = op.allocation degrees := by
  cases op <;> rfl

end Aiur.Bytecode
