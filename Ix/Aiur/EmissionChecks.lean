/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module
public import Ix.Aiur.Stages.Bytecode

/-!
Structural checks for circuit emission. Each operation reads the incoming
logical scope and then appends its outputs. Branches restore that scope;
continuations append only their merge values. Unconstrained advice and I/O
operations do not read their runtime operands while building constraints.

The checked addition matches the supported 64-bit native index domain. These
checks establish neither source typing nor the meaning of unchecked advice.
-/

public section
@[expose] section

namespace Aiur.Bytecode

def indicesInScope (available : Nat) (indices : Array ValIdx) : Bool :=
  indices.all fun index => decide (index < available)

def wordInScope (available : Nat) (indices : Array ValIdx) : Bool :=
  indices.size == 4 && indicesInScope available indices

/-- Logical outputs include virtual carries, which occupy no fresh column. -/
def Op.outputSize : Op → Nat
  | .const .. | .add .. | .sub .. | .mul .. | .eqZero .. | .store ..
  | .u8ShiftLeft .. | .u8ShiftRight .. | .u8Xor .. | .u8And .. | .u8Or ..
  | .u8LessThan .. | .u32LessThan .. | .unconstrainedGInverse .. | .u32ToField .. => 1
  | .call _ _ size _ | .load size _ | .ioRead _ _ size => size
  | .assertEq .. | .ioSetInfo .. | .ioWrite .. | .debug .. | .u8RangeCheck .. => 0
  | .ioGetInfo .. | .u8Add .. | .u8Mul .. | .u8Sub .. | .u8XorSplit7 ..
  | .u8XorSplit4 .. | .unconstrainedBigUintDivMod .. => 2
  | .u8BitDecomposition .. | .unconstrainedGToBytes .. => 8
  | .unconstrainedU32Add .. | .unconstrainedU32Add3 .. => 5

/-- Check precisely the operands consumed by the constraint builder. In
particular, a store cannot read its own newly allocated pointer. -/
def Op.emissionInputs (available : Nat) : Op → Bool
  | .add a b | .sub a b | .mul a b | .u8Xor a b | .u8Add a b | .u8Mul a b
  | .u8Sub a b | .u8And a b | .u8Or a b | .u8LessThan a b | .u32LessThan a b
  | .u8XorSplit7 a b | .u8XorSplit4 a b | .u8RangeCheck a b =>
    decide (a < available) && decide (b < available)
  | .eqZero index | .load _ index | .u8BitDecomposition index
  | .u8ShiftLeft index | .u8ShiftRight index => decide (index < available)
  | .call _ indices _ false | .store indices => indicesInScope available indices
  | .assertEq left right _ => left.size == right.size &&
      (indicesInScope available left && indicesInScope available right)
  | .unconstrainedU32Add left right => wordInScope available left && wordInScope available right
  | .unconstrainedU32Add3 left middle right =>
    wordInScope available left && (wordInScope available middle && wordInScope available right)
  | .u32ToField indices => wordInScope available indices
  | _ => true

def addScope (available count : Nat) : Option Nat :=
  let next := available + count
  if next < 2^64 then some next else none

def checkEmissionOps : List Op → Nat → Option Nat
  | [], available => some available
  | op :: ops, available => do
    if !op.emissionInputs available then none else do
      let next ← addScope available op.outputSize
      checkEmissionOps ops next

private theorem block_ctrl_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def Ctrl.emissionChecks (available selectors : Nat) (yieldSize : Option Nat) : Ctrl → Bool
  | .return index outputs => decide (index < selectors) && indicesInScope available outputs
  | .yield index outputs => decide (index < selectors) &&
      (indicesInScope available outputs && yieldSize == some outputs.size)
  | .match index branches fallback =>
    decide (index < available) &&
      (branches.attach.all (fun ⟨(_, block), _⟩ => block.emissionChecks available selectors yieldSize) &&
        (match fallback with | none => true | some block => block.emissionChecks available selectors yieldSize))
  | .matchContinue index branches fallback size _ _ continuation =>
    decide (index < available) &&
      (branches.attach.all (fun ⟨(_, block), _⟩ => block.emissionChecks available selectors (some size)) &&
        ((match fallback with | none => true | some block => block.emissionChecks available selectors (some size)) &&
          (match addScope available size with
          | none => false
          | some next => continuation.emissionChecks next selectors yieldSize)))
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.emissionChecks (available selectors : Nat) (yieldSize : Option Nat) (block : Block) : Bool :=
  match checkEmissionOps block.ops.toList available with
  | none => false
  | some next => block.ctrl.emissionChecks next selectors yieldSize
termination_by sizeOf block
decreasing_by exact block_ctrl_smaller block

end

def Function.emissionChecks (function : Function) : Bool :=
  decide (function.layout.inputSize < 2^64) &&
    function.body.emissionChecks function.layout.inputSize function.layout.selectors none

/-- Check every constrained body before invoking the native circuit builder. -/
def Toplevel.validateEmission (program : Toplevel) : Bool :=
  program.functions.all fun function => !function.constrained || function.emissionChecks

end Aiur.Bytecode

end
end
