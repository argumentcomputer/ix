/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module
public import Ix.Aiur.Stages.Bytecode

/-!
Total structural checks for the boundaries of zero-padded lookup messages.

Function messages contain the function index, inputs, outputs and rank,
without length separators. Calls must use their callee's input and return
arities. Public result arity is checked separately against the entry body.
These checks do not establish value-index or circuit-layout correctness.
-/

public section
@[expose] section

namespace Aiur.Bytecode

private theorem block_ctrl_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

/-- Check every function return, including early returns from continuation
arms. A yield returns to its enclosing continuation, not the function. -/
def Ctrl.returnsHaveSize (size : Nat) : Ctrl → Bool
  | .return _ values => values.size == size
  | .yield .. => true
  | .match _ branches fallback =>
    branches.attach.all (fun ⟨(_, block), _⟩ => block.returnsHaveSize size) &&
      (match fallback with | none => true | some block => block.returnsHaveSize size)
  | .matchContinue _ branches fallback _ _ _ continuation =>
    branches.attach.all (fun ⟨(_, block), _⟩ => block.returnsHaveSize size) &&
      ((match fallback with | none => true | some block => block.returnsHaveSize size) &&
        continuation.returnsHaveSize size)
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.returnsHaveSize (size : Nat) (block : Block) : Bool :=
  block.ctrl.returnsHaveSize size
termination_by sizeOf block
decreasing_by exact block_ctrl_smaller block

end

def Op.lookupShape (program : Toplevel) : Op → Bool
  | .call index inputs outputs false =>
    match program.functions[index]? with
    | none => false
    | some callee => callee.constrained &&
        (callee.layout.inputSize == inputs.size && callee.body.returnsHaveSize outputs)
  | .store values => decide (values.size < gSize.toNat)
  | .load size _ => decide (size < gSize.toNat)
  | _ => true

mutual

def Ctrl.lookupShapes (program : Toplevel) (yieldSize : Option Nat) : Ctrl → Bool
  | .return .. => true
  | .yield _ values => yieldSize == some values.size
  | .match _ branches fallback =>
    branches.attach.all (fun ⟨(_, block), _⟩ => block.lookupShapes program yieldSize) &&
      (match fallback with | none => true | some block => block.lookupShapes program yieldSize)
  | .matchContinue _ branches fallback size _ _ continuation =>
    branches.attach.all (fun ⟨(_, block), _⟩ => block.lookupShapes program (some size)) &&
      ((match fallback with | none => true | some block => block.lookupShapes program (some size)) &&
        continuation.lookupShapes program yieldSize)
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.lookupShapes (program : Toplevel) (yieldSize : Option Nat) (block : Block) : Bool :=
  block.ops.all (Op.lookupShape program) && block.ctrl.lookupShapes program yieldSize
termination_by sizeOf block
decreasing_by exact block_ctrl_smaller block

end

/-- Mirror the native construction guard, including canonical function
indices, canonical memory widths and continuation-yield arities. -/
def Toplevel.validateLookupShapes (program : Toplevel) : Bool :=
  decide (program.functions.size < gSize.toNat) &&
    (program.memorySizes.all (fun size => decide (size < gSize.toNat)) &&
      program.functions.all (fun function =>
        !function.constrained || function.body.lookupShapes program none))

/-- A public claim names a constrained public function and has exactly its
input and return widths. The final zero rank is omitted from this encoding. -/
def Toplevel.validClaimShape (program : Toplevel) (claim : Array G) : Bool :=
  match claim.toList with
  | channel :: index :: arguments =>
    channel == 0 &&
      (match program.functions[index.n]? with
      | none => false
      | some function => function.entry && function.constrained &&
          (decide (function.layout.inputSize ≤ arguments.length) &&
            function.body.returnsHaveSize (arguments.length - function.layout.inputSize)))
  | _ => false

end Aiur.Bytecode

end
end
