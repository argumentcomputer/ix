/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module
public import Ix.Aiur.Stages.Bytecode

/-! Total control counts and circuit checks independent of witness values.
These checks bound branch/terminal counts and the number of raw return writers.
Physical columns, lookup cursors and value indices remain separate. -/

public section
@[expose] section

namespace Aiur.Bytecode

/-- Counts of control nodes, allocated leaf selectors, returns and escaping
yields. Consumed yields still allocate selectors. -/
structure ControlCounts where
  nodes : Nat
  leaves : Nat
  returns : Nat
  yields : Nat
  deriving Repr, DecidableEq

def ControlCounts.sum (items : List ControlCounts) : ControlCounts :=
  ⟨(items.map (·.nodes)).sum, (items.map (·.leaves)).sum,
    (items.map (·.returns)).sum, (items.map (·.yields)).sum⟩

def ControlCounts.branch (items : List ControlCounts) : ControlCounts :=
  { sum items with nodes := (sum items).nodes + 1 }

def ControlCounts.continue (branches continuation : ControlCounts) : ControlCounts :=
  ⟨branches.nodes + continuation.nodes, branches.leaves + continuation.leaves,
    branches.returns + continuation.returns, continuation.yields⟩

private theorem counts_block_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def Ctrl.controlCounts : Ctrl → ControlCounts
  | .return .. => ⟨1, 1, 1, 0⟩
  | .yield .. => ⟨1, 1, 0, 1⟩
  | .match _ branches fallback => ControlCounts.branch (
      (branches.attach.toList.map fun ⟨pair, _⟩ => pair.2.controlCounts) ++
      (match fallback with | none => [] | some block => [block.controlCounts]))
  | .matchContinue _ branches fallback _ _ _ continuation => (ControlCounts.branch (
      (branches.attach.toList.map fun ⟨pair, _⟩ => pair.2.controlCounts) ++
      (match fallback with | none => [] | some block => [block.controlCounts]))).continue
        continuation.controlCounts
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.controlCounts (block : Block) : ControlCounts := block.ctrl.controlCounts
termination_by sizeOf block
decreasing_by exact counts_block_smaller block

end

def branchControlCounts (branches : Array (G × Block)) (fallback : Option Block) : List ControlCounts :=
  branches.toList.map (fun pair => pair.2.controlCounts) ++
    fallback.toList.map (fun block => block.controlCounts)

/-- Syntax-only count checks for the functions actually named by a circuit.
The allocated selector count bounds all return/yield leaves, including yields
consumed by continuations. Other layout and value-index checks are separate. -/
def Circuit.validateRowCounts (program : Toplevel) (circuit : Circuit) : Bool :=
  circuit.members.size < gSize.toNat &&
    match circuit.members.toList.mapM (fun index => program.functions[index]?) with
    | none => false
    | some functions =>
      functions.all (fun function => function.body.controlCounts.nodes < gSize.toNat) &&
        (functions.map (fun function => function.body.controlCounts.leaves)).sum ≤ circuit.layout.selectors

def Toplevel.validateRowCounts (program : Toplevel) : Bool :=
  program.circuits.all (Circuit.validateRowCounts program)

theorem Ctrl.controlCounts_match (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).controlCounts =
      ControlCounts.branch (branchControlCounts branches fallback) := by
  rw [Ctrl.controlCounts.eq_def]
  simp only [branchControlCounts, Array.toList_attach]
  rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.controlCounts)]
  cases fallback <;> rfl

theorem Ctrl.controlCounts_matchContinue (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (outputs aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback outputs aux lookups continuation).controlCounts =
      (ControlCounts.branch (branchControlCounts branches fallback)).continue continuation.controlCounts := by
  rw [Ctrl.controlCounts.eq_def]
  simp only [branchControlCounts, Array.toList_attach]
  rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.controlCounts)]
  cases fallback <;> rfl

end Aiur.Bytecode

end
end
