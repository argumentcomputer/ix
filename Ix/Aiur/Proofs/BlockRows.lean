/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CallInventory
import Ix.Aiur.Proofs.BranchSelection

/-!
A total valued model of native block constraint emission. Branches share
columns and lookup slots, default arms allocate inverse witnesses, and
continuations consume local yields while preserving early returns. Selector
gates match native emission even on assignments that violate its equations.

Native expression reflection and successful emission from validated layouts
remain separate obligations.
-/

namespace Aiur.AIR
open Bytecode

structure RowContext where
  function : FunIdx
  inputSize : Nat
  rank : G

structure QueryPart where
  slot : Nat
  selector : G
  message : List G
  deriving Repr

def queryParts (slot : Nat) (selector : G) (queries : List (List G)) : List QueryPart :=
  queries.mapIdx fun index message => ⟨slot + index, selector, message⟩

structure BlockEmission where
  values : Array RowValue
  column : Nat
  lookup : Nat
  equations : List G := []
  queries : List QueryPart := []
  returns : List (G × Bytecode.AIR.Call) := []
  yields : List (G × Array RowValue) := []
  calls : List (G × (Bytecode.AIR.Call × (Fin 6 → G))) := []

def BlockEmission.prefix (equations : List G) (emission : BlockEmission) : BlockEmission :=
  { emission with equations := equations ++ emission.equations }

def BlockEmission.afterOps (incoming : G) (lookup : Nat) (ops : OpsEmission)
    (control : BlockEmission) : BlockEmission :=
  { control with
    equations := ops.equations ++ control.equations
    queries := queryParts lookup incoming ops.queries ++ control.queries
    calls := ops.calls.map (incoming, ·) ++ control.calls }

def joinBlockEmissions (values : Array RowValue) (column lookup : Nat)
    (emissions : List BlockEmission) : BlockEmission :=
  { values
    column := emissions.foldl (fun column emission => max column emission.column) column
    lookup := emissions.foldl (fun lookup emission => max lookup emission.lookup) lookup
    equations := emissions.flatMap (·.equations)
    queries := emissions.flatMap (·.queries)
    returns := emissions.flatMap (·.returns)
    yields := emissions.flatMap (·.yields)
    calls := emissions.flatMap (·.calls) }

def mergeEquations (row : Nat → G) (parent : G) (column size : Nat)
    (yields : List (G × Array RowValue)) : List G :=
  (List.range size).map fun index => parent * (row (column + index) -
    selectorSum (yields.map fun part => part.1 * (rowValues part.2)[index]?.getD 0))

def BlockEmission.continued (branches : BlockEmission) (equations : List G)
    (continuation : BlockEmission) : BlockEmission :=
  { continuation with
    equations := branches.equations ++ equations ++ continuation.equations
    queries := branches.queries ++ continuation.queries
    returns := branches.returns ++ continuation.returns
    calls := branches.calls ++ continuation.calls }

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

private theorem block_row_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def Ctrl.emitRow (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) : Ctrl → Option BlockEmission
  | .return _ indices => do
    let inputs ← AIR.readValues (rowValues values) (Array.range context.inputSize)
    let outputs ← AIR.readValues (rowValues values) indices
    return {
      values, column, lookup
      returns := [(incoming, ⟨context.function, inputs, outputs, context.rank⟩)] }
  | .yield index indices => do
    let outputs ← indices.toList.mapM fun index => values[index]?
    return { values, column, lookup, yields := [(selector index, outputs.toArray)] }
  | .match index branches fallback => do
    let matched ← values[index]?
    let cases ← branches.attach.toList.mapM fun ⟨pair, _⟩ => do
      let entry := (pair.2.selectorFlow selector).entry
      let emission ← pair.2.emitRow row selector context entry values column lookup
      return emission.prefix [entry * (matched.value - pair.1)]
    let default : List BlockEmission ← match fallback with
      | none => some []
      | some block => do
        let entry := (block.selectorFlow selector).entry
        let emission ← block.emitRow row selector context entry values (column + branches.size) lookup
        pure [emission.prefix (branches.toList.mapIdx fun i pair =>
          entry * ((matched.value - pair.1) * row (column + i) - 1))]
    return joinBlockEmissions values column lookup (cases ++ default)
  | .matchContinue index branches fallback size _ _ continuation => do
    let matched ← values[index]?
    let cases ← branches.attach.toList.mapM fun ⟨pair, _⟩ => do
      let entry := (pair.2.selectorFlow selector).entry
      let emission ← pair.2.emitRow row selector context entry values column lookup
      return emission.prefix [entry * (matched.value - pair.1)]
    let default : List BlockEmission ← match fallback with
      | none => some []
      | some block => do
        let entry := (block.selectorFlow selector).entry
        let emission ← block.emitRow row selector context entry values (column + branches.size) lookup
        pure [emission.prefix (branches.toList.mapIdx fun i pair =>
          entry * ((matched.value - pair.1) * row (column + i) - 1))]
    let joined := joinBlockEmissions values column lookup (cases ++ default)
    if joined.yields.all (fun part => part.2.size == size) then do
      let gate := selectorSum (joined.yields.map Prod.fst)
      let merged := rowAdvice row joined.column size
      let equations := mergeEquations row incoming joined.column size joined.yields ++
        [(continuation.selectorFlow selector).entry - gate]
      let continued ← continuation.emitRow row selector context gate (values ++ merged)
        (joined.column + size) joined.lookup
      return joined.continued equations continued
    else none
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.emitRow (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat)
    (block : Block) : Option BlockEmission := do
  let operations ← emitOps row incoming context.rank block.ops.toList values column
  let control ← block.ctrl.emitRow row selector context incoming operations.values
    operations.column (lookup + operations.queries.length)
  return (control.afterOps incoming lookup operations).prefix
    [oneSubBooleanConstraint (block.selectorFlow selector).entry]
termination_by sizeOf block
decreasing_by exact block_row_smaller block

end

end Aiur.Bytecode
