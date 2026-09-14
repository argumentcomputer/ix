/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.QuerySlotMessages

/-!
Function-row validity using the query pool computed from valued block
emissions. Slot exclusivity supplies active raw-query membership, removing
that separate premise from the function-row theorem. Exact global lookup
balance, count/layout validity and native verifier reflection remain open.
-/

namespace Aiur.AIR

def blockQueryPool (emissions : List BlockEmission) : List (List G) :=
  emissions.flatMap fun emission => decodedQueries emission.queries emission.lookup

theorem QuerySlots.queried_pool {gate : G} {start : Nat} {emission : BlockEmission}
    (slots : QuerySlots gate start emission.lookup emission.queries)
    {emissions : List BlockEmission} (member : emission ∈ emissions) :
    emission.QueriesIn (blockQueryPool emissions) := by
  intro query present active
  exact List.mem_flatMap.mpr ⟨emission, member, slots.decoded_member present active⟩

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Block.emitRow_queried_pool (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    (bounds : block.rowBounds selector) {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission)
    (linked : incoming = (block.selectorFlow selector).entry)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    {emissions : List BlockEmission} (member : emission ∈ emissions) :
    emission.QueriesIn (blockQueryPool emissions) :=
  (block.emitRow_equation_querySlots row selector context incoming values column lookup
    bounds emitted linked satisfied).queried_pool member

theorem Function.emitRow_pool_valid {tables : LookupTables} {width : Nat}
    {emissions : List BlockEmission} (global : GlobalLookups tables width (blockQueryPool emissions))
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (program : Toplevel) (row : Nat → G) (selector : SelIdx → G)
    (functionIndex : FunIdx) (rankBytes : Fin 6 → G) (values : Array RowValue) (column lookup : Nat)
    (function : Function) (present : program.functions[functionIndex]? = some function)
    (arity : values.size = function.layout.inputSize)
    (shape : function.body.lookupShapes program none = true) (bounds : function.body.rowBounds selector)
    {emission : BlockEmission}
    (emitted : function.emitRow row selector functionIndex (packRank rankBytes) values column lookup = some emission)
    (member : emission ∈ emissions)
    (multiplicity : G) (nonzero : multiplicity ≠ 0)
    (activity : activityConstraint multiplicity (function.body.selectorFlow selector).entry = 0)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    ∃ interpreted : FunctionRow, interpreted.Valid program (memoryFacts tables.memory) ∧
      (1, interpreted.request) ∈ emission.returns ∧
      interpreted.request.function = functionIndex ∧ interpreted.request.inputs = rowValues values ∧
      interpreted.request.rank = packRank rankBytes ∧ interpreted.rankBytes = rankBytes ∧
      interpreted.selector = (function.body.selectorFlow selector).entry ∧
      interpreted.multiplicity = multiplicity ∧ emission.CallsAt interpreted.calls ∧
      CallsEmitted (packRank rankBytes) 1 emission.equations (blockQueryPool emissions) interpreted.calls := by
  have bodyEmitted := emitted
  rw [Function.emitRow] at bodyEmitted
  have queried := function.body.emitRow_queried_pool row selector _ _ _ _ _ bounds bodyEmitted rfl satisfied member
  exact function.emitRow_valid global memoryValid canonical program row selector functionIndex rankBytes
    values column lookup present arity shape bounds emitted multiplicity nonzero activity satisfied queried

end Aiur.Bytecode
