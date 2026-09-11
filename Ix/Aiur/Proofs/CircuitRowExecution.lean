/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitPoolExecution

/-!
A nonzero provider row of the valued circuit model yields a valid
function row from the same bytecode program. The interpreted inputs, rank
bytes and multiplicity agree with the circuit, and its padded provider
message names that same semantic call. All selected call and rank-byte
queries belong to the computed circuit pool.

Exact global lookup balance, memory validity, shape and count/layout bounds
remain explicit. This is not yet extraction from native public verification.
-/

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_valid {tables : LookupTables} {width : Nat} {emissions : List CircuitEmission}
    (global : GlobalLookups tables width (circuitQueryPool emissions))
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (member : emission ∈ emissions)
    (bounded : circuit.members.size < gSize.toNat)
    (bounds : ∀ part ∈ emission.members, part.function.body.rowBounds (part.selector row))
    (shape : ∀ part ∈ emission.members, part.function.body.lookupShapes program none = true)
    (returnBound : ∀ part ∈ emission.members,
      (part.function.body.selectorFlow (part.selector row)).returns.length < gSize.toNat)
    (reserved : 4 ≤ circuit.layout.lookups)
    (limits : ∀ part ∈ emission.members, part.body.lookup ≤ circuit.layout.lookups)
    (single : emission.branchless = true → emission.returns.length ≤ 1)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (nonzero : emission.multiplicity ≠ 0) :
    ∃ selected ∈ emission.members, ∃ interpreted : FunctionRow,
      interpreted.Valid program (memoryFacts tables.memory) ∧
      interpreted.request.function = selected.functionIndex ∧
      interpreted.request.inputs = rowValues (rowAdvice row 0 selected.function.layout.inputSize) ∧
      interpreted.request.rank = packRank emission.rankBytes ∧
      interpreted.rankBytes = emission.rankBytes ∧
      interpreted.selector = emission.selector ∧ interpreted.multiplicity = emission.multiplicity ∧
      (1, interpreted.request) ∈ emission.returns ∧
      padMessage width (emission.lookup 0).2 = padMessage width (functionMessage interpreted.request) ∧
      selected.body.CallsAt interpreted.calls ∧
      (interpreted.requests.map functionMessage) ⊆ circuitQueryPool emissions ∧
      (interpreted.byteQueries.map rangeMessage) ⊆ circuitQueryPool emissions := by
  exact circuit.emitRow_valid_in_pool global memoryValid canonical row program emitted member
    (List.Subset.refl _) bounded bounds shape returnBound reserved limits single satisfied nonzero

end Aiur.Bytecode
