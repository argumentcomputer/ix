/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitTableExecution

/-! Finite execution of the selected public success call from valued circuit
witnesses. Public rank-zero padding is normalized without changing lookup
balance. Native witness/lookup reflection and cryptographic reduction remain
separate obligations. -/

namespace Aiur.AIR

theorem PaddedLookupBalance.congr_queries {width : Nat} {left right : List (List G)}
    {providers : List (Provider (List G))} (balanced : PaddedLookupBalance width left providers)
    (same : left.map (padMessage width) = right.map (padMessage width)) :
    PaddedLookupBalance width right providers := by
  change ExactLookupBalance _ _ at balanced ⊢
  rwa [← same]

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem claim_message (selection : Selection) (input : Array G) :
    functionMessage ⟨selection.function, input, selection.success, 0⟩ =
      (buildClaim selection.function input selection.success).toList ++ [0] := by
  simp only [functionMessage, buildClaim, Array.toList_append, List.cons_append,
    List.nil_append, functionChannel]
  rfl

/-- The selected public success call executes from valued circuit witnesses
and their physical provider balance. The public query has the actual claim
encoding, whose omitted rank is zero. Native witness extraction, lookup-slot
encoding/layout reflection and the cryptographic reduction remain separate. -/
theorem Backend.public_circuit_execution {selection : Selection} (backend : Backend selection)
    (tables : AuxiliaryTables) (witnesses : List CircuitWitness) (width : Nat)
    (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        circuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : (circuitQueryPool (witnesses.map (·.emission))).length + 1 < gSize.toNat)
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ circuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ backend.compiled.bytecode.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.Emitted backend.compiled.bytecode)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes backend.compiled.bytecode)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory)
      ⟨selection.function, input, selection.success, 0⟩ := by
  let request : Call := ⟨selection.function, input, selection.success, 0⟩
  have normalized : PaddedLookupBalance width
      (functionMessage request :: circuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))) := by
    apply balanced.congr_queries
    change padMessage width (buildClaim selection.function input selection.success).toList :: _ =
      padMessage width (functionMessage request) :: _
    rw [show padMessage width (functionMessage request) =
      padMessage width (buildClaim selection.function input selection.success).toList from
      claim_padding selection width input]
  apply circuitWitnesses_execute tables witnesses normalized bounded ?_ memoryValid canonical
    backend.rowCounts backend.lookupShapes circuits emitted satisfied shapes limits
    (fun _ member => List.mem_cons_of_mem _ member) (backend.root_lookupShape input arity) List.mem_cons_self
  intro query member
  rcases List.mem_cons.mp member with same | rest
  · subst query
    change (functionMessage ⟨selection.function, input, selection.success, 0⟩).length ≤ width
    rw [claim_message, List.length_append, List.length_singleton, Array.length_toList]
    exact publicWidth
  · exact queryWidths query rest

end Aiur.BoundVerifier
