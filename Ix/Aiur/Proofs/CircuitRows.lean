/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockQueryPool
import Ix.Aiur.Branchless

/-!
A valued model of the complete native function-circuit builder. Grouped
members share auxiliary columns, rank bytes, multiplicity and lookup slots,
while their selector columns occupy consecutive regions. The model retains
the native header equations and provider-message combination on arbitrary
assignments. Native expression/codec reflection and layout validity remain
separate obligations.
-/

namespace Aiur.AIR
open Bytecode

structure MemberEmission where
  functionIndex : FunIdx
  function : Function
  selectorBase : Nat
  body : BlockEmission

def MemberEmission.selector (row : Nat → G) (member : MemberEmission) : SelIdx → G :=
  fun index => row (member.selectorBase + index)

def MemberEmission.entry (row : Nat → G) (member : MemberEmission) : G :=
  (member.function.body.selectorFlow (member.selector row)).entry

def emitMember (row : Nat → G) (rank : G) (column lookup selectorBase : Nat)
    (program : Toplevel) (functionIndex : FunIdx) : Option MemberEmission := do
  let function ← program.functions[functionIndex]?
  let body ← function.emitRow row (fun index => row (selectorBase + index)) functionIndex rank
    (rowAdvice row 0 function.layout.inputSize) column lookup
  return ⟨functionIndex, function, selectorBase, body⟩

def emitMembers (row : Nat → G) (rank : G) (column lookup selectorBase : Nat)
    (program : Toplevel) : List FunIdx → Option (List MemberEmission)
  | [] => some []
  | index :: indices => do
    let member ← emitMember row rank column lookup selectorBase program index
    let rest ← emitMembers row rank column lookup (selectorBase + member.function.layout.selectors) program indices
    return member :: rest

structure CircuitEmission where
  members : List MemberEmission
  selector : G
  multiplicity : G
  rankBytes : Fin 6 → G
  width : Nat
  selectorStart : Nat
  selectorCount : Nat
  lookupCount : Nat
  branchless : Bool
  equations : List G
  queries : List QueryPart
  returns : List (G × Bytecode.AIR.Call)

def circuitRankBytes (row : Nat → G) (layout : Bytecode.FunctionLayout) : Fin 6 → G :=
  fun index => row (layout.inputSize + layout.selectors + 1 + index.val)

def circuitEmission (row : Nat → G) (circuit : Circuit) (members : List MemberEmission) : CircuitEmission :=
  let selector := selectorSum (members.map (·.entry row))
  let multiplicity := row (circuit.layout.inputSize + circuit.layout.selectors)
  let rankBytes := circuitRankBytes row circuit.layout
  { members, selector, multiplicity, rankBytes
    width := circuit.layout.width
    selectorStart := circuit.layout.inputSize
    selectorCount := circuit.layout.selectors
    lookupCount := circuit.layout.lookups
    branchless := circuitBranchless circuit.layout.selectors (members.map (·.function))
    equations := members.flatMap (·.body.equations) ++
      (List.range circuit.layout.selectors).map (fun index => booleanConstraint (row (circuit.layout.inputSize + index))) ++
      (if 1 < circuit.members.size then [oneSubBooleanConstraint selector] else []) ++
      [activityConstraint multiplicity selector]
    queries := members.flatMap (·.body.queries) ++
      queryParts 1 selector ((rankByteQueries rankBytes).map rangeMessage)
    returns := members.flatMap (·.body.returns) }

def CircuitEmission.lookup (emission : CircuitEmission) (slot : Nat) : G × List G :=
  if slot = 0 then
    (0 - emission.multiplicity,
      slotMessage emission.branchless (emission.returns.map fun part => (part.1, functionMessage part.2)))
  else
    (querySlotMultiplicity emission.queries slot,
      slotMessage emission.branchless (querySlotParts emission.queries slot))

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

def Circuit.emitRow (row : Nat → G) (program : Toplevel) (circuit : Circuit) : Option CircuitEmission := do
  let rank := packRank (circuitRankBytes row circuit.layout)
  let column := circuit.layout.inputSize + circuit.layout.selectors + 1 + 6
  let members ← emitMembers row rank column 4 circuit.layout.inputSize program circuit.members.toList
  return circuitEmission row circuit members

end Aiur.Bytecode
