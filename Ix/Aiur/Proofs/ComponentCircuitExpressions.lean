/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitRows
import Ix.Aiur.Proofs.CompiledCircuitRows

/-! Native expression order for circuits with static components. The generic
circuit emitter remains available for programs using the fallback layout. -/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter LookupEmitter BlockEmitter Compiler Bytecode

def emitComponentMember (rank : Expr) (base selectorBase : Nat)
    (program : Toplevel) (functionIndex : Nat) : Option Member :=
  let ranked := (program.componentFor functionIndex).ranked
  emitMember (if ranked then rank else .konst 0) (AIR.componentColumn ranked base)
    (AIR.componentLookup ranked) selectorBase program functionIndex (program.callRanksFor functionIndex)

def emitComponentMembers (rank : Expr) (base selectorBase : Nat)
    (program : Toplevel) : List Nat → Option (List Member)
  | [] => some []
  | index :: indices => do
    let member ← emitComponentMember rank base selectorBase program index
    let rest ← emitComponentMembers rank base (selectorBase + member.function.layout.selectors) program indices
    return member :: rest

def componentMembers (program : Toplevel) (members : List Member) : List Member :=
  members.filter fun member => (program.componentFor member.functionIndex).ranked

def componentCircuitEmission (program : Toplevel) (circuit : Circuit) (members : List Member) : Emission :=
  let ranked := componentMembers program members
  let bytes := rankBytes circuit.layout
  let rankSelector := sum (ranked.map (·.entry))
  { circuitEmission circuit members with
    rankBytes := if ranked.isEmpty then fun _ => .konst 0 else bytes
    queries := members.flatMap (·.body.queries) ++
      (if ranked.isEmpty then [] else queryParts 1 rankSelector (rangeSix bytes)) }

def emitComponentCircuit (program : Toplevel) (circuit : Circuit) : Option Emission := do
  let rank := packSix (rankBytes circuit.layout)
  let base := circuit.layout.inputSize + circuit.layout.selectors + 1
  let members ← emitComponentMembers rank base circuit.layout.inputSize program circuit.members.toList
  return componentCircuitEmission program circuit members

/-- The metadata includes rank reads only when a ranked member exists. -/
def Emission.componentReadBound (program : Toplevel) (emission : Emission) : Nat :=
  emission.members.foldl (fun bound member => max bound member.readBound)
    (emission.selectorStart + emission.selectorCount + 1 +
      if (componentMembers program emission.members).isEmpty then 0 else 6)

/-- Checked extents needed to interpret every emitted read and logical slot.
Slot zero is reserved for the shared provider. -/
def Emission.componentFootprint (program : Toplevel) (width : Nat) (emission : Emission) : Bool :=
  emission.componentReadBound program ≤ width &&
    (0 < emission.lookupCount &&
      emission.queries.all (fun part => 0 < part.slot && part.slot < emission.lookupCount))

theorem Emission.componentFootprint_read {program : Toplevel} {width : Nat} {emission : Emission}
    (checked : emission.componentFootprint program width = true) : emission.componentReadBound program ≤ width := by
  simp only [componentFootprint, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1

theorem Emission.componentFootprint_slots {program : Toplevel} {width : Nat} {emission : Emission}
    (checked : emission.componentFootprint program width = true) :
    ∀ part ∈ emission.queries, 0 < part.slot ∧ part.slot < emission.lookupCount := by
  intro part present
  simp only [componentFootprint, Bool.and_eq_true, decide_eq_true_eq] at checked
  have bound := List.all_eq_true.mp checked.2.2 part present
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using bound

end Aiur.NativeAIR.CircuitEmitter
