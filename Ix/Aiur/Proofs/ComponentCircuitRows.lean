/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentFunctionRows
import Ix.Aiur.Proofs.CircuitRows

/-! Valued circuit emission for checked static components. Each member
starts at its own auxiliary and lookup offsets. Acyclic members reuse the
rank columns and slots; only ranked member selectors gate rank ranges. -/

namespace Aiur.AIR
open Bytecode

def componentColumn (ranked : Bool) (base : Nat) : Nat := base + if ranked then 6 else 0
def componentLookup (ranked : Bool) : Nat := 1 + if ranked then 3 else 0

def emitComponentMember (row : Nat → G) (rank : G) (base selectorBase : Nat)
    (program : Toplevel) (functionIndex : FunIdx) : Option MemberEmission :=
  let ranked := (program.componentFor functionIndex).ranked
  emitMember row (if ranked then rank else 0) (componentColumn ranked base)
    (componentLookup ranked) selectorBase program functionIndex (program.callRanksFor functionIndex)

def emitComponentMembers (row : Nat → G) (rank : G) (base selectorBase : Nat)
    (program : Toplevel) : List FunIdx → Option (List MemberEmission)
  | [] => some []
  | index :: indices => do
    let member ← emitComponentMember row rank base selectorBase program index
    let rest ← emitComponentMembers row rank base
      (selectorBase + member.function.layout.selectors) program indices
    return member :: rest

def componentMembers (program : Toplevel) (members : List MemberEmission) : List MemberEmission :=
  members.filter fun member => (program.componentFor member.functionIndex).ranked

def componentCircuitEmission (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    (members : List MemberEmission) : CircuitEmission :=
  let ranked := componentMembers program members
  let rankBytes := circuitRankBytes row circuit.layout
  let rankSelector := selectorSum (ranked.map (·.entry row))
  { circuitEmission row circuit members with
    rankBytes := if ranked.isEmpty then fun _ => 0 else rankBytes
    queries := members.flatMap (·.body.queries) ++
      (if ranked.isEmpty then [] else
        queryParts 1 rankSelector ((rankByteQueries rankBytes).map rangeMessage)) }

theorem emitComponentMember_present {row : Nat → G} {rank : G} {base selectorBase : Nat}
    {program : Toplevel} {functionIndex : FunIdx} {member : MemberEmission}
    (emitted : emitComponentMember row rank base selectorBase program functionIndex = some member) :
    member.functionIndex = functionIndex ∧ program.functions[functionIndex]? = some member.function ∧
      member.selectorBase = selectorBase ∧
      member.function.emitRow row (member.selector row) functionIndex
        (if (program.componentFor functionIndex).ranked then rank else 0)
        (rowAdvice row 0 member.function.layout.inputSize)
        (componentColumn (program.componentFor functionIndex).ranked base)
        (componentLookup (program.componentFor functionIndex).ranked)
        (program.callRanksFor functionIndex) = some member.body := by
  simp only [emitComponentMember, emitMember, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i function present
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i body bodyEmitted
  cases emitted
  exact ⟨rfl, present, rfl, bodyEmitted⟩

theorem emitComponentMembers_present {row : Nat → G} {rank : G} {base selectorBase : Nat}
    {program : Toplevel} {indices : List FunIdx} {members : List MemberEmission}
    (emitted : emitComponentMembers row rank base selectorBase program indices = some members) :
    members.map MemberEmission.functionIndex = indices ∧
      ∀ member ∈ members,
        emitComponentMember row rank base member.selectorBase program member.functionIndex = some member := by
  induction indices generalizing selectorBase members with
  | nil => cases emitted; exact ⟨rfl, by simp⟩
  | cons index indices ih =>
    simp only [emitComponentMembers, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i first firstEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i rest restEmitted
    cases emitted
    obtain ⟨functionEq, _, selectorEq, _⟩ := emitComponentMember_present firstEmitted
    obtain ⟨indicesEq, membersEq⟩ := ih restEmitted
    refine ⟨by simp only [List.map_cons, functionEq, indicesEq], ?_⟩
    intro member present
    rcases List.mem_cons.mp present with equal | later
    · subst member
      rw [functionEq, selectorEq]
      exact firstEmitted
    · exact membersEq member later

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

def Circuit.emitComponentRow (row : Nat → G) (program : Toplevel) (circuit : Circuit) :
    Option CircuitEmission := do
  let rank := packRank (circuitRankBytes row circuit.layout)
  let base := circuit.layout.inputSize + circuit.layout.selectors + 1
  let members ← emitComponentMembers row rank base circuit.layout.inputSize program circuit.members.toList
  return componentCircuitEmission row program circuit members

end Aiur.Bytecode
