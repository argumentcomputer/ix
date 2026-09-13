/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRowQueries

/-!
The combined circuit return slot encodes the selected semantic return.
Per-function selector conservation and return-count bounds compose across
grouped members without an extra bound on the total inactive return count.
The single-writer premise for the ungated branchless optimization is explicit.
-/

namespace Aiur.AIR
open Bytecode

theorem MemberEmission.FromProgram.return_gates {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {member : MemberEmission} (source : member.FromProgram row rank column lookup program)
    (satisfied : ∀ equation ∈ member.body.equations, equation = 0) :
    member.body.returns.map Prod.fst = (member.function.body.selectorFlow (member.selector row)).returns := by
  have emitted := source.emitted
  rw [Bytecode.Function.emitRow] at emitted
  have projected := member.function.body.emitRow_projection row (member.selector row) _ _ _ _ _ emitted
  exact projected.returned.trans (member.function.body.returnGates_reflects (member.selector row) _
    (source.selector_satisfied satisfied) rfl)

theorem MemberEmission.FromProgram.return_boolean {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {member : MemberEmission} (source : member.FromProgram row rank column lookup program)
    (satisfied : ∀ equation ∈ member.body.equations, equation = 0) :
    ∀ part ∈ member.body.returns, booleanConstraint part.1 = 0 := by
  intro part present
  have sound := member.function.body.selectorFlow_sound (member.selector row) (source.selector_satisfied satisfied)
  apply sound.returned part.1
  rw [← source.return_gates satisfied]
  exact List.mem_map.mpr ⟨part, present, rfl⟩

theorem MemberEmission.FromProgram.return_count {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {member : MemberEmission} (source : member.FromProgram row rank column lookup program)
    (shape : member.function.body.lookupShapes program none = true)
    (bounded : (member.function.body.selectorFlow (member.selector row)).returns.length < gSize.toNat)
    (satisfied : ∀ equation ∈ member.body.equations, equation = 0) :
    (member.body.returns.map Prod.fst).count 1 = gateCount (member.entry row) := by
  have valid := source.selector_satisfied satisfied
  have sound := member.function.body.selectorFlow_sound (member.selector row) valid
  have empty := member.function.body.selectorFlow_yields_empty (member.selector row) program shape
  have conservation := sound.conservation
  rw [empty] at conservation
  change _ = selectorSum (member.function.body.selectorFlow (member.selector row)).returns + 0 at conservation
  rw [G.add_zero] at conservation
  rw [source.return_gates satisfied, MemberEmission.entry, conservation]
  apply selector_gateCount sound.returned bounded
  rw [← conservation]
  exact member.function.body.selectorFlow_boolean (member.selector row) valid

theorem flatMap_return_count {α β : Type} (items : List α) (gate : α → G) (parts : α → List (G × β))
    (count : ∀ item ∈ items, ((parts item).map Prod.fst).count 1 = gateCount (gate item)) :
    ((items.flatMap parts).map Prod.fst).count 1 = (items.map gate).count 1 := by
  have summed : ((items.flatMap parts).map Prod.fst).count 1 = ((items.map gate).map gateCount).sum := by
    induction items with
    | nil => rfl
    | cons item rest ih =>
      rw [List.flatMap_cons, List.map_append, List.count_append, count item List.mem_cons_self,
        ih (fun item member => count item (List.mem_cons_of_mem _ member))]
      rfl
  exact summed.trans (gateCount_list _)

theorem circuitEmission_return_count {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromProgram row rank column lookup program)
    (shape : ∀ member ∈ members, member.function.body.lookupShapes program none = true)
    (bounded : members.length < gSize.toNat)
    (returnBound : ∀ member ∈ members,
      (member.function.body.selectorFlow (member.selector row)).returns.length < gSize.toNat)
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0)
    (active : (circuitEmission row circuit members).selector = 1) :
    ((circuitEmission row circuit members).returns.map Prod.fst).count 1 = 1 := by
  have each := fun member present => (source member present).return_count (shape member present)
    (returnBound member present) (circuitEmission_member_satisfied satisfied present)
  change ((members.flatMap (·.body.returns)).map Prod.fst).count 1 = 1
  rw [flatMap_return_count members (fun member => member.entry row) (fun member => member.body.returns) each]
  have individual := circuitEmission_member_boolean source satisfied
  apply selectorSum_active_count
  · intro gate member
    obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
    subst gate
    exact individual part partMember
  · simpa only [List.length_map] using bounded
  · exact active

theorem circuitEmission_return_message {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromProgram row rank column lookup program)
    (shape : ∀ member ∈ members, member.function.body.lookupShapes program none = true)
    (bounded : members.length < gSize.toNat)
    (returnBound : ∀ member ∈ members,
      (member.function.body.selectorFlow (member.selector row)).returns.length < gSize.toNat)
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0)
    (active : (circuitEmission row circuit members).selector = 1)
    (width : Nat)
    (single : (circuitEmission row circuit members).branchless = true →
      (circuitEmission row circuit members).returns.length ≤ 1)
    {request : Bytecode.AIR.Call} (present : (1, request) ∈ (circuitEmission row circuit members).returns) :
    padMessage width ((circuitEmission row circuit members).lookup 0).2 = padMessage width (functionMessage request) := by
  have count := circuitEmission_return_count source shape bounded returnBound satisfied active
  apply slotMessage_chosen_count width (circuitEmission row circuit members).branchless
    (by simpa only [List.length_map] using single)
    (fun part member => ?_)
    (by simpa only [List.map_map, Function.comp_def] using count)
    (List.mem_map.mpr ⟨(1, request), present, rfl⟩) rfl
  obtain ⟨returned, returnMember, equal⟩ := List.mem_map.mp member
  subst part
  obtain ⟨body, bodyMember, returnedMember⟩ := List.mem_flatMap.mp returnMember
  exact (source body bodyMember).return_boolean (circuitEmission_member_satisfied satisfied bodyMember)
    returned returnedMember

end Aiur.AIR
