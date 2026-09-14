/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCalls
import Ix.Aiur.Proofs.Execution

/-! Static-component row obligations and exact byte-query accounting.
The component certificate supplies constrained edges; range lookups supply
dynamic rank bounds. Physical emitter reflection is a separate link. -/

namespace Aiur.AIR
open Bytecode.AIR

def FunctionRow.componentByteQueries (program : Bytecode.Toplevel) (row : FunctionRow) : List (G × G) :=
  (if (program.componentFor row.request.function).ranked then rankByteQueries row.rankBytes else []) ++
    row.calls.flatMap (fun edge =>
      if (program.componentFor row.request.function).order = (program.componentFor edge.1.function).order then
        rankByteQueries edge.2 else [])

def componentFunctionByteQueries (program : Bytecode.Toplevel) (rows : List FunctionRow) : List (G × G) :=
  rows.flatMap fun row => if row.selector = 1 then row.componentByteQueries program else []

/-- Local obligations for static components. The checked bytecode certificate
supplies component edges; row constraints supply ranks only where used. -/
structure FunctionRow.ComponentValid (program : Bytecode.Toplevel) (memory : Memory)
    (row : FunctionRow) : Prop where
  selector : row.selector = 0 ∨ row.selector = 1
  activity : activityConstraint row.multiplicity row.selector = 0
  constrained : row.selector = 1 → ∃ function,
    program.functions[row.request.function]? = some function ∧ function.constrained = true
  rank : row.selector = 1 → row.request.rank =
    if (program.componentFor row.request.function).ranked then packRank row.rankBytes else 0
  execution : row.selector = 1 → RunFunction program memory row.request row.requests
  order : ∀ edge ∈ row.calls,
    (program.componentFor row.request.function).order = (program.componentFor edge.1.function).order →
      row.selector * callOrderConstraint row.request.rank edge.1.rank (packRank edge.2) = 0

theorem FunctionRow.ComponentValid.active_of_nonzero {program : Bytecode.Toplevel}
    {memory : Memory} {row : FunctionRow} (valid : row.ComponentValid program memory)
    (nonzero : row.multiplicity ≠ 0) : row.selector = 1 := by
  rcases valid.selector with inactive | active
  · exact False.elim (nonzero (inactive_multiplicity_zero inactive valid.activity))
  · exact active

theorem componentByteQueries_member {program : Bytecode.Toplevel} {rows : List FunctionRow} {row : FunctionRow}
    (member : row ∈ rows) (active : row.selector = 1) :
    row.componentByteQueries program ⊆ componentFunctionByteQueries program rows := by
  intro query queried
  exact List.mem_flatMap.mpr ⟨row, member, by simpa only [if_pos active] using queried⟩

theorem componentQueries_provider {program : Bytecode.Toplevel} {memory : Memory}
    {roots : List Call} {rows : List FunctionRow}
    (valid : ∀ row ∈ rows, row.ComponentValid program memory)
    (balanced : ExactLookupBalance (functionQueries roots rows) (functionProviders rows))
    (bounded : (functionQueries roots rows).length < gSize.toNat)
    {request : Call} (queried : request ∈ functionQueries roots rows) :
    ∃ row ∈ rows, row.request = request ∧ row.selector = 1 := by
  obtain ⟨provider, member, same, nonzero⟩ := exactLookupBalance_provider balanced bounded queried
  obtain ⟨row, rowMember, providerEq⟩ := List.mem_map.mp member
  subst provider
  exact ⟨row, rowMember, same, (valid row rowMember).active_of_nonzero nonzero⟩

theorem FunctionRow.ComponentValid.rank_bounded {program : Bytecode.Toplevel}
    {memory : Memory} {rows : List FunctionRow} {row : FunctionRow}
    (valid : row.ComponentValid program memory) (member : row ∈ rows) (active : row.selector = 1)
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance (componentFunctionByteQueries program rows) (byteRangeProviders weights))
    (bounded : (componentFunctionByteQueries program rows).length < gSize.toNat) :
    row.request.rank.n < callRankBound := by
  rw [valid.rank active]
  cases ranked : (program.componentFor row.request.function).ranked
  · simp only [Bool.false_eq_true, if_false]
    decide
  · simp only [if_true]
    apply packRank_lt
    apply exactLookupBalance_rankBytes weights balanced bounded
    intro pair queried
    apply componentByteQueries_member member active
    apply List.mem_append_left
    simpa only [ranked, if_true] using queried

theorem FunctionRow.ComponentValid.call_order {program : Bytecode.Toplevel} {memory : Memory}
    {rows : List FunctionRow} {row : FunctionRow} (valid : row.ComponentValid program memory)
    (member : row ∈ rows) (active : row.selector = 1)
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance (componentFunctionByteQueries program rows) (byteRangeProviders weights))
    (bounded : (componentFunctionByteQueries program rows).length < gSize.toNat)
    {edge : Call × (Fin 6 → G)} (called : edge ∈ row.calls)
    (same : (program.componentFor row.request.function).order = (program.componentFor edge.1.function).order)
    (childBound : edge.1.rank.n < callRankBound) : row.request.rank.n < edge.1.rank.n := by
  have gapBound : (packRank edge.2).n < callRankBound := by
    apply packRank_lt
    apply exactLookupBalance_rankBytes weights balanced bounded
    intro pair queried
    apply componentByteQueries_member member active
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨edge, called, by simpa only [if_pos same] using queried⟩
  exact active_call_order_strict active (valid.rank_bounded member active weights balanced bounded)
    childBound gapBound (valid.order edge called same)

/-- Exact providers and checked component edges give finite execution. A
boundary call binds its child's rank through the full provider message;
only calls within a component use the gap-range queries. -/
theorem componentRows_execute {program : Bytecode.Toplevel} {memory : Memory}
    {roots : List Call} {rows : List FunctionRow}
    (components : program.validCallComponents = true)
    (valid : ∀ row ∈ rows, row.ComponentValid program memory)
    (balanced : ExactLookupBalance (functionQueries roots rows) (functionProviders rows))
    (bounded : (functionQueries roots rows).length < gSize.toNat)
    (weights : Fin 65536 → G)
    (bytesBalanced : ExactLookupBalance (componentFunctionByteQueries program rows) (byteRangeProviders weights))
    (bytesBounded : (componentFunctionByteQueries program rows).length < gSize.toNat)
    {row : FunctionRow} (member : row ∈ rows) (active : row.selector = 1) :
    Execution program memory row.request := by
  let ActiveRow := { row : FunctionRow // row ∈ rows ∧ row.selector = 1 }
  let component := fun row : ActiveRow => program.componentFor row.val.request.function
  let rank := fun row : ActiveRow => row.val.request.rank.n
  have componentBound : ∀ row : ActiveRow, (component row).order < program.functions.size := by
    intro current
    obtain ⟨function, present, _⟩ := (valid current.val current.property.1).constrained current.property.2
    exact Bytecode.Toplevel.validCallComponents_component_order components present
  have rankBound : ∀ row : ActiveRow, rank row < callRankBound := by
    intro current
    exact (valid current.val current.property.1).rank_bounded current.property.1 current.property.2
      weights bytesBalanced bytesBounded
  have wellFounded := Bytecode.CallComponent.wellFounded_calls component rank
    program.functions.size callRankBound componentBound rankBound
  have all : ∀ current : ActiveRow, Execution program memory current.val.request := by
    intro current
    induction current using wellFounded.induction with
    | h parent ih =>
      have parentValid := valid parent.val parent.property.1
      have localExecution := parentValid.execution parent.property.2
      obtain ⟨function, present, constrained⟩ := parentValid.constrained parent.property.2
      apply Execution.function localExecution
      intro child called
      obtain ⟨provider, providerMember, same, providerActive⟩ :=
        componentQueries_provider valid balanced bounded
          (functionQueries_member parent.property.1 parent.property.2 called)
      let found : ActiveRow := ⟨provider, providerMember, providerActive⟩
      have permitted := (localExecution.calls_components components present constrained child called).permits
      have relation : (component parent).permits (component found) = true ∧
          ((component parent).order = (component found).order → rank parent < rank found) := by
        constructor
        · simpa only [component, found, same] using permitted
        · intro shared
          obtain ⟨edge, edgeMember, edgeEq⟩ := List.mem_map.mp called
          have childBound := rankBound found
          have sameComponent : (program.componentFor parent.val.request.function).order =
              (program.componentFor edge.1.function).order := by
            simpa only [component, found, same, edgeEq] using shared
          have edgeBound : edge.1.rank.n < callRankBound := by
            simpa only [rank, found, same, edgeEq] using childBound
          have order := parentValid.call_order parent.property.1 parent.property.2
            weights bytesBalanced bytesBounded edgeMember sameComponent edgeBound
          simpa only [rank, found, same, edgeEq] using order
      simpa only [found, same] using ih found relation
  exact all ⟨row, member, active⟩

theorem componentRoots_execute {program : Bytecode.Toplevel} {memory : Memory}
    {roots : List Call} {rows : List FunctionRow}
    (components : program.validCallComponents = true)
    (valid : ∀ row ∈ rows, row.ComponentValid program memory)
    (balanced : ExactLookupBalance (functionQueries roots rows) (functionProviders rows))
    (bounded : (functionQueries roots rows).length < gSize.toNat)
    (weights : Fin 65536 → G)
    (bytesBalanced : ExactLookupBalance (componentFunctionByteQueries program rows) (byteRangeProviders weights))
    (bytesBounded : (componentFunctionByteQueries program rows).length < gSize.toNat)
    {request : Call} (root : request ∈ roots) : Execution program memory request := by
  obtain ⟨row, member, same, active⟩ := componentQueries_provider valid balanced bounded
    (List.mem_append_left _ root)
  rw [← same]
  exact componentRows_execute components valid balanced bounded weights bytesBalanced bytesBounded member active

end Aiur.AIR
