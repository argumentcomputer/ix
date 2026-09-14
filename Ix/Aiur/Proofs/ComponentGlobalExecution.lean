/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentExecution
import Ix.Aiur.Proofs.GlobalLookups

/-! Finite component execution from a single mixed padded balance. The
global consumer bound gives active providers; only the component-selected
rank and gap queries are used to rule out dynamic cycles. -/

namespace Aiur.AIR
open Bytecode.AIR

theorem GlobalLookups.component_function_provider {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory}
    (valid : ∀ row ∈ tables.functions, row.ComponentValid program memory)
    (programBound : program.functions.size < gSize.toNat)
    {request : Call} (shape : request.LookupShape program) (queried : functionMessage request ∈ queries) :
    ∃ row ∈ tables.functions, row.request = request ∧ row.selector = 1 := by
  obtain ⟨provider, member, same, nonzero⟩ := paddedLookupBalance_provider global.balance global.count queried
  have widthBound := global.widths _ queried
  have minimum := functionMessage_minimum request
  have channel := padMessage_channel (by omega : 0 < width) same
  obtain ⟨row, rowMember, equal⟩ := tables.function_provider member channel
  subst provider
  have active := (valid row rowMember).active_of_nonzero nonzero
  have exactCall := padded_functionMessage_reflects programBound shape
    ((valid row rowMember).execution active) widthBound same.symm
  exact ⟨row, rowMember, exactCall.symm, active⟩

theorem FunctionRow.ComponentValid.global_rank_bounded {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {row : FunctionRow}
    (valid : row.ComponentValid program memory) (member : row ∈ tables.functions) (active : row.selector = 1)
    (queried : (componentFunctionByteQueries program tables.functions).map rangeMessage ⊆ queries) :
    row.request.rank.n < callRankBound := by
  rw [valid.rank active]
  cases ranked : (program.componentFor row.request.function).ranked with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    decide
  | true =>
    simp only [if_true]
    apply packRank_lt
    apply global.rank_bytes
    intro message messageMember
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp messageMember
    apply queried
    refine List.mem_map.mpr ⟨pair, componentByteQueries_member member active ?_, equal⟩
    apply List.mem_append_left
    simpa only [ranked, if_true] using pairMember

theorem FunctionRow.ComponentValid.global_call_order {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {row : FunctionRow}
    (valid : row.ComponentValid program memory) (member : row ∈ tables.functions) (active : row.selector = 1)
    (queried : (componentFunctionByteQueries program tables.functions).map rangeMessage ⊆ queries)
    {edge : Call × (Fin 6 → G)} (called : edge ∈ row.calls)
    (same : (program.componentFor row.request.function).order = (program.componentFor edge.1.function).order)
    (childBound : edge.1.rank.n < callRankBound) : row.request.rank.n < edge.1.rank.n := by
  have gapBound : (packRank edge.2).n < callRankBound := by
    apply packRank_lt
    apply global.rank_bytes
    intro message messageMember
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp messageMember
    apply queried
    refine List.mem_map.mpr ⟨pair, componentByteQueries_member member active ?_, equal⟩
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨edge, called, by simpa only [if_pos same] using pairMember⟩
  exact active_call_order_strict active (valid.global_rank_bounded global member active queried)
    childBound gapBound (valid.order edge called same)

theorem GlobalLookups.component_rows_execute {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {roots : List Call}
    (components : program.validCallComponents = true) (programValid : program.validateLookupShapes = true)
    (valid : ∀ row ∈ tables.functions, row.ComponentValid program memory)
    (functionsQueried : (functionQueries roots tables.functions).map functionMessage ⊆ queries)
    (bytesQueried : (componentFunctionByteQueries program tables.functions).map rangeMessage ⊆ queries)
    {row : FunctionRow} (member : row ∈ tables.functions) (active : row.selector = 1)
    (shape : row.request.LookupShape program) : Execution program memory row.request := by
  have programBound : program.functions.size < gSize.toNat := by
    have checked := programValid
    simp only [Bytecode.Toplevel.validateLookupShapes, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1
  let ActiveRow := { row : FunctionRow // row ∈ tables.functions ∧ row.selector = 1 ∧ row.request.LookupShape program }
  let component := fun row : ActiveRow => program.componentFor row.val.request.function
  let rank := fun row : ActiveRow => row.val.request.rank.n
  have componentBound : ∀ row : ActiveRow, (component row).order < program.functions.size := by
    intro current
    obtain ⟨function, present, _⟩ := (valid current.val current.property.1).constrained current.property.2.1
    exact Bytecode.Toplevel.validCallComponents_component_order components present
  have rankBound : ∀ row : ActiveRow, rank row < callRankBound := by
    intro current
    exact (valid current.val current.property.1).global_rank_bounded global
      current.property.1 current.property.2.1 bytesQueried
  have wellFounded := Bytecode.CallComponent.wellFounded_calls component rank
    program.functions.size callRankBound componentBound rankBound
  have all : ∀ current : ActiveRow, Execution program memory current.val.request := by
    intro current
    induction current using wellFounded.induction with
    | h parent ih =>
      have parentValid := valid parent.val parent.property.1
      have localExecution := parentValid.execution parent.property.2.1
      obtain ⟨function, present, constrained, _, _⟩ := parent.property.2.2
      have children := localExecution.calls_lookupShape programValid present constrained
      apply Execution.function localExecution
      intro child called
      obtain ⟨provider, providerMember, same, providerActive⟩ :=
        global.component_function_provider valid programBound (children child called)
          (functionsQueried (List.mem_map.mpr
            ⟨child, functionQueries_member parent.property.1 parent.property.2.1 called, rfl⟩))
      let found : ActiveRow := ⟨provider, providerMember, providerActive, by rw [same]; exact children child called⟩
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
          have order := parentValid.global_call_order global parent.property.1 parent.property.2.1
            bytesQueried edgeMember sameComponent edgeBound
          simpa only [rank, found, same, edgeEq] using order
      simpa only [found, same] using ih found relation
  exact all ⟨row, member, active, shape⟩

theorem GlobalLookups.component_roots_execute {tables : LookupTables} {width : Nat}
    {queries : List (List G)} (global : GlobalLookups tables width queries)
    {program : Bytecode.Toplevel} {memory : Memory} {roots : List Call}
    (components : program.validCallComponents = true) (programValid : program.validateLookupShapes = true)
    (valid : ∀ row ∈ tables.functions, row.ComponentValid program memory)
    (functionsQueried : (functionQueries roots tables.functions).map functionMessage ⊆ queries)
    (bytesQueried : (componentFunctionByteQueries program tables.functions).map rangeMessage ⊆ queries)
    {request : Call} (shape : request.LookupShape program) (root : request ∈ roots) :
    Execution program memory request := by
  have programBound : program.functions.size < gSize.toNat := by
    have checked := programValid
    simp only [Bytecode.Toplevel.validateLookupShapes, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1
  obtain ⟨row, member, same, active⟩ := global.component_function_provider valid programBound shape
    (functionsQueried (List.mem_map.mpr ⟨request, List.mem_append_left _ root, rfl⟩))
  rw [← same]
  exact global.component_rows_execute components programValid valid functionsQueried bytesQueried
    member active (same ▸ shape)

end Aiur.AIR
