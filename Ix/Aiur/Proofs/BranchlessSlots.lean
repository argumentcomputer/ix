/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRowCounts

/-! Every circuit eligible for ungated messages has a single function
with terminal control. Its queries occupy disjoint slots, independent of
witness selectors. This closes the single-writer premise and reflects all
encoded consumer slots after padding; native expression reflection remains
a separate obligation. -/

namespace Aiur.AIR
open Bytecode

def unitQuerySelectors (queries : List QueryPart) : List QueryPart :=
  queries.map fun query => { query with selector := 1 }

def QueryWriters (start finish : Nat) (queries : List QueryPart) : Prop :=
  QuerySlots 1 start finish (unitQuerySelectors queries)

theorem unitQuerySelectors_parts (slot : Nat) (selector : G) (queries : List (List G)) :
    unitQuerySelectors (queryParts slot selector queries) = queryParts slot 1 queries := by
  induction queries generalizing slot with
  | nil => rfl
  | cons message queries ih =>
    rw [queryParts_cons, queryParts_cons]
    change _ :: unitQuerySelectors (queryParts (slot + 1) selector queries) = _
    rw [ih]

theorem QueryWriters.indexed (slot : Nat) (selector : G) (queries : List (List G)) :
    QueryWriters slot (slot + queries.length) (queryParts slot selector queries) := by
  rw [QueryWriters, unitQuerySelectors_parts]
  exact QuerySlots.indexed 1 slot queries (by decide +kernel)

theorem QueryWriters.append {start middle finish : Nat} {first rest : List QueryPart}
    (left : QueryWriters start middle first) (right : QueryWriters middle finish rest) :
    QueryWriters start finish (first ++ rest) := by
  unfold QueryWriters unitQuerySelectors
  rw [List.map_append]
  exact QuerySlots.append left right

theorem QueryWriters.extend {start finish limit : Nat} {queries : List QueryPart}
    (writers : QueryWriters start finish queries) (bound : finish ≤ limit) :
    QueryWriters start limit queries := QuerySlots.extend writers bound

theorem QueryWriters.permuted {start finish : Nat} {queries other : List QueryPart}
    (writers : QueryWriters start finish queries) (permutation : queries.Perm other) :
    QueryWriters start finish other := QuerySlots.permuted writers (permutation.map _)

theorem unitQuerySelectors_count (queries : List QueryPart) (slot : Nat) :
    queryCount (unitQuerySelectors queries) slot = (querySlotParts queries slot).length := by
  simp only [queryCount, unitQuerySelectors, List.filter_map, List.length_map,
    querySlotParts, Function.comp_def, beq_self_eq_true, Bool.and_true]

theorem QueryWriters.single {start finish : Nat} {queries : List QueryPart}
    (writers : QueryWriters start finish queries) (slot : Nat) :
    (querySlotParts queries slot).length ≤ 1 := by
  rw [← unitQuerySelectors_count]
  exact writers.count slot

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Function.emitRow_terminal_writers (row : Nat → G) (selector : SelIdx → G)
    (function : Function) (functionIndex : FunIdx) (rank : G)
    (inputs : Array RowValue) (column lookup : Nat) {emission : BlockEmission}
    (terminal : function.hasTerminalControl = true)
    (emitted : function.emitRow row selector functionIndex rank inputs column lookup = some emission) :
    QueryWriters lookup emission.lookup emission.queries := by
  rw [Function.emitRow, Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i ops opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control controlEmitted
      have equal := Option.some.inj emitted
      subst emission
      cases ctrlEq : function.body.ctrl with
      | «match» index branches fallback =>
        simp only [Function.hasTerminalControl, ctrlEq, Bool.false_eq_true] at terminal
      | matchContinue index branches fallback size aux slots continuation =>
        simp only [Function.hasTerminalControl, ctrlEq, Bool.false_eq_true] at terminal
      | «return» index indices =>
        rw [ctrlEq, Ctrl.emitRow.eq_def] at controlEmitted
        simp only [bind, Option.bind] at controlEmitted
        split at controlEmitted
        · cases controlEmitted
        · dsimp only at controlEmitted
          split at controlEmitted
          · cases controlEmitted
          · have equal := Option.some.inj controlEmitted
            subst control
            simpa only [BlockEmission.prefix, BlockEmission.afterOps, List.append_nil] using
              QueryWriters.indexed lookup (function.body.selectorFlow selector).entry ops.queries
      | yield index indices =>
        rw [ctrlEq, Ctrl.emitRow.eq_def] at controlEmitted
        simp only [bind, Option.bind] at controlEmitted
        split at controlEmitted
        · cases controlEmitted
        · have equal := Option.some.inj controlEmitted
          subst control
          simpa only [BlockEmission.prefix, BlockEmission.afterOps, List.append_nil] using
            QueryWriters.indexed lookup (function.body.selectorFlow selector).entry ops.queries

end Aiur.Bytecode

namespace Aiur.AIR
open Bytecode

theorem circuitBranchless_member {selectors : Nat} {members : List MemberEmission}
    (enabled : circuitBranchless selectors (members.map (·.function)) = true) :
    ∃ member, members = [member] ∧ member.function.hasTerminalControl = true := by
  cases members with
  | nil => simp only [List.map_nil, circuitBranchless, Bool.and_false, Bool.false_eq_true] at enabled
  | cons member rest =>
    cases rest with
    | nil =>
      refine ⟨member, rfl, ?_⟩
      simp only [List.map_cons, List.map_nil, circuitBranchless, Bool.and_eq_true] at enabled
      exact enabled.2
    | cons next rest =>
      simp only [List.map_cons, circuitBranchless, Bool.and_false, Bool.false_eq_true] at enabled

theorem circuitEmission_queryWriters {row : Nat → G} {rank : G} {column : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromProgram row rank column 4 program)
    (enabled : (circuitEmission row circuit members).branchless = true)
    (limits : ∀ member ∈ members, member.body.lookup ≤ circuit.layout.lookups) :
    QueryWriters 1 circuit.layout.lookups (circuitEmission row circuit members).queries := by
  obtain ⟨member, membersEq, terminal⟩ := circuitBranchless_member enabled
  subst members
  have body := member.function.emitRow_terminal_writers row (member.selector row)
    member.functionIndex rank (rowAdvice row 0 member.function.layout.inputSize) column 4
    terminal (source member List.mem_cons_self).emitted
  have headers := QueryWriters.indexed 1 (circuitEmission row circuit [member]).selector
    ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage)
  have combined := (headers.append (body.extend (limits member List.mem_cons_self))).permuted List.perm_append_comm
  simpa only [circuitEmission, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.isEmpty_cons, Bool.false_eq_true, if_false] using combined

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_queryWriters (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (enabled : emission.branchless = true)
    (limits : ∀ member ∈ emission.members, member.body.lookup ≤ circuit.layout.lookups) :
    QueryWriters 1 emission.lookupCount emission.queries := by
  obtain ⟨description, _, source⟩ := circuit.emitRow_spec row program emitted
  have writers := circuitEmission_queryWriters source (by rw [← description]; exact enabled) limits
  have lookupEq := congrArg CircuitEmission.lookupCount description
  change emission.lookupCount = circuit.layout.lookups at lookupEq
  rw [← lookupEq, ← description] at writers
  exact writers

theorem Circuit.emitRow_queries_reflect (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (validated : circuit.validateRowCounts program = true)
    (reserved : 4 ≤ circuit.layout.lookups)
    (limits : ∀ member ∈ emission.members, member.body.lookup ≤ circuit.layout.lookups)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (width : Nat) :
    (encodedQueries emission.branchless emission.queries emission.lookupCount).map (padMessage width) =
      (decodedQueries emission.queries emission.lookupCount).map (padMessage width) := by
  obtain ⟨bounded, bounds, _, _⟩ := circuit.emitRow_count_bounds row program emitted validated satisfied
  have slots := circuit.emitRow_querySlots row program emitted bounded bounds reserved limits satisfied
  apply slots.queries_reflect
  exact fun enabled slot => (circuit.emitRow_queryWriters row program emitted enabled limits).single slot

end Aiur.Bytecode
