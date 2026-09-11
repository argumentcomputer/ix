/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Semantics.AIR
import Ix.Aiur.Proofs.Lookup

/-!
Finite execution from locally interpreted rows and exact lookup balance.

The interface keeps function requests, provider multiplicities, active-row
rank bytes and call-gap bytes explicit. Local row interpretation is still an
extraction obligation for the native constraint emitter. This theorem closes
the global call-table obligation once those local interpretations, exact
balance and the query-count bounds have been established. In particular, it
does not assume that a matching provider already has a finite execution.
-/

namespace Aiur.AIR

open Bytecode.AIR

/-- One interpreted function row; each call carries its six gap bytes. -/
structure FunctionRow where
  request : Call
  calls : List (Call × (Fin 6 → G))
  rankBytes : Fin 6 → G
  selector : G
  multiplicity : G

def FunctionRow.requests (row : FunctionRow) : List Call := row.calls.map Prod.fst

def FunctionRow.byteQueries (row : FunctionRow) : List (G × G) :=
  rankByteQueries row.rankBytes ++ row.calls.flatMap fun edge => rankByteQueries edge.2

/-- The concrete local obligations of an interpreted row. The execution
field resolves operations and control flow but leaves calls as requests. -/
structure FunctionRow.Valid (program : Bytecode.Toplevel) (memory : Memory)
    (row : FunctionRow) : Prop where
  selector : row.selector = 0 ∨ row.selector = 1
  activity : activityConstraint row.multiplicity row.selector = 0
  rank : row.selector = 1 → row.request.rank = packRank row.rankBytes
  execution : row.selector = 1 → RunFunction program memory row.request row.requests
  order : ∀ edge ∈ row.calls,
    row.selector * callOrderConstraint row.request.rank edge.1.rank (packRank edge.2) = 0

def functionProviders (rows : List FunctionRow) : List (Provider Call) :=
  rows.map fun row => (row.request, row.multiplicity)

def functionQueries (roots : List Call) (rows : List FunctionRow) : List Call :=
  roots ++ rows.flatMap fun row => if row.selector = 1 then row.requests else []

def functionByteQueries (rows : List FunctionRow) : List (G × G) :=
  rows.flatMap fun row => if row.selector = 1 then row.byteQueries else []

theorem FunctionRow.Valid.active_of_nonzero {program : Bytecode.Toplevel}
    {memory : Memory} {row : FunctionRow} (valid : row.Valid program memory)
    (nonzero : row.multiplicity ≠ 0) : row.selector = 1 := by
  rcases valid.selector with inactive | active
  · exact False.elim (nonzero (inactive_multiplicity_zero inactive valid.activity))
  · exact active

theorem functionByteQueries_member {rows : List FunctionRow} {row : FunctionRow}
    (member : row ∈ rows) (active : row.selector = 1) :
    row.byteQueries ⊆ functionByteQueries rows := by
  intro query queried
  apply List.mem_flatMap.mpr
  exact ⟨row, member, by simpa only [if_pos active] using queried⟩

theorem functionQueries_member {roots : List Call} {rows : List FunctionRow}
    {row : FunctionRow} (member : row ∈ rows) (active : row.selector = 1) :
    row.requests ⊆ functionQueries roots rows := by
  intro query queried
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨row, member, by simpa only [if_pos active] using queried⟩

/-- Every requested call has an active row supplying exactly that call,
including its rank. Provider multiplicities need not be natural counts. -/
theorem functionQueries_provider {program : Bytecode.Toplevel} {memory : Memory}
    {roots : List Call} {rows : List FunctionRow}
    (valid : ∀ row ∈ rows, row.Valid program memory)
    (balanced : ExactLookupBalance (functionQueries roots rows) (functionProviders rows))
    (bounded : (functionQueries roots rows).length < gSize.toNat)
    {request : Call} (queried : request ∈ functionQueries roots rows) :
    ∃ row ∈ rows, row.request = request ∧ row.selector = 1 := by
  obtain ⟨provider, member, same, nonzero⟩ :=
    exactLookupBalance_provider balanced bounded queried
  obtain ⟨row, rowMember, providerEq⟩ := List.mem_map.mp member
  subst provider
  exact ⟨row, rowMember, same, (valid row rowMember).active_of_nonzero nonzero⟩

theorem FunctionRow.Valid.rank_bounded {program : Bytecode.Toplevel}
    {memory : Memory} {rows : List FunctionRow} {row : FunctionRow}
    (valid : row.Valid program memory) (member : row ∈ rows) (active : row.selector = 1)
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance (functionByteQueries rows) (byteRangeProviders weights))
    (bounded : (functionByteQueries rows).length < gSize.toNat) :
    row.request.rank.n < callRankBound := by
  rw [valid.rank active]
  apply packRank_lt
  apply exactLookupBalance_rankBytes weights balanced bounded
  intro pair queried
  apply functionByteQueries_member member active
  exact List.mem_append_left _ queried

theorem FunctionRow.Valid.call_order {program : Bytecode.Toplevel} {memory : Memory}
    {rows : List FunctionRow} {row : FunctionRow} (valid : row.Valid program memory)
    (member : row ∈ rows) (active : row.selector = 1)
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance (functionByteQueries rows) (byteRangeProviders weights))
    (bounded : (functionByteQueries rows).length < gSize.toNat)
    {edge : Call × (Fin 6 → G)} (called : edge ∈ row.calls)
    (childBound : edge.1.rank.n < callRankBound) :
    row.request.rank.n < edge.1.rank.n := by
  have gapBound : (packRank edge.2).n < callRankBound := by
    apply packRank_lt
    apply exactLookupBalance_rankBytes weights balanced bounded
    intro pair queried
    apply functionByteQueries_member member active
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨edge, called, queried⟩
  exact active_call_order_strict active
    (valid.rank_bounded member active weights balanced bounded)
    childBound gapBound (valid.order edge called)

/-- Active locally valid rows give finite call derivations. The proof uses
the actual 48-bit rank/gap equations and balanced byte-table queries, not a
postulated acyclic call graph or an execution assumption on callees. -/
theorem balancedRows_execute {program : Bytecode.Toplevel} {memory : Memory}
    {roots : List Call} {rows : List FunctionRow}
    (valid : ∀ row ∈ rows, row.Valid program memory)
    (balanced : ExactLookupBalance (functionQueries roots rows) (functionProviders rows))
    (bounded : (functionQueries roots rows).length < gSize.toNat)
    (weights : Fin 65536 → G)
    (bytesBalanced : ExactLookupBalance (functionByteQueries rows) (byteRangeProviders weights))
    (bytesBounded : (functionByteQueries rows).length < gSize.toNat)
    {row : FunctionRow} (member : row ∈ rows) (active : row.selector = 1) :
    Execution program memory row.request := by
  have all : ∀ n : Nat, ∀ row : FunctionRow,
      callRankBound - row.request.rank.n = n → row ∈ rows → row.selector = 1 →
      Execution program memory row.request := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro parent measure member active
      apply Execution.function ((valid parent member).execution active)
      intro child called
      obtain ⟨edge, edgeMember, edgeEq⟩ := List.mem_map.mp called
      obtain ⟨provider, providerMember, same, providerActive⟩ :=
        functionQueries_provider valid balanced bounded
          (functionQueries_member member active called)
      have childBound := (valid provider providerMember).rank_bounded
        providerMember providerActive weights bytesBalanced bytesBounded
      have order := (valid parent member).call_order member active weights
        bytesBalanced bytesBounded edgeMember
        (by simpa only [edgeEq, ← same] using childBound)
      rw [edgeEq, ← same] at order
      have smaller : callRankBound - provider.request.rank.n < n := by omega
      rw [← same]
      exact ih _ smaller provider rfl providerMember providerActive
  exact all _ row rfl member active

/-- Every public/root request has a finite derivation under the same local,
balance and count obligations. Root rank zero may be imposed by the public
message encoding without changing this statement. -/
theorem balancedRoots_execute {program : Bytecode.Toplevel} {memory : Memory}
    {roots : List Call} {rows : List FunctionRow}
    (valid : ∀ row ∈ rows, row.Valid program memory)
    (balanced : ExactLookupBalance (functionQueries roots rows) (functionProviders rows))
    (bounded : (functionQueries roots rows).length < gSize.toNat)
    (weights : Fin 65536 → G)
    (bytesBalanced : ExactLookupBalance (functionByteQueries rows) (byteRangeProviders weights))
    (bytesBounded : (functionByteQueries rows).length < gSize.toNat)
    {request : Call} (root : request ∈ roots) : Execution program memory request := by
  obtain ⟨row, member, same, active⟩ := functionQueries_provider valid balanced bounded
    (List.mem_append_left _ root)
  rw [← same]
  exact balancedRows_execute valid balanced bounded weights bytesBalanced bytesBounded member active

end Aiur.AIR
