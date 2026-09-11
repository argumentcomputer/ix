/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationRows

/-!
Call inventories retain the exact function and gap queries and rank-order
polynomials emitted alongside each operation. Sequence composition preserves
this inventory. Active satisfying calls have strictly increasing bounded ranks
when their byte queries belong to the shared global lookup pool.
-/

namespace Aiur.AIR
open Bytecode

/-- Every recorded call has its function query, all gap range queries and
its selector-gated rank-order equation in the same emission. -/
def CallsEmitted (rank selector : G) (equations : List G) (queries : List (List G))
    (calls : List (Bytecode.AIR.Call × (Fin 6 → G))) : Prop :=
  ∀ edge ∈ calls, functionMessage edge.1 ∈ queries ∧
    (rankByteQueries edge.2).map rangeMessage ⊆ queries ∧
    selector * callOrderConstraint rank edge.1.rank (packRank edge.2) ∈ equations

theorem emitOp_calls {row : Nat → G} {selector rank : G} {op : Op}
    {values : Array RowValue} {emission : OpEmission}
    (emitted : emitOp row selector rank op values = some emission) :
    CallsEmitted rank selector emission.equations emission.queries emission.calls := by
  cases op <;> simp only [emitOp, emitByte1, emitByte2, emitU32LessThan, emitU32Add,
    emitAdvice, bind, Option.bind, Option.map, pure] at emitted
  all_goals
    repeat' first
      | split at emitted
      | (dsimp only at emitted; split at emitted)
  all_goals cases emitted
  all_goals simp [CallsEmitted]

theorem CallsEmitted.append {rank selector : G} {firstEquations restEquations : List G}
    {firstQueries restQueries : List (List G)}
    {firstCalls restCalls : List (Bytecode.AIR.Call × (Fin 6 → G))}
    (first : CallsEmitted rank selector firstEquations firstQueries firstCalls)
    (rest : CallsEmitted rank selector restEquations restQueries restCalls) :
    CallsEmitted rank selector (firstEquations ++ restEquations)
      (firstQueries ++ restQueries) (firstCalls ++ restCalls) := by
  intro edge member
  rcases List.mem_append.mp member with left | right
  · obtain ⟨query, bytes, equation⟩ := first edge left
    exact ⟨List.mem_append_left _ query,
      fun _ member => List.mem_append_left _ (bytes member),
      List.mem_append_left _ equation⟩
  · obtain ⟨query, bytes, equation⟩ := rest edge right
    exact ⟨List.mem_append_right _ query,
      fun _ member => List.mem_append_right _ (bytes member),
      List.mem_append_right _ equation⟩

theorem emitOps_calls {row : Nat → G} {selector rank : G} {ops : List Op}
    {values : Array RowValue} {column : Nat} {emission : OpsEmission}
    (emitted : emitOps row selector rank ops values column = some emission) :
    CallsEmitted rank selector emission.equations emission.queries emission.calls := by
  induction ops generalizing values column emission with
  | nil =>
    simp only [emitOps, Option.some.injEq] at emitted
    subst emission
    simp [CallsEmitted]
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i first firstEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i rest restEmitted
        have equal := Option.some.inj emitted
        subst emission
        exact (emitOp_calls firstEmitted).append (ih restEmitted)

theorem CallsEmitted.ordered {tables : LookupTables} {width : Nat} {pool : List (List G)}
    (global : GlobalLookups tables width pool)
    {rank selector : G} {equations : List G} {queries : List (List G)}
    {calls : List (Bytecode.AIR.Call × (Fin 6 → G))}
    (tracked : CallsEmitted rank selector equations queries calls)
    (active : selector = 1) (satisfied : ∀ equation ∈ equations, equation = 0)
    (queried : queries ⊆ pool) (rankBound : rank.n < callRankBound)
    {edge : Bytecode.AIR.Call × (Fin 6 → G)} (called : edge ∈ calls)
    (childBound : edge.1.rank.n < callRankBound) :
    functionMessage edge.1 ∈ pool ∧ rank.n < edge.1.rank.n := by
  obtain ⟨query, bytes, equation⟩ := tracked edge called
  refine ⟨queried query, active_call_order_strict active rankBound childBound ?_ (satisfied _ equation)⟩
  exact packRank_lt edge.2 (global.rank_bytes edge.2 (fun _ member => queried (bytes member)))

end Aiur.AIR
