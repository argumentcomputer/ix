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

/-- A valued relation is either identically zero at this emission or checked
by one of its equations. Derived call ranks use the first case. -/
def EquationAvailable (equations : List G) (value : G) : Prop :=
  value = 0 ∨ value ∈ equations

theorem EquationAvailable.mono {first last : List G} {value : G}
    (equation : EquationAvailable first value) (included : first ⊆ last) :
    EquationAvailable last value := equation.imp_right (fun member => included member)

theorem EquationAvailable.satisfied {equations : List G} {value : G}
    (equation : EquationAvailable equations value)
    (zero : ∀ value ∈ equations, value = 0) : value = 0 :=
  equation.elim id (zero value)

/-- Every call has its complete function query. Ordered calls additionally
have gap range queries and a selector-gated order relation. -/
def CallRankChecks (callRanks : Array CallRank) (rank selector : G) (equations : List G)
    (hasQuery : List G → Prop) (edge : Bytecode.AIR.Call × (Fin 6 → G)) : Prop :=
  match callRanks[edge.1.function]?.getD .ordered with
  | .ordered => (∀ ⦃message⦄, message ∈ (rankByteQueries edge.2).map rangeMessage → hasQuery message) ∧
      EquationAvailable equations (selector * callOrderConstraint rank edge.1.rank (packRank edge.2))
  | .zero | .bound => True

theorem CallRankChecks.mono {callRanks : Array CallRank} {rank selector : G}
    {firstEquations lastEquations : List G} {firstQuery lastQuery : List G → Prop}
    {edge : Bytecode.AIR.Call × (Fin 6 → G)}
    (checked : CallRankChecks callRanks rank selector firstEquations firstQuery edge)
    (equations : firstEquations ⊆ lastEquations)
    (queries : ∀ message, firstQuery message → lastQuery message) :
    CallRankChecks callRanks rank selector lastEquations lastQuery edge := by
  unfold CallRankChecks at *
  cases mode : callRanks[edge.1.function]?.getD .ordered <;> simp only [mode] at checked ⊢
  exact ⟨fun {message} member => queries message (checked.1 member), checked.2.mono equations⟩

theorem CallRankChecks.ordered {callRanks : Array CallRank} {rank selector : G}
    {equations : List G} {hasQuery : List G → Prop} {edge : Bytecode.AIR.Call × (Fin 6 → G)}
    (checked : CallRankChecks callRanks rank selector equations hasQuery edge)
    (mode : callRanks[edge.1.function]?.getD .ordered = .ordered) :
    (∀ ⦃message⦄, message ∈ (rankByteQueries edge.2).map rangeMessage → hasQuery message) ∧
      EquationAvailable equations (selector * callOrderConstraint rank edge.1.rank (packRank edge.2)) := by
  simpa only [CallRankChecks, mode] using checked

def CallsEmitted (rank selector : G) (equations : List G) (queries : List (List G))
    (calls : List (Bytecode.AIR.Call × (Fin 6 → G)))
    (callRanks : Array CallRank := #[]) : Prop :=
  ∀ edge ∈ calls, functionMessage edge.1 ∈ queries ∧
    CallRankChecks callRanks rank selector equations (· ∈ queries) edge

theorem emitCallRow_calls (row : Nat → G) (rank selector : G) (function : FunIdx)
    (inputs : Array G) (size : Nat) (callRanks : Array CallRank) :
    let emission := emitCallRow row rank function inputs size (callRanks[function]?.getD .ordered)
    CallsEmitted rank selector emission.equations emission.queries emission.calls callRanks := by
  cases mode : callRanks[function]?.getD .ordered <;>
    simp only [emitCallRow, CallsEmitted, List.mem_singleton, forall_eq, List.mem_cons_self,
      true_and, CallRankChecks, mode, calleeRank, callGap, callRangeQueries]
  exact ⟨fun _ member => List.mem_cons_of_mem _ member,
    Or.inl (by rw [callOrderConstraint_derived, G.mul_zero])⟩

theorem emitOp_calls {row : Nat → G} {selector rank : G} {op : Op}
    {values : Array RowValue} {emission : OpEmission} {callRanks : Array CallRank}
    (emitted : emitOp row selector rank op values callRanks = some emission) :
    CallsEmitted rank selector emission.equations emission.queries emission.calls callRanks := by
  cases op <;> simp only [emitOp, emitByte1, emitByte2, emitU32LessThan, emitU32Add,
    emitAdvice, bind, Option.bind, Option.map, pure] at emitted
  all_goals
    repeat' first
      | split at emitted
      | (dsimp only at emitted; split at emitted)
  all_goals cases emitted
  all_goals first | exact emitCallRow_calls _ _ _ _ _ _ _ | simp [CallsEmitted]

theorem CallsEmitted.append {rank selector : G} {firstEquations restEquations : List G}
    {firstQueries restQueries : List (List G)}
    {firstCalls restCalls : List (Bytecode.AIR.Call × (Fin 6 → G))}
    {callRanks : Array CallRank}
    (first : CallsEmitted rank selector firstEquations firstQueries firstCalls callRanks)
    (rest : CallsEmitted rank selector restEquations restQueries restCalls callRanks) :
    CallsEmitted rank selector (firstEquations ++ restEquations)
      (firstQueries ++ restQueries) (firstCalls ++ restCalls) callRanks := by
  intro edge member
  rcases List.mem_append.mp member with left | right
  · obtain ⟨query, ordered⟩ := first edge left
    exact ⟨List.mem_append_left _ query, ordered.mono
      (fun _ member => List.mem_append_left _ member) (fun _ member => List.mem_append_left _ member)⟩
  · obtain ⟨query, ordered⟩ := rest edge right
    exact ⟨List.mem_append_right _ query, ordered.mono
      (fun _ member => List.mem_append_right _ member) (fun _ member => List.mem_append_right _ member)⟩

theorem emitOps_calls {row : Nat → G} {selector rank : G} {ops : List Op}
    {values : Array RowValue} {column : Nat} {emission : OpsEmission} {callRanks : Array CallRank}
    (emitted : emitOps row selector rank ops values column callRanks = some emission) :
    CallsEmitted rank selector emission.equations emission.queries emission.calls callRanks := by
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
  refine ⟨queried query,
    active_call_order_strict active rankBound childBound ?_ (equation.satisfied satisfied)⟩
  exact packRank_lt edge.2 (global.rank_bytes edge.2 (fun _ member => queried (bytes member)))

end Aiur.AIR
