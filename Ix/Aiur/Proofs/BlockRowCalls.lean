/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockRowExecution

/-!
Every call recorded by the valued block emitter retains its own gate,
function query, rank-byte queries and call-order equation through branching
and continuations. Tracking holds for arbitrary assignments; an active
execution then inherits the inventory required by the rank argument.
-/

namespace Aiur.AIR
open Bytecode

def BlockEmission.HasQuery (emission : BlockEmission) (selector : G) (message : List G) : Prop :=
  ∃ part ∈ emission.queries, part.selector = selector ∧ part.message = message

def BlockEmission.TracksCalls (rank : G) (emission : BlockEmission)
    (callRanks : Array CallRank := #[]) : Prop :=
  ∀ part ∈ emission.calls,
    emission.HasQuery part.1 (functionMessage part.2.1) ∧
    CallRankChecks callRanks rank part.1 emission.equations (emission.HasQuery part.1) part.2

theorem BlockEmission.HasQuery.mono {first last : BlockEmission}
    (included : first.queries ⊆ last.queries) {selector : G} {message : List G}
    (queried : first.HasQuery selector message) : last.HasQuery selector message := by
  obtain ⟨part, member, gate, equal⟩ := queried
  exact ⟨part, included member, gate, equal⟩

theorem BlockEmission.HasQuery.active {emission : BlockEmission} {queries : List (List G)}
    (queried : emission.QueriesIn queries) {message : List G} (present : emission.HasQuery 1 message) :
    message ∈ queries := by
  obtain ⟨part, member, gate, equal⟩ := present
  rw [← equal]
  exact queried part member gate

variable {callRanks : Array CallRank}

theorem BlockEmission.TracksCalls.prefix {rank : G} {emission : BlockEmission}
    (tracked : emission.TracksCalls rank callRanks) (equations : List G) :
    (emission.prefix equations).TracksCalls rank callRanks := by
  intro part member
  obtain ⟨query, checked⟩ := tracked part member
  exact ⟨query, checked.mono (fun _ member => List.mem_append_right _ member) (fun _ query => query)⟩

theorem BlockEmission.TracksCalls.afterOps {rank incoming : G} {lookup : Nat}
    {operations : OpsEmission} {control : BlockEmission}
    (opsTracked : CallsEmitted rank incoming operations.equations operations.queries operations.calls callRanks)
    (ctrlTracked : control.TracksCalls rank callRanks) :
    (control.afterOps incoming lookup operations).TracksCalls rank callRanks := by
  intro part member
  rcases List.mem_append.mp member with first | last
  · obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp first
    subst part
    obtain ⟨query, checked⟩ := opsTracked edge edgeMember
    have memberQuery : ∀ message ∈ operations.queries,
        (control.afterOps incoming lookup operations).HasQuery incoming message := by
      intro message member
      obtain ⟨query, queryMember, gate, equal⟩ := queryParts_member lookup incoming member
      exact ⟨query, List.mem_append_left _ queryMember, gate, equal⟩
    exact ⟨memberQuery _ query, checked.mono
      (fun _ member => List.mem_append_left _ member) memberQuery⟩
  · obtain ⟨query, checked⟩ := ctrlTracked part last
    exact ⟨query.mono (fun _ member => List.mem_append_right _ member), checked.mono
      (fun _ member => List.mem_append_right _ member)
      (fun _ query => query.mono (fun _ member => List.mem_append_right _ member))⟩

theorem BlockEmission.TracksCalls.join (rank : G) (values : Array RowValue) (column lookup : Nat)
    (emissions : List BlockEmission)
    (tracked : ∀ emission ∈ emissions, emission.TracksCalls rank callRanks) :
    (joinBlockEmissions values column lookup emissions).TracksCalls rank callRanks := by
  intro part member
  obtain ⟨emission, emissionMember, partMember⟩ := List.mem_flatMap.mp member
  obtain ⟨query, checked⟩ := tracked emission emissionMember part partMember
  have included := EmissionIncluded.join values column lookup emissionMember
  exact ⟨query.mono included.queries, checked.mono included.equations
    (fun _ query => query.mono included.queries)⟩

theorem BlockEmission.TracksCalls.continued {rank : G} {branches continuation : BlockEmission}
    (first : branches.TracksCalls rank callRanks) (last : continuation.TracksCalls rank callRanks)
    (equations : List G) :
    (branches.continued equations continuation).TracksCalls rank callRanks := by
  intro part member
  rcases List.mem_append.mp member with left | right
  · obtain ⟨query, checked⟩ := first part left
    exact ⟨query.mono (fun _ member => List.mem_append_left _ member), checked.mono
      (fun _ member => List.mem_append_left _ (List.mem_append_left _ member))
      (fun _ query => query.mono (fun _ member => List.mem_append_left _ member))⟩
  · obtain ⟨query, checked⟩ := last part right
    exact ⟨query.mono (fun _ member => List.mem_append_right _ member), checked.mono
      (fun _ member => List.mem_append_right _ member)
      (fun _ query => query.mono (fun _ member => List.mem_append_right _ member))⟩

theorem BlockEmission.TracksCalls.active {rank : G} {emission : BlockEmission}
    (tracked : emission.TracksCalls rank callRanks)
    {queries : List (List G)} (queried : emission.QueriesIn queries)
    {calls : List (Bytecode.AIR.Call × (Fin 6 → G))} (called : emission.CallsAt calls) :
    CallsEmitted rank 1 emission.equations queries calls callRanks := by
  intro edge member
  obtain ⟨query, checked⟩ := tracked (1, edge) (called edge member)
  exact ⟨query.active queried, checked.mono (fun _ member => member)
    (fun _ query => query.active queried)⟩

theorem forall₂_right_property {α β : Type} {source : List α} {emissions : List β} {property : β → Prop}
    (related : List.Forall₂ (fun _ emission => property emission) source emissions) :
    ∀ emission ∈ emissions, property emission := by
  induction related with
  | nil => simp
  | cons first _ ih =>
    intro emission member
    rcases List.mem_cons.mp member with equal | tail
    · subst emission; exact first
    · exact ih emission tail

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem branchRows_tracks_calls (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (caseSound : ∀ pair ∈ branches.toList, ∀ emission,
      pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup = some emission →
      emission.TracksCalls context.rank context.callRanks)
    (defaultSound : ∀ block, fallback = some block → ∀ emission,
      block.emitRow row selector context (block.selectorFlow selector).entry values
        (column + branches.size) lookup = some emission → emission.TracksCalls context.rank context.callRanks) :
    emission.TracksCalls context.rank context.callRanks := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i cases casesEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i default defaultEmitted
      have equal := Option.some.inj emitted
      subst emission
      have casesTracked : ∀ emission ∈ cases, emission.TracksCalls context.rank context.callRanks := by
        apply forall₂_right_property
        apply mapM_forall₂ casesEmitted
        intro pair member result resultEmitted
        simp only [caseRow, bind, Option.bind] at resultEmitted
        split at resultEmitted
        · cases resultEmitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj resultEmitted
          subst result
          exact (caseSound pair member body bodyEmitted).prefix _
      have defaultTracked : ∀ emission ∈ default, emission.TracksCalls context.rank context.callRanks := by
        cases fallback with
        | none =>
          simp only [defaultRow, Option.some.injEq] at defaultEmitted
          subst default
          simp
        | some block =>
          simp only [defaultRow, bind, Option.bind] at defaultEmitted
          split at defaultEmitted
          · cases defaultEmitted
          · rename_i body bodyEmitted
            have equal := Option.some.inj defaultEmitted
            subst default
            intro emission member
            have equal := List.mem_singleton.mp member
            subst emission
            exact (defaultSound block rfl body bodyEmitted).prefix _
      apply BlockEmission.TracksCalls.join
      intro emission member
      rcases List.mem_append.mp member with left | right
      · exact casesTracked emission left
      · exact defaultTracked emission right

private theorem block_call_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

theorem Ctrl.emitRow_tracks_calls (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (ctrl : Ctrl)
    {emission : BlockEmission}
    (emitted : ctrl.emitRow row selector context incoming values column lookup = some emission) :
    emission.TracksCalls context.rank context.callRanks := by
  cases ctrl with
  | «return» index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · dsimp only at emitted
      split at emitted
      · cases emitted
      · have equal := Option.some.inj emitted
        subst emission
        simp [BlockEmission.TracksCalls]
  | yield index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · have equal := Option.some.inj emitted
      subst emission
      simp [BlockEmission.TracksCalls]
  | «match» index branches fallback =>
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      apply branchRows_tracks_calls row selector context matched.value values column lookup branches fallback emitted
      · intro pair member body bodyEmitted
        exact Block.emitRow_tracks_calls row selector context _ values column lookup pair.2 bodyEmitted
      · intro block present body bodyEmitted
        exact Block.emitRow_tracks_calls row selector context _ values _ lookup block bodyEmitted
  | matchContinue index branches fallback size aux slots continuation =>
    rw [Ctrl.emitRow_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i joined branchesEmitted
        have branchesTracked := branchRows_tracks_calls row selector context matched.value values column lookup
          branches fallback branchesEmitted
          (fun pair member body bodyEmitted =>
            Block.emitRow_tracks_calls row selector context _ values column lookup pair.2 bodyEmitted)
          (fun block present body bodyEmitted =>
            Block.emitRow_tracks_calls row selector context _ values _ lookup block bodyEmitted)
        simp only [continueRow] at emitted
        split at emitted
        · simp only [bind, Option.bind] at emitted
          split at emitted
          · cases emitted
          · rename_i continued contEmitted
            have contTracked := Block.emitRow_tracks_calls row selector context _ _ _ _ continuation contEmitted
            have equal := Option.some.inj emitted
            subst emission
            exact branchesTracked.continued contTracked _
        · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr ‹_ ∈ _›); grind)

theorem Block.emitRow_tracks_calls (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission) :
    emission.TracksCalls context.rank context.callRanks := by
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i operations opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control ctrlEmitted
      have tracked := Ctrl.emitRow_tracks_calls row selector context incoming _ _ _ block.ctrl ctrlEmitted
      have equal := Option.some.inj emitted
      subst emission
      exact (BlockEmission.TracksCalls.afterOps (emitOps_calls opsEmitted) tracked).prefix _
termination_by sizeOf block
decreasing_by exact block_call_smaller block

end

end Aiur.Bytecode
