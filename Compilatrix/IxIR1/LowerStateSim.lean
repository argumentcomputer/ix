import Compilatrix.IxIR1.LowerSim

/-!
# Compile-state simulation for IxIR₀ → IxIR₁ lowering

This companion proves that successful lowering consumes exactly each source
entry's syntactic occurrence count. In particular, a counted let binder is
released before the executable lowerer removes its logical entry.
-/

namespace Compilatrix.IxIR1.LowerSim

open Compilatrix.Ixon (Owned Uses)
open Compilatrix.IxIR1.Lower
open Compilatrix.IxIR1.Sim

theorem trackedThrowRun_not_ok {error state α : Type}
    {err : error} {initial final : state} {value : α}
    (h : (throw err : EStateM error state α).run initial =
      .ok value final) : False := by
  change EStateM.Result.error err initial = .ok value final at h
  contradiction

theorem trackedBindRun_ok_inv {error state α β : Type}
    {action : EStateM error state α} {next : α → EStateM error state β}
    {initial final : state} {result : β}
    (h : (action >>= next).run initial = .ok result final) :
    ∃ value middle,
      action.run initial = .ok value middle ∧
      (next value).run middle = .ok result final := by
  change
    (match action.run initial with
      | .ok value nextState => (next value).run nextState
      | .error err nextState => .error err nextState) =
      .ok result final at h
  cases haction : action.run initial with
  | ok value middle =>
    rw [haction] at h
    exact ⟨value, middle, rfl, h⟩
  | error err middle =>
    rw [haction] at h
    contradiction

def EntryTracksAt (Γ : VEnv) (index abs : Nat) (uses : Uses)
    (remaining : Nat) : Prop :=
  Γ.entries[index]? =
    some (.slot abs remaining uses (remaining != 0))

def EntryConsumption (input output : VEnv)
    (consumed : Nat → Nat) : Prop :=
  ∀ index abs uses base,
    EntryTracksAt input index abs uses (base + consumed index) →
    EntryTracksAt output index abs uses base

/-- Every entry in a fixed logical prefix has the requested remaining-use
count and the canonical held bit. -/
def EntriesTrackCounts (Γ : VEnv) (count : Nat)
    (remaining : Nat → Nat) : Prop :=
  ∀ index, index < count →
    ∃ abs uses, EntryTracksAt Γ index abs uses (remaining index)

private theorem entriesReleased_of_getElem_slot_false :
    ∀ entries : List VEntry,
      (∀ index, index < entries.length →
        ∃ abs remaining uses,
          entries[index]? = some (.slot abs remaining uses false)) →
      EntriesReleased entries := by
  intro entries
  induction entries with
  | nil => exact fun _ => .nil
  | cons entry tail ih =>
    intro hall
    obtain ⟨abs, remaining, uses, hhead⟩ := hall 0 (by simp)
    have hentry : entry = .slot abs remaining uses false := by
      simpa using hhead
    subst entry
    apply EntriesReleased.slot
    apply ih
    intro index hindex
    obtain ⟨tailAbs, tailRemaining, tailUses, htail⟩ :=
      hall (index + 1) (by simp; omega)
    exact ⟨tailAbs, tailRemaining, tailUses, by simpa using htail⟩

/-- Exact consumption releases every tracked entry once the output is known to
have no additional logical entries. -/
theorem EntryConsumption.entriesReleased {input output : VEnv}
    {consumed : Nat → Nat} {count : Nat}
    (hconsume : EntryConsumption input output consumed)
    (htracks : EntriesTrackCounts input count consumed)
    (hlength : output.entries.length = count) :
    EntriesReleased output.entries := by
  apply entriesReleased_of_getElem_slot_false
  intro index hindex
  have hcount : index < count := by simpa [hlength] using hindex
  obtain ⟨abs, uses, htrack⟩ := htracks index hcount
  have hout := hconsume index abs uses 0 (by simpa using htrack)
  exact ⟨abs, 0, uses, by simpa [EntryTracksAt] using hout⟩

private theorem entriesReleased_of_prefix_slots_recSelf :
    ∀ (count : Nat) (entries : List VEntry) (arity : Nat),
      entries.length = count + 1 →
      (∀ index, index < count →
        ∃ abs remaining uses,
          entries[index]? = some (.slot abs remaining uses false)) →
      entries[count]? = some (.recSelf arity) →
      EntriesReleased entries := by
  intro count
  induction count with
  | zero =>
    intro entries arity hlength _ hself
    cases entries with
    | nil => simp at hlength
    | cons entry tail =>
      have htailLength : tail.length = 0 := by simpa using hlength
      cases tail with
      | nil =>
        have hentry : entry = .recSelf arity := by simpa using hself
        subst entry
        exact EntriesReleased.recSelf EntriesReleased.nil
      | cons tailHead tailRest => simp at htailLength
  | succ count ih =>
    intro entries arity hlength hprefix hself
    cases entries with
    | nil => simp at hlength
    | cons entry tail =>
      obtain ⟨abs, remaining, uses, hhead⟩ :=
        hprefix 0 (Nat.zero_lt_succ count)
      have hentry : entry = .slot abs remaining uses false := by
        simpa using hhead
      subst entry
      apply EntriesReleased.slot
      apply ih tail arity
      · simpa using hlength
      · intro index hindex
        obtain ⟨tailAbs, tailRemaining, tailUses, htail⟩ :=
          hprefix (index + 1) (by omega)
        exact ⟨tailAbs, tailRemaining, tailUses, by simpa using htail⟩
      · simpa using hself

/-- Exact consumption releases every ordinary entry in a tracked prefix while
the structural lowering invariant preserves the trailing recursive-self
entry used by recursor rule bodies. -/
theorem EntryConsumption.entriesReleasedWithRecSelf
    {input output : VEnv} {consumed : Nat → Nat}
    {count arity : Nat}
    (hconsume : EntryConsumption input output consumed)
    (htracks : EntriesTrackCounts input count consumed)
    (hlength : output.entries.length = count + 1)
    (hself : RecSelfAt output count arity) :
    EntriesReleased output.entries := by
  apply entriesReleased_of_prefix_slots_recSelf count output.entries arity
    hlength
  · intro index hindex
    obtain ⟨abs, uses, htrack⟩ := htracks index hindex
    have hout := hconsume index abs uses 0 (by simpa using htrack)
    exact ⟨abs, 0, uses, by simpa [EntryTracksAt] using hout⟩
  · exact hself

private theorem EntriesTrackCounts.frameLiveSlot
    {Γ : VEnv} {count abs : Nat} {uses : Uses}
    {remaining : Nat → Nat}
    (htracks : EntriesTrackCounts Γ count remaining)
    (hlength : Γ.entries.length = count)
    (hlive : remaining count ≠ 0) :
    EntriesTrackCounts
      (frameVEnvEntries Γ
        [.slot abs (remaining count) uses true])
      (count + 1) remaining := by
  intro index hindex
  by_cases hprefix : index < count
  · obtain ⟨trackedAbs, trackedUses, htrack⟩ := htracks index hprefix
    refine ⟨trackedAbs, trackedUses, ?_⟩
    have hΓ : index < Γ.entries.length := by simpa [hlength] using hprefix
    rw [EntryTracksAt] at htrack ⊢
    change (Γ.entries ++ [.slot abs (remaining count) uses true])[index]? = _
    rw [List.getElem?_append_left hΓ]
    exact htrack
  · have hi : index = count := by omega
    subst index
    refine ⟨abs, uses, ?_⟩
    simp [EntryTracksAt, frameVEnvEntries, hlength, hlive]

private theorem EntriesTrackCounts.frameReleasedSlot
    {Γ : VEnv} {count abs : Nat} {uses : Uses}
    {remaining : Nat → Nat}
    (htracks : EntriesTrackCounts Γ count remaining)
    (hlength : Γ.entries.length = count)
    (hdead : remaining count = 0) :
    let framed := frameVEnvEntries Γ [.slot abs 0 uses true]
    EntriesTrackCounts
      ((framed.setEntry count (.slot abs 0 uses false)).bump)
      (count + 1) remaining := by
  dsimp only
  intro index hindex
  by_cases hprefix : index < count
  · obtain ⟨trackedAbs, trackedUses, htrack⟩ := htracks index hprefix
    refine ⟨trackedAbs, trackedUses, ?_⟩
    have hframed : EntryTracksAt
        (frameVEnvEntries Γ [.slot abs 0 uses true]) index trackedAbs
          trackedUses (remaining index) := by
      have hΓ : index < Γ.entries.length := by simpa [hlength] using hprefix
      rw [EntryTracksAt] at htrack ⊢
      change (Γ.entries ++ [.slot abs 0 uses true])[index]? = _
      rw [List.getElem?_append_left hΓ]
      exact htrack
    have hne : count ≠ index := by omega
    simpa [EntryTracksAt, VEnv.setEntry, VEnv.bump, hne] using hframed
  · have hi : index = count := by omega
    subst index
    refine ⟨abs, uses, ?_⟩
    rw [hdead]
    simp [EntryTracksAt, frameVEnvEntries, VEnv.setEntry, VEnv.bump,
      hlength]

theorem EntriesTrackCounts.frameCanonicalSlot
    {Γ : VEnv} {count abs : Nat} {uses : Uses}
    {remaining : Nat → Nat}
    (htracks : EntriesTrackCounts Γ count remaining)
    (hlength : Γ.entries.length = count) :
    EntriesTrackCounts
      (frameVEnvEntries Γ
        [.slot abs (remaining count) uses (remaining count != 0)])
      (count + 1) remaining := by
  intro index hindex
  by_cases hprefix : index < count
  · obtain ⟨trackedAbs, trackedUses, htrack⟩ := htracks index hprefix
    refine ⟨trackedAbs, trackedUses, ?_⟩
    have hΓ : index < Γ.entries.length := by simpa [hlength] using hprefix
    rw [EntryTracksAt] at htrack ⊢
    change
      (Γ.entries ++
        [.slot abs (remaining count) uses (remaining count != 0)])[index]? = _
    rw [List.getElem?_append_left hΓ]
    exact htrack
  · have hi : index = count := by omega
    subst index
    refine ⟨abs, uses, ?_⟩
    simp [EntryTracksAt, frameVEnvEntries, hlength]

/-- The canonical generated parameter-drop plan leaves every logical parameter
at its original remaining-use count with the canonical held bit. This
strengthens `parameterDrops_releasePlan_atDepth` by recording the state fact
needed after the body consumes those remaining occurrences. -/
theorem parameterDrops_releasePlan_tracked_atDepth (base depth : Nat)
    (modes : List Uses) (remaining : Nat → Nat)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      ReleasePlan
        ⟨parameterEntries base modes remaining, depth⟩
        (parameterDrops base modes remaining) output emit ∧
      EntriesTrackCounts output modes.length remaining := by
  induction modes generalizing base depth with
  | nil =>
    refine ⟨⟨[], depth⟩, (_root_.id : Emit), ReleasePlan.nil, ?_⟩
    intro index hindex
    simp at hindex
  | cons mode modes ih =>
    obtain ⟨htail, hmode⟩ := hadmissible
    obtain ⟨innerOutput, innerEmit, hinner, hinnerTracks⟩ :=
      ih (base + 1) depth htail
    let outerEntry : VEntry :=
      .slot base (remaining modes.length) mode true
    let framedOutput := frameVEnvEntries innerOutput [outerEntry]
    have hinnerFull : ReleasePlan
        ⟨parameterEntries base (mode :: modes) remaining, depth⟩
        (parameterDrops (base + 1) modes remaining)
        framedOutput innerEmit := by
      have hframed := hinner.frameEntries [outerEntry]
      have hinputEq :
          frameVEnvEntries
              ⟨parameterEntries (base + 1) modes remaining, depth⟩
              [outerEntry] =
            ⟨parameterEntries base (mode :: modes) remaining, depth⟩ := by
        simp [frameVEnvEntries, parameterEntries, outerEntry]
      rw [hinputEq] at hframed
      simpa [framedOutput, outerEntry] using hframed
    have hlength : innerOutput.entries.length = modes.length := by
      calc
        innerOutput.entries.length =
            (parameterEntries (base + 1) modes remaining).length :=
          hinner.entries_length
        _ = modes.length := parameterEntries_length _ _ _
    by_cases hzero : remaining modes.length = 0
    · rcases hmode hzero with rfl | rfl
      · have hentry : framedOutput.entries[modes.length]? =
            some (.slot base 0 .many true) := by
          simp [framedOutput, frameVEnvEntries, outerEntry, hlength, hzero]
        let finalOutput :=
          (framedOutput.setEntry modes.length
            (.slot base 0 .many false)).bump
        have houter : ReleasePlan framedOutput
            [⟨modes.length, base, .many⟩] finalOutput
            (emitOp (.drop (.var (framedOutput.rel base))) ∘
              (_root_.id : Emit)) := by
          exact ReleasePlan.many hentry ReleasePlan.nil
        refine ⟨finalOutput, innerEmit ∘
          (emitOp (.drop (.var (framedOutput.rel base))) ∘
            (_root_.id : Emit)), ?_, ?_⟩
        · simpa [parameterDrops, hzero] using hinnerFull.comp houter
        · have htracks := EntriesTrackCounts.frameReleasedSlot
            (abs := base) (uses := .many) hinnerTracks hlength hzero
          simpa [finalOutput, framedOutput, outerEntry, hzero] using htracks
      · have hentry : framedOutput.entries[modes.length]? =
            some (.slot base 0 .affine true) := by
          simp [framedOutput, frameVEnvEntries, outerEntry, hlength, hzero]
        let finalOutput :=
          (framedOutput.setEntry modes.length
            (.slot base 0 .affine false)).bump
        have houter : ReleasePlan framedOutput
            [⟨modes.length, base, .affine⟩] finalOutput
            (emitOp (.dropU (.var (framedOutput.rel base))) ∘
              (_root_.id : Emit)) := by
          exact ReleasePlan.affine hentry ReleasePlan.nil
        refine ⟨finalOutput, innerEmit ∘
          (emitOp (.dropU (.var (framedOutput.rel base))) ∘
            (_root_.id : Emit)), ?_, ?_⟩
        · simpa [parameterDrops, hzero] using hinnerFull.comp houter
        · have htracks := EntriesTrackCounts.frameReleasedSlot
            (abs := base) (uses := .affine) hinnerTracks hlength hzero
          simpa [finalOutput, framedOutput, outerEntry, hzero] using htracks
    · refine ⟨framedOutput, innerEmit, ?_, ?_⟩
      · simpa [parameterDrops, hzero] using hinnerFull
      · have htracks := EntriesTrackCounts.frameLiveSlot
          (abs := base) (uses := mode) hinnerTracks hlength hzero
        simpa [framedOutput, outerEntry] using htracks

/-- Canonical ordinary-function entry specialization. -/
theorem parameterDrops_releasePlan_tracked (base : Nat)
    (modes : List Uses) (remaining : Nat → Nat)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      ReleasePlan
        ⟨parameterEntries base modes remaining, base + modes.length⟩
        (parameterDrops base modes remaining) output emit ∧
      EntriesTrackCounts output modes.length remaining :=
  parameterDrops_releasePlan_tracked_atDepth base (base + modes.length)
    modes remaining hadmissible

/-- The generated recursor-field retain fold leaves each field placeholder at
exactly its RHS occurrence count.  Zero-use fields remain released; live
fields are activated by the corresponding `dup`. -/
theorem recursorFieldRetains_plan_tracked
    (fieldAbs depth fieldCount : Nat) (rhs : IxIR0.Expr) :
    let dead : VEntry := .slot 0 0 .many false
    ∃ output emit,
      FieldRetainPlan
        ⟨List.replicate fieldCount dead, depth⟩
        (recursorFieldRetains fieldAbs rhs fieldCount)
        output emit ∧
      EntriesTrackCounts output fieldCount
        (fun index => countUses index rhs) := by
  dsimp only
  induction fieldCount generalizing fieldAbs depth with
  | zero =>
    refine ⟨⟨[], depth⟩, (_root_.id : Emit), FieldRetainPlan.nil, ?_⟩
    intro index hindex
    simp at hindex
  | succ fieldCount ih =>
    let dead : VEntry := .slot 0 0 .many false
    let uses := countUses fieldCount rhs
    have hrep : List.replicate (fieldCount + 1) dead =
        List.replicate fieldCount dead ++ [dead] := by
      symm
      simpa using (List.replicate_append_replicate
        (n := fieldCount) (m := 1) (a := dead))
    by_cases hzero : uses = 0
    · obtain ⟨tailOutput, tailEmit, htail, htailTracks⟩ :=
        ih (fieldAbs + 1) depth
      have hframed := htail.frameEntries [dead]
      have hlength : tailOutput.entries.length = fieldCount := by
        calc
          tailOutput.entries.length =
              (List.replicate fieldCount dead).length :=
            htail.entries_length
          _ = fieldCount := by simp
      have htracks := EntriesTrackCounts.frameCanonicalSlot
        (abs := 0) (uses := .many) htailTracks hlength
      refine ⟨frameVEnvEntries tailOutput [dead], tailEmit, ?_, ?_⟩
      · rw [hrep]
        simpa [recursorFieldRetains, uses, hzero, dead,
          frameVEnvEntries] using hframed
      · simpa [dead, uses, hzero] using htracks
    · obtain ⟨tailOutput, tailEmit, htail, htailTracks⟩ :=
        ih (fieldAbs + 1) (depth + 1)
      let held : VEntry := .slot depth uses .many true
      have hframed := htail.frameEntries [held]
      let input : VEnv :=
        ⟨List.replicate (fieldCount + 1) dead, depth⟩
      have hentry : input.entries[fieldCount]? = some dead := by
        simp [input, dead]
      have hnext :
          ((input.setEntry fieldCount held).bump) =
            frameVEnvEntries
              ⟨List.replicate fieldCount dead, depth + 1⟩ [held] := by
        simp only [input, VEnv.setEntry, VEnv.bump]
        rw [hrep]
        simp [held, dead, frameVEnvEntries, List.set_append_right]
      have htailFull : FieldRetainPlan
          ((input.setEntry fieldCount held).bump)
          (recursorFieldRetains (fieldAbs + 1) rhs fieldCount)
          (frameVEnvEntries tailOutput [held]) tailEmit := by
        rw [hnext]
        exact hframed
      have hfirst := FieldRetainPlan.retain
        (fieldAbs := fieldAbs) hentry htailFull
      have hlength : tailOutput.entries.length = fieldCount := by
        calc
          tailOutput.entries.length =
              (List.replicate fieldCount dead).length :=
            htail.entries_length
          _ = fieldCount := by simp
      have htracks := EntriesTrackCounts.frameLiveSlot
        (abs := depth) (uses := .many) htailTracks hlength
        (by simpa [uses] using hzero)
      refine ⟨frameVEnvEntries tailOutput [held],
        emitOp (.dup (.var (input.rel fieldAbs))) ∘ tailEmit, ?_, ?_⟩
      · simpa [input, recursorFieldRetains, uses, hzero, dead, held]
          using hfirst
      · simpa [held, uses] using htracks

theorem replicate_many_parameterDropsAdmissible
    (count : Nat) (remaining : Nat → Nat) :
    ParameterDropsAdmissible (List.replicate count .many) remaining := by
  induction count with
  | zero => simp [ParameterDropsAdmissible]
  | succ count ih =>
    simp only [List.replicate_succ, ParameterDropsAdmissible]
    exact ⟨ih, by simp⟩

/-- The exact generated field/parameter prefix establishes the logical RHS
layout needed by occurrence accounting: every ordinary entry is tracked by
its RHS count and the final entry is the untouched recursive-self marker. -/
theorem recursorPrefix_entries_tracked
    (numArgs fields : Nat) (rhs : IxIR0.Expr) (state : LowSt)
    {fieldOutput : VEnv} {fieldEmit : Emit}
    {rhsInput : VEnv} {parameterEmit : Emit}
    (hfieldRun :
      applyRecursorFieldRetains
          ⟨List.replicate fields (.slot 0 0 .many false),
            (numArgs + 1) + fields⟩
          (recursorFieldRetains (numArgs + 1) rhs fields) =
        (fieldOutput, fieldEmit))
    (hparameterRun :
      (releaseSlots
          ⟨fieldOutput.entries ++
              parameterEntries 0 (List.replicate numArgs .many)
                (fun i => countUses (fields + i) rhs) ++
              [.recSelf (numArgs + 1)],
            fieldOutput.depth + 1⟩
          ((parameterDrops 0 (List.replicate numArgs .many)
              (fun i => countUses (fields + i) rhs)).map
            (SlotDrop.offsetEntry fields))).run state =
        .ok (rhsInput, parameterEmit) state) :
    EntriesTrackCounts rhsInput (fields + numArgs)
        (fun index => countUses index rhs) ∧
      rhsInput.entries.length = fields + numArgs + 1 ∧
      RecSelfAt rhsInput (fields + numArgs) (numArgs + 1) := by
  obtain ⟨plannedFieldOutput, plannedFieldEmit,
      hfieldPlan, hfieldTracks⟩ :=
    recursorFieldRetains_plan_tracked
      (numArgs + 1) ((numArgs + 1) + fields) fields rhs
  have hfieldEq :
      (fieldOutput, fieldEmit) =
        (plannedFieldOutput, plannedFieldEmit) :=
    hfieldRun.symm.trans hfieldPlan.run
  cases hfieldEq
  have hfieldLength : fieldOutput.entries.length = fields := by
    calc
      fieldOutput.entries.length =
          (List.replicate fields
            (VEntry.slot 0 0 Uses.many false)).length :=
        hfieldPlan.entries_length
      _ = fields := by simp
  let paramModes := List.replicate numArgs Uses.many
  let paramRemaining : Nat → Nat :=
    fun index => countUses (fields + index) rhs
  obtain ⟨parameterOutput, plannedParameterEmit,
      hparameterPlan, hparameterTracks⟩ :=
    parameterDrops_releasePlan_tracked_atDepth
      0 (fieldOutput.depth + 1) paramModes paramRemaining
      (replicate_many_parameterDropsAdmissible numArgs paramRemaining)
  have hparameterLength : parameterOutput.entries.length = numArgs := by
    calc
      parameterOutput.entries.length =
          (parameterEntries 0 paramModes paramRemaining).length :=
        hparameterPlan.entries_length
      _ = numArgs := by simp [paramModes]
  let plannedRhsInput :=
    prependVEnvEntries fieldOutput.entries
      (frameVEnvEntries parameterOutput [.recSelf (numArgs + 1)])
  have hfullPlan : ReleasePlan
      ⟨fieldOutput.entries ++
          parameterEntries 0 (List.replicate numArgs .many)
            (fun i => countUses (fields + i) rhs) ++
          [.recSelf (numArgs + 1)],
        fieldOutput.depth + 1⟩
      ((parameterDrops 0 (List.replicate numArgs .many)
          (fun i => countUses (fields + i) rhs)).map
        (SlotDrop.offsetEntry fields))
      plannedRhsInput plannedParameterEmit := by
    have hframed := hparameterPlan.frameEntries
      [.recSelf (numArgs + 1)]
    have hprepended := hframed.prependEntries fieldOutput.entries
    simpa [plannedRhsInput, prependVEnvEntries, frameVEnvEntries,
      paramModes, paramRemaining, hfieldLength, List.append_assoc]
      using hprepended
  have hfullRun := hfullPlan.run state
  have hrhsEq :
      (plannedRhsInput, plannedParameterEmit) =
          (rhsInput, parameterEmit) ∧ state = state := by
    simpa using hfullRun.symm.trans hparameterRun
  have hinputs := hrhsEq.1
  have hrhsInput : plannedRhsInput = rhsInput :=
    congrArg Prod.fst hinputs
  subst rhsInput
  refine ⟨?_, ?_, ?_⟩
  · intro index hindex
    by_cases hfield : index < fields
    · obtain ⟨abs, uses, htrack⟩ := hfieldTracks index hfield
      refine ⟨abs, uses, ?_⟩
      rw [EntryTracksAt] at htrack ⊢
      change
        (fieldOutput.entries ++
          (parameterOutput.entries ++ [.recSelf (numArgs + 1)]))[index]? = _
      have hfield' : index < fieldOutput.entries.length := by
        simpa [hfieldLength] using hfield
      rw [List.getElem?_append_left hfield']
      exact htrack
    · let parameterIndex := index - fields
      have hparameterIndex : parameterIndex < numArgs := by
        dsimp only [parameterIndex]
        omega
      obtain ⟨abs, uses, htrack⟩ :=
        hparameterTracks parameterIndex
          (by simpa [paramModes] using hparameterIndex)
      refine ⟨abs, uses, ?_⟩
      rw [EntryTracksAt] at htrack ⊢
      change
        (fieldOutput.entries ++
          (parameterOutput.entries ++ [.recSelf (numArgs + 1)]))[index]? = _
      have hindexEq :
          index = fieldOutput.entries.length + parameterIndex := by
        dsimp only [parameterIndex]
        omega
      rw [hindexEq]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      have hparameter' :
          parameterIndex < parameterOutput.entries.length := by
        simpa [hparameterLength] using hparameterIndex
      rw [List.getElem?_append_left hparameter']
      simpa only [paramRemaining, hfieldLength] using htrack
  · simp [plannedRhsInput, prependVEnvEntries, frameVEnvEntries,
      hfieldLength, hparameterLength]
    omega
  · simp [RecSelfAt, plannedRhsInput, prependVEnvEntries,
      frameVEnvEntries, hfieldLength, hparameterLength]

theorem EntryTracksAt.index_lt {Γ : VEnv} {index abs : Nat}
    {uses : Uses} {remaining : Nat}
    (htrack : EntryTracksAt Γ index abs uses remaining) :
    index < Γ.entries.length := by
  rw [EntryTracksAt] at htrack
  exact (List.getElem?_eq_some_iff.mp htrack).choose

theorem EntryTracksAt.bump {Γ : VEnv} {index abs : Nat}
    {uses : Uses} {remaining : Nat}
    (htrack : EntryTracksAt Γ index abs uses remaining) :
    EntryTracksAt Γ.bump index abs uses remaining := by
  exact htrack

theorem EntryTracksAt.of_entries_eq {Γ Δ : VEnv} {index abs : Nat}
    {uses : Uses} {remaining : Nat}
    (hentries : Δ.entries = Γ.entries)
    (htrack : EntryTracksAt Γ index abs uses remaining) :
    EntryTracksAt Δ index abs uses remaining := by
  simpa [EntryTracksAt, hentries] using htrack

theorem EntryTracksAt.set_self {Γ : VEnv} {index abs remaining : Nat}
    {uses : Uses}
    (htrack : EntryTracksAt Γ index abs uses remaining) :
    EntryTracksAt
      (Γ.setEntry index
        (.slot abs remaining uses (remaining != 0)))
      index abs uses remaining := by
  rw [EntryTracksAt, VEnv.setEntry, List.getElem?_set]
  simp [htrack.index_lt]

theorem EntryTracksAt.set_self_to {Γ : VEnv}
    {index oldAbs oldRemaining : Nat} {oldUses : Uses}
    (newAbs remaining : Nat) (uses : Uses)
    (htrack : EntryTracksAt Γ index oldAbs oldUses oldRemaining) :
    EntryTracksAt
      (Γ.setEntry index
        (.slot newAbs remaining uses (remaining != 0)))
      index newAbs uses remaining := by
  rw [EntryTracksAt, VEnv.setEntry, List.getElem?_set]
  simp [htrack.index_lt]

theorem EntryTracksAt.set_ne {Γ : VEnv} {tracked changed abs : Nat}
    {uses : Uses} {remaining : Nat} {entry : VEntry}
    (hne : changed ≠ tracked)
    (htrack : EntryTracksAt Γ tracked abs uses remaining) :
    EntryTracksAt (Γ.setEntry changed entry) tracked abs uses remaining := by
  rw [EntryTracksAt, VEnv.setEntry, List.getElem?_set]
  simp [hne]
  simpa [EntryTracksAt] using htrack

theorem EntryTracksAt.slot_inj {Γ : VEnv} {index : Nat}
    {knownAbs knownRemaining trackedAbs trackedRemaining : Nat}
    {knownUses trackedUses : Uses} {knownHeld : Bool}
    (htrack : EntryTracksAt Γ index trackedAbs trackedUses
      trackedRemaining)
    (hentry : Γ.entries[index]? = some
      (.slot knownAbs knownRemaining knownUses knownHeld)) :
    knownAbs = trackedAbs ∧ knownRemaining = trackedRemaining ∧
      knownUses = trackedUses ∧
      knownHeld = (trackedRemaining != 0) := by
  rw [EntryTracksAt] at htrack
  have hsome := Option.some.inj (hentry.symm.trans htrack)
  exact VEntry.slot.inj hsome

theorem EntryTracksAt.cons {Γ : VEnv} {index abs : Nat}
    {uses : Uses} {remaining : Nat} {entry : VEntry}
    (htrack : EntryTracksAt Γ index abs uses remaining) :
    EntryTracksAt { Γ with entries := entry :: Γ.entries }
      (index + 1) abs uses remaining := by
  simpa [EntryTracksAt] using htrack

theorem EntryTracksAt.pop_succ {Γ : VEnv} {index abs : Nat}
    {uses : Uses} {remaining : Nat}
    (htrack : EntryTracksAt Γ (index + 1) abs uses remaining) :
    EntryTracksAt Γ.pop index abs uses remaining := by
  simpa [EntryTracksAt, VEnv.pop] using htrack

theorem EntryConsumption.zero (Γ : VEnv) :
    EntryConsumption Γ Γ (fun _ => 0) := by
  intro index abs uses base htrack
  simpa using htrack

theorem EntryConsumption.bump {input output : VEnv}
    {consumed : Nat → Nat}
    (hconsume : EntryConsumption input output consumed) :
    EntryConsumption input output.bump consumed := by
  intro index abs uses base htrack
  exact (hconsume index abs uses base htrack).bump

theorem EntryConsumption.comp {first middle final : VEnv}
    {left right : Nat → Nat}
    (hleft : EntryConsumption first middle left)
    (hright : EntryConsumption middle final right) :
    EntryConsumption first final (fun i => left i + right i) := by
  intro index abs uses base htrack
  have hfirst : EntryTracksAt first index abs uses
      ((base + right index) + left index) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrack
  exact hright index abs uses base
    (hleft index abs uses (base + right index) hfirst)

theorem EntryConsumption.bind_under_binder
    {input middle bodyInput bodyOutput : VEnv}
    {value body : IxIR0.Expr} {binder : VEntry}
    (hvalue : EntryConsumption input middle
      (fun index => countUses index value))
    (hbody : EntryConsumption bodyInput bodyOutput
      (fun index => countUses index body))
    (hentries : bodyInput.entries = binder :: middle.entries) :
    EntryConsumption input bodyOutput.pop
      (fun index => countUses index value + countUses (index + 1) body) := by
  intro index abs uses base htrack
  have hvalueInput : EntryTracksAt input index abs uses
      ((base + countUses (index + 1) body) + countUses index value) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrack
  have hmiddle := hvalue index abs uses
    (base + countUses (index + 1) body) hvalueInput
  have hbodyInput : EntryTracksAt bodyInput (index + 1) abs uses
      (base + countUses (index + 1) body) := by
    rw [EntryTracksAt, hentries]
    simpa [EntryTracksAt] using hmiddle
  exact EntryTracksAt.pop_succ
    (hbody (index + 1) abs uses base hbodyInput)

theorem EntryConsumption.of_entries_eq {input output : VEnv}
    (hentries : output.entries = input.entries) :
    EntryConsumption input output (fun _ => 0) := by
  intro index abs uses base htrack
  simpa [EntryTracksAt, hentries] using htrack

theorem releaseAll_entries_eq (input : VEnv) :
    ∀ values : List AVal,
      (releaseAll input values).1.entries = input.entries := by
  intro values
  induction values generalizing input with
  | nil => rfl
  | cons value rest ih =>
    cases value with
    | constA atom => exact ih input
    | slotA abs => exact ih input.bump

theorem releaseAll_consumes_zero (input : VEnv) (values : List AVal) :
    EntryConsumption input (releaseAll input values).1 (fun _ => 0) :=
  EntryConsumption.of_entries_eq (releaseAll_entries_eq input values)

theorem FirstEntryTracks.entryTracksAt
    {Γ : VEnv} {uses : Uses} {remaining : Nat}
    (htrack : FirstEntryTracks Γ uses remaining) :
    ∃ abs, EntryTracksAt Γ 0 abs uses remaining := by
  obtain ⟨abs, tail, hentries⟩ := htrack
  exact ⟨abs, by simp [EntryTracksAt, hentries]⟩

theorem EntryTracksAt.zeroReleased {Γ : VEnv} {abs : Nat}
    {uses : Uses}
    (htrack : EntryTracksAt Γ 0 abs uses 0) :
    FirstEntryReleased Γ := by
  cases hentries : Γ.entries with
  | nil => simp [EntryTracksAt, hentries] at htrack
  | cons entry tail =>
    have hentry : entry = .slot abs 0 uses false := by
      simpa [EntryTracksAt, hentries] using htrack
    subst entry
    exact ⟨abs, 0, uses, tail, hentries⟩

def countUsesExprs (index : Nat) (exprs : List IxIR0.Expr) : Nat :=
  (exprs.map (countUses index)).sum

def countUsesArgs (index : Nat)
    (args : List (IxIR0.Expr × Owned)) : Nat :=
  (args.map (fun arg => countUses index arg.1)).sum

@[simp] theorem countUsesArgs_map_shared (index : Nat)
    (exprs : List IxIR0.Expr) :
    countUsesArgs index (exprs.map (fun expr => (expr, Owned.shared))) =
      countUsesExprs index exprs := by
  induction exprs with
  | nil => rfl
  | cons expr rest ih =>
    simp [countUsesArgs, countUsesExprs, Function.comp_def]

theorem countUsesArgs_zip (index : Nat) :
    ∀ (exprs : List IxIR0.Expr) (worlds : List Owned),
      exprs.length ≤ worlds.length →
      countUsesArgs index (exprs.zip worlds) =
        countUsesExprs index exprs := by
  intro exprs
  induction exprs with
  | nil => intro worlds _; rfl
  | cons expr rest ih =>
    intro worlds hlength
    cases worlds with
    | nil => simp at hlength
    | cons world worlds =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlength
      change countUses index expr +
          countUsesArgs index (rest.zip worlds) =
        countUses index expr + countUsesExprs index rest
      rw [ih worlds hlength]

@[simp] theorem padWorlds_length (worlds : List Owned) (count : Nat) :
    (padWorlds worlds count).length = count := by
  simp [padWorlds]
  omega

theorem countUsesArgs_knownPrefix (index : Nat)
    (args : List IxIR0.Expr) (worlds : List Owned) (count : Nat) :
    countUsesArgs index ((args.take count).zip (padWorlds worlds count)) =
      countUsesExprs index (args.take count) := by
  apply countUsesArgs_zip
  simpa using Nat.min_le_left count args.length

theorem countUsesExprs_take_add_drop (index count : Nat)
    (args : List IxIR0.Expr) :
    countUsesExprs index (args.take count) +
        countUsesExprs index (args.drop count) =
      countUsesExprs index args := by
  simp only [countUsesExprs]
  rw [← List.sum_append, ← List.map_append]
  simp

def LowerEConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit} {av : AVal},
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState →
    EntryConsumption input output (fun index => countUses index expr)

theorem LowerEConsumesEntries.releasesTrackedFirst
    {src : IxIR0.Env} {fuel : Nat}
    (hconsume : LowerEConsumesEntries src fuel) (expr : IxIR0.Expr) :
    LowerEReleasesTrackedFirst src fuel expr := by
  intro input output world uses state finalState emit av htrack hrun
  obtain ⟨abs, hat⟩ := htrack.entryTracksAt
  apply EntryTracksAt.zeroReleased (abs := abs)
  exact hconsume hrun 0 abs uses 0 (by simpa using hat)

theorem lowerE_var_consumesEntries
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {varIndex : Nat} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world (.var varIndex)).run state =
      .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.var varIndex)) := by
  have hssNe : (Owned.shared != Owned.shared) = false := by decide
  have huuNe : (Owned.unique != Owned.unique) = false := by decide
  have hsuNe : (Owned.shared != Owned.unique) = true := by decide
  have husNe : (Owned.unique != Owned.shared) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  intro index abs uses base htrack
  by_cases heq : varIndex = index
  · subst index
    cases base with
    | zero =>
      have hentry : input.entries[varIndex]? =
          some (.slot abs 1 uses true) := by
        simpa [EntryTracksAt, countUses] using htrack
      by_cases hworld : worldOfUses uses = world
      · subst world
        have hsame :
            (worldOfUses uses != worldOfUses uses) = false := by
          cases uses <;> decide
        have hpure :
            (input.setEntry varIndex (.slot abs 0 uses false),
              (_root_.id : Emit), AVal.slotA abs) =
                (output, emit, av) ∧ state = finalState := by
          simpa [lowerE, hentry, hsame] using hrun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        apply EntryTracksAt.set_self_to abs 0 uses
        exact htrack
      · cases uses <;> cases world
        all_goals
          try { exact (hworld (by rfl)).elim }
        all_goals
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hentry, worldOfUses, hssNe, huuNe, hsuNe,
              husNe, hsuEq, huuEq] using hrun)).elim
    | succ base =>
      have hentry : input.entries[varIndex]? =
          some (.slot abs (base + 2) uses true) := by
        simpa [EntryTracksAt, countUses, Nat.add_assoc] using htrack
      by_cases hworld : worldOfUses uses = world
      · subst world
        have hsame :
            (worldOfUses uses != worldOfUses uses) = false := by
          cases uses <;> decide
        cases uses with
        | erased =>
          have heqUnique :
              (Owned.shared == Owned.unique) = false := by decide
          have hpure :
              let changed := input.setEntry varIndex
                (.slot abs (base + 1) .erased true)
              (changed.bump,
                emitOp (.dup (.var (changed.rel abs))),
                AVal.slotA changed.depth) = (output, emit, av) ∧
                state = finalState := by
            simpa [lowerE, hentry, worldOfUses, hsame, heqUnique,
              hssNe] using hrun
          dsimp only at hpure
          obtain ⟨hvalue, hstate⟩ := hpure
          cases hvalue
          subst finalState
          apply EntryTracksAt.bump
          apply EntryTracksAt.set_self_to abs (base + 1) .erased
          exact htrack
        | linear =>
          have heqUnique :
              (Owned.unique == Owned.unique) = true := by decide
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hentry, worldOfUses, hsame, heqUnique,
              huuNe] using hrun)).elim
        | affine =>
          have heqUnique :
              (Owned.unique == Owned.unique) = true := by decide
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hentry, worldOfUses, hsame, heqUnique,
              huuNe] using hrun)).elim
        | many =>
          have heqUnique :
              (Owned.shared == Owned.unique) = false := by decide
          have hpure :
              let changed := input.setEntry varIndex
                (.slot abs (base + 1) .many true)
              (changed.bump,
                emitOp (.dup (.var (changed.rel abs))),
                AVal.slotA changed.depth) = (output, emit, av) ∧
                state = finalState := by
            simpa [lowerE, hentry, worldOfUses, hsame, heqUnique,
              hssNe] using hrun
          dsimp only at hpure
          obtain ⟨hvalue, hstate⟩ := hpure
          cases hvalue
          subst finalState
          apply EntryTracksAt.bump
          apply EntryTracksAt.set_self_to abs (base + 1) .many
          exact htrack
      · cases uses <;> cases world
        all_goals
          try { exact (hworld (by rfl)).elim }
        all_goals
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hentry, worldOfUses, hssNe, huuNe, hsuNe,
              husNe, hsuEq, huuEq] using hrun)).elim
  · have hcount : countUses index (.var varIndex) = 0 := by
      simp [countUses, heq]
    have htrack' : EntryTracksAt input index abs uses base := by
      simpa [hcount] using htrack
    cases hentry : input.entries[varIndex]? with
    | none =>
      exact (trackedThrowRun_not_ok (by
        simpa [lowerE, hentry] using hrun)).elim
    | some entry =>
      cases entry with
      | recSelf arity =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerE, hentry] using hrun)).elim
      | slot variableAbs remaining variableUses held =>
        cases held with
        | false =>
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hentry] using hrun)).elim
        | true =>
          by_cases hworld : worldOfUses variableUses = world
          · subst world
            have hsame :
                (worldOfUses variableUses != worldOfUses variableUses) =
                  false := by
              cases variableUses <;> decide
            cases remaining with
            | zero =>
              exact (trackedThrowRun_not_ok (by
                simpa [lowerE, hentry, hsame] using hrun)).elim
            | succ remaining =>
              cases remaining with
              | zero =>
                have hpure :
                    (input.setEntry varIndex
                        (.slot variableAbs 0 variableUses false),
                      (_root_.id : Emit), AVal.slotA variableAbs) =
                        (output, emit, av) ∧ state = finalState := by
                  simpa [lowerE, hentry, hsame] using hrun
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact EntryTracksAt.set_ne heq htrack'
              | succ remaining =>
                cases variableUses with
                | erased =>
                  have heqUnique :
                      (Owned.shared == Owned.unique) = false := by decide
                  have hpure :
                      let changed := input.setEntry varIndex
                        (.slot variableAbs (Nat.succ remaining) .erased true)
                      (changed.bump,
                        emitOp (.dup (.var (changed.rel variableAbs))),
                        AVal.slotA changed.depth) = (output, emit, av) ∧
                        state = finalState := by
                    simpa [lowerE, hentry, worldOfUses, hsame,
                      heqUnique, hssNe] using hrun
                  dsimp only at hpure
                  obtain ⟨hvalue, hstate⟩ := hpure
                  cases hvalue
                  subst finalState
                  exact (EntryTracksAt.set_ne heq htrack').bump
                | linear =>
                  have heqUnique :
                      (Owned.unique == Owned.unique) = true := by decide
                  exact (trackedThrowRun_not_ok (by
                    simpa [lowerE, hentry, worldOfUses, hsame, heqUnique,
                      huuNe] using hrun)).elim
                | affine =>
                  have heqUnique :
                      (Owned.unique == Owned.unique) = true := by decide
                  exact (trackedThrowRun_not_ok (by
                    simpa [lowerE, hentry, worldOfUses, hsame, heqUnique,
                      huuNe] using hrun)).elim
                | many =>
                  have heqUnique :
                      (Owned.shared == Owned.unique) = false := by decide
                  have hpure :
                      let changed := input.setEntry varIndex
                        (.slot variableAbs (Nat.succ remaining) .many true)
                      (changed.bump,
                        emitOp (.dup (.var (changed.rel variableAbs))),
                        AVal.slotA changed.depth) = (output, emit, av) ∧
                        state = finalState := by
                    simpa [lowerE, hentry, worldOfUses, hsame,
                      heqUnique, hssNe] using hrun
                  dsimp only at hpure
                  obtain ⟨hvalue, hstate⟩ := hpure
                  cases hvalue
                  subst finalState
                  exact (EntryTracksAt.set_ne heq htrack').bump
          · have hdiff : (worldOfUses variableUses != world) = true := by
              cases variableUses <;> cases world <;>
                simp_all [worldOfUses] <;> decide
            cases variableUses <;> cases world
            all_goals
              try { exact (hworld (by rfl)).elim }
            all_goals
              exact (trackedThrowRun_not_ok (by
                simpa [lowerE, hentry, worldOfUses, hdiff, hssNe, huuNe,
                  hsuNe, husNe, hsuEq, huuEq] using hrun)).elim

def LowerBorrowConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit}
      {av : AVal} {release : Bool},
    (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, av, release) finalState →
    EntryConsumption input output (fun index => countUses index expr)

def LowerSpineConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {head : IxIR0.Expr}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {av : AVal},
    (lowerSpine src fuel input world head args).run state =
      .ok (output, emit, av) finalState →
    EntryConsumption input output
      (fun index => countUses index head + countUsesExprs index args)

def LowerArgsConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {args : List (IxIR0.Expr × Owned)}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {avs : List AVal},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, avs) finalState →
    EntryConsumption input output (fun index => countUsesArgs index args)

def KnownCallConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {build : Array Atom → Op} {count : Nat}
      {argWorlds : List Owned} {resultWorld : Owned}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {av : AVal},
    (knownCall src fuel input build count argWorlds resultWorld args).run
      state = .ok (output, emit, av) finalState →
    EntryConsumption input output (fun index => countUsesExprs index args)

def ApplyRestConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {resultWorld : Owned} {pre : Emit}
      {function : AVal} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {av : AVal},
    (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, av) finalState →
    EntryConsumption input output (fun index => countUsesExprs index args)

def LowerLamConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {av : AVal},
    (lowerLam src fuel input expr).run state =
      .ok (output, emit, av) finalState →
    EntryConsumption input output (fun index => countUses index expr)

structure LowerConsumesEntries (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEConsumesEntries src fuel
  borrow : LowerBorrowConsumesEntries src fuel
  spine : LowerSpineConsumesEntries src fuel
  knownCall : KnownCallConsumesEntries src fuel
  args : LowerArgsConsumesEntries src fuel
  applyRest : ApplyRestConsumesEntries src fuel
  lam : LowerLamConsumesEntries src fuel

theorem lowerConsumesEntries_zero (src : IxIR0.Env) :
    LowerConsumesEntries src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr state finalState output emit av hrun
    exact (trackedThrowRun_not_ok (by simpa [lowerE] using hrun)).elim
  · intro input expr state finalState output emit av release hrun
    exact (trackedThrowRun_not_ok (by
      simpa [lowerBorrow] using hrun)).elim
  · intro input world head args state finalState output emit av hrun
    exact (trackedThrowRun_not_ok (by
      simpa [lowerSpine] using hrun)).elim
  · intro input build count argWorlds resultWorld args state finalState
      output emit av hrun
    exact (trackedThrowRun_not_ok (by
      simpa [knownCall] using hrun)).elim
  · intro input args state finalState output emit avs hrun
    exact (trackedThrowRun_not_ok (by
      simpa [lowerArgs] using hrun)).elim
  · intro input resultWorld pre function args state finalState output emit av
      hrun
    exact (trackedThrowRun_not_ok (by
      simpa [applyRest] using hrun)).elim
  · intro input expr state finalState output emit av hrun
    exact (trackedThrowRun_not_ok (by simpa [lowerLam] using hrun)).elim

theorem lowerArgsConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    (hargs : LowerArgsConsumesEntries src fuel) :
    LowerArgsConsumesEntries src (fuel + 1) := by
  intro input args state finalState output emit avs hrun
  cases args with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, avs) ∧
          state = finalState := by
      simpa [lowerArgs] using hrun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    simpa [countUsesArgs] using EntryConsumption.zero input
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      trackedBindRun_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, av⟩
    obtain ⟨tailResult, tailState, htailRun, hpureRun⟩ :=
      trackedBindRun_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, tailEmit, tailValues⟩
    have hpure :
        (actualOutput, headEmit ∘ tailEmit, av :: tailValues) =
            (output, emit, avs) ∧ tailState = finalState := by
      simpa using hpureRun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have hcomposed := (hexpr hheadRun).comp (hargs htailRun)
    simpa [countUsesArgs] using hcomposed

theorem applyRestConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsConsumesEntries src fuel) :
    ApplyRestConsumesEntries src (fuel + 1) := by
  intro input resultWorld pre function args state finalState output emit av
    hrun
  cases function with
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest] at hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        trackedBindRun_ok_inv hrun
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hpure :
          ((releaseAll middle values).1,
            pre ∘ argsEmit ∘ (releaseAll middle values).2,
            AVal.constA .erased) = (output, emit, av) ∧
            argsState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      have hcomposed := (hargs hargsRun).comp
        (releaseAll_consumes_zero middle values)
      simpa using hcomposed
    | var functionIndex =>
      simp only [applyRest] at hrun
      obtain ⟨unitValue, checkedState, _, hafterCheck⟩ :=
        trackedBindRun_ok_inv hrun
      cases unitValue
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        trackedBindRun_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hpure :
          (middle.bump,
            pre ∘ argsEmit ∘ emitOp (.apply
              ((AVal.constA (.var functionIndex)).toAtom middle)
              (values.map (·.toAtom middle)).toArray),
            AVal.slotA middle.depth) = (output, emit, av) ∧
            argsState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      simpa using (hargs hargsRun).bump
    | lit literal =>
      simp only [applyRest] at hrun
      obtain ⟨unitValue, checkedState, _, hafterCheck⟩ :=
        trackedBindRun_ok_inv hrun
      cases unitValue
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        trackedBindRun_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hpure :
          (middle.bump,
            pre ∘ argsEmit ∘ emitOp (.apply
              ((AVal.constA (.lit literal)).toAtom middle)
              (values.map (·.toAtom middle)).toArray),
            AVal.slotA middle.depth) = (output, emit, av) ∧
            argsState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      simpa using (hargs hargsRun).bump
  | slotA functionAbs =>
    simp only [applyRest] at hrun
    obtain ⟨unitValue, checkedState, _, hafterCheck⟩ :=
      trackedBindRun_ok_inv hrun
    cases unitValue
    obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
      trackedBindRun_ok_inv hafterCheck
    rcases argsResult with ⟨middle, argsEmit, values⟩
    have hpure :
        (middle.bump,
          pre ∘ argsEmit ∘ emitOp (.apply
            ((AVal.slotA functionAbs).toAtom middle)
            (values.map (·.toAtom middle)).toArray),
          AVal.slotA middle.depth) = (output, emit, av) ∧
          argsState = finalState := by
      simpa using hpureRun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    simpa using (hargs hargsRun).bump

theorem knownCallConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsConsumesEntries src fuel)
    (hrest : ApplyRestConsumesEntries src fuel) :
    KnownCallConsumesEntries src (fuel + 1) := by
  intro input build count argWorlds resultWorld args state finalState output
    emit av hrun
  simp only [knownCall] at hrun
  obtain ⟨argsResult, argsState, hargsRun, hafterArgs⟩ :=
    trackedBindRun_ok_inv hrun
  rcases argsResult with ⟨middle, argsEmit, values⟩
  have hprefix := hargs hargsRun
  have hprefix' : EntryConsumption input middle
      (fun index => countUsesExprs index (args.take count)) := by
    simpa only [countUsesArgs_knownPrefix] using hprefix
  by_cases hterminal : args.length ≤ count
  · have hpure :
        (middle.bump,
          argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray),
          AVal.slotA middle.depth) = (output, emit, av) ∧
          argsState = finalState := by
      simpa [hterminal] using hafterArgs
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have htake : args.take count = args :=
      List.take_of_length_le hterminal
    simpa [htake] using hprefix'.bump
  · have hrestRun :
        (applyRest src fuel middle.bump resultWorld
          (argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray))
          (.slotA middle.depth) (args.drop count)).run argsState =
            .ok (output, emit, av) finalState := by
      simpa [hterminal] using hafterArgs
    have hcomposed := hprefix'.bump.comp (hrest hrestRun)
    simpa [countUsesArgs_knownPrefix,
      countUsesExprs_take_add_drop] using hcomposed

theorem lowerSpine_dynamic_consumesEntries
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    (hrest : ApplyRestConsumesEntries src fuel)
    {input output : VEnv} {world : Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (do
      let (middle, headEmit, function) ←
        lowerE src fuel input .shared head
      applyRest src fuel middle world headEmit function args).run state =
        .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index head + countUsesExprs index args) := by
  obtain ⟨headResult, middleState, hheadRun, hrestRun⟩ :=
    trackedBindRun_ok_inv hrun
  rcases headResult with ⟨middle, headEmit, function⟩
  exact (hexpr hheadRun).comp (hrest hrestRun)

theorem lowerSpine_var_consumesEntries
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    (hknown : KnownCallConsumesEntries src fuel)
    (hrest : ApplyRestConsumesEntries src fuel)
    {input output : VEnv} {world : Owned} {varIndex : Nat}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (lowerSpine src (fuel + 1) input world (.var varIndex)
      args).run state = .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.var varIndex) +
        countUsesExprs index args) := by
  simp only [lowerSpine] at hrun
  cases hentry : input.entries[varIndex]? with
  | none =>
    rw [hentry] at hrun
    simp only at hrun
    exact lowerSpine_dynamic_consumesEntries hexpr hrest hrun
  | some entry =>
    cases entry with
    | slot abs remaining uses held =>
      rw [hentry] at hrun
      simp only at hrun
      exact lowerSpine_dynamic_consumesEntries hexpr hrest hrun
    | recSelf arity =>
      rw [hentry] at hrun
      simp only at hrun
      by_cases hunder : args.length < arity
      · rw [if_pos hunder] at hrun
        exact (trackedThrowRun_not_ok hrun).elim
      · rw [if_neg hunder] at hrun
        obtain ⟨unitValue, checkedState, _, hknownRun⟩ :=
          trackedBindRun_ok_inv hrun
        cases unitValue
        have hargsConsume := hknown hknownRun
        intro index trackedAbs trackedUses base htrack
        have hne : varIndex ≠ index := by
          intro heq
          subst index
          rw [EntryTracksAt] at htrack
          rw [hentry] at htrack
          cases htrack
        have hzero : countUses index (.var varIndex) = 0 := by
          simp [countUses, hne]
        exact hargsConsume index trackedAbs trackedUses base
          (by simpa [hzero] using htrack)

theorem lowerSpine_ref_consumesEntries
    {src : IxIR0.Env} {fuel : Nat}
    (hknown : KnownCallConsumesEntries src fuel)
    {input output : VEnv} {world : Owned} {address : Ixon.Address}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (lowerSpine src (fuel + 1) input world (.ref address)
      args).run state = .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.ref address) +
        countUsesExprs index args) := by
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  simp only [lowerSpine] at hrun
  cases hsource : src address with
  | none =>
    rw [hsource] at hrun
    exact (trackedThrowRun_not_ok hrun).elim
  | some decl =>
    rw [hsource] at hrun
    cases decl with
    | defn result body =>
      simp only at hrun
      by_cases hunder : args.length < lamArity body
      · rw [if_pos hunder] at hrun
        cases world with
        | unique => exact (trackedThrowRun_not_ok hrun).elim
        | shared =>
          cases result with
          | unique => exact (trackedThrowRun_not_ok hrun).elim
          | shared =>
            cases hp : papSafe body with
            | false =>
              exact (trackedThrowRun_not_ok (by
                simpa [hp, hsuEq] using hrun)).elim
            | true =>
              have hknownRun :
                  (knownCall src fuel input (.papp address ·) args.length
                    (List.replicate args.length .shared) .shared args).run
                    state = .ok (output, emit, av) finalState := by
                simpa [hp, hsuEq] using hrun
              simpa [countUses] using hknown hknownRun
      · rw [if_neg hunder] at hrun
        obtain ⟨unitValue, checkedState, _, hknownRun⟩ :=
          trackedBindRun_ok_inv hrun
        cases unitValue
        simpa [countUses] using hknown hknownRun
    | ctor tag arity =>
      simp only at hrun
      by_cases hunder : args.length < arity
      · rw [if_pos hunder] at hrun
        cases world with
        | unique => exact (trackedThrowRun_not_ok hrun).elim
        | shared =>
          obtain ⟨wrapper, wrapperState, _, hknownRun⟩ :=
            trackedBindRun_ok_inv hrun
          simpa [countUses] using hknown hknownRun
      · rw [if_neg hunder] at hrun
        simpa [countUses] using hknown hrun
    | recursor numArgs natLit rules =>
      simp only at hrun
      by_cases hunder : args.length < numArgs + 1
      · rw [if_pos hunder] at hrun
        cases world with
        | unique => exact (trackedThrowRun_not_ok hrun).elim
        | shared => simpa [countUses] using hknown hrun
      · rw [if_neg hunder] at hrun
        obtain ⟨unitValue, checkedState, _, hknownRun⟩ :=
          trackedBindRun_ok_inv hrun
        cases unitValue
        simpa [countUses] using hknown hknownRun
    | extern arity =>
      simp only at hrun
      by_cases hunder : args.length < arity
      · rw [if_pos hunder] at hrun
        cases world with
        | unique => exact (trackedThrowRun_not_ok hrun).elim
        | shared => simpa [countUses] using hknown hrun
      · rw [if_neg hunder] at hrun
        simpa [countUses] using hknown hrun

theorem lowerSpineConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    (hspine : LowerSpineConsumesEntries src fuel)
    (hknown : KnownCallConsumesEntries src fuel)
    (hrest : ApplyRestConsumesEntries src fuel) :
    LowerSpineConsumesEntries src (fuel + 1) := by
  intro input world head args state finalState output emit av hrun
  cases head with
  | app function argument =>
    have hrecursive := hspine (by simpa [lowerSpine] using hrun)
    simpa [countUses, countUsesExprs, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hrecursive
  | erased =>
    have happly := hrest (by simpa [lowerSpine] using hrun)
    simpa [countUses] using happly
  | var index =>
    exact lowerSpine_var_consumesEntries hexpr hknown hrest hrun
  | ref address =>
    exact lowerSpine_ref_consumesEntries hknown hrun
  | lam uses body =>
    exact lowerSpine_dynamic_consumesEntries hexpr hrest
      (by simpa [lowerSpine] using hrun)
  | letE uses value body =>
    exact lowerSpine_dynamic_consumesEntries hexpr hrest
      (by simpa [lowerSpine] using hrun)
  | proj index source =>
    exact lowerSpine_dynamic_consumesEntries hexpr hrest
      (by simpa [lowerSpine] using hrun)
  | lit literal =>
    exact lowerSpine_dynamic_consumesEntries hexpr hrest
      (by simpa [lowerSpine] using hrun)

theorem lowerBorrow_var_consumesEntries
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {varIndex : Nat} {state finalState : LowSt}
    {emit : Emit} {av : AVal} {release : Bool}
    (hrun : (lowerBorrow src (fuel + 1) input (.var varIndex)).run state =
      .ok (output, emit, av, release) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.var varIndex)) := by
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  intro index abs uses base htrack
  by_cases heq : varIndex = index
  · subst index
    cases base with
    | zero =>
      have hentry : input.entries[varIndex]? =
          some (.slot abs 1 uses true) := by
        simpa [EntryTracksAt, countUses] using htrack
      cases uses with
      | erased =>
        have hpure :
            (input.setEntry varIndex (.slot abs 0 .erased false),
              (_root_.id : Emit), AVal.slotA abs, true) =
                (output, emit, av, release) ∧ state = finalState := by
          simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        apply EntryTracksAt.set_self_to abs 0 .erased
        exact htrack
      | linear =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerBorrow, hentry, worldOfUses, huuEq]
            using hrun)).elim
      | affine =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerBorrow, hentry, worldOfUses, huuEq]
            using hrun)).elim
      | many =>
        have hpure :
            (input.setEntry varIndex (.slot abs 0 .many false),
              (_root_.id : Emit), AVal.slotA abs, true) =
                (output, emit, av, release) ∧ state = finalState := by
          simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        apply EntryTracksAt.set_self_to abs 0 .many
        exact htrack
    | succ base =>
      have hentry : input.entries[varIndex]? =
          some (.slot abs (base + 2) uses true) := by
        simpa [EntryTracksAt, countUses, Nat.add_assoc] using htrack
      cases uses with
      | erased =>
        have hpure :
            (input.setEntry varIndex
                (.slot abs (base + 1) .erased true),
              (_root_.id : Emit), AVal.slotA abs, false) =
                (output, emit, av, release) ∧ state = finalState := by
          simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        apply EntryTracksAt.set_self_to abs (base + 1) .erased
        exact htrack
      | linear =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerBorrow, hentry, worldOfUses, huuEq]
            using hrun)).elim
      | affine =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerBorrow, hentry, worldOfUses, huuEq]
            using hrun)).elim
      | many =>
        have hpure :
            (input.setEntry varIndex
                (.slot abs (base + 1) .many true),
              (_root_.id : Emit), AVal.slotA abs, false) =
                (output, emit, av, release) ∧ state = finalState := by
          simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        apply EntryTracksAt.set_self_to abs (base + 1) .many
        exact htrack
  · have hcount : countUses index (.var varIndex) = 0 := by
      simp [countUses, heq]
    have htrack' : EntryTracksAt input index abs uses base := by
      simpa [hcount] using htrack
    cases hentry : input.entries[varIndex]? with
    | none =>
      exact (trackedThrowRun_not_ok (by
        simpa [lowerBorrow, hentry] using hrun)).elim
    | some entry =>
      cases entry with
      | recSelf arity =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerBorrow, hentry] using hrun)).elim
      | slot variableAbs remaining variableUses held =>
        cases held with
        | false =>
          exact (trackedThrowRun_not_ok (by
            simpa [lowerBorrow, hentry] using hrun)).elim
        | true =>
          cases variableUses with
          | linear =>
            exact (trackedThrowRun_not_ok (by
              simpa [lowerBorrow, hentry, worldOfUses, huuEq]
                using hrun)).elim
          | affine =>
            exact (trackedThrowRun_not_ok (by
              simpa [lowerBorrow, hentry, worldOfUses, huuEq]
                using hrun)).elim
          | erased =>
            cases remaining with
            | zero =>
              exact (trackedThrowRun_not_ok (by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                  using hrun)).elim
            | succ remaining =>
              cases remaining with
              | zero =>
                have hpure :
                    (input.setEntry varIndex
                        (.slot variableAbs 0 .erased false),
                      (_root_.id : Emit), AVal.slotA variableAbs, true) =
                        (output, emit, av, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                    using hrun
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact EntryTracksAt.set_ne heq htrack'
              | succ remaining =>
                have hpure :
                    (input.setEntry varIndex
                        (.slot variableAbs (remaining + 1) .erased true),
                      (_root_.id : Emit), AVal.slotA variableAbs, false) =
                        (output, emit, av, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                    using hrun
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact EntryTracksAt.set_ne heq htrack'
          | many =>
            cases remaining with
            | zero =>
              exact (trackedThrowRun_not_ok (by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                  using hrun)).elim
            | succ remaining =>
              cases remaining with
              | zero =>
                have hpure :
                    (input.setEntry varIndex
                        (.slot variableAbs 0 .many false),
                      (_root_.id : Emit), AVal.slotA variableAbs, true) =
                        (output, emit, av, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                    using hrun
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact EntryTracksAt.set_ne heq htrack'
              | succ remaining =>
                have hpure :
                    (input.setEntry varIndex
                        (.slot variableAbs (remaining + 1) .many true),
                      (_root_.id : Emit), AVal.slotA variableAbs, false) =
                        (output, emit, av, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                    using hrun
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact EntryTracksAt.set_ne heq htrack'

theorem lowerBorrow_dynamic_consumesEntries
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    {release : Bool}
    (hshape : DynamicBorrowHead expr)
    (hrun : (lowerBorrow src (fuel + 1) input expr).run state =
      .ok (output, emit, av, release) finalState) :
    EntryConsumption input output (fun index => countUses index expr) := by
  cases hshape <;> simp only [lowerBorrow] at hrun
  all_goals
    obtain ⟨exprResult, exprState, hexprRun, hpureRun⟩ :=
      trackedBindRun_ok_inv hrun
    rcases exprResult with ⟨actualOutput, actualEmit, value⟩
    simp at hpureRun
    have houtput : actualOutput = output := hpureRun.1.1
    subst output
    exact hexpr hexprRun

theorem lowerBorrowConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel) :
    LowerBorrowConsumesEntries src (fuel + 1) := by
  intro input expr state finalState output emit av release hrun
  cases expr with
  | var index => exact lowerBorrow_var_consumesEntries hrun
  | ref address =>
    exact lowerBorrow_dynamic_consumesEntries hexpr (.ref address) hrun
  | app function argument =>
    exact lowerBorrow_dynamic_consumesEntries hexpr
      (.app function argument) hrun
  | lam uses body =>
    exact lowerBorrow_dynamic_consumesEntries hexpr (.lam uses body) hrun
  | letE uses value body =>
    exact lowerBorrow_dynamic_consumesEntries hexpr
      (.letE uses value body) hrun
  | proj index source =>
    exact lowerBorrow_dynamic_consumesEntries hexpr
      (.proj index source) hrun
  | lit literal =>
    exact lowerBorrow_dynamic_consumesEntries hexpr (.lit literal) hrun
  | erased =>
    exact lowerBorrow_dynamic_consumesEntries hexpr .erased hrun

def captureUseCount (expr : IxIR0.Expr) (captures : List Nat)
    (index : Nat) : Nat :=
  captures.count index * countUses index expr

@[simp] theorem captureUseCount_nil (expr : IxIR0.Expr) :
    captureUseCount expr [] = fun _ => 0 := by
  funext index
  simp [captureUseCount]

theorem captureUseCount_cons (expr : IxIR0.Expr) (captured : Nat)
    (rest : List Nat) :
    captureUseCount expr (captured :: rest) = fun index =>
      (if captured = index then countUses index expr else 0) +
        captureUseCount expr rest index := by
  funext index
  by_cases heq : captured = index
  · subst index
    simp [captureUseCount, Nat.add_mul, Nat.add_comm]
  · have hne : index ≠ captured := Ne.symm heq
    simp [captureUseCount, heq]

theorem lowerCapture_consumesEntries
    {expr : IxIR0.Expr} {input output : VEnv} {captured : Nat}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hrun : (lowerCapture expr input captured).run state =
      .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => if captured = index then countUses index expr else 0) := by
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  simp only [lowerCapture] at hrun
  cases hentry : input.entries[captured]? with
  | none =>
    rw [hentry] at hrun
    exact (trackedThrowRun_not_ok hrun).elim
  | some entry =>
    rw [hentry] at hrun
    cases entry with
    | recSelf arity =>
      exact (trackedThrowRun_not_ok hrun).elim
    | slot capturedAbs remaining capturedUses held =>
      cases held with
      | false =>
        exact (trackedThrowRun_not_ok hrun).elim
      | true =>
        cases capturedUses with
        | linear =>
          exact (trackedThrowRun_not_ok (by
            simpa [worldOfUses, huuEq] using hrun)).elim
        | affine =>
          exact (trackedThrowRun_not_ok (by
            simpa [worldOfUses, huuEq] using hrun)).elim
        | erased =>
          by_cases hmore : remaining > countUses captured expr
          · have hpure :
                let changed := input.setEntry captured
                  (.slot capturedAbs
                    (remaining - countUses captured expr) .erased true)
                (changed.bump,
                  emitOp (.dup (.var (changed.rel capturedAbs))),
                  AVal.slotA changed.depth) = (output, emit, av) ∧
                  state = finalState := by
              simpa [worldOfUses, hsuEq, hmore] using hrun
            dsimp only at hpure
            obtain ⟨hvalue, hstate⟩ := hpure
            cases hvalue
            subst finalState
            intro index abs uses base htrack
            by_cases heq : captured = index
            · subst index
              obtain ⟨rfl, hremaining, rfl, _⟩ :=
                htrack.slot_inj hentry
              simp at hremaining
              have hbase : 0 < base := by omega
              have hbne : (base != 0) = true := by
                simp [Nat.ne_of_gt hbase]
              have hcanonical := EntryTracksAt.set_self_to capturedAbs
                base .erased htrack
              apply EntryTracksAt.bump
              simpa [hremaining, Nat.add_sub_cancel_right,
                Nat.ne_of_gt hbase, hbne] using hcanonical
            · have hzero :
                  (if captured = index then countUses index expr else 0) =
                    0 := by simp [heq]
              have htrack' :
                  EntryTracksAt input index abs uses base := by
                simpa [hzero] using htrack
              exact (EntryTracksAt.set_ne heq htrack').bump
          · by_cases hequal : remaining = countUses captured expr
            · have hpure :
                  (input.setEntry captured
                      (.slot capturedAbs 0 .erased false),
                    (_root_.id : Emit), AVal.slotA capturedAbs) =
                      (output, emit, av) ∧ state = finalState := by
                simpa [worldOfUses, hsuEq, hmore, hequal] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              intro index abs uses base htrack
              by_cases heq : captured = index
              · subst index
                obtain ⟨rfl, hremaining, rfl, _⟩ :=
                  htrack.slot_inj hentry
                simp at hremaining
                have hbase : base = 0 := by omega
                subst base
                apply EntryTracksAt.set_self_to capturedAbs 0 .erased
                exact htrack
              · have hzero :
                    (if captured = index then countUses index expr else 0) =
                      0 := by simp [heq]
                have htrack' :
                    EntryTracksAt input index abs uses base := by
                  simpa [hzero] using htrack
                exact EntryTracksAt.set_ne heq htrack'
            · exact (trackedThrowRun_not_ok (by
                simpa [worldOfUses, hsuEq, hmore, hequal]
                  using hrun)).elim
        | many =>
          by_cases hmore : remaining > countUses captured expr
          · have hpure :
                let changed := input.setEntry captured
                  (.slot capturedAbs
                    (remaining - countUses captured expr) .many true)
                (changed.bump,
                  emitOp (.dup (.var (changed.rel capturedAbs))),
                  AVal.slotA changed.depth) = (output, emit, av) ∧
                  state = finalState := by
              simpa [worldOfUses, hsuEq, hmore] using hrun
            dsimp only at hpure
            obtain ⟨hvalue, hstate⟩ := hpure
            cases hvalue
            subst finalState
            intro index abs uses base htrack
            by_cases heq : captured = index
            · subst index
              obtain ⟨rfl, hremaining, rfl, _⟩ :=
                htrack.slot_inj hentry
              simp at hremaining
              have hbase : 0 < base := by omega
              have hbne : (base != 0) = true := by
                simp [Nat.ne_of_gt hbase]
              have hcanonical := EntryTracksAt.set_self_to capturedAbs
                base .many htrack
              apply EntryTracksAt.bump
              simpa [hremaining, Nat.add_sub_cancel_right,
                Nat.ne_of_gt hbase, hbne] using hcanonical
            · have hzero :
                  (if captured = index then countUses index expr else 0) =
                    0 := by simp [heq]
              have htrack' :
                  EntryTracksAt input index abs uses base := by
                simpa [hzero] using htrack
              exact (EntryTracksAt.set_ne heq htrack').bump
          · by_cases hequal : remaining = countUses captured expr
            · have hpure :
                  (input.setEntry captured
                      (.slot capturedAbs 0 .many false),
                    (_root_.id : Emit), AVal.slotA capturedAbs) =
                      (output, emit, av) ∧ state = finalState := by
                simpa [worldOfUses, hsuEq, hmore, hequal] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              intro index abs uses base htrack
              by_cases heq : captured = index
              · subst index
                obtain ⟨rfl, hremaining, rfl, _⟩ :=
                  htrack.slot_inj hentry
                simp at hremaining
                have hbase : base = 0 := by omega
                subst base
                apply EntryTracksAt.set_self_to capturedAbs 0 .many
                exact htrack
              · have hzero :
                    (if captured = index then countUses index expr else 0) =
                      0 := by simp [heq]
                have htrack' :
                    EntryTracksAt input index abs uses base := by
                  simpa [hzero] using htrack
                exact EntryTracksAt.set_ne heq htrack'
            · exact (trackedThrowRun_not_ok (by
                simpa [worldOfUses, hsuEq, hmore, hequal]
                  using hrun)).elim

theorem lowerCaptures_consumesEntries (expr : IxIR0.Expr) :
    ∀ {captures : List Nat} {input output : VEnv}
      {state finalState : LowSt} {emit : Emit} {values : List AVal},
    (lowerCaptures expr input captures).run state =
      .ok (output, emit, values) finalState →
    EntryConsumption input output (captureUseCount expr captures) := by
  intro captures
  induction captures with
  | nil =>
    intro input output state finalState emit values hrun
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerCaptures] using hrun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    rw [captureUseCount_nil]
    exact EntryConsumption.zero input
  | cons captured rest ih =>
    intro input output state finalState emit values hrun
    simp only [lowerCaptures] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      trackedBindRun_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hpureRun⟩ :=
      trackedBindRun_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, tailEmit, tailValues⟩
    have hpure :
        (actualOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
            (output, emit, values) ∧ tailState = finalState := by
      simpa using hpureRun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have hcomposed :=
      (lowerCapture_consumesEntries hheadRun).comp (ih htailRun)
    rw [captureUseCount_cons]
    exact hcomposed

theorem captureUseCount_selected_at (expr : IxIR0.Expr) (length index : Nat)
    (hindex : index < length) :
    captureUseCount expr
        ((List.range length).filter (fun i => countUses i expr > 0))
        index =
      countUses index expr := by
  by_cases hzero : countUses index expr = 0
  · simp [captureUseCount, hzero]
  · have hpositive : (countUses index expr > 0 : Bool) = true := by
      simp
      omega
    have hcount :
        List.count index
            ((List.range length).filter
              (fun i => countUses i expr > 0)) =
          List.count index (List.range length) :=
      List.count_filter (p := fun i => countUses i expr > 0)
        (a := index) (l := List.range length) hpositive
    rw [captureUseCount, hcount, List.count_range]
    simp [hindex]

theorem lowerCaptures_selected_consumesEntries
    {expr : IxIR0.Expr} {input output : VEnv}
    {state finalState : LowSt} {emit : Emit} {values : List AVal}
    (hrun : (lowerCaptures expr input
      ((List.range input.entries.length).filter
        (fun i => countUses i expr > 0))).run state =
        .ok (output, emit, values) finalState) :
    EntryConsumption input output (fun index => countUses index expr) := by
  have hcaptures := lowerCaptures_consumesEntries expr hrun
  intro index abs uses base htrack
  have hcount := captureUseCount_selected_at expr input.entries.length
    index htrack.index_lt
  exact hcaptures index abs uses base (by simpa [hcount] using htrack)

theorem lowerLamConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat} :
    LowerLamConsumesEntries src (fuel + 1) := by
  intro input expr state finalState output emit av hrun
  cases hp : papSafe expr with
  | false =>
    simp [lowerLam, hp] at hrun
  | true =>
    simp only [lowerLam] at hrun
    simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
    let captures := (List.range input.entries.length).filter
      (fun i => countUses i expr > 0)
    have hcaptures : captures =
        (List.range input.entries.length).filter
          (fun i => countUses i expr > 0) := rfl
    rw [← hcaptures] at hrun
    obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
      trackedBindRun_ok_inv hrun
    rcases captureResult with
      ⟨captureOutput, captureEmit, captureValues⟩
    obtain ⟨fnAddr, addressState, _, hafterAddress⟩ :=
      trackedBindRun_ok_inv hafterCapture
    obtain ⟨code, bodyState, _, hafterBody⟩ :=
      trackedBindRun_ok_inv hafterAddress
    change
      (pushExtra
          (fnAddr, .fn
            ⟨captures.length + lamArity expr, .shared, code⟩) >>= fun _ =>
        pure (captureOutput.bump,
          captureEmit ∘ emitOp (.papp fnAddr
            (captureValues.map (·.toAtom captureOutput)).toArray),
          AVal.slotA captureOutput.depth)).run bodyState =
        .ok (output, emit, av) finalState at hafterBody
    obtain ⟨unitValue, pushedState, _, hpureRun⟩ :=
      trackedBindRun_ok_inv hafterBody
    cases unitValue
    have hpure :
        (captureOutput.bump,
          captureEmit ∘ emitOp (.papp fnAddr
            (captureValues.map (·.toAtom captureOutput)).toArray),
          AVal.slotA captureOutput.depth) = (output, emit, av) ∧
          pushedState = finalState := by
      simpa using hpureRun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have hselected :
        (lowerCaptures expr input
          ((List.range input.entries.length).filter
            (fun i => countUses i expr > 0))).run state =
          .ok (captureOutput, captureEmit, captureValues) captureState := by
      simpa [hcaptures] using hcaptureRun
    exact (lowerCaptures_selected_consumesEntries hselected).bump

theorem lowerE_let_consumesEntries
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    {input output : VEnv} {world : Owned} {binderUses : Uses}
    {value body : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.letE binderUses value body)).run state =
        .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.letE binderUses value body)) := by
  simp only [lowerE] at hrun
  obtain ⟨valueResult, valueState, hvalueRun, hafterValue⟩ :=
    trackedBindRun_ok_inv hrun
  rcases valueResult with ⟨middle, valueEmit, boundValue⟩
  have hvalueConsume := hexpr hvalueRun
  cases boundValue with
  | slotA boundAbs =>
    by_cases hzero : countUses 0 body = 0
    · cases binderUses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := trackedBindRun_ok_inv
          (by simpa [hzero] using hafterValue)
        exact (trackedThrowRun_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := trackedBindRun_ok_inv
          (by simpa [hzero] using hafterValue)
        exact (trackedThrowRun_not_ok hthrow).elim
      | affine =>
        let heldInput :=
          installAliasBinder middle boundAbs 0 Uses.affine true
        let bodyInput :=
          (heldInput.setEntry 0 (.slot boundAbs 0 .affine false)).bump
        have hcontinue :
            ((lowerE src fuel bodyInput world body) >>= fun result =>
              let (bodyOutput, bodyEmit, resultValue) := result
              pure (bodyOutput.pop,
                valueEmit ∘ emitOp (.dropU (.var (middle.rel boundAbs))) ∘
                  bodyEmit,
                resultValue)).run valueState =
              .ok (output, emit, av) finalState := by
          simpa [hzero, heldInput, bodyInput, installAliasBinder,
            VEnv.setEntry, VEnv.bump] using hafterValue
        obtain ⟨bodyResult, bodyState, hbodyRun, hpureRun⟩ :=
          trackedBindRun_ok_inv hcontinue
        rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
        have hpure :
            (bodyOutput.pop,
              valueEmit ∘ emitOp (.dropU (.var (middle.rel boundAbs))) ∘
                bodyEmit,
              resultValue) = (output, emit, av) ∧
              bodyState = finalState := by
          simpa using hpureRun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        have hentries : bodyInput.entries =
            (.slot boundAbs 0 .affine false) :: middle.entries := by
          simp [bodyInput, heldInput, installAliasBinder, VEnv.setEntry,
            VEnv.bump]
        simpa [countUses] using hvalueConsume.bind_under_binder
          (hexpr hbodyRun) hentries
      | many =>
        let heldInput :=
          installAliasBinder middle boundAbs 0 Uses.many true
        let bodyInput :=
          (heldInput.setEntry 0 (.slot boundAbs 0 .many false)).bump
        have hcontinue :
            ((lowerE src fuel bodyInput world body) >>= fun result =>
              let (bodyOutput, bodyEmit, resultValue) := result
              pure (bodyOutput.pop,
                valueEmit ∘ emitOp (.drop (.var (middle.rel boundAbs))) ∘
                  bodyEmit,
                resultValue)).run valueState =
              .ok (output, emit, av) finalState := by
          simpa [hzero, heldInput, bodyInput, installAliasBinder,
            VEnv.setEntry, VEnv.bump] using hafterValue
        obtain ⟨bodyResult, bodyState, hbodyRun, hpureRun⟩ :=
          trackedBindRun_ok_inv hcontinue
        rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
        have hpure :
            (bodyOutput.pop,
              valueEmit ∘ emitOp (.drop (.var (middle.rel boundAbs))) ∘
                bodyEmit,
              resultValue) = (output, emit, av) ∧
              bodyState = finalState := by
          simpa using hpureRun
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        have hentries : bodyInput.entries =
            (.slot boundAbs 0 .many false) :: middle.entries := by
          simp [bodyInput, heldInput, installAliasBinder, VEnv.setEntry,
            VEnv.bump]
        simpa [countUses] using hvalueConsume.bind_under_binder
          (hexpr hbodyRun) hentries
    · let bodyInput := installAliasBinder middle boundAbs
          (countUses 0 body) binderUses true
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop, valueEmit ∘ bodyEmit, resultValue)).run
            valueState = .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installAliasBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hpureRun⟩ :=
        trackedBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ bodyEmit, resultValue) =
              (output, emit, av) ∧ bodyState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      have hentries : bodyInput.entries =
          (.slot boundAbs (countUses 0 body) binderUses true) ::
            middle.entries := by
        simp [bodyInput, installAliasBinder]
      simpa [countUses] using hvalueConsume.bind_under_binder
        (hexpr hbodyRun) hentries
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · let bodyInput := installPushedBinder middle 0 binderUses false
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop,
              valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
              resultValue)).run valueState =
            .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installPushedBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hpureRun⟩ :=
        trackedBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop,
            valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
            resultValue) = (output, emit, av) ∧
            bodyState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      have hentries : bodyInput.entries =
          (.slot middle.depth 0 binderUses false) :: middle.entries := by
        simp [bodyInput, installPushedBinder]
      simpa [countUses] using hvalueConsume.bind_under_binder
        (hexpr hbodyRun) hentries
    · let bodyInput := installPushedBinder middle (countUses 0 body)
          binderUses true
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop,
              valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
              resultValue)).run valueState =
            .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installPushedBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hpureRun⟩ :=
        trackedBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop,
            valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
            resultValue) = (output, emit, av) ∧
            bodyState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      have hentries : bodyInput.entries =
          (.slot middle.depth (countUses 0 body) binderUses true) ::
            middle.entries := by
        simp [bodyInput, installPushedBinder]
      simpa [countUses] using hvalueConsume.bind_under_binder
        (hexpr hbodyRun) hentries

theorem lowerE_proj_consumesEntries
    {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowConsumesEntries src fuel)
    {input output : VEnv} {world : Owned} {fieldIndex : Nat}
    {source : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.proj fieldIndex source)).run state =
        .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.proj fieldIndex source)) := by
  cases world with
  | unique =>
    have huuEq : (Owned.unique == Owned.unique) = true := by decide
    simp [lowerE, huuEq] at hrun
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    simp only [lowerE, hsuEq, Bool.false_eq_true, if_false] at hrun
    obtain ⟨borrowResult, middleState, hborrowRun, hafterBorrow⟩ :=
      trackedBindRun_ok_inv hrun
    rcases borrowResult with
      ⟨borrowOutput, borrowEmit, borrowed, release⟩
    have hconsume := hborrow hborrowRun
    cases borrowed with
    | constA atom =>
      cases atom with
      | var relative =>
        have hpure :
            (borrowOutput.bump,
              borrowEmit ∘ emitOp (.fetch (.var relative) fieldIndex),
              AVal.slotA borrowOutput.depth) = (output, emit, av) ∧
              middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        simpa [countUses] using hconsume.bump
      | lit literal =>
        have hpure :
            (borrowOutput.bump,
              borrowEmit ∘ emitOp (.fetch (.lit literal) fieldIndex),
              AVal.slotA borrowOutput.depth) = (output, emit, av) ∧
              middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        simpa [countUses] using hconsume.bump
      | erased =>
        have hpure :
            (borrowOutput, borrowEmit, AVal.constA .erased) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        simpa [countUses] using hconsume
    | slotA targetAbs =>
      cases release with
      | false =>
        have hpure :
            (borrowOutput.bump.bump,
              borrowEmit ∘
                emitOp (.fetch (.var (borrowOutput.rel targetAbs))
                  fieldIndex) ∘
                emitOp (.dup
                  (.var (borrowOutput.bump.rel borrowOutput.depth))),
              AVal.slotA borrowOutput.bump.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        simpa [countUses] using hconsume.bump.bump
      | true =>
        have hpure :
            (borrowOutput.bump.bump.bump,
              borrowEmit ∘
                emitOp (.fetch (.var (borrowOutput.rel targetAbs))
                  fieldIndex) ∘
                emitOp (.dup
                  (.var (borrowOutput.bump.rel borrowOutput.depth))) ∘
                emitOp (.drop
                  (.var (borrowOutput.bump.bump.rel targetAbs))),
              AVal.slotA borrowOutput.bump.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        simpa [countUses] using hconsume.bump.bump.bump

theorem lowerE_lit_consumesEntries
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {literal : IxIR0.Literal}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.lit literal)).run state =
      .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.lit literal)) := by
  have hpure :
      (input, (_root_.id : Emit), AVal.constA (.lit literal)) =
          (output, emit, av) ∧ state = finalState := by
    simpa [lowerE] using hrun
  obtain ⟨hvalue, hstate⟩ := hpure
  cases hvalue
  subst finalState
  simpa [countUses] using EntryConsumption.zero input

theorem lowerE_erased_consumesEntries
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hrun : (lowerE src (fuel + 1) input world .erased).run state =
      .ok (output, emit, av) finalState) :
    EntryConsumption input output (fun index => countUses index .erased) := by
  have hpure :
      (input, (_root_.id : Emit), AVal.constA .erased) =
          (output, emit, av) ∧ state = finalState := by
    simpa [lowerE] using hrun
  obtain ⟨hvalue, hstate⟩ := hpure
  cases hvalue
  subst finalState
  simpa [countUses] using EntryConsumption.zero input

theorem lowerE_ref_entries_eq
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {address : Ixon.Address}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.ref address)).run state =
      .ok (output, emit, av) finalState) :
    output.entries = input.entries := by
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases hsource : src address with
  | none =>
    exact (trackedThrowRun_not_ok (by
      simpa [lowerE, hsource] using hrun)).elim
  | some decl =>
    cases decl with
    | defn result body =>
      cases harity : lamArity body with
      | zero =>
        have hrun' := hrun
        simp only [lowerE, hsource, harity] at hrun'
        obtain ⟨unitValue, checkedState, _, hpureRun⟩ :=
          trackedBindRun_ok_inv hrun'
        cases unitValue
        simp at hpureRun
        rw [← hpureRun.1.1]
        rfl
      | succ arity =>
        cases world with
        | unique =>
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hsource, harity, huuEq] using hrun)).elim
        | shared =>
          cases result with
          | unique =>
            exact (trackedThrowRun_not_ok (by
              simpa [lowerE, hsource, harity, hsuEq, huuEq]
                using hrun)).elim
          | shared =>
            cases hp : papSafe body with
            | false =>
              exact (trackedThrowRun_not_ok (by
                simpa [lowerE, hsource, harity, hsuEq, hp]
                  using hrun)).elim
            | true =>
              have hpure := hrun
              simp [lowerE, hsource, harity, hsuEq, hp] at hpure
              rw [← hpure.1.1]
              rfl
    | ctor tag arity =>
      cases arity with
      | zero =>
        have hpure := hrun
        simp [lowerE, hsource] at hpure
        rw [← hpure.1.1]
        rfl
      | succ arity =>
        cases world with
        | unique =>
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hsource, huuEq] using hrun)).elim
        | shared =>
          have hrun' := hrun
          simp only [lowerE, hsource, hsuEq, Bool.false_eq_true,
            if_false] at hrun'
          obtain ⟨wrapper, wrapperState, _, hpureRun⟩ :=
            trackedBindRun_ok_inv hrun'
          simp at hpureRun
          rw [← hpureRun.1.1]
          rfl
    | recursor numArgs natLit rules =>
      cases world with
      | unique =>
        exact (trackedThrowRun_not_ok (by
          simpa [lowerE, hsource, huuEq] using hrun)).elim
      | shared =>
        have hpure := hrun
        simp [lowerE, hsource, hsuEq] at hpure
        rw [← hpure.1.1]
        rfl
    | extern arity =>
      cases arity with
      | zero =>
        have hpure := hrun
        simp [lowerE, hsource] at hpure
        rw [← hpure.1.1]
        rfl
      | succ arity =>
        cases world with
        | unique =>
          exact (trackedThrowRun_not_ok (by
            simpa [lowerE, hsource, huuEq] using hrun)).elim
        | shared =>
          have hpure := hrun
          simp [lowerE, hsource, hsuEq] at hpure
          rw [← hpure.1.1]
          rfl

theorem lowerE_ref_consumesEntries
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {address : Ixon.Address}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.ref address)).run state =
      .ok (output, emit, av) finalState) :
    EntryConsumption input output
      (fun index => countUses index (.ref address)) := by
  have hzero := EntryConsumption.of_entries_eq (lowerE_ref_entries_eq hrun)
  simpa [countUses] using hzero

theorem lowerEConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEConsumesEntries src fuel)
    (hborrow : LowerBorrowConsumesEntries src fuel)
    (hspine : LowerSpineConsumesEntries src fuel)
    (hlam : LowerLamConsumesEntries src fuel) :
    LowerEConsumesEntries src (fuel + 1) := by
  intro input world expr state finalState output emit av hrun
  cases expr with
  | var index => exact lowerE_var_consumesEntries hrun
  | ref address => exact lowerE_ref_consumesEntries hrun
  | app function argument =>
    have hspineRun :
        (lowerSpine src fuel input world function [argument]).run state =
          .ok (output, emit, av) finalState := by
      simpa [lowerE] using hrun
    simpa [countUses, countUsesExprs] using hspine hspineRun
  | lam uses body =>
    cases world with
    | unique =>
      have huuEq : (Owned.unique == Owned.unique) = true := by decide
      have hthrow :
          (throw
              "function values live in the shared world (one-shot closures deferred)" :
            LowerM (VEnv × Emit × AVal)).run state =
            .ok (output, emit, av) finalState := by
        simpa [lowerE, huuEq] using hrun
      exact (trackedThrowRun_not_ok hthrow).elim
    | shared =>
      have hsuEq : (Owned.shared == Owned.unique) = false := by decide
      have hlamRun :
          (lowerLam src fuel input (.lam uses body)).run state =
            .ok (output, emit, av) finalState := by
        simpa [lowerE, hsuEq] using hrun
      exact hlam hlamRun
  | letE uses value body =>
    exact lowerE_let_consumesEntries hexpr hrun
  | proj index source =>
    exact lowerE_proj_consumesEntries hborrow hrun
  | lit literal => exact lowerE_lit_consumesEntries hrun
  | erased => exact lowerE_erased_consumesEntries hrun

theorem lowerConsumesEntries_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerConsumesEntries src fuel) :
    LowerConsumesEntries src (fuel + 1) where
  expr := lowerEConsumesEntries_succ
    hprev.expr hprev.borrow hprev.spine hprev.lam
  borrow := lowerBorrowConsumesEntries_succ hprev.expr
  spine := lowerSpineConsumesEntries_succ
    hprev.expr hprev.spine hprev.knownCall hprev.applyRest
  knownCall := knownCallConsumesEntries_succ hprev.args hprev.applyRest
  args := lowerArgsConsumesEntries_succ hprev.expr hprev.args
  applyRest := applyRestConsumesEntries_succ hprev.args
  lam := lowerLamConsumesEntries_succ

/-- Every successful lowering-cluster run consumes exactly the syntactic
occurrence count of each tracked source entry. -/
theorem lowerConsumesEntries (src : IxIR0.Env) :
    ∀ fuel, LowerConsumesEntries src fuel
  | 0 => lowerConsumesEntries_zero src
  | fuel + 1 => lowerConsumesEntries_succ (lowerConsumesEntries src fuel)

theorem lowerE_consumesEntries
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState) :
    EntryConsumption input output (fun index => countUses index expr) :=
  (lowerConsumesEntries src fuel).expr hrun

/-- The counted first entry installed for a let body is always released by
every successful lowering run. -/
theorem lowerE_releasesTrackedFirst
    (src : IxIR0.Env) (fuel : Nat) (expr : IxIR0.Expr) :
    LowerEReleasesTrackedFirst src fuel expr :=
  LowerEConsumesEntries.releasesTrackedFirst
    (lowerConsumesEntries src fuel).expr expr

/-! ## Reachable semantic fuel induction -/

/-- A lowering action cannot produce a successful result. This small
state-independent predicate packages the two administrative base cases of
the semantic fuel induction. -/
def LowerNoSuccess {α : Type} (action : LowerM α) : Prop :=
  ∀ {initial final result},
    action.run initial = .ok result final → False

theorem LowerNoSuccess.throw {α : Type} (message : String) :
    LowerNoSuccess (throw message : LowerM α) := by
  intro initial final result hrun
  exact trackedThrowRun_not_ok hrun

theorem LowerNoSuccess.bindLeft {α β : Type}
    {action : LowerM α} {next : α → LowerM β}
    (haction : LowerNoSuccess action) :
    LowerNoSuccess (action >>= next) := by
  intro initial final result hrun
  obtain ⟨value, middle, hfirst, _⟩ := trackedBindRun_ok_inv hrun
  exact haction hfirst

theorem LowerNoSuccess.bindRight {α β : Type}
    {action : LowerM α} {next : α → LowerM β}
    (hnext : ∀ value, LowerNoSuccess (next value)) :
    LowerNoSuccess (action >>= next) := by
  intro initial final result hrun
  obtain ⟨value, middle, _, hsecond⟩ := trackedBindRun_ok_inv hrun
  exact hnext value hsecond

theorem lowerE_noSuccess_zero (src : IxIR0.Env) (input : VEnv)
    (world : Owned) (expr : IxIR0.Expr) :
    LowerNoSuccess (lowerE src 0 input world expr) := by
  simp only [lowerE]
  exact LowerNoSuccess.throw _

theorem lowerBorrow_noSuccess_zero (src : IxIR0.Env) (input : VEnv)
    (expr : IxIR0.Expr) :
    LowerNoSuccess (lowerBorrow src 0 input expr) := by
  simp only [lowerBorrow]
  exact LowerNoSuccess.throw _

theorem lowerSpine_noSuccess_zero (src : IxIR0.Env) (input : VEnv)
    (world : Owned) (head : IxIR0.Expr) (args : List IxIR0.Expr) :
    LowerNoSuccess (lowerSpine src 0 input world head args) := by
  simp only [lowerSpine]
  exact LowerNoSuccess.throw _

theorem knownCall_noSuccess_zero (src : IxIR0.Env) (input : VEnv)
    (build : Array Atom → Op) (count : Nat) (argWorlds : List Owned)
    (resultWorld : Owned) (args : List IxIR0.Expr) :
    LowerNoSuccess
      (knownCall src 0 input build count argWorlds resultWorld args) := by
  simp only [knownCall]
  exact LowerNoSuccess.throw _

theorem applyRest_noSuccess_zero (src : IxIR0.Env) (input : VEnv)
    (resultWorld : Owned) (pre : Emit) (function : AVal)
    (args : List IxIR0.Expr) :
    LowerNoSuccess
      (applyRest src 0 input resultWorld pre function args) := by
  simp only [applyRest]
  exact LowerNoSuccess.throw _

/-- `lowerSpine` has one extra administrative layer over the other mutual
actions. At fuel one every branch reaches a zero-fuel action before it can
return, including the stateful constructor-wrapper branch. -/
theorem lowerSpine_noSuccess_one (src : IxIR0.Env) (input : VEnv)
    (world : Owned) (head : IxIR0.Expr) (args : List IxIR0.Expr) :
    LowerNoSuccess (lowerSpine src 1 input world head args) := by
  cases head with
  | app function argument =>
    simp only [lowerSpine]
    exact LowerNoSuccess.throw _
  | erased =>
    simp only [lowerSpine]
    exact applyRest_noSuccess_zero src input world id (.constA .erased) args
  | var index =>
    simp only [lowerSpine]
    cases hentry : input.entries[index]? with
    | none =>
      simp only
      exact LowerNoSuccess.bindLeft
        (lowerE_noSuccess_zero src input .shared (.var index))
    | some entry =>
      cases entry with
      | recSelf arity =>
        simp only
        by_cases hunder : args.length < arity
        · rw [if_pos hunder]
          exact LowerNoSuccess.throw _
        · rw [if_neg hunder]
          exact LowerNoSuccess.bindRight (fun _ =>
            knownCall_noSuccess_zero src input (.callSelf ·) arity
              (List.replicate arity .shared) world args)
      | slot abs remaining uses held =>
        simp only
        exact LowerNoSuccess.bindLeft
          (lowerE_noSuccess_zero src input .shared (.var index))
  | ref address =>
    simp only [lowerSpine]
    cases hsrc : src address with
    | none =>
      simp only
      exact LowerNoSuccess.throw _
    | some decl =>
      cases decl with
      | defn result body =>
        simp only
        by_cases hunder : args.length < lamArity body
        · rw [if_pos hunder]
          by_cases hworld : world == .unique
          · rw [if_pos hworld]
            exact LowerNoSuccess.throw _
          · rw [if_neg hworld]
            by_cases hresult : result == .unique
            · rw [if_pos hresult]
              exact LowerNoSuccess.throw _
            · rw [if_neg hresult]
              by_cases hpap : !papSafe body
              · rw [if_pos hpap]
                exact LowerNoSuccess.throw _
              · rw [if_neg hpap]
                exact knownCall_noSuccess_zero src input (.papp address ·)
                  args.length (List.replicate args.length .shared) world args
        · rw [if_neg hunder]
          exact LowerNoSuccess.bindRight (fun _ =>
            knownCall_noSuccess_zero src input (.call address ·)
              (lamArity body) ((lamUses body).map worldOfUses) world args)
      | ctor tag arity =>
        simp only
        by_cases hunder : args.length < arity
        · rw [if_pos hunder]
          by_cases hworld : world == .unique
          · rw [if_pos hworld]
            exact LowerNoSuccess.throw _
          · rw [if_neg hworld]
            exact LowerNoSuccess.bindRight (fun wrapper =>
              knownCall_noSuccess_zero src input (.papp wrapper ·)
                args.length (List.replicate args.length .shared) world args)
        · rw [if_neg hunder]
          exact knownCall_noSuccess_zero src input
            (.alloc world (ctorIdOf address tag) ·) arity
            (List.replicate arity world) world args
      | recursor numArgs natLit rules =>
        simp only
        by_cases hunder : args.length < numArgs + 1
        · rw [if_pos hunder]
          by_cases hworld : world == .unique
          · rw [if_pos hworld]
            exact LowerNoSuccess.throw _
          · rw [if_neg hworld]
            exact knownCall_noSuccess_zero src input (.papp address ·)
              args.length (List.replicate args.length .shared) world args
        · rw [if_neg hunder]
          exact LowerNoSuccess.bindRight (fun _ =>
            knownCall_noSuccess_zero src input (.call address ·)
              (numArgs + 1) (List.replicate (numArgs + 1) .shared)
              world args)
      | extern arity =>
        simp only
        by_cases hunder : args.length < arity
        · rw [if_pos hunder]
          by_cases hworld : world == .unique
          · rw [if_pos hworld]
            exact LowerNoSuccess.throw _
          · rw [if_neg hworld]
            exact knownCall_noSuccess_zero src input (.papp address ·)
              args.length (List.replicate args.length .shared) world args
        · rw [if_neg hunder]
          exact knownCall_noSuccess_zero src input (.extern address ·)
            arity (List.replicate arity .shared) world args
  | lam uses body =>
    simp only [lowerSpine]
    exact LowerNoSuccess.bindLeft
      (lowerE_noSuccess_zero src input .shared (.lam uses body))
  | letE uses value body =>
    simp only [lowerSpine]
    exact LowerNoSuccess.bindLeft
      (lowerE_noSuccess_zero src input .shared (.letE uses value body))
  | proj index source =>
    simp only [lowerSpine]
    exact LowerNoSuccess.bindLeft
      (lowerE_noSuccess_zero src input .shared (.proj index source))
  | lit literal =>
    simp only [lowerSpine]
    exact LowerNoSuccess.bindLeft
      (lowerE_noSuccess_zero src input .shared (.lit literal))

theorem lowerEPreservesBelow_zero
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env} :
    LowerEPreservesBelow ctx cur limit src 0 := by
  intro input world expr state finalState output emit av hrun hrepresented _
  exact (lowerE_noSuccess_zero src input world expr hrun).elim

theorem lowerBorrowPreservesBelow_zero
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env} :
    LowerBorrowPreservesBelow ctx cur limit src 0 := by
  intro input expr state finalState output emit av release hrun hrepresented _
  exact (lowerBorrow_noSuccess_zero src input expr hrun).elim

theorem lowerSpinePreservesBelow_zero
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env} :
    LowerSpinePreservesBelow ctx cur limit src 0 := by
  intro input world head args state finalState output emit av hrun hrepresented _
  exact (lowerSpine_noSuccess_zero src input world head args hrun).elim

theorem lowerSpinePreservesBelow_one
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env} :
    LowerSpinePreservesBelow ctx cur limit src 1 := by
  intro input world head args state finalState output emit av hrun hrepresented _
  exact (lowerSpine_noSuccess_one src input world head args hrun).elim

theorem lowerArgs_noSuccess_zero (src : IxIR0.Env) (input : VEnv)
    (args : List (IxIR0.Expr × Owned)) :
    LowerNoSuccess (lowerArgs src 0 input args) := by
  simp only [lowerArgs]
  exact LowerNoSuccess.throw _

theorem lowerArgsPreservesBelow_zero
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env} :
    LowerArgsPreservesBelow ctx cur limit src 0 := by
  intro input args state finalState output emit avs hrun hrepresented _
  exact (lowerArgs_noSuccess_zero src input args hrun).elim

theorem applyRestPreservesBelow_zero
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env} :
    ApplyRestPreservesBelow ctx cur limit src 0 := by
  intro start input resultWorld pre function args state finalState output emit
    av hfunction hrun hrepresented _
  exact (applyRest_noSuccess_zero src input resultWorld pre function args
    hrun).elim

/-- The mutually recursive semantic compiler invariant at one fuel. Its
successful-run premises are reachable-state premises: the target context
need represent only the declarations in that run's final lowering state. -/
structure LowerClusterPreservesBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEPreservesBelow ctx cur limit src fuel
  borrow : LowerBorrowPreservesBelow ctx cur limit src fuel
  spine : LowerSpinePreservesBelow ctx cur limit src fuel
  args : LowerArgsPreservesBelow ctx cur limit src fuel
  applyRest : ApplyRestPreservesBelow ctx cur limit src fuel

/-- The bounded source-declaration environment supplies exactly the current
self contract needed while lowering any recursor body. -/
theorem SourceDeclContractsBelow.recursorCurrentSelf
    {src : IxIR0.Env} {ctx : Ctx} {limit : Nat}
    (hcontracts : SourceDeclContractsBelow src ctx limit)
    {address : Ixon.Address} {numArgs : Nat} {natLit : Bool}
    {rules : Array IxIR0.RecRule}
    (hsrc : src address = some (.recursor numArgs natLit rules)) :
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = numArgs + 1 ∧ CurrentSelfContractBelow ctx d limit := by
  obtain ⟨d, hdecl, harity, hresult, hcontract⟩ :=
    hcontracts.recursor hsrc
  refine ⟨d, hdecl, harity, hresult, ?_⟩
  simpa [harity] using hcontract

/-- Complete fuel induction for the expression/borrow/spine/arguments/rest
lowering cluster. `ExtraRepresented` is threaded only along successful runs;
`ExtraExtends` transports both declarations and shape-indexed wrapper memos
to earlier sequential sub-runs. The remaining premises are evaluator and
source/self contracts, not compiler-recursion or wrapper-oracle hypotheses. -/
theorem lowerClusterPreservesBelow
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit) :
    ∀ fuel, LowerClusterPreservesBelow ctx cur limit src fuel
  | 0 => by
      exact {
        expr := lowerEPreservesBelow_zero
        borrow := lowerBorrowPreservesBelow_zero
        spine := lowerSpinePreservesBelow_zero
        args := lowerArgsPreservesBelow_zero
        applyRest := applyRestPreservesBelow_zero }
  | fuel + 1 => by
      have hprev := lowerClusterPreservesBelow (cur := cur) happly hdecls fuel
      have hargs : LowerArgsPreservesBelow ctx cur limit src (fuel + 1) :=
        lowerArgsPreservesBelow_succ hprev.expr hprev.args
          (lowerExtraMonotone src fuel).args
      have hrest : ApplyRestPreservesBelow ctx cur limit src (fuel + 1) :=
        applyRestPreservesBelow_succ hprev.args happly
      have hborrow : LowerBorrowPreservesBelow ctx cur limit src (fuel + 1) :=
        lowerBorrowPreservesBelow_succ hprev.expr
      cases fuel with
      | zero =>
        have hspine : LowerSpinePreservesBelow ctx cur limit src 1 :=
          lowerSpinePreservesBelow_one
        have hexpr : LowerEPreservesBelow ctx cur limit src 1 := by
          intro input world expr state finalState output emit av hrun
            hrepresented havailable
          exact lowerE_run_sound_below hprev.expr hprev.spine hargs
            (lowerExtraMonotone src 1).args hrest
            (lowerExtraMonotone src 1).applyRest hprev.borrow hdecls
            (fun body => lowerE_releasesTrackedFirst src 0 body)
            hrepresented hrun havailable
        exact {
          expr := hexpr
          borrow := hborrow
          spine := hspine
          args := hargs
          applyRest := hrest }
      | succ fuel =>
        have hprior := lowerClusterPreservesBelow (cur := cur) happly hdecls fuel
        have hspine : LowerSpinePreservesBelow ctx cur limit src
            (fuel + 2) := by
          intro input world head args state finalState output emit av hrun
            hrepresented havailable
          exact lowerSpine_run_sound_below hprev.spine hprev.expr
            hprior.args (lowerExtraMonotone src fuel).args
            hprior.applyRest hprev.applyRest
            (lowerExtraMonotone src fuel).applyRest
            (lowerExtraMonotone src (fuel + 1)).applyRest hdecls hrun
            hrepresented havailable
        have hexpr : LowerEPreservesBelow ctx cur limit src
            (fuel + 2) := by
          intro input world expr state finalState output emit av hrun
            hrepresented havailable
          exact lowerE_run_sound_below hprev.expr hprev.spine hargs
            (lowerExtraMonotone src (fuel + 2)).args hrest
            (lowerExtraMonotone src (fuel + 2)).applyRest hprev.borrow
            hdecls
            (fun body => lowerE_releasesTrackedFirst src (fuel + 1) body)
            hrepresented hrun havailable
        exact {
          expr := hexpr
          borrow := hborrow
          spine := hspine
          args := hargs
          applyRest := hrest }

/-- Ordinary generated bodies need no current-self assumption: successful
lowering from a self-free logical environment is covered directly by the
closed compiler-fuel cluster. -/
theorem lowerE_run_sound_below_noRecSelf
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (hno : NoRecSelf input) :
    LowerResultSoundBelow ctx cur limit input output world emit av :=
  (lowerClusterPreservesBelow (cur := cur) happly hdecls fuel).expr
    hrun hrepresented (SelfAvailableBelow.of_noRecSelf hno)

/-- Recursor-rule bodies use the same closed cluster with the substantive
current-function contract supplied by the generated recursor environment. -/
theorem lowerE_run_sound_below_currentSelf
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {av : AVal}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (hself : CurrentSelfContractBelow ctx cur limit) :
    LowerResultSoundBelow ctx cur limit input output world emit av :=
  (lowerClusterPreservesBelow (cur := cur) happly hdecls fuel).expr
    hrun hrepresented (SelfAvailableBelow.of_contract hself)

/-- A successful recursor-rule RHS run closes all ordinary logical entries
while preserving the trailing recursive-self marker.  This discharges the
state-side premise consumed by the generated alternative theorem. -/
theorem lowerRecursorRule_rhs_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (hself : CurrentSelfContractBelow ctx cur limit)
    {fuel numArgs : Nat} {rule : IxIR0.RecRule}
    {state finalState : LowSt}
    {fieldOutput rhsInput output : VEnv}
    {fieldEmit parameterEmit bodyEmit : Emit} {av : AVal}
    (hfieldRun :
      applyRecursorFieldRetains
          ⟨List.replicate rule.fields (.slot 0 0 .many false),
            (numArgs + 1) + rule.fields⟩
          (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields) =
        (fieldOutput, fieldEmit))
    (hparameterRun :
      (releaseSlots
          ⟨fieldOutput.entries ++
              parameterEntries 0 (List.replicate numArgs .many)
                (fun i => countUses (rule.fields + i) rule.rhs) ++
              [.recSelf (numArgs + 1)],
            fieldOutput.depth + 1⟩
          ((parameterDrops 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs)).map
            (SlotDrop.offsetEntry rule.fields))).run state =
        .ok (rhsInput, parameterEmit) state)
    (hbodyRun : (lowerE src fuel rhsInput .shared rule.rhs).run state =
      .ok (output, bodyEmit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    LowerResultSoundBelow ctx cur limit rhsInput output .shared
        bodyEmit av ∧
      EntriesReleased output.entries := by
  obtain ⟨htracks, hinputLength, hinputSelf⟩ :=
    recursorPrefix_entries_tracked numArgs rule.fields rule.rhs state
      hfieldRun hparameterRun
  have hsound := lowerE_run_sound_below_currentSelf
    happly hdecls hbodyRun hrepresented hself
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have houtputLength :
      output.entries.length = rule.fields + numArgs + 1 :=
    Eq.trans hcount hinputLength
  have houtputSelf :
      RecSelfAt output (rule.fields + numArgs) (numArgs + 1) :=
    lowerE_recSelfAt hbodyRun hinputSelf
  exact ⟨hsound,
    hconsume.entriesReleasedWithRecSelf htracks houtputLength houtputSelf⟩

/-- Determinism of the generated prefix turns one concrete successful RHS
run into the universally quantified body premise expected by
`lowerRecursorRule_generated_verified_below`. -/
theorem recursorRuleBodySoundBelow_of_run
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (hself : CurrentSelfContractBelow ctx cur limit)
    {fuel numArgs : Nat} {rule : IxIR0.RecRule}
    {state finalState : LowSt}
    {canonicalFieldOutput canonicalRhsInput output : VEnv}
    {canonicalFieldEmit canonicalParameterEmit bodyEmit : Emit}
    {av : AVal}
    (hfieldRun :
      applyRecursorFieldRetains
          ⟨List.replicate rule.fields (.slot 0 0 .many false),
            (numArgs + 1) + rule.fields⟩
          (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields) =
        (canonicalFieldOutput, canonicalFieldEmit))
    (hparameterRun :
      (releaseSlots
          ⟨canonicalFieldOutput.entries ++
              parameterEntries 0 (List.replicate numArgs .many)
                (fun i => countUses (rule.fields + i) rule.rhs) ++
              [.recSelf (numArgs + 1)],
            canonicalFieldOutput.depth + 1⟩
          ((parameterDrops 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs)).map
            (SlotDrop.offsetEntry rule.fields))).run state =
        .ok (canonicalRhsInput, canonicalParameterEmit) state)
    (hbodyRun :
      (lowerE src fuel canonicalRhsInput .shared rule.rhs).run state =
        .ok (output, bodyEmit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    RecursorRuleBodySoundBelow ctx cur limit src fuel numArgs rule state := by
  intro fieldOutput fieldEmit rhsInput parameterEmit
    hfieldRun' hparameterRun'
  have hfieldPair :
      (fieldOutput, fieldEmit) =
        (canonicalFieldOutput, canonicalFieldEmit) :=
    hfieldRun'.symm.trans hfieldRun
  have hfieldOutput : fieldOutput = canonicalFieldOutput :=
    congrArg Prod.fst hfieldPair
  subst fieldOutput
  have hparameterPair :
      (rhsInput, parameterEmit) =
          (canonicalRhsInput, canonicalParameterEmit) ∧ state = state := by
    simpa using hparameterRun'.symm.trans hparameterRun
  have hrhsInput : rhsInput = canonicalRhsInput :=
    congrArg Prod.fst hparameterPair.1
  subst rhsInput
  obtain ⟨hsound, hreleased⟩ := lowerRecursorRule_rhs_sound_below
    happly hdecls hself hfieldRun hparameterRun hbodyRun hrepresented
  exact ⟨output, bodyEmit, av, finalState,
    hbodyRun, hsound, hreleased⟩

/-- Actual successful lowering of one recursor rule produces a bounded
ownership-safe alternative; all generated-prefix and RHS cleanup obligations
are reconstructed from the run itself. -/
theorem lowerRecursorRule_preservesAlt_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (hself : CurrentSelfContractBelow ctx cur limit)
    (hresult : cur.result = .shared)
    {fuel numArgs : Nat} {rule : IxIR0.RecRule} {tag : Nat}
    {state finalState : LowSt} {alt : Alt}
    (hrun : (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
      .ok alt finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    AltOwnershipContractBelow ctx cur alt .shared
      (RecursorEntryValid numArgs) recursorEntryRoots limit := by
  obtain ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
      hfieldRun, hparameterRun, _⟩ :=
    recursorPrefix_generated_verified_below (ctx := ctx) (cur := cur)
      limit numArgs rule.fields rule.rhs state
  have hparameterRun' :
      (releaseSlots
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))).run state =
        .ok (rhsInput, parameterEmit) state := by
    simpa [List.append_assoc] using hparameterRun
  have horiginalRun := hrun
  simp only [lowerRecursorRule] at hrun
  rw [hfieldRun] at hrun
  simp only at hrun
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun
  rcases releaseResult with ⟨actualRhsInput, actualParameterEmit⟩
  have hreleaseEq :
      (rhsInput, parameterEmit) =
          (actualRhsInput, actualParameterEmit) ∧ state = releaseState := by
    simpa [VEnv.bump, List.append_assoc] using
      hparameterRun'.symm.trans hreleaseRun
  have hrhsInput : rhsInput = actualRhsInput :=
    congrArg Prod.fst hreleaseEq.1
  have hparameterEmit : parameterEmit = actualParameterEmit :=
    congrArg Prod.snd hreleaseEq.1
  have hreleaseState : state = releaseState := hreleaseEq.2
  subst actualRhsInput
  subst actualParameterEmit
  subst releaseState
  obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
    trackedBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, bodyEmit, av⟩
  have hpure :
      Alt.mk tag rule.fields
          (fieldEmit
            (emitOp (.drop (.var (fieldOutput.rel numArgs)))
              (parameterEmit
                (bodyEmit (.ret (av.toAtom output)))))) = alt ∧
        bodyState = finalState := by
    simpa using hafterBody
  obtain ⟨halt, hstate⟩ := hpure
  subst bodyState
  have hbody : RecursorRuleBodySoundBelow
      ctx cur limit src fuel numArgs rule state :=
    recursorRuleBodySoundBelow_of_run
      happly hdecls hself hfieldRun hparameterRun' hbodyRun hrepresented
  obtain ⟨generatedFinalState, generatedAlt,
      hgeneratedRun, hcontract⟩ :=
    lowerRecursorRule_generated_verified_below
      hresult src fuel numArgs rule tag state hbody
  have hrunEq : alt = generatedAlt ∧ finalState = generatedFinalState := by
    simpa using horiginalRun.symm.trans hgeneratedRun
  rw [hrunEq.1]
  exact hcontract

/-- Reconstruct the bounded proof-relevant rule plan from the compiler's
actual successful `mapM` traversal.  Final generated-state representation is
transported backward along each tail before proving its head alternative. -/
theorem recursorRulesPlanBelow_of_run
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (hself : CurrentSelfContractBelow ctx cur limit)
    (hresult : cur.result = .shared)
    (fuel numArgs : Nat) :
    ∀ {rules : List (IxIR0.RecRule × Nat)}
        {state finalState : LowSt} {alts : List Alt},
      (rules.mapM (lowerRecursorRule src fuel numArgs)).run state =
        .ok alts finalState →
      ExtraRepresented ctx finalState →
      RecursorRulesPlanBelow ctx cur limit src fuel numArgs
        state rules finalState alts := by
  intro rules
  induction rules with
  | nil =>
    intro state finalState alts hrun _
    have hpure : ([] : List Alt) = alts ∧ state = finalState := by
      simpa using hrun
    obtain ⟨halts, hstate⟩ := hpure
    subst alts
    subst finalState
    exact RecursorRulesPlanBelow.nil state
  | cons ruleTag rules ih =>
    intro state finalState alts hrun hrepresented
    rcases ruleTag with ⟨rule, tag⟩
    simp only [List.mapM_cons] at hrun
    obtain ⟨headAlt, middleState, hheadRun, hafterHead⟩ :=
      trackedBindRun_ok_inv hrun
    obtain ⟨tailAlts, tailState, htailRun, hafterTail⟩ :=
      trackedBindRun_ok_inv hafterHead
    have hpure : headAlt :: tailAlts = alts ∧
        tailState = finalState := by
      simpa using hafterTail
    obtain ⟨halts, hstate⟩ := hpure
    subst alts
    subst finalState
    have htailExtends : ExtraExtends middleState tailState :=
      (ExtraMonotone.listMapM
        (lowerRecursorRule src fuel numArgs)
        (lowerRecursorRule_extraMonotone src fuel numArgs) rules) htailRun
    have hmiddleRepresented : ExtraRepresented ctx middleState :=
      hrepresented.of_extends htailExtends
    have hheadContract : AltOwnershipContractBelow ctx cur headAlt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots limit :=
      lowerRecursorRule_preservesAlt_below
        happly hdecls hself hresult hheadRun hmiddleRepresented
    exact RecursorRulesPlanBelow.cons hheadRun hheadContract
      (ih htailRun hrepresented)

/-- Actual successful lowering of an entire recursor reconstructs the rule
plan and yields its exact-index function ownership theorem. -/
theorem lowerRecursor_preservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {fuel numArgs : Nat} {natLit : Bool}
    {rules : Array IxIR0.RecRule} {state finalState : LowSt} {d : FnDef}
    (hself : CurrentSelfContractBelow ctx d limit)
    (hrun : (lowerRecursor src fuel numArgs natLit rules).run state =
      .ok d finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    FnOwnershipPreservesAt ctx d
      (List.replicate (numArgs + 1) .shared) limit := by
  simp only [lowerRecursor] at hrun
  obtain ⟨alts, rulesState, hrulesRun, hafterRules⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      (⟨numArgs + 1, .shared,
          .case (.var 0) natLit alts.toArray⟩ : FnDef) = d ∧
        rulesState = finalState := by
    simpa using hafterRules
  obtain ⟨hd, hstate⟩ := hpure
  subst d
  subst rulesState
  have hplan : RecursorRulesPlanBelow ctx
      ⟨numArgs + 1, .shared, .case (.var 0) natLit alts.toArray⟩
      limit src fuel numArgs state rules.toList.zipIdx finalState alts :=
    recursorRulesPlanBelow_of_run happly hdecls hself rfl
      fuel numArgs hrulesRun hrepresented
  have hverified :
      (lowerRecursor src fuel numArgs natLit rules).run state =
          .ok ⟨numArgs + 1, .shared,
            .case (.var 0) natLit alts.toArray⟩ finalState ∧
        FnOwnershipPreservesAt ctx
          ⟨numArgs + 1, .shared,
            .case (.var 0) natLit alts.toArray⟩
          (List.replicate (numArgs + 1) .shared) limit :=
    lowerRecursor_generated_verified_below
      limit src fuel numArgs natLit rules state finalState alts
      ⟨numArgs + 1, .shared, .case (.var 0) natLit alts.toArray⟩
      rfl hplan
  have hpreserves : FnOwnershipPreservesAt ctx
      ⟨numArgs + 1, .shared, .case (.var 0) natLit alts.toArray⟩
      (List.replicate (numArgs + 1) .shared) limit := hverified.2
  intro store store' args value rest hlength hown hcodeRun
  exact hpreserves hlength hown hcodeRun

/-- Declaration-facing recursor rule over the actual `lowerDecl` result. -/
theorem lowerDecl_recursor_preservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {fuel : Nat} {address : Ixon.Address} {numArgs : Nat}
    {natLit : Bool} {rules : Array IxIR0.RecRule}
    {state finalState : LowSt} {d : FnDef}
    (hself : CurrentSelfContractBelow ctx d limit)
    (hrun :
      (lowerDecl src fuel (address, .recursor numArgs natLit rules)).run
        state = .ok (some (address, .fn d)) finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    FnOwnershipPreservesAt ctx d
      (List.replicate (numArgs + 1) .shared) limit := by
  simp only [lowerDecl] at hrun
  obtain ⟨actual, recursorState, hrecursorRun, hafterRecursor⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn actual) = some (address, Decl.fn d) ∧
        recursorState = finalState := by
    simpa using hafterRecursor
  have hd : actual = d := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2
  have hrecursorState : recursorState = finalState := hpure.2
  subst actual
  subst recursorState
  intro store store' args value rest hlength hown hcodeRun
  exact lowerRecursor_preservesAt
    happly hdecls hself hrecursorRun hrepresented hlength hown hcodeRun

/-- Declaration-facing inversion of an ordinary successful `lowerFnBody`.
The returned expression proof is self-contract-free; only the canonical
entry cleanup and the actual body run are exposed. -/
theorem lowerFnBody_run_sound_below_noRecSelf
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {fuel : Nat} {input : VEnv} {drops : List SlotDrop}
    {world : Owned} {body : IxIR0.Expr} {state finalState : LowSt}
    {code : Code}
    (hrun : (lowerFnBody src (fuel + 1) input drops world body).run state =
      .ok code finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (hno : NoRecSelf input) :
    ∃ middle releaseEmit releaseState output emit av,
      (releaseSlots input drops).run state =
        .ok (middle, releaseEmit) releaseState ∧
      (lowerE src fuel middle world body).run releaseState =
        .ok (output, emit, av) finalState ∧
      code = (releaseEmit ∘ emit) (.ret (av.toAtom output)) ∧
      LowerResultSoundBelow ctx cur limit middle output world emit av := by
  simp only [lowerFnBody] at hrun
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun
  rcases releaseResult with ⟨middle, releaseEmit⟩
  obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
    trackedBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, emit, av⟩
  have hpure :
      (releaseEmit ∘ emit) (.ret (av.toAtom output)) = code ∧
        bodyState = finalState := by
    simpa using hafterBody
  obtain ⟨hcode, hstate⟩ := hpure
  subst bodyState
  have hmiddleNo := releaseSlots_noRecSelf input hreleaseRun hno
  refine ⟨middle, releaseEmit, releaseState, output, emit, av,
    hreleaseRun, hbodyRun, hcode.symm, ?_⟩
  exact lowerE_run_sound_below_noRecSelf happly hdecls hbodyRun
    hrepresented hmiddleNo

/-- A successful ordinary function-body lowering over the canonical parameter
telescope preserves ownership at the exact evaluator index. Dead-entry release,
exact body consumption, logical-entry cardinality, and the self-free semantic
path are all discharged here. -/
theorem lowerFnBody_parameterEntries_preservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env} {fuel : Nat}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (modes : List Uses) (world : Owned) (body : IxIR0.Expr)
    {state finalState : LowSt} {code : Code}
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hrun : (lowerFnBody src (fuel + 1)
      ⟨parameterEntries 0 modes (fun index => countUses index body),
        modes.length⟩
      (parameterDrops 0 modes (fun index => countUses index body))
      world body).run state = .ok code finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    FnOwnershipPreservesAt ctx ⟨modes.length, world, code⟩
      (modes.map worldOfUses) limit := by
  let remaining : Nat → Nat := fun index => countUses index body
  let input : VEnv :=
    ⟨parameterEntries 0 modes remaining, modes.length⟩
  let drops := parameterDrops 0 modes remaining
  have hrun' :
      (lowerFnBody src (fuel + 1) input drops world body).run state =
        .ok code finalState := by
    simpa [input, drops, remaining] using hrun
  obtain ⟨middle, releaseEmit, releaseState, output, emit, av,
      hreleaseRun, hbodyRun, hcode, hbodySound⟩ :=
    lowerFnBody_run_sound_below_noRecSelf
      (cur := (⟨modes.length, world, code⟩ : FnDef))
      happly hdecls hrun' hrepresented
      (by simpa [input, remaining] using
        parameterEntries_noRecSelf 0 modes remaining modes.length)
  obtain ⟨plannedMiddle, plannedEmit, hplan, htracks⟩ :=
    parameterDrops_releasePlan_tracked 0 modes remaining
      (by simpa [remaining] using hadmissible)
  have hplan' : ReleasePlan input drops plannedMiddle plannedEmit := by
    simpa [input, drops] using hplan
  have hplanRun : (releaseSlots input drops).run state =
      .ok (plannedMiddle, plannedEmit) state := hplan'.run state
  have heq :
      (plannedMiddle, plannedEmit) = (middle, releaseEmit) ∧
        state = releaseState := by
    simpa using hplanRun.symm.trans hreleaseRun
  obtain ⟨hmiddle, hstate⟩ := heq
  cases hmiddle
  subst releaseState
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have hmiddleLength : middle.entries.length = modes.length := by
    calc
      middle.entries.length = input.entries.length := hplan'.entries_length
      _ = modes.length := by simp [input, remaining]
  have hreleased : EntriesReleased output.entries :=
    hconsume.entriesReleased htracks (Eq.trans hcount hmiddleLength)
  have hfull : LowerResultSoundBelow ctx
      (⟨modes.length, world, code⟩ : FnDef) limit input output world
      (releaseEmit ∘ emit) av :=
    hbodySound.afterRelease hplan'.soundBelow
  apply hfull.fnOwnershipPreservesAt
    (FnEntryRealizes.parameterEntries modes remaining)
  · simp
  · exact hreleased
  · exact hcode

/-- Declaration-facing ordinary-definition rule. The theorem follows the
actual `lowerDecl` result rather than a separately supplied body plan. -/
theorem lowerDecl_defn_preservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env} {fuel : Nat}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {d : FnDef}
    (hadmissible : ParameterDropsAdmissible (lamUses body)
      (fun index => countUses index (stripLams body)))
    (hrun : (lowerDecl src (fuel + 1) (address, .defn result body)).run
      state = .ok (some (address, .fn d)) finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    FnOwnershipPreservesAt ctx d ((lamUses body).map worldOfUses) limit := by
  simp only [lowerDecl] at hrun
  obtain ⟨code, bodyState, hbodyRun, hpureRun⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn ⟨lamArity body, result, code⟩) =
          some (address, Decl.fn d) ∧ bodyState = finalState := by
    simpa using hpureRun
  have hd : d = ⟨lamArity body, result, code⟩ := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2.symm
  cases hpure.2
  subst d
  have hpreserves : FnOwnershipPreservesAt ctx
      ⟨(lamUses body).length, result, code⟩
      ((lamUses body).map worldOfUses) limit :=
    lowerFnBody_parameterEntries_preservesAt
      happly hdecls (lamUses body) result (stripLams body) hadmissible
      (by simpa using hbodyRun) hrepresented
  have hfn : (⟨(lamUses body).length, result, code⟩ : FnDef) =
      ⟨lamArity body, result, code⟩ := by
    rw [lamUses_length]
  rw [← hfn]
  intro store store' args value rest hlength hown hcodeRun
  exact hpreserves hlength hown hcodeRun

/-- The complete bounded expression step with counted-binder release
discharged. Generated-declaration representation is now its only remaining
compile-state premise. -/
theorem lowerE_run_sound_below_counted
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    (hspine : LowerSpinePreservesBelow ctx cur limit src fuel)
    (hargsNext : LowerArgsPreservesBelow ctx cur limit src (fuel + 1))
    (hrestNext : ApplyRestPreservesBelow ctx cur limit src (fuel + 1))
    (hrestNextExtra : ApplyRestExtraMonotone src (fuel + 1))
    (hborrow : LowerBorrowPreservesBelow ctx cur limit src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {expr : IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrepresented : ExtraRepresented ctx finalState)
    (hrun : (lowerE src (fuel + 1) input world expr).run state =
      .ok (output, emit, av) finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av :=
  lowerE_run_sound_below hexpr hspine hargsNext
    (lowerExtraMonotone src (fuel + 1)).args hrestNext hrestNextExtra
    hborrow hdecls
    (fun body => lowerE_releasesTrackedFirst src fuel body) hrepresented hrun
    havailable

/-- Ambient whole-program form of the complete expression step. The final
context represents one later state, while `ExtraExtends` transports that
layout back to the successful expression run's own final state. -/
theorem lowerE_run_sound_below_ambient
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    (hspine : LowerSpinePreservesBelow ctx cur limit src fuel)
    (hargsNext : LowerArgsPreservesBelow ctx cur limit src (fuel + 1))
    (hrestNext : ApplyRestPreservesBelow ctx cur limit src (fuel + 1))
    (hrestNextExtra : ApplyRestExtraMonotone src (fuel + 1))
    (hborrow : LowerBorrowPreservesBelow ctx cur limit src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {expr : IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState ambient : LowSt}
    (hambient : ExtraRepresented ctx ambient)
    (hwithin : ExtraExtends finalState ambient)
    (hrun : (lowerE src (fuel + 1) input world expr).run state =
      .ok (output, emit, av) finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av :=
  lowerE_run_sound_below_counted hexpr hspine hargsNext hrestNext
    hrestNextExtra hborrow hdecls (hambient.of_extends hwithin) hrun
    havailable

/-! ## Lifted-function entry layout -/

/-- The structural capture-entry builder realizes an ordered selected subset
of shared runtime arguments. `next` is the next absolute capture slot; it is
threaded in lockstep with the selected values, while unselected source entries
remain released logical placeholders. -/
private theorem selectedEntriesFrom_entriesRealize
    {Γ : VEnv} {env : List RVal}
    (selected : Nat → Bool) (remaining : Nat → Nat) :
    ∀ (indices : List Nat) (next : Nat) (values : List RVal),
      values.length = (indices.filter selected).length →
      0 < Γ.depth →
      next + values.length ≤ Γ.depth →
      (∀ index, index < values.length →
        env[Γ.rel (next + index)]? = values[index]?) →
      EntriesRealize Γ env
        (selectedEntriesFrom selected remaining indices next)
        (rootsFor .shared values) := by
  intro indices
  induction indices with
  | nil =>
    intro next values hlength _ _ _
    cases values with
    | nil => exact EntriesRealize.nil
    | cons value values => simp at hlength
  | cons entry entries ih =>
    intro next values hlength hpositive hbound hslots
    cases hselected : selected entry with
    | false =>
      simp only [selectedEntriesFrom, hselected, Bool.false_eq_true, if_false]
      apply EntriesRealize.released (by omega)
      apply ih next values
      · simpa [hselected] using hlength
      · exact hpositive
      · exact hbound
      · exact hslots
    | true =>
      cases values with
      | nil => simp [hselected] at hlength
      | cons value values =>
        simp only [selectedEntriesFrom, hselected, ↓reduceIte, rootsFor,
          List.map_cons]
        apply EntriesRealize.held
        · exact Nat.lt_of_lt_of_le (by simp) hbound
        · have hhead := hslots 0 (by simp)
          simpa using hhead
        · apply ih (next + 1) values
          · simpa [hselected] using hlength
          · exact hpositive
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
          · intro index hindex
            have htail := hslots (index + 1) (by simp [hindex])
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Reading a bottom-indexed absolute slot from the evaluator's reversed
function environment recovers the corresponding source-order argument. -/
private theorem getElem?_reverse_at_absolute
    {values : List α} {depth index : Nat}
    (hlength : values.length = depth) (hindex : index < depth) :
    values.reverse[depth - 1 - index]? = values[index]? := by
  have hbound : depth - 1 - index < values.length := by omega
  have hreverse := List.getElem?_reverse (l := values) hbound
  have heq : values.length - 1 - (depth - 1 - index) = index := by omega
  simpa [heq] using hreverse

/-- A lifted function's mixed logical environment realizes its public
capture-then-parameter calling convention. Captures occupy the first shared
argument prefix; the canonical parameter telescope follows it, and released
outer placeholders contribute no roots. -/
theorem FnEntryRealizes.lifted
    (entryCount : Nat) (modes : List Uses)
    (parameterRemaining : Nat → Nat)
    (selected : Nat → Bool) (captureRemaining : Nat → Nat)
    (hpositive : 0 < modes.length)
    (hshared : modes.map worldOfUses =
      List.replicate modes.length .shared) :
    let captures := (List.range entryCount).filter selected
    FnEntryRealizes
      ⟨Lower.parameterEntries captures.length modes parameterRemaining ++
          selectedEntriesFrom selected captureRemaining
            (List.range entryCount) 0,
        captures.length + modes.length⟩
      (List.replicate (captures.length + modes.length) .shared) := by
  dsimp only
  let captures := (List.range entryCount).filter selected
  intro args hargs
  have htotal : args.length = captures.length + modes.length := by
    simpa [captures] using hargs
  let captureArgs := args.take captures.length
  let parameterArgs := args.drop captures.length
  have hcapturesLe : captures.length ≤ args.length := by omega
  have hcaptureLength : captureArgs.length = captures.length := by
    simp [captureArgs, List.length_take, Nat.min_eq_left hcapturesLe]
  have hparameterLength : parameterArgs.length = modes.length := by
    simp [parameterArgs, List.length_drop, htotal]
  have hsplit : captureArgs ++ parameterArgs = args := by
    exact List.take_append_drop captures.length args
  let Γ : VEnv :=
    ⟨Lower.parameterEntries captures.length modes parameterRemaining ++
        selectedEntriesFrom selected captureRemaining
          (List.range entryCount) 0,
      captures.length + modes.length⟩
  have hparameter₀ := parameterEntries_entriesRealize parameterRemaining
    captures.length modes (args := parameterArgs)
      (suffix := captureArgs.reverse) hparameterLength (by simp [hcaptureLength])
  have hparameter : EntriesRealize Γ args.reverse
      (Lower.parameterEntries captures.length modes parameterRemaining)
      (rootsForWorlds (modes.map worldOfUses) parameterArgs).reverse := by
    have htransport := hparameter₀.of_depth_eq (Δ := Γ) (by simp [Γ])
    have henv : args.reverse = parameterArgs.reverse ++ captureArgs.reverse := by
      rw [← hsplit, List.reverse_append]
    simpa [henv] using htransport
  have hcaptures : EntriesRealize Γ args.reverse
      (selectedEntriesFrom selected captureRemaining
        (List.range entryCount) 0)
      (rootsFor .shared captureArgs) := by
    apply selectedEntriesFrom_entriesRealize selected captureRemaining
    · simpa [captures, hcaptureLength]
    · dsimp [Γ]
      omega
    · simp [Γ, hcaptureLength]
    · intro index hindex
      have hindexArgs : index < args.length := by omega
      have hindexTotal : index < captures.length + modes.length := by omega
      have hreverse := getElem?_reverse_at_absolute
        (values := args) htotal hindexTotal
      have happend : args[index]? = captureArgs[index]? := by
        rw [← hsplit]
        exact List.getElem?_append_left
          (by simpa [hcaptureLength] using hindex)
      simpa [Γ, VEnv.rel, htotal] using hreverse.trans happend
  refine ⟨(rootsForWorlds (modes.map worldOfUses) parameterArgs).reverse ++
      rootsFor .shared captureArgs, ?_, ?_⟩
  · refine ⟨?_, hparameter.append hcaptures⟩
    simpa [Γ] using htotal
  · have hparameterRoots :
        rootsForWorlds (modes.map worldOfUses) parameterArgs =
          rootsFor .shared parameterArgs := by
      rw [hshared]
      exact rootsForWorlds_replicate_eq_rootsFor .shared hparameterLength
    have htarget :
        rootsForWorlds
            (List.replicate (captures.length + modes.length) .shared) args =
          rootsFor .shared captureArgs ++ rootsFor .shared parameterArgs := by
      rw [rootsForWorlds_replicate_eq_rootsFor .shared htotal]
      rw [← hsplit]
      simp [rootsFor]
    rw [hparameterRoots, htarget]
    exact (List.reverse_perm _).append_right _ |>.trans List.perm_append_comm

/-- Removing the leading lambda telescope shifts every older free-variable
index by exactly the telescope arity. -/
theorem countUses_eq_stripLams_shift (expr : IxIR0.Expr) (index : Nat) :
    countUses index expr =
      countUses (lamArity expr + index) (stripLams expr) := by
  induction expr generalizing index with
  | lam uses body ih =>
    simp only [countUses, lamArity, stripLams]
    rw [ih]
    have heq : lamArity body + (index + 1) =
        lamArity body + 1 + index := by omega
    rw [heq]
  | var => simp only [lamArity, Nat.zero_add, stripLams]
  | ref => simp only [lamArity, Nat.zero_add, stripLams]
  | app => simp only [lamArity, Nat.zero_add, stripLams]
  | letE => simp only [lamArity, Nat.zero_add, stripLams]
  | proj => simp only [lamArity, Nat.zero_add, stripLams]
  | lit => simp only [lamArity, Nat.zero_add, stripLams]
  | erased => simp only [lamArity, Nat.zero_add, stripLams]

private theorem uses_eq_many_of_beq {uses : Uses}
    (h : (uses == .many) = true) : uses = .many := by
  cases uses with
  | erased => exact Bool.noConfusion h
  | linear => exact Bool.noConfusion h
  | affine => exact Bool.noConfusion h
  | many => rfl

private theorem all_many_eq_replicate :
    ∀ modes : List Uses,
      modes.all (fun uses => uses == .many) = true →
      modes = List.replicate modes.length .many := by
  intro modes
  induction modes with
  | nil => simp
  | cons mode modes ih =>
    intro hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hmode : mode = .many := uses_eq_many_of_beq hall.1
    subst mode
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
    exact ih hall.2

/-- The executable `papSafe` check pins the entire lifted parameter telescope
to `many`, not merely its mapped ownership worlds. -/
theorem papSafe_lamUses_eq_replicate {expr : IxIR0.Expr}
    (hsafe : papSafe expr = true) :
    lamUses expr = List.replicate (lamArity expr) .many := by
  have hsafe' : (lamUses expr).all (fun uses => uses == .many) = true := by
    simpa [papSafe] using hsafe
  have hall := all_many_eq_replicate (lamUses expr) hsafe'
  simpa using hall

/-- Append the selected older-entry range to a tracked parameter prefix. The
selection bit is required to be exactly the canonical nonzero-count bit; this
turns both live captures and released placeholders into ordinary tracked
entries for the body-consumption theorem. -/
theorem EntriesTrackCounts.frameSelectedRange
    {Γ : VEnv} {baseCount : Nat} {counts : Nat → Nat}
    (htracks : EntriesTrackCounts Γ baseCount counts)
    (hlength : Γ.entries.length = baseCount)
    (selected : Nat → Bool) (remaining : Nat → Nat) :
    ∀ (start count next : Nat),
      (∀ offset, offset < count →
        selected (start + offset) = (counts (baseCount + offset) != 0)) →
      (∀ offset, offset < count →
        remaining (start + offset) = counts (baseCount + offset)) →
      EntriesTrackCounts
        (frameVEnvEntries Γ
          (selectedEntriesFrom selected remaining
            (List.range' start count) next))
        (baseCount + count) counts := by
  intro start count
  induction count generalizing Γ baseCount start with
  | zero =>
    intro next _ _
    simpa [selectedEntriesFrom, frameVEnvEntries] using htracks
  | succ count ih =>
    intro next hselected hremaining
    have hselectedHead := hselected 0 (by omega)
    have hremainingHead := hremaining 0 (by omega)
    cases hhead : selected start with
    | false =>
      have hzero : counts baseCount = 0 := by
        simp [hhead] at hselectedHead
        omega
      have hremainingHead' : remaining start = 0 := by
        simpa [hzero] using hremainingHead
      let head : VEntry := .slot 0 0 .many false
      let Γhead := frameVEnvEntries Γ [head]
      have hheadTracks : EntriesTrackCounts Γhead (baseCount + 1) counts := by
        have hcanonical := EntriesTrackCounts.frameCanonicalSlot
          (abs := 0) (uses := .many) htracks hlength
        simpa [Γhead, head, hzero] using hcanonical
      have hheadLength : Γhead.entries.length = baseCount + 1 := by
        simp [Γhead, head, frameVEnvEntries, hlength]
      have htail := ih (Γ := Γhead) (baseCount := baseCount + 1)
        hheadTracks hheadLength (start := start + 1) next
        (fun offset hoffset => by
          have h := hselected (offset + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
        (fun offset hoffset => by
          have h := hremaining (offset + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      simpa [List.range'_succ, selectedEntriesFrom, hhead, Γhead, head,
        frameVEnvEntries, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail
    | true =>
      have hnonzero : counts baseCount ≠ 0 := by
        simpa [hhead] using hselectedHead
      have hremainingHead' : remaining start = counts baseCount := by
        simpa using hremainingHead
      let head : VEntry := .slot next (remaining start) .many true
      let Γhead := frameVEnvEntries Γ [head]
      have hheadTracks : EntriesTrackCounts Γhead (baseCount + 1) counts := by
        have hcanonical := EntriesTrackCounts.frameCanonicalSlot
          (abs := next) (uses := .many) htracks hlength
        have hheld : (counts baseCount != 0) = true := by simp [hnonzero]
        rw [hheld] at hcanonical
        simpa [Γhead, head, hremainingHead'] using hcanonical
      have hheadLength : Γhead.entries.length = baseCount + 1 := by
        simp [Γhead, head, frameVEnvEntries, hlength]
      have htail := ih (Γ := Γhead) (baseCount := baseCount + 1)
        hheadTracks hheadLength (start := start + 1) (next + 1)
        (fun offset hoffset => by
          have h := hselected (offset + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
        (fun offset hoffset => by
          have h := hremaining (offset + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      simpa [List.range'_succ, selectedEntriesFrom, hhead, Γhead, head,
        frameVEnvEntries, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail

/-- Every selected-entry frame consists solely of ordinary slots. -/
theorem selectedEntriesFrom_noRecSelf
    (selected : Nat → Bool) (remaining : Nat → Nat) :
    ∀ (indices : List Nat) (next depth : Nat),
      NoRecSelf
        ⟨selectedEntriesFrom selected remaining indices next, depth⟩ := by
  intro indices
  induction indices with
  | nil =>
    intro next depth
    exact NoRecSelf.empty
  | cons index indices ih =>
    intro next depth
    cases hselected : selected index with
    | false =>
      simpa [selectedEntriesFrom, hselected] using
        (ih next depth).consSlot 0 0 .many false
    | true =>
      simpa [selectedEntriesFrom, hselected] using
        (ih (next + 1) depth).consSlot next (remaining index) .many true

/-- Concatenating two self-free logical entry blocks remains self-free. -/
theorem NoRecSelf.appendEntries
    {left right : List VEntry} {depth : Nat}
    (hleft : NoRecSelf ⟨left, depth⟩)
    (hright : NoRecSelf ⟨right, depth⟩) :
    NoRecSelf ⟨left ++ right, depth⟩ := by
  apply NoRecSelf.of_mem_not_recSelf
  intro entry hmember arity heq
  rw [List.mem_append] at hmember
  cases hmember with
  | inl hleftMember =>
    obtain ⟨index, hget⟩ := List.mem_iff_getElem?.mp hleftMember
    subst entry
    exact hleft index arity hget
  | inr hrightMember =>
    obtain ⟨index, hget⟩ := List.mem_iff_getElem?.mp hrightMember
    subst entry
    exact hright index arity hget

/-- A successfully lowered lifted body preserves the all-shared public
capture-plus-parameter signature. This closes entry realization, generated
parameter cleanup, exact consumption of both parameter and captured-variable
entries, and the self-free body boundary in one declaration-level rule. -/
theorem lowerFnBody_liftedEntries_preservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env} {fuel : Nat}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (entryCount : Nat) (modes : List Uses) (body : IxIR0.Expr)
    (selected : Nat → Bool)
    {state finalState : LowSt} {code : Code}
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hselected : ∀ index, index < entryCount →
      selected index = (countUses (modes.length + index) body != 0))
    (hpositive : 0 < modes.length)
    (hshared : modes.map worldOfUses =
      List.replicate modes.length .shared)
    (hrun : (lowerFnBody src (fuel + 1)
      (let captures := (List.range entryCount).filter selected
       ⟨parameterEntries captures.length modes
            (fun index => countUses index body) ++
          selectedEntriesFrom selected
            (fun index => countUses (modes.length + index) body)
            (List.range entryCount) 0,
        captures.length + modes.length⟩)
      (let captures := (List.range entryCount).filter selected
       parameterDrops captures.length modes
          (fun index => countUses index body))
      .shared body).run state = .ok code finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    let captures := (List.range entryCount).filter selected
    FnOwnershipPreservesAt ctx
      ⟨captures.length + modes.length, .shared, code⟩
      (List.replicate (captures.length + modes.length) .shared) limit := by
  dsimp only
  let captures := (List.range entryCount).filter selected
  let parameterRemaining : Nat → Nat := fun index => countUses index body
  let captureRemaining : Nat → Nat :=
    fun index => countUses (modes.length + index) body
  let outerEntries := selectedEntriesFrom selected captureRemaining
    (List.range entryCount) 0
  let input : VEnv :=
    ⟨parameterEntries captures.length modes parameterRemaining ++ outerEntries,
      captures.length + modes.length⟩
  let drops := parameterDrops captures.length modes parameterRemaining
  have hrun' :
      (lowerFnBody src (fuel + 1) input drops .shared body).run state =
        .ok code finalState := by
    simpa [input, drops, outerEntries, parameterRemaining, captureRemaining,
      captures] using hrun
  have hno : NoRecSelf input := by
    apply NoRecSelf.appendEntries
    · exact parameterEntries_noRecSelf captures.length modes
        parameterRemaining (captures.length + modes.length)
    · simpa [outerEntries] using
        selectedEntriesFrom_noRecSelf selected captureRemaining
          (List.range entryCount) 0 (captures.length + modes.length)
  obtain ⟨middle, releaseEmit, releaseState, output, emit, av,
      hreleaseRun, hbodyRun, hcode, hbodySound⟩ :=
    lowerFnBody_run_sound_below_noRecSelf
      (cur := (⟨captures.length + modes.length, .shared, code⟩ : FnDef))
      happly hdecls hrun' hrepresented hno
  obtain ⟨parameterOutput, plannedEmit, hparameterPlan, hparameterTracks⟩ :=
    parameterDrops_releasePlan_tracked_atDepth captures.length
      (captures.length + modes.length) modes parameterRemaining
      (by simpa [parameterRemaining] using hadmissible)
  let plannedMiddle := frameVEnvEntries parameterOutput outerEntries
  have hplan : ReleasePlan input drops plannedMiddle plannedEmit := by
    have hframed := hparameterPlan.frameEntries outerEntries
    simpa [input, drops, plannedMiddle, outerEntries, frameVEnvEntries]
      using hframed
  have hplanRun : (releaseSlots input drops).run state =
      .ok (plannedMiddle, plannedEmit) state := hplan.run state
  have heq :
      (plannedMiddle, plannedEmit) = (middle, releaseEmit) ∧
        state = releaseState := by
    simpa using hplanRun.symm.trans hreleaseRun
  have hmiddle : plannedMiddle = middle := congrArg Prod.fst heq.1
  have hemit : plannedEmit = releaseEmit := congrArg Prod.snd heq.1
  subst middle
  subst releaseEmit
  have hstate := heq.2
  subst releaseState
  have hparameterLength : parameterOutput.entries.length = modes.length := by
    calc
      parameterOutput.entries.length =
          (parameterEntries captures.length modes parameterRemaining).length :=
        hparameterPlan.entries_length
      _ = modes.length := parameterEntries_length _ _ _
  have htracks : EntriesTrackCounts plannedMiddle (modes.length + entryCount)
      (fun index => countUses index body) := by
    have hframed := hparameterTracks.frameSelectedRange hparameterLength
      selected captureRemaining 0 entryCount 0
      (fun offset hoffset => by
        simpa [captureRemaining] using hselected offset hoffset)
      (fun offset hoffset => by
        simp [captureRemaining, parameterRemaining])
    simpa [plannedMiddle, outerEntries, List.range_eq_range'] using hframed
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have hmiddleLength : plannedMiddle.entries.length =
      modes.length + entryCount := by
    calc
      plannedMiddle.entries.length = input.entries.length := hplan.entries_length
      _ = modes.length + entryCount := by
        simp [input, outerEntries, parameterRemaining, captureRemaining]
  have hreleased : EntriesReleased output.entries :=
    hconsume.entriesReleased htracks (Eq.trans hcount hmiddleLength)
  have hfull : LowerResultSoundBelow ctx
      (⟨captures.length + modes.length, .shared, code⟩ : FnDef)
      limit input output .shared (plannedEmit ∘ emit) av :=
    hbodySound.afterRelease hplan.soundBelow
  apply hfull.fnOwnershipPreservesAt
    (FnEntryRealizes.lifted entryCount modes parameterRemaining selected
      captureRemaining hpositive hshared)
  · simp [captures]
  · exact hreleased
  · exact hcode

/-- A successful lambda lowering adds the generated lifted declaration to the
compile state, and that declaration has the all-shared ownership contract
advertised by the emitted partial application. -/
theorem lowerLam_generatedFn_preservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env} {fuel : Nat}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    (hpositive : 0 < lamArity expr)
    (hrun : (lowerLam src (fuel + 1) input expr).run state =
      .ok (output, emit, value) finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    let captures := (List.range input.entries.length).filter
      (fun index => countUses index expr > 0)
    ∃ address code,
      (address, .fn
        ⟨captures.length + lamArity expr, .shared, code⟩) ∈
          finalState.extra ∧
      ctx.decls address = some (.fn
        ⟨captures.length + lamArity expr, .shared, code⟩) ∧
      FnOwnershipPreservesAt ctx
        ⟨captures.length + lamArity expr, .shared, code⟩
        (List.replicate (captures.length + lamArity expr) .shared) limit := by
  dsimp only
  cases hp : papSafe expr with
  | false => simp [lowerLam, hp] at hrun
  | true =>
    simp only [lowerLam] at hrun
    simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
    let captures := (List.range input.entries.length).filter
      (fun index => countUses index expr > 0)
    have hcaptures : captures = (List.range input.entries.length).filter
        (fun index => countUses index expr > 0) := rfl
    rw [← hcaptures] at hrun
    obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
      trackedBindRun_ok_inv hrun
    rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
    obtain ⟨fnAddr, addressState, hfreshRun, hafterFresh⟩ :=
      trackedBindRun_ok_inv hafterCapture
    obtain ⟨code, bodyState, hbodyRun, hafterBody⟩ :=
      trackedBindRun_ok_inv hafterFresh
    change
      (pushExtra (fnAddr, .fn
          ⟨captures.length + lamArity expr, .shared, code⟩) >>= fun _ =>
        pure (captureOutput.bump,
          captureEmit ∘ emitOp (.papp fnAddr
            (captureValues.map (·.toAtom captureOutput)).toArray),
          .slotA captureOutput.depth)).run bodyState =
        .ok (output, emit, value) finalState at hafterBody
    obtain ⟨unitValue, pushedState, hpushRun, hpureRun⟩ :=
      trackedBindRun_ok_inv hafterBody
    cases unitValue
    have hpure :
        (captureOutput.bump,
            captureEmit ∘ emitOp (.papp fnAddr
              (captureValues.map (·.toAtom captureOutput)).toArray),
            AVal.slotA captureOutput.depth) = (output, emit, value) ∧
          pushedState = finalState := by
      simpa using hpureRun
    have hstate := hpure.2
    subst finalState
    have hbodyRepresented : ExtraRepresented ctx bodyState :=
      hrepresented.of_extends (pushExtra_extraExtends hpushRun)
    have hmember :
        (fnAddr, .fn
          ⟨captures.length + lamArity expr, .shared, code⟩) ∈
            pushedState.extra := by
      simp [pushExtra] at hpushRun
      subst pushedState
      simp
    have hdecl := hrepresented.decl hmember
    have hmodes := papSafe_lamUses_eq_replicate hp
    have hentryCount : captureOutput.entries.length = input.entries.length :=
      lowerCaptures_preservesEntryCount expr hcaptureRun
    have hadmissible : ParameterDropsAdmissible (lamUses expr)
        (fun index => countUses index (stripLams expr)) := by
      rw [hmodes]
      exact parameterDropsAdmissible_replicate_many _ _
    have hselected : ∀ index, index < input.entries.length →
        decide (0 < countUses index expr) =
          (countUses ((lamUses expr).length + index) (stripLams expr) != 0) := by
      intro index _
      rw [lamUses_length]
      rw [← countUses_eq_stripLams_shift expr index]
      cases countUses index expr <;> rfl
    have hshared : (lamUses expr).map worldOfUses =
        List.replicate (lamUses expr).length .shared := by
      rw [hmodes]
      simp [worldOfUses]
    cases fuel with
    | zero =>
      exact (trackedThrowRun_not_ok
        (by simpa [lowerFnBody] using hbodyRun)).elim
    | succ bodyFuel =>
      have hbodyRun' :
          (lowerFnBody src (bodyFuel + 1)
            (let generatedCaptures :=
                (List.range input.entries.length).filter
                  (fun index => countUses index expr > 0)
             ⟨parameterEntries generatedCaptures.length (lamUses expr)
                  (fun index => countUses index (stripLams expr)) ++
                selectedEntriesFrom
                  (fun index => countUses index expr > 0)
                  (fun index => countUses ((lamUses expr).length + index)
                    (stripLams expr))
                  (List.range input.entries.length) 0,
              generatedCaptures.length + (lamUses expr).length⟩)
            (let generatedCaptures :=
                (List.range input.entries.length).filter
                  (fun index => countUses index expr > 0)
             parameterDrops generatedCaptures.length (lamUses expr)
                (fun index => countUses index (stripLams expr)))
            .shared (stripLams expr)).run addressState =
              .ok code bodyState := by
        simpa [captures, lamUses_length, hentryCount] using hbodyRun
      have hpreserves : FnOwnershipPreservesAt ctx
          ⟨captures.length + (lamUses expr).length, .shared, code⟩
          (List.replicate
            (captures.length + (lamUses expr).length) .shared) limit := by
        exact lowerFnBody_liftedEntries_preservesAt
          (fuel := bodyFuel) (state := addressState)
          (finalState := bodyState) (code := code)
          happly hdecls input.entries.length
          (lamUses expr) (stripLams expr)
          (fun index => countUses index expr > 0)
          hadmissible hselected (by simpa using hpositive) hshared
          hbodyRun' hbodyRepresented
      refine ⟨fnAddr, code, hmember, hdecl, ?_⟩
      rw [lamUses_length] at hpreserves
      exact hpreserves

private theorem wrapperBindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

private theorem wrapperBindErr {error α β : Type} (err : error)
    (next : α → Except error β) :
    ((Except.error err : Except error α) >>= next) = .error err := rfl

private theorem descendingVars_resolveFrom (args suffix : List RVal) :
    ∀ accum,
      (descendingVars args.length).toArray.foldlM
        (fun acc atom => do pure (acc ++ [← resolveAtom
          (args.reverse ++ suffix) atom])) accum =
        .ok (accum ++ args) := by
  induction args generalizing suffix with
  | nil =>
    intro accum
    simp only [List.length_nil, descendingVars, List.foldlM_toArray,
      List.foldlM_nil, List.append_nil]
    rfl
  | cons head tail ih =>
    intro accum
    simp only [List.length_cons, descendingVars, List.foldlM_toArray,
      List.foldlM_cons]
    have hhead : resolveAtom ((head :: tail).reverse ++ suffix)
        (.var tail.length) = .ok head := by
      simp [resolveAtom]
    rw [hhead, wrapperBindOk]
    have htail := ih (head :: suffix) (accum ++ [head])
    simpa [List.append_assoc] using htail

theorem descendingVars_resolveAtoms (args : List RVal) :
    resolveAtoms args.reverse (descendingVars args.length).toArray =
      .ok args := by
  unfold resolveAtoms
  simpa using descendingVars_resolveFrom args [] []

/-- A generated constructor eta-wrapper consumes its all-shared argument
vector and returns ownership of the freshly allocated shared constructor. -/
theorem ctorWrapper_fnOwnershipContract (ctx : Ctx)
    (source : Ixon.Address) (tag arity : Nat) :
    FnOwnershipContract ctx
      ⟨arity, .shared,
        .letOp (.alloc .shared (ctorIdOf source tag)
          (descendingVars arity).toArray)
          (.ret (.var 0))⟩
      (List.replicate arity .shared) := by
  constructor
  · simp
  · intro fuel store store' args value rest hlength hown hrun
    have hargsLength : args.length = arity := by simpa using hlength
    have hresolve : resolveAtoms args.reverse
        (descendingVars arity).toArray = .ok args := by
      rw [← hargsLength]
      exact descendingVars_resolveAtoms args
    have hroots : rootsForWorlds (List.replicate arity .shared) args =
        rootsFor .shared args :=
      rootsForWorlds_replicate_eq_rootsFor .shared hargsLength
    have hinput : RootOwnership store
        (rootsFor .shared args ++ rest) := by
      rwa [hroots] at hown
    cases fuel with
    | zero => simp [runCode] at hrun
    | succ outerFuel =>
      cases outerFuel with
      | zero => simp [runCode, runOp, wrapperBindErr] at hrun
      | succ innerFuel =>
        simp only [runCode] at hrun
        simp only [runOp] at hrun
        rw [hresolve] at hrun
        simp [resolveAtom, wrapperBindOk] at hrun
        obtain ⟨hstore, hvalue⟩ := hrun
        subst store'
        subst value
        apply RootOwnership.allocNode
        · simpa [nodeChildren] using hinput
        · trivial

/-- Package the exact declaration shape and callable contract of a generated
constructor wrapper. -/
theorem ctorWrapper_ownershipContract (ctx : Ctx)
    (source : Ixon.Address) (tag arity : Nat) :
    ∃ d, ctorWrapperDecl source tag arity = .fn d ∧
      d.result = .shared ∧
      FnOwnershipContract ctx d (List.replicate d.arity .shared) := by
  refine ⟨⟨arity, .shared,
      .letOp (.alloc .shared (ctorIdOf source tag)
        (descendingVars arity).toArray) (.ret (.var 0))⟩, rfl, rfl, ?_⟩
  exact ctorWrapper_fnOwnershipContract ctx source tag arity

end Compilatrix.IxIR1.LowerSim
