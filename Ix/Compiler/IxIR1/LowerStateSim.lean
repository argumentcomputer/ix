import Ix.Compiler.IxIR1.LowerSim

/-!
# Compile-state simulation for IxIR₀ → IxIR₁ lowering

This companion proves that successful lowering consumes exactly each source
entry's syntactic occurrence count. In particular, a counted let binder is
released before the executable lowerer removes its logical entry.
-/

namespace Ix.Compiler.IxIR1.LowerSim

open Ix.Compiler.Ixon (Owned Uses)
open Ix.Compiler.IxIR1.Lower
open Ix.Compiler.IxIR1.Sim

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

theorem trackedMapRun_ok_inv {error state α β : Type}
    {action : EStateM error state α} {f : α → β}
    {initial final : state} {result : β}
    (hrun : (f <$> action).run initial = .ok result final) :
    ∃ value, action.run initial = .ok value final ∧ f value = result := by
  have hbind : (action >>= fun value => pure (f value)).run initial =
      .ok result final := by
    simpa only [bind_pure_comp] using hrun
  obtain ⟨value, middle, haction, hpure⟩ := trackedBindRun_ok_inv hbind
  have hresult : f value = result ∧ middle = final := by
    simpa using hpure
  cases hresult.2
  exact ⟨value, haction, hresult.1⟩

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
  exact parameterDrops_releasePlan_traverse remaining
    (Result := fun _ _ sourceModes output =>
      EntriesTrackCounts output sourceModes.length remaining)
    (hnil := by
      intro _ _ index hindex
      simp at hindex)
    (hlive := by
      intro current _ mode rest innerOutput htracks hlength hlive
      simpa using EntriesTrackCounts.frameLiveSlot
        (abs := current) (uses := mode) htracks hlength hlive)
    (hmany := by
      intro current _ rest innerOutput htracks hlength hdead
      simpa using EntriesTrackCounts.frameReleasedSlot
        (abs := current) (uses := .many) htracks hlength hdead)
    (haffine := by
      intro current _ rest innerOutput htracks hlength hdead
      simpa using EntriesTrackCounts.frameReleasedSlot
        (abs := current) (uses := .affine) htracks hlength hdead)
    base depth modes hadmissible

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
  exact recursorFieldRetains_plan_traverse rhs
    (Result := fun _ _ currentCount output =>
      EntriesTrackCounts output currentCount
        (fun index => countUses index rhs))
    (hnilResult := by
      intro _ _ index hindex
      simp at hindex)
    (hskipResult := by
      intro _ _ currentCount tailOutput htracks hlength hzero
      simpa [hzero] using EntriesTrackCounts.frameCanonicalSlot
        (abs := 0) (uses := .many) htracks hlength)
    (hretainResult := by
      intro _ currentDepth currentCount tailOutput htracks hlength
        hnonzero
      simpa using EntriesTrackCounts.frameLiveSlot
        (abs := currentDepth) (uses := .many) htracks hlength hnonzero)
    fieldAbs depth fieldCount

theorem replicate_many_parameterDropsAdmissible
    (count : Nat) (remaining : Nat → Nat) :
    ParameterDropsAdmissible (List.replicate count .many) remaining :=
  parameterDropsAdmissible_replicate_many count remaining

/-- Every descriptor in a successfully executed release list has a runtime
release mode.  The other two source modes are precisely the error branches
of `releaseSlots`. -/
theorem releaseSlots_run_drop_admissible
    {input output : VEnv} {drops : List SlotDrop} {emit : Emit}
    {state finalState : LowSt}
    (hrun : (releaseSlots input drops).run state =
      .ok (output, emit) finalState) :
    ∀ drop ∈ drops, drop.uses = .many ∨ drop.uses = .affine := by
  exact releaseSlots_run_core
    (Result := fun _ _ selectedDrops _ =>
      ∀ drop ∈ selectedDrops,
        drop.uses = .many ∨ drop.uses = .affine)
    (hnil := by simp)
    (haffine := by
      intro entry abs rest initial final tailEmit htail selected hselected
      rcases List.mem_cons.mp hselected with rfl | hrest
      · exact Or.inr rfl
      · exact htail selected hrest)
    (hmany := by
      intro entry abs rest initial final tailEmit htail selected hselected
      rcases List.mem_cons.mp hselected with rfl | hrest
      · exact Or.inl rfl
      · exact htail selected hrest)
    hrun

/-- If every generated dead-parameter descriptor has a runtime release
mode, the source telescope satisfies the exact syntactic admissibility
predicate used by the function-entry proof. -/
theorem parameterDropsAdmissible_of_drop_admissible
    (base : Nat) (modes : List Uses) (remaining : Nat → Nat)
    (hdrops : ∀ drop ∈ parameterDrops base modes remaining,
      drop.uses = .many ∨ drop.uses = .affine) :
    ParameterDropsAdmissible modes remaining := by
  induction modes generalizing base with
  | nil => trivial
  | cons mode modes ih =>
    constructor
    · apply ih (base + 1)
      intro drop hdrop
      apply hdrops drop
      simpa [parameterDrops] using
        List.mem_append_left
          (if remaining modes.length == 0 then
            [⟨modes.length, base, mode⟩]
          else []) hdrop
    · intro hzero
      apply hdrops ⟨modes.length, base, mode⟩
      simp [parameterDrops, hzero]

/-- Successful execution of the compiler-generated parameter release list
is itself the missing admissibility certificate. -/
theorem parameterDropsAdmissible_of_releaseSlots_run
    (base : Nat) (modes : List Uses) (remaining : Nat → Nat)
    {input output : VEnv} {emit : Emit} {state finalState : LowSt}
    (hrun : (releaseSlots input (parameterDrops base modes remaining)).run
      state = .ok (output, emit) finalState) :
    ParameterDropsAdmissible modes remaining :=
  parameterDropsAdmissible_of_drop_admissible base modes remaining
    (releaseSlots_run_drop_admissible hrun)

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
  exact releaseAll_traverse_core
    (Result := fun initial _ output _ =>
      output.entries = initial.entries)
    (hnil := fun _ => rfl)
    (hconst := fun htail => htail)
    (hslot := by
      intro initial abs rest output tailEmit htail
      simpa [VEnv.bump] using htail)
    input values

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
  intro captures input output state finalState emit values hrun
  apply lowerCaptures_run_core
    (Result := fun input output captures _ _ =>
      EntryConsumption input output (captureUseCount expr captures))
    (e := expr) (hrun := hrun)
  · intro input
    rw [captureUseCount_nil]
    exact EntryConsumption.zero input
  · intro captured rest input middle output headEmit tailEmit headValue
      tailValues state middleState hheadRun htail
    have hcomposed :=
      (lowerCapture_consumesEntries hheadRun).comp htail
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
  apply lowerLam_run_core
    (Result := fun _ output _ _ =>
      EntryConsumption input output (fun index => countUses index expr))
    (hrun := hrun)
  intro _bodyFuel captureOutput captureEmit captureValues captureState
    _fnAddr _addressState _code _bodyState _hfuel _hp hcaptureRun _hfreshRun
    _hbodyRun
  have hselected :
      (lowerCaptures expr input
        ((List.range input.entries.length).filter
          (fun index => countUses index expr > 0))).run state =
        .ok (captureOutput, captureEmit, captureValues) captureState := by
    simpa [liftCaptureIndices] using hcaptureRun
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

/-- Shared compiler-fuel recursion for reachable semantic and progress
clusters.  The cluster fields and their one-step constructors are predicate
parameters, so the zero case, the special spine-at-one case, and the
two-predecessor successor case are assembled once without identifying any
public interface or proof flavor. -/
theorem lowerValueClusterWithin_core
    {Expr Borrow Spine Args ApplyRest Cluster : Nat → Prop}
    (hzero : Cluster 0)
    (hclusterExpr : ∀ {fuel}, Cluster fuel → Expr fuel)
    (hclusterBorrow : ∀ {fuel}, Cluster fuel → Borrow fuel)
    (hclusterSpine : ∀ {fuel}, Cluster fuel → Spine fuel)
    (hclusterArgs : ∀ {fuel}, Cluster fuel → Args fuel)
    (hclusterApplyRest : ∀ {fuel}, Cluster fuel → ApplyRest fuel)
    (hmake : ∀ {fuel}, Expr fuel → Borrow fuel → Spine fuel →
      Args fuel → ApplyRest fuel → Cluster fuel)
    (hargsSucc : ∀ {fuel}, Expr fuel → Args fuel → Args (fuel + 1))
    (happlyRestSucc : ∀ {fuel}, Args fuel → ApplyRest (fuel + 1))
    (hborrowSucc : ∀ {fuel}, Expr fuel → Borrow (fuel + 1))
    (hspineOne : Spine 1)
    (hspineSucc : ∀ {fuel},
      Spine (fuel + 1) → Expr (fuel + 1) → Args fuel →
      ApplyRest fuel → ApplyRest (fuel + 1) → Spine (fuel + 2))
    (hexprSucc : ∀ {fuel},
      Expr fuel → Spine fuel → Borrow fuel → Args (fuel + 1) →
      ApplyRest (fuel + 1) → Expr (fuel + 1)) :
    ∀ fuel, Cluster fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    cases fuel with
    | zero => exact hzero
    | succ previous =>
      have hprev : Cluster previous :=
        ih previous (Nat.lt_succ_self previous)
      have hargs : Args (previous + 1) :=
        hargsSucc (hclusterExpr hprev) (hclusterArgs hprev)
      have hrest : ApplyRest (previous + 1) :=
        happlyRestSucc (hclusterArgs hprev)
      have hborrow : Borrow (previous + 1) :=
        hborrowSucc (hclusterExpr hprev)
      have hspine : Spine (previous + 1) := by
        cases previous with
        | zero => exact hspineOne
        | succ prior =>
          have hprior : Cluster prior := ih prior (by omega)
          exact hspineSucc (hclusterSpine hprev) (hclusterExpr hprev)
            (hclusterArgs hprior) (hclusterApplyRest hprior)
            (hclusterApplyRest hprev)
      exact hmake
        (hexprSucc (hclusterExpr hprev) (hclusterSpine hprev)
          (hclusterBorrow hprev) hargs hrest)
        hborrow hspine hargs hrest

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
    ∀ fuel, LowerClusterPreservesBelow ctx cur limit src fuel :=
  lowerValueClusterWithin_core
    (Expr := LowerEPreservesBelow ctx cur limit src)
    (Borrow := LowerBorrowPreservesBelow ctx cur limit src)
    (Spine := LowerSpinePreservesBelow ctx cur limit src)
    (Args := LowerArgsPreservesBelow ctx cur limit src)
    (ApplyRest := ApplyRestPreservesBelow ctx cur limit src)
    (Cluster := LowerClusterPreservesBelow ctx cur limit src)
    (hzero := {
      expr := lowerEPreservesBelow_zero
      borrow := lowerBorrowPreservesBelow_zero
      spine := lowerSpinePreservesBelow_zero
      args := lowerArgsPreservesBelow_zero
      applyRest := applyRestPreservesBelow_zero })
    (hclusterExpr := fun hcluster => hcluster.expr)
    (hclusterBorrow := fun hcluster => hcluster.borrow)
    (hclusterSpine := fun hcluster => hcluster.spine)
    (hclusterArgs := fun hcluster => hcluster.args)
    (hclusterApplyRest := fun hcluster => hcluster.applyRest)
    (hmake := fun hexpr hborrow hspine hargs hrest => {
      expr := hexpr
      borrow := hborrow
      spine := hspine
      args := hargs
      applyRest := hrest })
    (hargsSucc := by
      intro fuel hexpr hargs
      exact lowerArgsPreservesBelow_succ hexpr hargs
        (lowerExtraMonotone src fuel).args)
    (happlyRestSucc := fun hargs =>
      applyRestPreservesBelow_succ hargs happly)
    (hborrowSucc := fun hexpr =>
      lowerBorrowPreservesBelow_succ hexpr)
    (hspineOne := lowerSpinePreservesBelow_one)
    (hspineSucc := by
      intro fuel hprevSpine hprevExpr hpriorArgs hpriorRest hprevRest
      intro input world head args state finalState output emit av hrun
        hrepresented havailable
      exact lowerSpine_run_sound_below hprevSpine hprevExpr hpriorArgs
        (lowerExtraMonotone src fuel).args hpriorRest hprevRest
        (lowerExtraMonotone src fuel).applyRest
        (lowerExtraMonotone src (fuel + 1)).applyRest hdecls hrun
        hrepresented havailable)
    (hexprSucc := by
      intro fuel hprevExpr hprevSpine hprevBorrow hargs hrest
      intro input world expr state finalState output emit av hrun
        hrepresented havailable
      exact lowerE_run_sound_below hprevExpr hprevSpine hargs
        (lowerExtraMonotone src (fuel + 1)).args hrest
        (lowerExtraMonotone src (fuel + 1)).applyRest hprevBorrow
        hdecls (fun body => lowerE_releasesTrackedFirst src fuel body)
        hrepresented hrun havailable)

/-! ### Closed reachable-state value induction -/

/-- At compiler fuel one, `lowerSpine` still cannot complete: every branch
reaches a zero-fuel recursive action first. This is the semantic companion
to `lowerSpinePreservesBelow_one`. -/
theorem lowerSpineValuePreservesWithin_one
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {cur : FnDef}
    {src : IxIR0.Env} {ambient : LowSt} :
    LowerSpineValuePreservesWithin funRel recSelfRel sourceCtx ctx cur src
      ambient 1 := by
  intro input output world head args sourceEnv sourceResult state finalState
    emit av _ hrun _ _
  exact (lowerSpine_noSuccess_one src input world head args hrun).elim

/-- The complete reachable-state semantic invariant for the mutually
recursive lowering cluster at one compiler-fuel index. All function
provenance is indexed by the ambient state of the enclosing whole-pass run;
individual successful subruns supply only an `ExtraExtends` suffix proof. -/
structure LowerValueClusterWithin
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ambient : LowSt)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (fuel : Nat) : Prop where
  expr : LowerEValuePreservesWithin
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur src ambient fuel
  borrow : LowerBorrowValuePreservesWithin
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur src ambient fuel
  spine : LowerSpineValuePreservesWithin
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur src ambient fuel
  args : LowerArgsValuePreservesWithin
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur src ambient fuel
  applyRest : ApplyRestNonErasedValuePreservesWithin
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur src ambient fuel

/-- Complete compiler-fuel induction for value correspondence. The static
declaration and higher-order application hypotheses are semantic contracts
of the final target context; compiler recursion, erased reflection, let
cleanup, and generated-declaration reachability are all discharged here. -/
theorem lowerValueClusterWithin
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx) :
    ∀ fuel,
      LowerValueClusterWithin sourceCtx src ambient recSelfRel ctx cur fuel :=
  lowerValueClusterWithin_core
    (Expr := LowerEValuePreservesWithin
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur src ambient)
    (Borrow := LowerBorrowValuePreservesWithin
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur src ambient)
    (Spine := LowerSpineValuePreservesWithin
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur src ambient)
    (Args := LowerArgsValuePreservesWithin
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur src ambient)
    (ApplyRest := ApplyRestNonErasedValuePreservesWithin
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur src ambient)
    (Cluster := LowerValueClusterWithin sourceCtx src ambient recSelfRel ctx
      cur)
    (hzero := {
      expr := lowerEValuePreservesWithin_zero src ambient
      borrow := lowerBorrowValuePreservesWithin_zero src ambient
      spine := lowerSpineValuePreservesWithin_zero src ambient
      args := lowerArgsValuePreservesWithin_zero src ambient
      applyRest := applyRestNonErasedValuePreservesWithin_zero src ambient })
    (hclusterExpr := fun hcluster => hcluster.expr)
    (hclusterBorrow := fun hcluster => hcluster.borrow)
    (hclusterSpine := fun hcluster => hcluster.spine)
    (hclusterArgs := fun hcluster => hcluster.args)
    (hclusterApplyRest := fun hcluster => hcluster.applyRest)
    (hmake := fun hexpr hborrow hspine hargs hrest => {
      expr := hexpr
      borrow := hborrow
      spine := hspine
      args := hargs
      applyRest := hrest })
    (hargsSucc := fun hexpr hargs =>
      lowerArgsValuePreservesWithin_succ hexpr hargs)
    (happlyRestSucc := fun hargs =>
      applyRestNonErasedValuePreservesWithin_succ hargs
        hcontracts.apply hvalues.apply)
    (hborrowSucc := fun hexpr =>
      lowerBorrowValuePreservesWithin_succ hexpr)
    (hspineOne := lowerSpineValuePreservesWithin_one)
    (hspineSucc := by
      intro fuel hprevSpine hprevExpr hpriorArgs hpriorRest hprevRest
      intro input output world head args sourceEnv sourceResult state
        finalState emit av hsource hrun hextends havailable
      exact lowerSpine_run_value_sound_within (fuel := fuel) henv
        hprevSpine hprevExpr
        (lowerE_reflectsErased sourceCtx src (fuel + 1)) hpriorArgs
        hpriorRest hprevRest
        (lowerExtraMonotone src (fuel + 1)).knownCall hcontracts hvalues
        hsource hrun hextends hrepresented havailable)
    (hexprSucc := by
      intro fuel hprevExpr hprevSpine hprevBorrow hargs hrest
      intro input output world expr sourceEnv sourceFuel sourceValue state
        finalState emit av hsource hrun hextends havailable
      exact lowerE_run_value_sound_within (fuel := fuel) henv hprevExpr
        hprevSpine hprevBorrow hargs hrest
        (lowerExtraMonotone src (fuel + 2)).knownCall hcontracts hvalues
        (fun body => lowerE_releasesTrackedFirst src fuel body)
        hsource hrun hextends hrepresented havailable)

/-- At compiler fuel one, the bounded semantic spine interface is likewise
vacuous because every executable branch reaches a zero-fuel subaction. -/
theorem lowerSpineValuePreservesWithinBelow_one
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {src : IxIR0.Env} {ambient : LowSt} :
    LowerSpineValuePreservesWithinBelow funRel recSelfRel sourceCtx ctx cur
      limit src ambient 1 := by
  intro input output world head args sourceEnv sourceResult state finalState
    emit av _ hrun _ _
  exact (lowerSpine_noSuccess_one src input world head args hrun).elim

/-- Fuel-bounded reachable-state semantic invariant for the complete
mutually recursive lowering cluster. -/
structure LowerValueClusterWithinBelow
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ambient : LowSt)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (limit fuel : Nat) : Prop where
  expr : LowerEValuePreservesWithinBelow
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur limit src ambient fuel
  borrow : LowerBorrowValuePreservesWithinBelow
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur limit src ambient fuel
  spine : LowerSpineValuePreservesWithinBelow
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur limit src ambient fuel
  args : LowerArgsValuePreservesWithinBelow
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur limit src ambient fuel
  applyRest : ApplyRestNonErasedValuePreservesWithinBelow
    (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
    cur limit src ambient fuel

/-- Complete compiler-fuel induction under semantic contracts bounded at a
single target evaluator limit. This is the contractive cluster used while
the declaration and higher-order apply contracts themselves are sealed. -/
theorem lowerValueClusterWithinBelow
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit) :
    ∀ fuel, LowerValueClusterWithinBelow sourceCtx src ambient recSelfRel
      ctx cur limit fuel :=
  lowerValueClusterWithin_core
    (Expr := LowerEValuePreservesWithinBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit src ambient)
    (Borrow := LowerBorrowValuePreservesWithinBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit src ambient)
    (Spine := LowerSpineValuePreservesWithinBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit src ambient)
    (Args := LowerArgsValuePreservesWithinBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit src ambient)
    (ApplyRest := ApplyRestNonErasedValuePreservesWithinBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit src ambient)
    (Cluster := LowerValueClusterWithinBelow sourceCtx src ambient
      recSelfRel ctx cur limit)
    (hzero := {
      expr := lowerEValuePreservesWithinBelow_zero src ambient
      borrow := lowerBorrowValuePreservesWithinBelow_zero src ambient
      spine := lowerSpineValuePreservesWithinBelow_zero src ambient
      args := lowerArgsValuePreservesWithinBelow_zero src ambient
      applyRest :=
        applyRestNonErasedValuePreservesWithinBelow_zero src ambient })
    (hclusterExpr := fun hcluster => hcluster.expr)
    (hclusterBorrow := fun hcluster => hcluster.borrow)
    (hclusterSpine := fun hcluster => hcluster.spine)
    (hclusterArgs := fun hcluster => hcluster.args)
    (hclusterApplyRest := fun hcluster => hcluster.applyRest)
    (hmake := fun hexpr hborrow hspine hargs hrest => {
      expr := hexpr
      borrow := hborrow
      spine := hspine
      args := hargs
      applyRest := hrest })
    (hargsSucc := fun hexpr hargs =>
      lowerArgsValuePreservesWithinBelow_succ hexpr hargs)
    (happlyRestSucc := fun hargs =>
      applyRestNonErasedValuePreservesWithinBelow_succ hargs
        (hcontracts.apply.below limit) hvalues.apply)
    (hborrowSucc := fun hexpr =>
      lowerBorrowValuePreservesWithinBelow_succ hexpr)
    (hspineOne := lowerSpineValuePreservesWithinBelow_one)
    (hspineSucc := by
      intro fuel hprevSpine hprevExpr hpriorArgs hpriorRest hprevRest
      intro input output world head args sourceEnv sourceResult state
        finalState emit av hsource hrun hextends havailable
      exact lowerSpine_run_value_sound_within_below (fuel := fuel) henv
        hprevSpine hprevExpr
        (lowerE_reflectsErased sourceCtx src (fuel + 1)) hpriorArgs
        hpriorRest hprevRest
        (lowerExtraMonotone src (fuel + 1)).knownCall hcontracts hvalues
        hsource hrun hextends hrepresented havailable)
    (hexprSucc := by
      intro fuel hprevExpr hprevSpine hprevBorrow hargs hrest
      intro input output world expr sourceEnv sourceFuel sourceValue state
        finalState emit av hsource hrun hextends havailable
      exact lowerE_run_value_sound_within_below (fuel := fuel) henv
        hprevExpr hprevSpine hprevBorrow hargs hrest
        (lowerExtraMonotone src (fuel + 2)).knownCall hcontracts hvalues
        (fun body => lowerE_releasesTrackedFirst src fuel body)
        hsource hrun hextends hrepresented havailable)

/-- Bounded ordinary-expression interface with no recursive-self entry. -/
theorem lowerE_run_value_sound_within_noRecSelf_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {sourceEnv : List IxIR0.Value}
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hsource : IxIR0.eval sourceCtx sourceFuel sourceEnv expr =
      .ok sourceValue)
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState)
    (hextends : ExtraExtends finalState ambient)
    (hno : NoRecSelf input) :
    LowerResultValueSoundBelow (CompilerFunctionRel sourceCtx src ambient)
      recSelfRel ctx cur limit input output sourceEnv sourceEnv sourceValue
      world emit av :=
  (lowerValueClusterWithinBelow (recSelfRel := recSelfRel) (cur := cur)
    henv hrepresented hcontracts hvalues fuel).expr hsource hrun hextends
      (SelfValueAvailableBelow.of_noRecSelf hno)

/-- Bounded recursor-rule expression interface with current-self semantics. -/
theorem lowerE_run_value_sound_within_currentSelf_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {sourceEnv : List IxIR0.Value}
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hsource : IxIR0.eval sourceCtx sourceFuel sourceEnv expr =
      .ok sourceValue)
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState)
    (hextends : ExtraExtends finalState ambient)
    (hself : CurrentSelfValueContractBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit) :
    LowerResultValueSoundBelow (CompilerFunctionRel sourceCtx src ambient)
      recSelfRel ctx cur limit input output sourceEnv sourceEnv sourceValue
      world emit av :=
  (lowerValueClusterWithinBelow (recSelfRel := recSelfRel) (cur := cur)
    henv hrepresented hcontracts hvalues fuel).expr hsource hrun hextends
      (SelfValueAvailableBelow.of_contract hself)

/-- Ordinary expressions expose the closed semantic compiler induction
without requiring a current recursive-self contract. -/
theorem lowerE_run_value_sound_within_noRecSelf
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx)
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {sourceEnv : List IxIR0.Value}
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hsource : IxIR0.eval sourceCtx sourceFuel sourceEnv expr =
      .ok sourceValue)
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState)
    (hextends : ExtraExtends finalState ambient)
    (hno : NoRecSelf input) :
    LowerResultValueSound (CompilerFunctionRel sourceCtx src ambient)
      recSelfRel ctx cur input output sourceEnv sourceEnv sourceValue world
      emit av :=
  (lowerValueClusterWithin (recSelfRel := recSelfRel) (cur := cur) henv
    hrepresented hcontracts hvalues fuel).expr hsource hrun hextends
      (SelfValueAvailable.of_noRecSelf hno)

/-- Recursor-rule expressions use the same closed semantic induction with
the generated current-function value contract. -/
theorem lowerE_run_value_sound_within_currentSelf
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx)
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {sourceEnv : List IxIR0.Value}
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    {state finalState : LowSt} {emit : Emit} {av : AVal}
    (hsource : IxIR0.eval sourceCtx sourceFuel sourceEnv expr =
      .ok sourceValue)
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState)
    (hextends : ExtraExtends finalState ambient)
    (hself : CurrentSelfValueContract
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur) :
    LowerResultValueSound (CompilerFunctionRel sourceCtx src ambient)
      recSelfRel ctx cur input output sourceEnv sourceEnv sourceValue world
      emit av :=
  (lowerValueClusterWithin (recSelfRel := recSelfRel) (cur := cur) henv
    hrepresented hcontracts hvalues fuel).expr hsource hrun hextends
      (SelfValueAvailable.of_contract hself)

/-! ### Source saturation lemmas for declaration contracts -/

/-- Evaluating an expression and then supplying exactly its leading lambda
telescope is the same source computation as evaluating `stripLams` in the
reversed argument environment. Fuel witnesses remain existential because
source fuel is a totality witness, not a cost. -/
theorem sourceEval_stripLams_of_applies (sourceCtx : IxIR0.Ctx) :
    ∀ {sourceEnv : List IxIR0.Value} {expr : IxIR0.Expr}
      {function result : IxIR0.Value} {args : List IxIR0.Value}
      {evalFuel : Nat},
      IxIR0.eval sourceCtx evalFuel sourceEnv expr = .ok function →
      args.length = lamArity expr →
      SourceApplies sourceCtx function args result →
      ∃ bodyFuel,
        IxIR0.eval sourceCtx bodyFuel (args.reverse ++ sourceEnv)
          (stripLams expr) = .ok result := by
  intro sourceEnv expr
  induction expr generalizing sourceEnv with
  | var index =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩
  | ref address =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩
  | app fn arg =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩
  | lam uses body ih =>
    intro function result args evalFuel heval hlength happlies
    cases evalFuel with
    | zero => simp [IxIR0.eval] at heval
    | succ evalFuel =>
      have hfunction : function = .clos uses sourceEnv body := by
        simpa [IxIR0.eval] using heval.symm
      subst function
      cases args with
      | nil => simp [lamArity] at hlength
      | cons argument arguments =>
        have htailLength : arguments.length = lamArity body := by
          simpa [lamArity] using hlength
        cases happlies with
        | @cons _ _ middle _ _ applyFuel hstep htail =>
          cases applyFuel with
          | zero => simp [IxIR0.apply] at hstep
          | succ applyFuel =>
            have hbodyEval : IxIR0.eval sourceCtx applyFuel
                (argument :: sourceEnv) body = .ok middle := by
              simpa [IxIR0.apply] using hstep
            obtain ⟨bodyFuel, hresult⟩ :=
              ih hbodyEval htailLength htail
            refine ⟨bodyFuel, ?_⟩
            simpa [stripLams, List.reverse_cons, List.append_assoc] using
              hresult
  | letE uses value body =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩
  | proj index value =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩
  | lit literal =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩
  | erased =>
    intro function result args evalFuel heval hlength happlies
    have hnil : args = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [lamArity] using hlength)
    subst args
    cases happlies
    exact ⟨evalFuel, by simpa [stripLams] using heval⟩

/-- Complete a residual lifted-closure prefix with the remaining arguments.
The resulting source environment is exactly the selected prefix's full
application order reversed, followed by the original closure environment. -/
theorem LambdaPrefix.saturate
    {sourceCtx : IxIR0.Ctx} {sourceEnv : List IxIR0.Value}
    {expr : IxIR0.Expr} {supplied remaining : List IxIR0.Value}
    {function result : IxIR0.Value}
    (hprefix : LambdaPrefix sourceEnv expr supplied function)
    (hlength : (supplied ++ remaining).length = lamArity expr)
    (happlies : SourceApplies sourceCtx function remaining result) :
    ∃ fuel,
      IxIR0.eval sourceCtx fuel
        ((supplied ++ remaining).reverse ++ sourceEnv)
        (stripLams expr) = .ok result := by
  exact (LambdaPrefix.traverse
    (Result := fun currentEnv currentExpr currentSupplied currentFunction =>
      (currentSupplied ++ remaining).length = lamArity currentExpr →
      SourceApplies sourceCtx currentFunction remaining result →
      ∃ fuel,
        IxIR0.eval sourceCtx fuel
          ((currentSupplied ++ remaining).reverse ++ currentEnv)
          (stripLams currentExpr) = .ok result)
    (hnil := by
      intro currentEnv uses body hlength happlies
      have heval : IxIR0.eval sourceCtx 1 currentEnv (.lam uses body) =
          .ok (.clos uses currentEnv body) := by
        simp [IxIR0.eval]
      simpa using sourceEval_stripLams_of_applies sourceCtx heval
        (by simpa using hlength) happlies)
    (hcons := by
      intro currentEnv uses body argument currentSupplied currentFunction
        hinner ih hlength happlies
      have hinnerLength : (currentSupplied ++ remaining).length =
          lamArity body := by
        simpa [lamArity] using hlength
      obtain ⟨fuel, hresult⟩ := ih hinnerLength happlies
      refine ⟨fuel, ?_⟩
      simpa [stripLams, List.reverse_cons, List.append_assoc] using hresult)
    (h := hprefix)) hlength happlies

/-- A source definition reference exposes the exact closed evaluation of its
body, independent of the existential reference fuel. -/
theorem SourceRefValue.defnBody
    {sourceCtx : IxIR0.Ctx} {address : Ixon.Address}
    {world : Owned} {body : IxIR0.Expr} {function : IxIR0.Value}
    (hlookup : sourceCtx.env address = some (.defn world body))
    (href : SourceRefValue sourceCtx address function) :
    ∃ fuel, IxIR0.eval sourceCtx fuel [] body = .ok function := by
  obtain ⟨fuel, href⟩ := href
  cases fuel with
  | zero => simp [IxIR0.eval] at href
  | succ fuel =>
    exact ⟨fuel, by simpa [IxIR0.eval, hlookup] using href⟩

/-- Saturating a source definition reference reaches its stripped body under
the reversed source argument vector. -/
theorem SourceRefValue.defnSaturate
    {sourceCtx : IxIR0.Ctx} {address : Ixon.Address}
    {world : Owned} {body : IxIR0.Expr}
    {function result : IxIR0.Value} {args : List IxIR0.Value}
    (hlookup : sourceCtx.env address = some (.defn world body))
    (href : SourceRefValue sourceCtx address function)
    (hlength : args.length = lamArity body)
    (happlies : SourceApplies sourceCtx function args result) :
    ∃ fuel, IxIR0.eval sourceCtx fuel args.reverse
      (stripLams body) = .ok result := by
  obtain ⟨evalFuel, heval⟩ := href.defnBody hlookup
  simpa using sourceEval_stripLams_of_applies sourceCtx heval hlength
    happlies

/-! ### Semantic function closure -/

/-- Closing a semantic lowering result with its generated `ret` exposes the
source result graph and preserves an arbitrary semantic caller frame. This
is the value-level counterpart of `LowerResultSound.close`; ownership of the
returned root remains available through the parent judgment when needed. -/
theorem LowerResultValueSound.closeGraph
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {world : Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceInput sourceOutput sourceValue world emit av)
    (hreleased : EntriesReleased output.entries)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root) :
    CodeOwns ctx cur
      (GraphOwnsVEnv funRel recSelfRel input sourceInput sourceRest rest)
      (fun store value =>
        Sim.ValueGraph funRel store sourceValue value ∧
          Sim.RootsGraph funRel store sourceRest rest)
      (emit (.ret (av.toAtom output))) := by
  have hret : CodeOwns ctx cur
      (GraphOwnsResultProtected funRel recSelfRel output sourceOutput
        sourceValue world av sourceRest rest [])
      (fun store value =>
        Sim.ValueGraph funRel store sourceValue value ∧
          Sim.RootsGraph funRel store sourceRest rest)
      (.ret (av.toAtom output)) := by
    intro fuel store env store' value hprotected hrun
    obtain ⟨⟨roots, result, houtput, hav, hvalue, hframe, _⟩, _⟩ :=
      hprotected
    have hroots : roots = [] :=
      EntriesRealize.eq_nil_of_released hreleased
        houtput.entries.entriesRealize
    subst roots
    cases fuel with
    | zero => simp [runCode] at hrun
    | succ fuel =>
      rw [Nat.add_one] at hrun
      rw [runCode.eq_def] at hrun
      dsimp only at hrun
      rw [hav.resolveAtom] at hrun
      have hpair : (store, result) = (store', value) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨hvalue, hframe⟩
  intro fuel store env store' value hpre hrun
  exact hsound.graphEmits sourceRest rest []
    (fun store value =>
      Sim.ValueGraph funRel store sourceValue value ∧
        Sim.RootsGraph funRel store sourceRest rest)
    (.ret (av.toAtom output)) hret
    ⟨hpre, SlotsRealize.nil⟩ hrun

/-- Bounded counterpart of `closeGraph`; this is the function-exit rule used
while mutually recursive declaration contracts are available only below the
current evaluator index. -/
theorem LowerResultValueSoundBelow.closeGraph
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {world : Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultValueSoundBelow funRel recSelfRel ctx cur limit
      input output sourceInput sourceOutput sourceValue world emit av)
    (hreleased : EntriesReleased output.entries)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root) :
    CodeOwnsBelow ctx cur limit
      (GraphOwnsVEnv funRel recSelfRel input sourceInput sourceRest rest)
      (fun store value =>
        Sim.ValueGraph funRel store sourceValue value ∧
          Sim.RootsGraph funRel store sourceRest rest)
      (emit (.ret (av.toAtom output))) := by
  have hret : CodeOwnsBelow ctx cur limit
      (GraphOwnsResultProtected funRel recSelfRel output sourceOutput
        sourceValue world av sourceRest rest [])
      (fun store value =>
        Sim.ValueGraph funRel store sourceValue value ∧
          Sim.RootsGraph funRel store sourceRest rest)
      (.ret (av.toAtom output)) := by
    intro fuel store env store' value _ hprotected hrun
    obtain ⟨⟨roots, result, houtput, hav, hvalue, hframe, _⟩, _⟩ :=
      hprotected
    have hroots : roots = [] :=
      EntriesRealize.eq_nil_of_released hreleased
        houtput.entries.entriesRealize
    subst roots
    cases fuel with
    | zero => simp [runCode] at hrun
    | succ fuel =>
      rw [Nat.add_one] at hrun
      rw [runCode.eq_def] at hrun
      dsimp only at hrun
      rw [hav.resolveAtom] at hrun
      have hpair : (store, result) = (store', value) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨hvalue, hframe⟩
  intro fuel store env store' value hfuel hpre hrun
  exact hsound.graphEmits sourceRest rest [] limit (Nat.le_refl _)
    (fun store value =>
      Sim.ValueGraph funRel store sourceValue value ∧
        Sim.RootsGraph funRel store sourceRest rest)
    (.ret (av.toAtom output)) hret hfuel
    ⟨hpre, SlotsRealize.nil⟩ hrun

/-- Contractive function-entry/exit adapter. A bounded expression theorem
for the lowered body is enough to prove the function at the bound itself;
all declaration/apply dependencies used by that expression theorem may
therefore remain strictly below the bound. -/
theorem lowerFnBody_parameterEntries_valuePreservesAt_below
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {src : IxIR0.Env}
    {compilerFuel limit : Nat}
    (modes : List Uses) (world : Owned) (body : IxIR0.Expr)
    {state finalState : LowSt} {code : Code} {papSafeFlag : Bool}
    (hbodyPreserves : LowerEValuePreservesBelow funRel recSelfRel
      sourceCtx ctx ⟨modes.length, world, papSafeFlag, code⟩
        limit src compilerFuel)
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hrun : (lowerFnBody src (compilerFuel + 1)
      ⟨parameterEntries 0 modes (fun index => countUses index body),
        modes.length⟩
      (parameterDrops 0 modes (fun index => countUses index body))
      world body).run state = .ok code finalState)
    {sourceFunction : IxIR0.Value}
    (hsaturates : ∀ {sourceArgs : List IxIR0.Value}
        {sourceResult : IxIR0.Value},
      sourceArgs.length = modes.length →
      SourceApplies sourceCtx sourceFunction sourceArgs sourceResult →
      ∃ sourceFuel,
        IxIR0.eval sourceCtx sourceFuel sourceArgs.reverse body =
          .ok sourceResult) :
    FnValuePreservesAt funRel sourceCtx ctx
      ⟨modes.length, world, papSafeFlag, code⟩ (modes.map worldOfUses)
      sourceFunction limit := by
  let remaining : Nat → Nat := fun index => countUses index body
  let input : VEnv :=
    ⟨parameterEntries 0 modes remaining, modes.length⟩
  let drops := parameterDrops 0 modes remaining
  have hrun' :
      (lowerFnBody src (compilerFuel + 1) input drops world body).run state =
        .ok code finalState := by
    simpa [input, drops, remaining] using hrun
  simp only [lowerFnBody] at hrun'
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun'
  rcases releaseResult with ⟨middle, releaseEmit⟩
  obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
    trackedBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, emit, av⟩
  have hpure :
      (releaseEmit ∘ emit) (.ret (av.toAtom output)) = code ∧
        bodyState = finalState := by
    simpa using hafterBody
  obtain ⟨hcode, hbodyState⟩ := hpure
  subst bodyState
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
  have hmiddle : plannedMiddle = middle := congrArg Prod.fst heq.1
  have hemit : plannedEmit = releaseEmit := congrArg Prod.snd heq.1
  subst middle
  subst releaseEmit
  cases heq.2
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have hmiddleLength : plannedMiddle.entries.length = modes.length := by
    calc
      plannedMiddle.entries.length = input.entries.length :=
        hplan'.entries_length
      _ = modes.length := by simp [input, remaining]
  have hreleased : EntriesReleased output.entries :=
    hconsume.entriesReleased htracks (Eq.trans hcount hmiddleLength)
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  have hargsLength : args.length = modes.length := by
    simpa using hlength
  have hsourceArgsLength : sourceArgs.length = args.length := by
    simpa using hargs.length
  obtain ⟨sourceFuel, hsource⟩ := hsaturates
    (hsourceArgsLength.trans hargsLength) happlies
  have hbodySound : LowerResultValueSoundBelow funRel recSelfRel ctx
      ⟨modes.length, world, papSafeFlag, code⟩ limit plannedMiddle output
      sourceArgs.reverse sourceArgs.reverse sourceResult world emit av :=
    hbodyPreserves hsource hbodyRun
  have hfull : LowerResultValueSoundBelow funRel recSelfRel ctx
      ⟨modes.length, world, papSafeFlag, code⟩ limit input output
      sourceArgs.reverse sourceArgs.reverse sourceResult world
      (plannedEmit ∘ emit) av :=
    hbodySound.afterRelease (hplan'.valueSoundBelow sourceArgs.reverse)
  have hpre : GraphOwnsVEnv funRel recSelfRel input sourceArgs.reverse
      sourceRest rest store args.reverse := by
    refine ⟨(rootsForWorlds (modes.map worldOfUses) args).reverse,
      ?_, hframe, ?_⟩
    · simpa [input] using VEnvValueGraph.parameterEntries
        (recSelfRel := recSelfRel) modes remaining hargsLength hargs hown
    · exact hown.perm
        ((List.reverse_perm
          (rootsForWorlds (modes.map worldOfUses) args)).symm.append_right
            rest)
  have hcodeRun' : runCode ctx limit
      ⟨modes.length, world, papSafeFlag, code⟩ store args.reverse
      ((plannedEmit ∘ emit) (.ret (av.toAtom output))) =
        .ok (store', value) := by
    rw [hcode]
    exact hcodeRun
  exact hfull.closeGraph hreleased sourceRest rest (Nat.le_refl _)
    hpre hcodeRun'

/-- Contractive ordinary-declaration producer. Once the bounded expression
induction is available for the actual emitted function, this proves that
function at the current evaluator bound without assuming its own unbounded
semantic contract. -/
theorem lowerDecl_defn_valuePreservesAt_below
    {funRel : Sim.FunctionRel} {sourceCtx : IxIR0.Ctx}
    {src : IxIR0.Env} {ctx : Ctx} {compilerFuel limit : Nat}
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {d : FnDef}
    {sourceFunction : IxIR0.Value}
    (hlookup : sourceCtx.env address = some (.defn result body))
    (href : SourceRefValue sourceCtx address sourceFunction)
    (hbodyPreserves : LowerEValuePreservesBelow funRel
      (fun _ _ => False) sourceCtx ctx d limit src compilerFuel)
    (hadmissible : ParameterDropsAdmissible (lamUses body)
      (fun index => countUses index (stripLams body)))
    (hrun : (lowerDecl src (compilerFuel + 1)
      (address, .defn result body)).run state =
        .ok (some (address, .fn d)) finalState) :
    FnValuePreservesAt funRel sourceCtx ctx d
      ((lamUses body).map worldOfUses) sourceFunction limit := by
  simp only [lowerDecl] at hrun
  obtain ⟨code, bodyState, hbodyRun, hpureRun⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩) =
          some (address, Decl.fn d) ∧
        bodyState = finalState := by
    simpa using hpureRun
  have hd : d = ⟨lamArity body, result,
      result == .shared && papSafe body, code⟩ := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2.symm
  cases hpure.2
  subst d
  have hbodyPreserves' : LowerEValuePreservesBelow funRel
      (fun _ _ => False) sourceCtx ctx
      ⟨(lamUses body).length, result,
        result == .shared && papSafe body, code⟩ limit src compilerFuel := by
    intro input output world expr sourceEnv sourceFuel sourceValue
      state finalState emit av hsource hrun
    simpa using hbodyPreserves hsource hrun
  have hpreserves : FnValuePreservesAt funRel sourceCtx ctx
      ⟨(lamUses body).length, result,
        result == .shared && papSafe body, code⟩
      ((lamUses body).map worldOfUses) sourceFunction limit :=
    lowerFnBody_parameterEntries_valuePreservesAt_below
      (recSelfRel := fun _ _ => False)
      (compilerFuel := compilerFuel) (limit := limit)
      (lamUses body) result (stripLams body) hbodyPreserves'
      hadmissible (by simpa using hbodyRun)
      (by
        intro sourceArgs sourceResult hlength happlies
        exact href.defnSaturate hlookup (by simpa using hlength) happlies)
  have hfn : (⟨(lamUses body).length, result,
      result == .shared && papSafe body, code⟩ : FnDef) =
      ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩ := by
    rw [lamUses_length]
  rw [← hfn]
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  exact hpreserves hlength hargs happlies hframe hown hcodeRun

/-- Reachable-state specialization of the contractive function-entry
adapter.  Unlike `lowerFnBody_parameterEntries_valuePreservesAt_below`, this
version follows the one actual body run into the ambient final lowering
state.  That is the shape supplied by `lowerAllAction`: generated function
provenance is only known in the final accumulated state, and
`ExtraExtends` transports it back to this particular body run. -/
theorem lowerFnBody_parameterEntries_valuePreservesAt_within_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx}
    {compilerFuel limit : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    (modes : List Uses) (world : Owned) (body : IxIR0.Expr)
    {state finalState : LowSt} {code : Code} {papSafeFlag : Bool}
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hrun : (lowerFnBody src (compilerFuel + 1)
      ⟨parameterEntries 0 modes (fun index => countUses index body),
        modes.length⟩
      (parameterDrops 0 modes (fun index => countUses index body))
      world body).run state = .ok code finalState)
    (hextends : ExtraExtends finalState ambient)
    {sourceFunction : IxIR0.Value}
    (hsaturates : ∀ {sourceArgs : List IxIR0.Value}
        {sourceResult : IxIR0.Value},
      sourceArgs.length = modes.length →
      SourceApplies sourceCtx sourceFunction sourceArgs sourceResult →
      ∃ sourceFuel,
        IxIR0.eval sourceCtx sourceFuel sourceArgs.reverse body =
          .ok sourceResult) :
    FnValuePreservesAt (CompilerFunctionRel sourceCtx src ambient)
      sourceCtx ctx ⟨modes.length, world, papSafeFlag, code⟩
      (modes.map worldOfUses) sourceFunction limit := by
  let remaining : Nat → Nat := fun index => countUses index body
  let input : VEnv :=
    ⟨parameterEntries 0 modes remaining, modes.length⟩
  let drops := parameterDrops 0 modes remaining
  have hrun' :
      (lowerFnBody src (compilerFuel + 1) input drops world body).run state =
        .ok code finalState := by
    simpa [input, drops, remaining] using hrun
  simp only [lowerFnBody] at hrun'
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun'
  rcases releaseResult with ⟨middle, releaseEmit⟩
  obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
    trackedBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, emit, av⟩
  have hpure :
      (releaseEmit ∘ emit) (.ret (av.toAtom output)) = code ∧
        bodyState = finalState := by
    simpa using hafterBody
  obtain ⟨hcode, hbodyState⟩ := hpure
  subst bodyState
  have hmiddleNo : NoRecSelf middle :=
    releaseSlots_noRecSelf input hreleaseRun (by
      simpa [input, remaining] using
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
  have hmiddle : plannedMiddle = middle := congrArg Prod.fst heq.1
  have hemit : plannedEmit = releaseEmit := congrArg Prod.snd heq.1
  subst middle
  subst releaseEmit
  cases heq.2
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have hmiddleLength : plannedMiddle.entries.length = modes.length := by
    calc
      plannedMiddle.entries.length = input.entries.length :=
        hplan'.entries_length
      _ = modes.length := by simp [input, remaining]
  have hreleased : EntriesReleased output.entries :=
    hconsume.entriesReleased htracks (Eq.trans hcount hmiddleLength)
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  have hargsLength : args.length = modes.length := by
    simpa using hlength
  have hsourceArgsLength : sourceArgs.length = args.length := by
    simpa using hargs.length
  obtain ⟨sourceFuel, hsource⟩ := hsaturates
    (hsourceArgsLength.trans hargsLength) happlies
  have hbodySound : LowerResultValueSoundBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel ctx
      ⟨modes.length, world, papSafeFlag, code⟩ limit plannedMiddle output
      sourceArgs.reverse sourceArgs.reverse sourceResult world emit av :=
    lowerE_run_value_sound_within_noRecSelf_below
      (recSelfRel := recSelfRel)
      (cur := (⟨modes.length, world, papSafeFlag, code⟩ : FnDef))
      henv hrepresented hcontracts hvalues hsource hbodyRun hextends
      hmiddleNo
  have hfull : LowerResultValueSoundBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel ctx
      ⟨modes.length, world, papSafeFlag, code⟩ limit input output
      sourceArgs.reverse sourceArgs.reverse sourceResult world
      (plannedEmit ∘ emit) av :=
    hbodySound.afterRelease (hplan'.valueSoundBelow sourceArgs.reverse)
  have hpre : GraphOwnsVEnv
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel input
      sourceArgs.reverse sourceRest rest store args.reverse := by
    refine ⟨(rootsForWorlds (modes.map worldOfUses) args).reverse,
      ?_, hframe, ?_⟩
    · simpa [input] using VEnvValueGraph.parameterEntries
        (recSelfRel := recSelfRel) modes remaining hargsLength hargs hown
    · exact hown.perm
        ((List.reverse_perm
          (rootsForWorlds (modes.map worldOfUses) args)).symm.append_right
            rest)
  have hcodeRun' : runCode ctx limit
      ⟨modes.length, world, papSafeFlag, code⟩ store args.reverse
      ((plannedEmit ∘ emit) (.ret (av.toAtom output))) =
        .ok (store', value) := by
    rw [hcode]
    exact hcodeRun
  exact hfull.closeGraph hreleased sourceRest rest (Nat.le_refl _)
    hpre hcodeRun'

/-- A successful ordinary declaration run proves its own dead-parameter
admissibility: `lowerFnBody` executes the generated release list before any
body lowering, and the forbidden modes are exactly its error cases. -/
theorem lowerDecl_defn_parameterDropsAdmissible
    {src : IxIR0.Env} {compilerFuel : Nat}
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {d : FnDef}
    (hrun : (lowerDecl src compilerFuel (address, .defn result body)).run
      state = .ok (some (address, .fn d)) finalState) :
    ParameterDropsAdmissible (lamUses body)
      (fun index => countUses index (stripLams body)) := by
  simp only [lowerDecl] at hrun
  obtain ⟨code, bodyState, hbodyRun, _⟩ :=
    trackedBindRun_ok_inv hrun
  cases compilerFuel with
  | zero =>
    exact (trackedThrowRun_not_ok (by
      simpa [lowerFnBody] using hbodyRun)).elim
  | succ bodyFuel =>
    simp only [lowerFnBody] at hbodyRun
    obtain ⟨releaseResult, releaseState, hreleaseRun, _⟩ :=
      trackedBindRun_ok_inv hbodyRun
    exact parameterDropsAdmissible_of_releaseSlots_run 0 (lamUses body)
      (fun index => countUses index (stripLams body)) hreleaseRun

/-- An ordinary source declaration produced by a reachable whole-pass run
satisfies the exact semantic contract at the current evaluator index using
only strictly-smaller semantic declaration/application contracts. -/
theorem lowerDecl_defn_valuePreservesAt_within_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {compilerFuel limit : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {d : FnDef}
    {sourceFunction : IxIR0.Value}
    (hsrc : src address = some (.defn result body))
    (href : SourceRefValue sourceCtx address sourceFunction)
    (hadmissible : ParameterDropsAdmissible (lamUses body)
      (fun index => countUses index (stripLams body)))
    (hrun : (lowerDecl src (compilerFuel + 1)
      (address, .defn result body)).run state =
        .ok (some (address, .fn d)) finalState)
    (hextends : ExtraExtends finalState ambient) :
    FnValuePreservesAt
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx d
      ((lamUses body).map worldOfUses) sourceFunction limit := by
  simp only [lowerDecl] at hrun
  obtain ⟨code, bodyState, hbodyRun, hpureRun⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩) =
          some (address, Decl.fn d) ∧
        bodyState = finalState := by
    simpa using hpureRun
  have hd : d = ⟨lamArity body, result,
      result == .shared && papSafe body, code⟩ := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2.symm
  cases hpure.2
  subst d
  have hlookup : sourceCtx.env address = some (.defn result body) := by
    rw [henv]
    exact hsrc
  have hpreserves : FnValuePreservesAt
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx
      ⟨(lamUses body).length, result,
        result == .shared && papSafe body, code⟩
      ((lamUses body).map worldOfUses) sourceFunction limit :=
    lowerFnBody_parameterEntries_valuePreservesAt_within_below
      (recSelfRel := fun _ _ => False)
      (compilerFuel := compilerFuel) (limit := limit)
      henv hrepresented hcontracts hvalues (lamUses body) result
      (stripLams body) hadmissible (by simpa using hbodyRun) hextends
      (by
        intro sourceArgs sourceResult hlength happlies
        exact href.defnSaturate hlookup (by simpa using hlength) happlies)
  have hfn : (⟨(lamUses body).length, result,
      result == .shared && papSafe body, code⟩ : FnDef) =
      ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩ := by
    rw [lamUses_length]
  rw [← hfn]
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  exact hpreserves hlength hargs happlies hframe hown hcodeRun

/-- A successfully lowered ordinary body realizes any source function whose
saturated applications evaluate the source body in the canonical reversed
argument environment. This is the semantic function-entry/exit adapter;
recursive call contracts remain explicit in `hvalues`. -/
theorem lowerFnBody_parameterEntries_valuePreservesAt
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx}
    {compilerFuel targetFuel : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx)
    (modes : List Uses) (world : Owned) (body : IxIR0.Expr)
    {state finalState : LowSt} {code : Code} {papSafeFlag : Bool}
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hrun : (lowerFnBody src (compilerFuel + 1)
      ⟨parameterEntries 0 modes (fun index => countUses index body),
        modes.length⟩
      (parameterDrops 0 modes (fun index => countUses index body))
      world body).run state = .ok code finalState)
    (hextends : ExtraExtends finalState ambient)
    {sourceFunction : IxIR0.Value}
    (hsaturates : ∀ {sourceArgs : List IxIR0.Value}
        {sourceResult : IxIR0.Value},
      sourceArgs.length = modes.length →
      SourceApplies sourceCtx sourceFunction sourceArgs sourceResult →
      ∃ sourceFuel,
        IxIR0.eval sourceCtx sourceFuel sourceArgs.reverse body =
          .ok sourceResult) :
    FnValuePreservesAt (CompilerFunctionRel sourceCtx src ambient)
      sourceCtx ctx ⟨modes.length, world, papSafeFlag, code⟩
      (modes.map worldOfUses) sourceFunction targetFuel := by
  let remaining : Nat → Nat := fun index => countUses index body
  let input : VEnv :=
    ⟨parameterEntries 0 modes remaining, modes.length⟩
  let drops := parameterDrops 0 modes remaining
  have hrun' :
      (lowerFnBody src (compilerFuel + 1) input drops world body).run state =
        .ok code finalState := by
    simpa [input, drops, remaining] using hrun
  simp only [lowerFnBody] at hrun'
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun'
  rcases releaseResult with ⟨middle, releaseEmit⟩
  obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
    trackedBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, emit, av⟩
  have hpure :
      (releaseEmit ∘ emit) (.ret (av.toAtom output)) = code ∧
        bodyState = finalState := by
    simpa using hafterBody
  obtain ⟨hcode, hbodyState⟩ := hpure
  subst bodyState
  have hmiddleNo : NoRecSelf middle :=
    releaseSlots_noRecSelf input hreleaseRun (by
      simpa [input, remaining] using
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
  have hmiddle : plannedMiddle = middle := congrArg Prod.fst heq.1
  have hemit : plannedEmit = releaseEmit := congrArg Prod.snd heq.1
  subst middle
  subst releaseEmit
  cases heq.2
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have hmiddleLength : plannedMiddle.entries.length = modes.length := by
    calc
      plannedMiddle.entries.length = input.entries.length :=
        hplan'.entries_length
      _ = modes.length := by simp [input, remaining]
  have hreleased : EntriesReleased output.entries :=
    hconsume.entriesReleased htracks (Eq.trans hcount hmiddleLength)
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  have hargsLength : args.length = modes.length := by
    simpa using hlength
  have hsourceArgsLength : sourceArgs.length = args.length := by
    simpa using hargs.length
  obtain ⟨sourceFuel, hsource⟩ := hsaturates
    (hsourceArgsLength.trans hargsLength) happlies
  have hbodySound : LowerResultValueSound
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel ctx
      ⟨modes.length, world, papSafeFlag, code⟩ plannedMiddle output
      sourceArgs.reverse sourceArgs.reverse sourceResult world emit av :=
    lowerE_run_value_sound_within_noRecSelf
      (recSelfRel := recSelfRel)
      (cur := (⟨modes.length, world, papSafeFlag, code⟩ : FnDef))
      henv hrepresented hcontracts hvalues hsource hbodyRun hextends
      hmiddleNo
  have hfull : LowerResultValueSound
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel ctx
      ⟨modes.length, world, papSafeFlag, code⟩ input output
      sourceArgs.reverse sourceArgs.reverse sourceResult world
      (plannedEmit ∘ emit) av :=
    hbodySound.afterRelease (hplan'.valueSound sourceArgs.reverse)
  have hpre : GraphOwnsVEnv
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel input
      sourceArgs.reverse sourceRest rest store args.reverse := by
    refine ⟨(rootsForWorlds (modes.map worldOfUses) args).reverse,
      ?_, hframe, ?_⟩
    · simpa [input] using VEnvValueGraph.parameterEntries
        (recSelfRel := recSelfRel) modes remaining hargsLength hargs hown
    · exact hown.perm
        ((List.reverse_perm
          (rootsForWorlds (modes.map worldOfUses) args)).symm.append_right
            rest)
  have hcodeRun' : runCode ctx targetFuel
      ⟨modes.length, world, papSafeFlag, code⟩ store args.reverse
      ((plannedEmit ∘ emit) (.ret (av.toAtom output))) =
        .ok (store', value) := by
    rw [hcode]
    exact hcodeRun
  exact hfull.closeGraph hreleased sourceRest rest hpre hcodeRun'

/-- An actual successful ordinary `lowerDecl` run satisfies the exact-fuel
semantic contract of the source definition it compiled. The public source
reference fixes the source function, while `defnSaturate` supplies the body
evaluation required by the generic function-entry adapter. -/
theorem lowerDecl_defn_valuePreservesAt
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {compilerFuel targetFuel : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx)
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {d : FnDef}
    {sourceFunction : IxIR0.Value}
    (hsrc : src address = some (.defn result body))
    (href : SourceRefValue sourceCtx address sourceFunction)
    (hadmissible : ParameterDropsAdmissible (lamUses body)
      (fun index => countUses index (stripLams body)))
    (hrun : (lowerDecl src (compilerFuel + 1)
      (address, .defn result body)).run state =
        .ok (some (address, .fn d)) finalState)
    (hextends : ExtraExtends finalState ambient) :
    FnValuePreservesAt
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx d
      ((lamUses body).map worldOfUses) sourceFunction targetFuel := by
  simp only [lowerDecl] at hrun
  obtain ⟨code, bodyState, hbodyRun, hpureRun⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩) =
          some (address, Decl.fn d) ∧
        bodyState = finalState := by
    simpa using hpureRun
  have hd : d = ⟨lamArity body, result,
      result == .shared && papSafe body, code⟩ := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2.symm
  cases hpure.2
  subst d
  have hlookup : sourceCtx.env address = some (.defn result body) := by
    rw [henv]
    exact hsrc
  have hpreserves : FnValuePreservesAt
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx
      ⟨(lamUses body).length, result,
        result == .shared && papSafe body, code⟩
      ((lamUses body).map worldOfUses) sourceFunction targetFuel :=
    lowerFnBody_parameterEntries_valuePreservesAt
      (recSelfRel := fun _ _ => False)
      (compilerFuel := compilerFuel) (targetFuel := targetFuel)
      henv hrepresented hcontracts hvalues (lamUses body) result
      (stripLams body) hadmissible (by simpa using hbodyRun) hextends
      (by
        intro sourceArgs sourceResult hlength happlies
        exact href.defnSaturate hlookup (by simpa using hlength) happlies)
  have hfn : (⟨(lamUses body).length, result,
      result == .shared && papSafe body, code⟩ : FnDef) =
      ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩ := by
    rw [lamUses_length]
  rw [← hfn]
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  exact hpreserves hlength hargs happlies hframe hown hcodeRun

/-- Unbounded packaging of the ordinary declaration adapter. This theorem
does not seal the mutually recursive compiler contracts—`hvalues` is still
an explicit premise—but it removes all function-entry, cleanup, and source
saturation obligations from that eventual contractive construction. -/
theorem lowerDecl_defn_valueContract
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {compilerFuel : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx)
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {d : FnDef}
    {sourceFunction : IxIR0.Value}
    (hsrc : src address = some (.defn result body))
    (href : SourceRefValue sourceCtx address sourceFunction)
    (hadmissible : ParameterDropsAdmissible (lamUses body)
      (fun index => countUses index (stripLams body)))
    (hrun : (lowerDecl src (compilerFuel + 1)
      (address, .defn result body)).run state =
        .ok (some (address, .fn d)) finalState)
    (hextends : ExtraExtends finalState ambient) :
    FnValueContract (CompilerFunctionRel sourceCtx src ambient)
      sourceCtx ctx d ((lamUses body).map worldOfUses) sourceFunction := by
  have hshape : d.arity = lamArity body := by
    have hrunShape := hrun
    simp only [lowerDecl] at hrunShape
    obtain ⟨code, bodyState, _, hpureRun⟩ :=
      trackedBindRun_ok_inv hrunShape
    have hpure :
        some (address, Decl.fn ⟨lamArity body, result,
          result == .shared && papSafe body, code⟩) =
            some (address, Decl.fn d) ∧
          bodyState = finalState := by
      simpa using hpureRun
    have hd : d = ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩ := by
      have hp := Option.some.inj hpure.1
      exact Decl.fn.inj (Prod.mk.inj hp).2.symm
    rw [hd]
  refine ⟨?_, ?_⟩
  · calc
      ((lamUses body).map worldOfUses).length = lamArity body := by simp
      _ = d.arity := hshape.symm
  · intro targetFuel
    exact lowerDecl_defn_valuePreservesAt
      (targetFuel := targetFuel) henv hrepresented hcontracts hvalues
      hsrc href hadmissible hrun hextends

/-! ### Whole-main value agreement -/

/-- Recover the exact main-body lowering run from a successful whole-program
action. Declaration traversal supplies the initial state; the trailing
`get` and `pure` leave the main body's final state unchanged. -/
theorem lowerAllAction_main_trace
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat} {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    (hrun : (lowerAllAction decls main mainWorld fuel).run initial =
      .ok (targetDecls, mainCode) finalState) :
    ∃ mainInitial,
      (lowerFnBody (IxIR0.Env.ofList decls) fuel ⟨[], 0⟩ [] mainWorld
        main).run mainInitial = .ok mainCode finalState := by
  simp only [lowerAllAction] at hrun
  obtain ⟨base, baseState, _, hafterBase⟩ :=
    trackedBindRun_ok_inv hrun
  obtain ⟨compiledMain, mainState, hmain, hafterMain⟩ :=
    trackedBindRun_ok_inv hafterBase
  obtain ⟨observed, getState, hget, hpure⟩ :=
    trackedBindRun_ok_inv hafterMain
  have hget' : mainState = observed ∧ mainState = getState := by
    simpa using hget
  obtain ⟨hobserved, hgetState⟩ := hget'
  subst observed
  subst getState
  have hpure' :
      (base ++ mainState.extra, compiledMain) =
          (targetDecls, mainCode) ∧
        mainState = finalState := by
    simpa using hpure
  have hcode : compiledMain = mainCode := congrArg Prod.snd hpure'.1
  subst mainCode
  refine ⟨baseState, ?_⟩
  rw [← hpure'.2]
  exact hmain

/-- Every successful execution of an actually lowered closed main owns
exactly its declared result root.  This is the ownership half of
`Reclamation`; unlike value agreement it needs no successful source run. -/
theorem lowerAllAction_main_owned
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx} {targetFuel : Nat} {targetStore : Store}
    {targetValue : RVal}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (htarget : runMain ctx mainCode targetFuel =
      .ok (targetStore, targetValue)) :
    RootOwnership targetStore [⟨mainWorld, targetValue⟩] := by
  obtain ⟨mainInitial, hmain⟩ := lowerAllAction_main_trace hlower
  cases compilerFuel with
  | zero =>
    simp only [lowerFnBody] at hmain
    exact (trackedThrowRun_not_ok hmain).elim
  | succ bodyFuel =>
    simp only [lowerFnBody] at hmain
    obtain ⟨releaseResult, releaseState, hrelease, hafterRelease⟩ :=
      trackedBindRun_ok_inv hmain
    rcases releaseResult with ⟨middle, releaseEmit⟩
    obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
      trackedBindRun_ok_inv hafterRelease
    rcases bodyResult with ⟨output, emit, av⟩
    have hpure :
        (releaseEmit ∘ emit) (.ret (av.toAtom output)) = mainCode ∧
          bodyState = finalState := by
      simpa using hafterBody
    obtain ⟨hcode, hbodyState⟩ := hpure
    subst bodyState
    let input : VEnv := ⟨[], 0⟩
    have hplan : ReleasePlan input [] input (_root_.id : Emit) := .nil
    have hplanRun : (releaseSlots input []).run mainInitial =
        .ok (input, (_root_.id : Emit)) mainInitial :=
      hplan.run mainInitial
    have heq :
        (input, (_root_.id : Emit)) = (middle, releaseEmit) ∧
          mainInitial = releaseState := by
      simpa [input] using hplanRun.symm.trans hrelease
    have hmiddle : input = middle := congrArg Prod.fst heq.1
    have hemitting : (_root_.id : Emit) = releaseEmit :=
      congrArg Prod.snd heq.1
    subst middle
    subst releaseEmit
    cases heq.2
    let cur : FnDef := ⟨0, .shared, false, mainCode⟩
    have hbodySound : LowerResultSoundBelow ctx cur targetFuel input output
        mainWorld emit av :=
      (lowerClusterPreservesBelow (cur := cur)
        (hcontracts.apply.below targetFuel)
        (hcontracts.decls.below targetFuel) bodyFuel).expr
        hbodyRun hrepresented
        (SelfAvailableBelow.of_noRecSelf
          (by intro index arity hentry; simp [input] at hentry))
    have hfull : LowerResultSoundBelow ctx cur targetFuel input output
        mainWorld ((_root_.id : Emit) ∘ emit) av :=
      hbodySound.afterRelease hplan.soundBelow
    have hcount := lowerE_preservesEntryCount hbodyRun
    have houtputEntries : output.entries = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [EntryCountPreserved, input] using hcount
    have hreleased : EntriesReleased output.entries := by
      rw [houtputEntries]
      exact .nil
    have hpre : OwnsVEnv input [] ({} : Store) [] := by
      refine ⟨[], ?_, ?_⟩
      · exact ⟨by simp [input], EntriesRealize.nil⟩
      · simpa using RootOwnership.empty
    have htarget' : runCode ctx targetFuel cur ({} : Store) []
        (((_root_.id : Emit) ∘ emit) (.ret (av.toAtom output))) =
          .ok (targetStore, targetValue) := by
      unfold runMain at htarget
      change runCode ctx targetFuel cur ({} : Store) [] mainCode =
        .ok (targetStore, targetValue) at htarget
      rw [hcode]
      exact htarget
    exact hfull.close hreleased [] (Nat.le_refl _) hpre htarget'

/-- Generic value agreement for the compiled whole-program main. The theorem
deliberately accepts a successful target execution: proving that such an
execution exists for every successful source run is the separate progress
obligation (`MemoryErrorUnreachable` and ordinary-stuck exclusion). -/
theorem lowerAllAction_main_value_graph
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx} {sourceFuel targetFuel : Nat}
    {sourceValue : IxIR0.Value} {targetStore : Store}
    {targetValue : RVal}
    (henv : sourceCtx.env = IxIR0.Env.ofList decls)
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx (IxIR0.Env.ofList decls) ctx)
    (hsource : IxIR0.eval sourceCtx sourceFuel [] main = .ok sourceValue)
    (htarget : runMain ctx mainCode targetFuel =
      .ok (targetStore, targetValue)) :
    Sim.ValueGraph
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      targetStore sourceValue targetValue := by
  obtain ⟨mainInitial, hmain⟩ := lowerAllAction_main_trace hlower
  cases compilerFuel with
  | zero =>
    simp only [lowerFnBody] at hmain
    exact (trackedThrowRun_not_ok hmain).elim
  | succ bodyFuel =>
    simp only [lowerFnBody] at hmain
    obtain ⟨releaseResult, releaseState, hrelease, hafterRelease⟩ :=
      trackedBindRun_ok_inv hmain
    rcases releaseResult with ⟨middle, releaseEmit⟩
    obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
      trackedBindRun_ok_inv hafterRelease
    rcases bodyResult with ⟨output, emit, av⟩
    have hpure :
        (releaseEmit ∘ emit) (.ret (av.toAtom output)) = mainCode ∧
          bodyState = finalState := by
      simpa using hafterBody
    obtain ⟨hcode, hbodyState⟩ := hpure
    subst bodyState
    let input : VEnv := ⟨[], 0⟩
    have hplan : ReleasePlan input [] input (_root_.id : Emit) := by
      exact .nil
    have hplanRun : (releaseSlots input []).run mainInitial =
        .ok (input, (_root_.id : Emit)) mainInitial :=
      hplan.run mainInitial
    have heq :
        (input, (_root_.id : Emit)) = (middle, releaseEmit) ∧
          mainInitial = releaseState := by
      simpa [input] using hplanRun.symm.trans hrelease
    have hmiddle : input = middle := congrArg Prod.fst heq.1
    have hemitting : (_root_.id : Emit) = releaseEmit :=
      congrArg Prod.snd heq.1
    subst middle
    subst releaseEmit
    cases heq.2
    let cur : FnDef := ⟨0, .shared, false, mainCode⟩
    have hbodySound : LowerResultValueSound
        (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
        (fun _ _ => False) ctx cur input output [] [] sourceValue
        mainWorld emit av :=
      lowerE_run_value_sound_within_noRecSelf
        (recSelfRel := fun _ _ => False) (cur := cur) henv hrepresented
        hcontracts hvalues hsource hbodyRun (ExtraExtends.refl _)
        (by intro index arity hentry; simp [input] at hentry)
    have hfull : LowerResultValueSound
        (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
        (fun _ _ => False) ctx cur input output [] [] sourceValue
        mainWorld ((_root_.id : Emit) ∘ emit) av :=
      hbodySound.afterRelease (hplan.valueSound [])
    have hcount := lowerE_preservesEntryCount hbodyRun
    have houtputEntries : output.entries = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [EntryCountPreserved, input] using hcount
    have hreleased : EntriesReleased output.entries := by
      rw [houtputEntries]
      exact .nil
    have hpre : GraphOwnsVEnv
        (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
        (fun _ _ => False) input [] [] [] ({} : Store) [] := by
      refine ⟨[], ?_, Sim.RootsGraph.nil, RootOwnership.empty⟩
      exact ⟨by simp [input], EntriesValueGraph.nil⟩
    have htarget' : runCode ctx targetFuel cur ({} : Store) []
        (((_root_.id : Emit) ∘ emit) (.ret (av.toAtom output))) =
          .ok (targetStore, targetValue) := by
      unfold runMain at htarget
      change runCode ctx targetFuel cur ({} : Store) [] mainCode =
        .ok (targetStore, targetValue) at htarget
      rw [hcode]
      exact htarget
    exact (hfull.closeGraph hreleased [] [] hpre htarget').1

/-- Lift whole-main value agreement to the public forward-simulation
proposition once target progress is supplied independently. This statement
makes the remaining split explicit: compiler value contracts establish
agreement, while the progress premise establishes existence of a successful
target run. -/
theorem lowerAllAction_semanticForwardSimulation_of_targetProgress
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (henv : sourceCtx.env = IxIR0.Env.ofList decls)
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (hvalues : CompilerValueContracts
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx (IxIR0.Env.ofList decls) ctx)
    (hprogress : ∀ {sourceFuel sourceValue},
      IxIR0.eval sourceCtx sourceFuel [] main = .ok sourceValue →
      ∃ targetFuel targetStore targetValue,
        runMain ctx mainCode targetFuel = .ok (targetStore, targetValue)) :
    SemanticForwardSimulation sourceCtx ctx main mainCode
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls)
        finalState) := by
  intro sourceFuel sourceValue hsource
  obtain ⟨targetFuel, targetStore, targetValue, htarget⟩ :=
    hprogress hsource
  refine ⟨targetFuel, targetStore, targetValue, htarget, ?_⟩
  exact lowerAllAction_main_value_graph henv hlower hrepresented
    hcontracts hvalues hsource htarget

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

/-- Invert one successful generated-rule lowering into the two exact prefix
plans and the concrete semantic RHS run.  The static retain/release plans
also prove that neither prefix phase changes the compiler state. -/
theorem lowerRecursorRule_run_plan_inv
    {src : IxIR0.Env} {fuel numArgs : Nat}
    {rule : IxIR0.RecRule} {tag : Nat}
    {state finalState : LowSt} {alt : Alt}
    (hrun : (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
      .ok alt finalState) :
    ∃ fieldOutput fieldEmit rhsInput parameterEmit
        output bodyEmit av,
      FieldRetainPlan
        ⟨List.replicate rule.fields (.slot 0 0 .many false),
          (numArgs + 1) + rule.fields⟩
        (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields)
        fieldOutput fieldEmit ∧
      ReleasePlan
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))
        rhsInput parameterEmit ∧
      (lowerE src fuel rhsInput .shared rule.rhs).run state =
        .ok (output, bodyEmit, av) finalState ∧
      alt = .mk tag rule.fields
        (fieldEmit
          (emitOp (.drop (.var (fieldOutput.rel numArgs)))
            (parameterEmit
              (bodyEmit (.ret (av.toAtom output)))))) := by
  obtain ⟨fieldOutput, fieldEmit, hfieldPlan⟩ :=
    recursorFieldRetains_plan (numArgs + 1)
      ((numArgs + 1) + rule.fields) rule.fields rule.rhs
  have hfieldLength : fieldOutput.entries.length = rule.fields := by
    calc
      fieldOutput.entries.length =
          (⟨List.replicate rule.fields (.slot 0 0 .many false),
            (numArgs + 1) + rule.fields⟩ : VEnv).entries.length :=
        hfieldPlan.entries_length
      _ = rule.fields := by simp
  obtain ⟨rhsInput, parameterEmit, hparameterPlan⟩ :=
    recursorParameterDrops_releasePlan numArgs rule.fields
      (fieldOutput.depth + 1) rule.rhs fieldOutput.entries hfieldLength
  have hfieldRun := hfieldPlan.run
  have horiginal := hrun
  simp only [lowerRecursorRule] at hrun
  rw [hfieldRun] at hrun
  simp only at hrun
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun
  rcases releaseResult with ⟨actualRhsInput, actualParameterEmit⟩
  have hparameterRun := hparameterPlan.run state
  have hreleaseEq :
      (rhsInput, parameterEmit) =
          (actualRhsInput, actualParameterEmit) ∧
        state = releaseState := by
    simpa [VEnv.bump, List.append_assoc] using
      hparameterRun.symm.trans hreleaseRun
  obtain ⟨hrhsInput, hreleaseState⟩ := hreleaseEq
  have hparameterEmit : parameterEmit = actualParameterEmit :=
    congrArg Prod.snd hrhsInput
  have hrhsInputOnly : rhsInput = actualRhsInput :=
    congrArg Prod.fst hrhsInput
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
  obtain ⟨halt, hbodyState⟩ := hpure
  subst bodyState
  exact ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
    output, bodyEmit, av, hfieldPlan,
    by simpa [List.append_assoc] using hparameterPlan,
    hbodyRun, halt.symm⟩

/-- Invert a successful target alternative selection all the way back to
the indexed source rule that generated it.  Besides the exact rule lookup,
the result retains both executable prefix plans, the semantic RHS run, and
the remaining state-threaded traversal after the selected rule. -/
theorem RecursorRulesPlanBelow.find?_run_plan_inv
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel numArgs : Nat} {state finalState : LowSt}
    {rules : Array IxIR0.RecRule} {alts : List Alt}
    (hplan : RecursorRulesPlanBelow ctx cur limit src fuel numArgs
      state rules.toList.zipIdx finalState alts)
    {cidx selectedTag fieldCount : Nat} {body : Code}
    (hfind : alts.toArray.find? (fun alt => alt.cidx == cidx) =
      some (.mk selectedTag fieldCount body)) :
    ∃ rule headState nextState tailRules tailAlts
        fieldOutput fieldEmit rhsInput parameterEmit
        output bodyEmit av,
      rules[cidx]? = some rule ∧
      selectedTag = cidx ∧
      fieldCount = rule.fields ∧
      FieldRetainPlan
        ⟨List.replicate rule.fields (.slot 0 0 .many false),
          (numArgs + 1) + rule.fields⟩
        (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields)
        fieldOutput fieldEmit ∧
      ReleasePlan
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))
        rhsInput parameterEmit ∧
      (lowerE src fuel rhsInput .shared rule.rhs).run headState =
        .ok (output, bodyEmit, av) nextState ∧
      body = fieldEmit
        (emitOp (.drop (.var (fieldOutput.rel numArgs)))
          (parameterEmit
            (bodyEmit (.ret (av.toAtom output))))) ∧
      RecursorRulesPlanBelow ctx cur limit src fuel numArgs
        nextState tailRules finalState tailAlts := by
  have hmember : (.mk selectedTag fieldCount body : Alt) ∈ alts := by
    simpa using Array.mem_of_find?_eq_some hfind
  obtain ⟨rule, tag, headState, nextState, tailRules, tailAlts,
      hsourceMember, hheadRun, htailPlan⟩ :=
    hplan.trace_mem (.mk selectedTag fieldCount body) hmember
  obtain ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
      output, bodyEmit, av, hfieldPlan, hparameterPlan,
      hbodyRun, halt⟩ :=
    lowerRecursorRule_run_plan_inv hheadRun
  have hselectedTag : selectedTag = cidx := by
    have hmatch := Array.find?_some
      (p := fun alt : Alt => alt.cidx == cidx)
      (a := .mk selectedTag fieldCount body)
      (xs := alts.toArray) hfind
    exact beq_iff_eq.mp hmatch
  have htag : selectedTag = tag := by
    injection halt
  have hfieldCount : fieldCount = rule.fields := by
    injection halt
  have hbody : body = fieldEmit
      (emitOp (.drop (.var (fieldOutput.rel numArgs)))
        (parameterEmit
          (bodyEmit (.ret (av.toAtom output))))) := by
    injection halt
  have htagCidx : tag = cidx := htag.symm.trans hselectedTag
  obtain ⟨_, htagBound, hruleElem⟩ :=
    List.mem_zipIdx hsourceMember
  have htagLt : tag < rules.toList.length := by
    simpa using htagBound
  have hruleTag : rules[tag]? = some rule := by
    rw [← Array.getElem?_toList]
    rw [List.getElem?_eq_getElem htagLt]
    exact congrArg some hruleElem.symm
  have hrule : rules[cidx]? = some rule := by
    rwa [← htagCidx]
  exact ⟨rule, headState, nextState, tailRules, tailAlts,
    fieldOutput, fieldEmit, rhsInput, parameterEmit,
    output, bodyEmit, av, hrule, hselectedTag, hfieldCount,
    hfieldPlan, hparameterPlan, hbodyRun, hbody, htailPlan⟩

/-- Execute the exact generated prefix and RHS for one selected recursor
rule while transporting the source result and the caller's framed graphs.
This is independent of how the case dispatcher represented the major; the
caller supplies the corresponding source/target field graph and field-world
facts. -/
theorem lowerRecursorRule_branch_value_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {fuel numArgs : Nat} {rule : IxIR0.RecRule}
    {headState nextState : LowSt}
    {fieldOutput rhsInput output : VEnv}
    {fieldEmit parameterEmit bodyEmit : Emit} {av : AVal}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    (hself : CurrentSelfValueContractBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      cur limit)
    (hfieldPlan : FieldRetainPlan
      ⟨List.replicate rule.fields (.slot 0 0 .many false),
        (numArgs + 1) + rule.fields⟩
      (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields)
      fieldOutput fieldEmit)
    (hparameterPlan : ReleasePlan
      ⟨fieldOutput.entries ++
          parameterEntries 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs) ++
          [.recSelf (numArgs + 1)],
        fieldOutput.depth + 1⟩
      ((parameterDrops 0 (List.replicate numArgs .many)
          (fun i => countUses (rule.fields + i) rule.rhs)).map
        (SlotDrop.offsetEntry rule.fields))
      rhsInput parameterEmit)
    (hbodyRun : (lowerE src fuel rhsInput .shared rule.rhs).run headState =
      .ok (output, bodyEmit, av) nextState)
    (hextends : ExtraExtends nextState ambient)
    {sourcePre : List IxIR0.Value} {pre : List RVal}
    {sourceFields : List IxIR0.Value} {fields : List RVal}
    {sourceSelf sourceValue : IxIR0.Value} {major : RVal}
    {sourceFuel : Nat}
    (hsource : IxIR0.eval sourceCtx sourceFuel
      (sourceFields.reverse ++ sourcePre.reverse ++ [sourceSelf])
      rule.rhs = .ok sourceValue)
    (hpreLength : pre.length = numArgs)
    (hfieldsLength : fields.length = rule.fields)
    {store store' : Store} {value : RVal}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hpreGraphs : Sim.ValuesGraph
      (CompilerFunctionRel sourceCtx src ambient) store sourcePre pre)
    (hfieldGraphs : Sim.ValuesGraph
      (CompilerFunctionRel sourceCtx src ambient) store sourceFields fields)
    (hsourceSelf : recSelfRel sourceSelf (numArgs + 1))
    (hframe : Sim.RootsGraph
      (CompilerFunctionRel sourceCtx src ambient) store sourceRest rest)
    (hown : RootOwnership store
      (rootsFor .shared (pre ++ [major]) ++ rest))
    (hfieldWorld : ∀ field ∈ fields, HasWorld store .shared field)
    {branchFuel : Nat} (hbound : branchFuel ≤ limit)
    (hbranchRun : runCode ctx branchFuel cur store
      (fields.reverse ++ major :: pre.reverse)
      (fieldEmit
        (emitOp (.drop (.var (fieldOutput.rel numArgs)))
          (parameterEmit
            (bodyEmit (.ret (av.toAtom output)))))) =
        .ok (store', value)) :
    Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceValue value ∧
      Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceRest rest := by
  have hentry := recursorAltEntry_value_state
    (funRel := CompilerFunctionRel sourceCtx src ambient)
    (recSelfRel := recSelfRel) numArgs rule.fields rule.rhs
    hpreLength hfieldsLength hpreGraphs hfieldGraphs hsourceSelf hframe hown
    hfieldWorld
  have hprefix := recursorPrefixPlans_valueSoundBelow
    (funRel := CompilerFunctionRel sourceCtx src ambient)
    (recSelfRel := recSelfRel) (ctx := ctx) (cur := cur) (limit := limit)
    numArgs rule.fields rule.rhs hfieldPlan hparameterPlan
    (sourceFields.reverse ++ sourcePre.reverse ++ [sourceSelf])
    sourceRest rest major fields
  have hbodySound := lowerE_run_value_sound_within_currentSelf_below
    henv hrepresented hcontracts hvalues hsource hbodyRun hextends hself
  have hnextRepresented : ExtraRepresented ctx nextState :=
    hrepresented.of_extends hextends
  have hownershipSelf : CurrentSelfContractBelow ctx cur limit :=
    ⟨hself.result, hself.ownership⟩
  have hfieldRun := hfieldPlan.run
  have hparameterRun := hparameterPlan.run headState
  obtain ⟨_, hreleased⟩ := lowerRecursorRule_rhs_sound_below
    (hcontracts.below limit).apply (hcontracts.below limit).decls
    hownershipSelf hfieldRun hparameterRun hbodyRun hnextRepresented
  have hbodyCode : CodeOwnsBelow ctx cur limit
      (GraphOwnsVEnv (CompilerFunctionRel sourceCtx src ambient)
        recSelfRel rhsInput
        (sourceFields.reverse ++ sourcePre.reverse ++ [sourceSelf])
        sourceRest rest)
      (fun resultStore resultValue =>
        Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient)
            resultStore sourceValue resultValue ∧
          Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient)
            resultStore sourceRest rest)
      (bodyEmit (.ret (av.toAtom output))) :=
    hbodySound.closeGraph hreleased sourceRest rest
  exact hprefix limit (Nat.le_refl limit)
    (fun resultStore resultValue =>
      Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient)
          resultStore sourceValue resultValue ∧
        Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient)
          resultStore sourceRest rest)
    (bodyEmit (.ret (av.toAtom output))) hbodyCode
    (fuel := branchFuel) (store := store)
    (env := fields.reverse ++ major :: pre.reverse)
    (store' := store') (value := value) hbound hentry
    (by simpa [Function.comp_def] using hbranchRun)

private theorem lowerStateSimExceptBindOk {error α β : Type}
    (value : α) (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

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
      (⟨numArgs + 1, .shared, true,
          .case (.var 0) natLit alts.toArray⟩ : FnDef) = d ∧
        rulesState = finalState := by
    simpa using hafterRules
  obtain ⟨hd, hstate⟩ := hpure
  subst d
  subst rulesState
  have hplan : RecursorRulesPlanBelow ctx
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      limit src fuel numArgs state rules.toList.zipIdx finalState alts :=
    recursorRulesPlanBelow_of_run happly hdecls hself rfl
      fuel numArgs hrulesRun hrepresented
  have hverified :
      (lowerRecursor src fuel numArgs natLit rules).run state =
          .ok ⟨numArgs + 1, .shared, true,
            .case (.var 0) natLit alts.toArray⟩ finalState ∧
        FnOwnershipPreservesAt ctx
          ⟨numArgs + 1, .shared, true,
            .case (.var 0) natLit alts.toArray⟩
          (List.replicate (numArgs + 1) .shared) limit :=
    lowerRecursor_generated_verified_below
      limit src fuel numArgs natLit rules state finalState alts
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      rfl hplan
  have hpreserves : FnOwnershipPreservesAt ctx
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      (List.replicate (numArgs + 1) .shared) limit := hverified.2
  intro store store' args value rest hlength hown hcodeRun
  exact hpreserves hlength hown hcodeRun

/-- Exact-fuel semantic preservation for a successfully generated source
recursor.  Source saturation identifies the chosen rule and its evaluator
environment; target case dispatch is then joined to the exact generated
prefix/RHS trace for that same indexed rule. -/
theorem lowerRecursor_valuePreservesAt_within_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {limit compilerFuel numArgs : Nat}
    {natLit : Bool} {rules : Array IxIR0.RecRule}
    {address : Ixon.Address} {sourceFunction : IxIR0.Value}
    {state finalState : LowSt} {d : FnDef}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    (hsrc : src address = some (.recursor numArgs natLit rules))
    (hdecl : ctx.decls address = some (.fn d))
    (href : SourceRefValue sourceCtx address sourceFunction)
    (hrun : (lowerRecursor src compilerFuel numArgs natLit rules).run state =
      .ok d finalState)
    (hextends : ExtraExtends finalState ambient) :
    FnValuePreservesAt (CompilerFunctionRel sourceCtx src ambient)
      sourceCtx ctx d (List.replicate (numArgs + 1) .shared)
      sourceFunction limit := by
  simp only [lowerRecursor] at hrun
  obtain ⟨alts, rulesState, hrulesRun, hafterRules⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      (⟨numArgs + 1, .shared, true,
          .case (.var 0) natLit alts.toArray⟩ : FnDef) = d ∧
        rulesState = finalState := by
    simpa using hafterRules
  obtain ⟨hd, hstate⟩ := hpure
  subst d
  subst rulesState
  have hsourceLookup : sourceCtx.env address =
      some (.recursor numArgs natLit rules) := by
    rw [henv]
    exact hsrc
  have hsourceFunction := href.recursorValue hsourceLookup
  subst sourceFunction
  let recSelfRel : RecSelfRel := fun value arity =>
    value = .pap (.rec_ address (numArgs + 1)) [] ∧
      arity = numArgs + 1
  obtain ⟨ownedD, hownedDecl, _, _, hownedContract⟩ :=
    hcontracts.decls.recursor hsrc
  have hownedD : ownedD =
      (⟨numArgs + 1, .shared, true,
        .case (.var 0) natLit alts.toArray⟩ : FnDef) := by
    have hsame : some (Decl.fn ownedD) = some
        (.fn ⟨numArgs + 1, .shared, true,
          .case (.var 0) natLit alts.toArray⟩) :=
      hownedDecl.symm.trans hdecl
    exact Decl.fn.inj (Option.some.inj hsame)
  subst ownedD
  have hvalueContract : FnValueContractBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      (List.replicate (numArgs + 1) .shared)
      (.pap (.rec_ address (numArgs + 1)) []) limit := by
    apply hvalues.decls.fnContract hsrc (by rfl) hdecl href
    simp
  have hself : CurrentSelfValueContractBelow
      (CompilerFunctionRel sourceCtx src ambient) recSelfRel sourceCtx ctx
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      limit := by
    refine ⟨rfl, ?_, ?_⟩
    · simpa using hownedContract.below limit
    · intro candidate hcandidate
      change candidate = .pap (.rec_ address (numArgs + 1)) [] ∧
        numArgs + 1 = numArgs + 1 at hcandidate
      rcases hcandidate with ⟨rfl, _⟩
      exact hvalueContract
  have hfinalRepresented : ExtraRepresented ctx finalState :=
    hrepresented.of_extends hextends
  have hownershipSelf : CurrentSelfContractBelow ctx
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      limit := ⟨hself.result, hself.ownership⟩
  have hplan : RecursorRulesPlanBelow ctx
      ⟨numArgs + 1, .shared, true, .case (.var 0) natLit alts.toArray⟩
      limit src compilerFuel numArgs state rules.toList.zipIdx
      finalState alts :=
    recursorRulesPlanBelow_of_run (hcontracts.below limit).apply
      (hcontracts.below limit).decls hownershipSelf rfl
      compilerFuel numArgs hrulesRun hfinalRepresented
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hargsLength hargs happlies hframe hown htarget
  have hargsArity : args.length = numArgs + 1 := by
    simpa using hargsLength
  have hrootShape :
      rootsForWorlds (List.replicate (numArgs + 1) .shared) args =
        rootsFor .shared args :=
    rootsForWorlds_replicate_eq_rootsFor .shared hargsArity
  rw [hrootShape] at hown
  cases limit with
  | zero => simp [runCode] at htarget
  | succ branchFuel =>
    cases hreverse : args.reverse with
    | nil =>
      have hargsNil : args = [] := by
        have h := congrArg List.reverse hreverse
        simpa using h
      simp [hargsNil] at hargsArity
    | cons major runtimePre =>
      have hargsForm : args = runtimePre.reverse ++ [major] := by
        have h := congrArg List.reverse hreverse
        simpa [List.reverse_cons] using h
      have hruntimePreLength : runtimePre.length = numArgs := by
        rw [hargsForm] at hargsArity
        simp only [List.length_append, List.length_reverse,
          List.length_singleton] at hargsArity
        omega
      obtain ⟨sourcePre, sourceMajor, hsourceArgsForm,
          hsourcePreLength, hpreGraphs, hmajorGraph⟩ :=
        valuesGraph_splitLast hargs hargsForm hruntimePreLength
      rw [hsourceArgsForm] at happlies
      obtain ⟨sourceTag, sourceFields, sourceRule, sourceFuel,
          hsourceMajor, hsourceRule, hsourceFieldsLength, hsourceEval⟩ :=
        sourceRecursorRef_saturates_inv hsourceLookup href
          hsourcePreLength happlies
      have hmajorWorld : HasWorld store .shared major := by
        apply hown.roots_world ⟨.shared, major⟩
        apply List.mem_append_left rest
        simp [rootsFor, hargsForm]
      have hentryOwn : RootOwnership store
          (rootsFor .shared (runtimePre.reverse ++ [major]) ++ rest) := by
        simpa [hargsForm] using hown
      rw [hreverse] at htarget
      change runCode ctx (branchFuel + 1)
          ⟨numArgs + 1, .shared, true,
            .case (.var 0) natLit alts.toArray⟩
          store (major :: runtimePre)
          (.case (.var 0) natLit alts.toArray) =
        .ok (store', value) at htarget
      have hdispatch := htarget
      rw [runCode.eq_def] at hdispatch
      dsimp only at hdispatch
      rw [show resolveAtom (major :: runtimePre) (.var 0) = .ok major
        from rfl, lowerStateSimExceptBindOk] at hdispatch
      have finish {cidx selectedTag fieldCount : Nat} {body : Code}
          (halt : alts.toArray.find? (fun alt => alt.cidx == cidx) =
            some (.mk selectedTag fieldCount body))
          (hcidx : cidx = sourceTag)
          {targetFields : List RVal}
          (hfieldGraphs : Sim.ValuesGraph
            (CompilerFunctionRel sourceCtx src ambient) store
            sourceFields targetFields)
          (htargetFieldsLength : targetFields.length = fieldCount)
          (hfieldWorld : ∀ field ∈ targetFields,
            HasWorld store .shared field)
          (hbranchRun : runCode ctx branchFuel
            ⟨numArgs + 1, .shared, true,
              .case (.var 0) natLit alts.toArray⟩
            store (targetFields.reverse ++ major :: runtimePre) body =
              .ok (store', value)) :
          Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient)
              store' sourceResult value ∧
            Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient)
              store' sourceRest rest := by
        obtain ⟨rule, headState, nextState, tailRules, tailAlts,
            fieldOutput, fieldEmit, rhsInput, parameterEmit,
            output, bodyEmit, av, hrule, _, hfieldCount,
            hfieldPlan, hparameterPlan, hbodyRun, hbody, htailPlan⟩ :=
          hplan.find?_run_plan_inv halt
        have hsourceRuleAt : rules[cidx]? = some sourceRule := by
          rw [hcidx]
          exact hsourceRule
        have hruleEq : rule = sourceRule :=
          Option.some.inj (hrule.symm.trans hsourceRuleAt)
        subst rule
        have htargetRuleLength : targetFields.length = sourceRule.fields :=
          htargetFieldsLength.trans hfieldCount
        have htailExtends : ExtraExtends nextState finalState :=
          (ExtraMonotone.listMapM
            (lowerRecursorRule src compilerFuel numArgs)
            (lowerRecursorRule_extraMonotone src compilerFuel numArgs)
            tailRules) htailPlan.run
        have hnextExtends : ExtraExtends nextState ambient :=
          htailExtends.trans hextends
        rw [hbody] at hbranchRun
        exact lowerRecursorRule_branch_value_below
          (recSelfRel := recSelfRel) (limit := branchFuel + 1)
          (branchFuel := branchFuel)
          henv hrepresented hcontracts hvalues
          hself hfieldPlan hparameterPlan hbodyRun hnextExtends
          (sourcePre := sourcePre) (pre := runtimePre.reverse)
          (sourceFields := sourceFields) (fields := targetFields)
          (sourceSelf := .pap (.rec_ address (numArgs + 1)) [])
          (sourceValue := sourceResult) (major := major)
          hsourceEval (by simpa using hruntimePreLength)
          htargetRuleLength hpreGraphs hfieldGraphs ⟨rfl, rfl⟩
          hframe hentryOwn hfieldWorld (by omega)
          (by simpa using hbranchRun)
      cases hmajorGraph with
      | @lit literal =>
        cases literal with
        | str string => simp [IxIR0.majorCtor] at hsourceMajor
        | nat n =>
          cases hpeel : natLit with
          | false => simp [IxIR0.majorCtor, hpeel] at hsourceMajor
          | true =>
              cases n with
              | zero =>
                have hmajorPair :
                    0 = sourceTag ∧ sourceFields = [] := by
                  simpa [IxIR0.majorCtor, hpeel] using hsourceMajor
                have htag : sourceTag = 0 :=
                  hmajorPair.1.symm
                have hfields : sourceFields = [] :=
                  hmajorPair.2
                subst sourceTag
                subst sourceFields
                cases halt : alts.toArray.find?
                    (fun alt => alt.cidx == 0) with
                | none => simp [hpeel, halt] at hdispatch
                | some alt =>
                  cases alt with
                  | mk selectedTag fieldCount body =>
                    cases fieldCount with
                    | zero =>
                      have hbranch := hdispatch
                      simp [hpeel, halt] at hbranch
                      exact finish halt rfl Sim.ValuesGraph.nil rfl
                        (by simp) (by simpa [hpeel] using hbranch)
                    | succ fieldCount =>
                      simp [hpeel, halt] at hdispatch
              | succ n =>
                have hmajorPair :
                    1 = sourceTag ∧
                      [.lit (.nat n)] = sourceFields := by
                  simpa [IxIR0.majorCtor, hpeel] using hsourceMajor
                have htag : sourceTag = 1 :=
                  hmajorPair.1.symm
                have hfields : sourceFields = [.lit (.nat n)] :=
                  hmajorPair.2.symm
                subst sourceTag
                subst sourceFields
                cases halt : alts.toArray.find?
                    (fun alt => alt.cidx == 1) with
                | none => simp [hpeel, halt] at hdispatch
                | some alt =>
                  cases alt with
                  | mk selectedTag fieldCount body =>
                    by_cases hfieldCount : fieldCount = 1
                    · subst fieldCount
                      have hbranch := hdispatch
                      simp [hpeel, halt] at hbranch
                      exact finish halt rfl
                        (.cons .lit .nil) rfl (by simp [HasWorld])
                        (by simpa [hpeel] using hbranch)
                    · simp [hpeel, halt, hfieldCount] at hdispatch
      | erased => simp [IxIR0.majorCtor] at hsourceMajor
      | @ctor sourceAddress sourceCtorTag sourceCtorFields loc
          world rc cid targetFields hget haddress htag hfieldGraphs =>
        have hmajorPair :
            sourceCtorTag = sourceTag ∧
              sourceCtorFields = sourceFields := by
          simpa [IxIR0.majorCtor] using hsourceMajor
        have hsourceTagEq : sourceTag = sourceCtorTag :=
          hmajorPair.1.symm
        have hsourceFieldsEq : sourceFields = sourceCtorFields :=
          hmajorPair.2.symm
        subst sourceTag
        subst sourceFields
        obtain ⟨ownedBox, hownedBox, hownedWorld⟩ := hmajorWorld
        rw [hget] at hownedBox
        have hboxEq :
            (⟨world, rc, .ctorN cid targetFields⟩ : NodeBox) =
              ownedBox := Option.some.inj hownedBox
        subst ownedBox
        dsimp only [NodeBox.world] at hownedWorld
        subst world
        cases halt : alts.toArray.find?
            (fun alt => alt.cidx == cid.cidx) with
        | none => simp [hget, halt] at hdispatch
        | some alt =>
          cases alt with
          | mk selectedTag fieldCount body =>
            by_cases hsize : targetFields.size = fieldCount
            · have hbranch := htarget
              rw [runCode_case_ctor rfl hget halt hsize] at hbranch
              rw [Array.foldl_cons_eq_reverse_append] at hbranch
              exact finish halt htag
                (by simpa using hfieldGraphs)
                (by simpa using hsize)
                (hown.caseFieldsBorrowed hget)
                hbranch
            · simp [hget, halt, hsize] at hdispatch
      | function hget hfun hcaptures =>
        simp [hget] at hdispatch

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

/-- Declaration-facing semantic recursor rule over the actual `lowerDecl`
result.  The declaration adapter contributes no runtime behavior; it only
recovers the exact generated recursor body and final compiler state used by
`lowerRecursor_valuePreservesAt_within_below`. -/
theorem lowerDecl_recursor_valuePreservesAt_within_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {limit compilerFuel numArgs : Nat}
    {natLit : Bool} {rules : Array IxIR0.RecRule}
    {address : Ixon.Address} {sourceFunction : IxIR0.Value}
    {state finalState : LowSt} {d : FnDef}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    (hsrc : src address = some (.recursor numArgs natLit rules))
    (hdecl : ctx.decls address = some (.fn d))
    (href : SourceRefValue sourceCtx address sourceFunction)
    (hrun :
      (lowerDecl src compilerFuel
        (address, .recursor numArgs natLit rules)).run state =
          .ok (some (address, .fn d)) finalState)
    (hextends : ExtraExtends finalState ambient) :
    FnValuePreservesAt (CompilerFunctionRel sourceCtx src ambient)
      sourceCtx ctx d (List.replicate (numArgs + 1) .shared)
      sourceFunction limit := by
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
  intro store store' args value sourceArgs sourceResult sourceRest rest
    hlength hargs happlies hframe hown hcodeRun
  exact lowerRecursor_valuePreservesAt_within_below
    henv hrepresented hcontracts hvalues hsrc hdecl href
    hrecursorRun hextends hlength hargs happlies hframe hown hcodeRun

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
    {state finalState : LowSt} {code : Code} {papSafeFlag : Bool}
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hrun : (lowerFnBody src (fuel + 1)
      ⟨parameterEntries 0 modes (fun index => countUses index body),
        modes.length⟩
      (parameterDrops 0 modes (fun index => countUses index body))
      world body).run state = .ok code finalState)
    (hrepresented : ExtraRepresented ctx finalState) :
    FnOwnershipPreservesAt ctx ⟨modes.length, world, papSafeFlag, code⟩
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
      (cur := (⟨modes.length, world, papSafeFlag, code⟩ : FnDef))
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
      (⟨modes.length, world, papSafeFlag, code⟩ : FnDef)
        limit input output world
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
      some (address, Decl.fn ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩) =
          some (address, Decl.fn d) ∧ bodyState = finalState := by
    simpa using hpureRun
  have hd : d = ⟨lamArity body, result,
      result == .shared && papSafe body, code⟩ := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2.symm
  cases hpure.2
  subst d
  have hpreserves : FnOwnershipPreservesAt ctx
      ⟨(lamUses body).length, result,
        result == .shared && papSafe body, code⟩
      ((lamUses body).map worldOfUses) limit :=
    lowerFnBody_parameterEntries_preservesAt
      happly hdecls (lamUses body) result (stripLams body) hadmissible
      (by simpa using hbodyRun) hrepresented
  have hfn : (⟨(lamUses body).length, result,
      result == .shared && papSafe body, code⟩ : FnDef) =
      ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩ := by
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
  intro indices next values hlength hpositive hbound hslots
  exact selectedEntriesFrom_traverse selected remaining
    (Result := fun sourceIndices current entries =>
      ∀ runtimeValues,
        runtimeValues.length = (sourceIndices.filter selected).length →
        0 < Γ.depth →
        current + runtimeValues.length ≤ Γ.depth →
        (∀ index, index < runtimeValues.length →
          env[Γ.rel (current + index)]? = runtimeValues[index]?) →
        EntriesRealize Γ env entries (rootsFor .shared runtimeValues))
    (hnil := by
      intro current runtimeValues hlength _ _ _
      cases runtimeValues with
      | nil => exact EntriesRealize.nil
      | cons value values => simp at hlength)
    (hfalse := by
      intro entry entries current tail hselected ih runtimeValues hlength
        hpositive hbound hslots
      apply EntriesRealize.released (by omega)
      apply ih runtimeValues
      · simpa [hselected] using hlength
      · exact hpositive
      · exact hbound
      · exact hslots)
    (htrue := by
      intro entry entries current tail hselected ih runtimeValues hlength
        hpositive hbound hslots
      cases runtimeValues with
      | nil => simp [hselected] at hlength
      | cons value values =>
        simp only [rootsFor, List.map_cons]
        apply EntriesRealize.held
        · exact Nat.lt_of_lt_of_le (by simp) hbound
        · have hhead := hslots 0 (by simp)
          simpa using hhead
        · apply ih values
          · simpa [hselected] using hlength
          · exact hpositive
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
          · intro index hindex
            have htail := hslots (index + 1) (by simp [hindex])
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail)
    indices next values hlength hpositive hbound hslots

/-- Semantic companion to `selectedEntriesFrom_entriesRealize`.  The first
`ValuesAt` witness supplies every logical source entry, while the filtered
witness and pointwise runtime graph supply exactly the held capture subset;
unselected entries remain present on the source side but own no root. -/
private theorem selectedEntriesFrom_entriesValueGraph
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {store : Store} {Γ : VEnv} {env : List RVal}
    {sourceEnv : List IxIR0.Value}
    (selected : Nat → Bool) (remaining : Nat → Nat) :
    ∀ (indices : List Nat) (next : Nat)
        (allSources selectedSources : List IxIR0.Value)
        (values : List RVal),
      ValuesAt sourceEnv indices allSources →
      ValuesAt sourceEnv (indices.filter selected) selectedSources →
      Sim.ValuesGraph funRel store selectedSources values →
      0 < Γ.depth →
      next + values.length ≤ Γ.depth →
      (∀ index, index < values.length →
        env[Γ.rel (next + index)]? = values[index]?) →
      (∀ value, value ∈ values → HasWorld store .shared value) →
      EntriesValueGraph funRel recSelfRel store Γ env
        (selectedEntriesFrom selected remaining indices next)
        allSources (rootsFor .shared values) := by
  intro indices next allSources selectedSources values hall hselected hgraphs
    hpositive hbound hslots hworlds
  exact selectedEntriesFrom_traverse selected remaining
    (Result := fun sourceIndices current entries =>
      ∀ allSourceValues selectedSourceValues runtimeValues,
        ValuesAt sourceEnv sourceIndices allSourceValues →
        ValuesAt sourceEnv (sourceIndices.filter selected)
          selectedSourceValues →
        Sim.ValuesGraph funRel store selectedSourceValues runtimeValues →
        0 < Γ.depth →
        current + runtimeValues.length ≤ Γ.depth →
        (∀ index, index < runtimeValues.length →
          env[Γ.rel (current + index)]? = runtimeValues[index]?) →
        (∀ value, value ∈ runtimeValues → HasWorld store .shared value) →
        EntriesValueGraph funRel recSelfRel store Γ env entries
          allSourceValues (rootsFor .shared runtimeValues))
    (hnil := by
      intro current allSourceValues selectedSourceValues runtimeValues
        hall hselected hgraphs _ _ _ _
      cases hall
      cases hselected
      cases hgraphs
      exact EntriesValueGraph.nil)
    (hfalse := by
      intro entry entries current tail hselectedBit ih allSourceValues
        selectedSourceValues runtimeValues hall hselected hgraphs hpositive
        hbound hslots hworlds
      cases hall with
      | @cons _ source _ tailSources hsource htailAll =>
        simp only [List.filter_cons, hselectedBit, Bool.false_eq_true,
          if_false] at hselected
        apply EntriesValueGraph.released (by omega)
        exact ih tailSources selectedSourceValues runtimeValues htailAll
          hselected hgraphs hpositive hbound hslots hworlds)
    (htrue := by
      intro entry entries current tail hselectedBit ih allSourceValues
        selectedSourceValues runtimeValues hall hselected hgraphs hpositive
        hbound hslots hworlds
      cases hall with
      | @cons _ source _ tailSources hsource htailAll =>
        simp only [List.filter_cons, hselectedBit, ↓reduceIte] at hselected
        cases hselected with
        | @cons _ selectedSource _ selectedTail hselectedSource
            hselectedTail =>
          cases hgraphs with
          | @cons _ runtimeValue _ runtimeTail hvalue htailGraphs =>
            have hsourceEq : selectedSource = source := by
              exact Option.some.inj (hselectedSource.symm.trans hsource)
            subst selectedSource
            simp only [rootsFor, List.map_cons]
            apply EntriesValueGraph.held
            · exact Nat.lt_of_lt_of_le (by simp) hbound
            · have hhead := hslots 0 (by simp)
              simpa using hhead
            · exact hworlds runtimeValue (by simp)
            · exact hvalue
            · apply ih tailSources selectedTail runtimeTail htailAll
                hselectedTail htailGraphs hpositive
              · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using hbound
              · intro index hindex
                have htail := hslots (index + 1) (by simp [hindex])
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using htail
              · intro value hvalueMem
                exact hworlds value (by simp [hvalueMem]))
    indices next allSources selectedSources values hall hselected hgraphs
      hpositive hbound hslots hworlds

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

/-- Consecutive valid source-environment indices select the corresponding
list segment. -/
private theorem ValuesAt.range'_of_get (sourceEnv : List IxIR0.Value) :
    ∀ (start : Nat) (values : List IxIR0.Value),
      (∀ offset, offset < values.length →
        sourceEnv[start + offset]? = values[offset]?) →
      ValuesAt sourceEnv (List.range' start values.length) values := by
  intro start values
  induction values generalizing start with
  | nil =>
    intro _
    exact ValuesAt.nil
  | cons head tail ih =>
    intro hget
    have hhead : sourceEnv[start]? = some head := by
      have h := hget 0 (by simp)
      simpa using h
    apply ValuesAt.cons hhead
    have htail := ih (start + 1) (by
      intro offset hoffset
      have h := hget (offset + 1) (by simp [hoffset])
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
    simpa [List.range'_succ] using htail

/-- The full source environment is selected by its canonical index range. -/
private theorem ValuesAt.range_self (sourceEnv : List IxIR0.Value) :
    ValuesAt sourceEnv (List.range sourceEnv.length) sourceEnv := by
  have h := ValuesAt.range'_of_get sourceEnv 0 sourceEnv (by
    intro offset hoffset
    simp)
  simpa [List.range_eq_range'] using h

/-- Semantic entry graph for a lifted function's public
capture-then-parameter calling convention.  Runtime arguments are supplied
in public order, while both the evaluator stack and the leading source
parameter environment are reversed at function entry. -/
theorem VEnvValueGraph.lifted
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel} {store : Store}
    (entryCount : Nat) (modes : List Uses)
    (parameterRemaining : Nat → Nat)
    (selected : Nat → Bool) (captureRemaining : Nat → Nat)
    {sourceEnv selectedSources parameterSources : List IxIR0.Value}
    {captureArgs parameterArgs : List RVal} {rest : List Root}
    (hsourceLength : sourceEnv.length = entryCount)
    (hselected : ValuesAt sourceEnv
      ((List.range entryCount).filter selected) selectedSources)
    (hcaptureLength : captureArgs.length =
      ((List.range entryCount).filter selected).length)
    (hparameterLength : parameterArgs.length = modes.length)
    (hcaptures : Sim.ValuesGraph funRel store selectedSources captureArgs)
    (hparameters : Sim.ValuesGraph funRel store parameterSources
      parameterArgs)
    (hpositive : 0 < modes.length)
    (hshared : modes.map worldOfUses =
      List.replicate modes.length .shared)
    (hown : RootOwnership store
      (rootsFor .shared (captureArgs ++ parameterArgs) ++ rest)) :
    let captures := (List.range entryCount).filter selected
    let Γ : VEnv :=
      ⟨Lower.parameterEntries captures.length modes parameterRemaining ++
          selectedEntriesFrom selected captureRemaining
            (List.range entryCount) 0,
        captures.length + modes.length⟩
    VEnvValueGraph funRel recSelfRel store Γ
      (parameterSources.reverse ++ sourceEnv)
      (captureArgs ++ parameterArgs).reverse
      ((rootsForWorlds (modes.map worldOfUses) parameterArgs).reverse ++
        rootsFor .shared captureArgs) := by
  dsimp only
  let captures := (List.range entryCount).filter selected
  let args := captureArgs ++ parameterArgs
  let Γ : VEnv :=
    ⟨Lower.parameterEntries captures.length modes parameterRemaining ++
        selectedEntriesFrom selected captureRemaining
          (List.range entryCount) 0,
      captures.length + modes.length⟩
  have hcaptureLength' : captureArgs.length = captures.length := by
    simpa [captures] using hcaptureLength
  have htotal : args.length = captures.length + modes.length := by
    simp [args, hcaptureLength', hparameterLength]
  have hrootShape : rootsFor .shared args =
      rootsFor .shared captureArgs ++ rootsFor .shared parameterArgs := by
    simp [args, rootsFor]
  have hparameterWorlds : ∀ root,
      root ∈ rootsForWorlds (modes.map worldOfUses) parameterArgs →
      HasWorld store root.world root.value := by
    intro root hroot
    rw [hshared,
      rootsForWorlds_replicate_eq_rootsFor .shared hparameterLength] at hroot
    apply hown.roots_world root
    rw [hrootShape]
    exact List.mem_append_left rest (List.mem_append_right _ hroot)
  have hparameter₀ := parameterEntries_entriesValueGraph
    (funRel := funRel) (recSelfRel := recSelfRel) (store := store)
    parameterRemaining captures.length modes
    (sourceArgs := parameterSources) (args := parameterArgs)
    (suffix := captureArgs.reverse) hparameterLength
    (by simp [hcaptureLength']) hparameters hparameterWorlds
  have hparameter : EntriesValueGraph funRel recSelfRel store Γ
      args.reverse
      (Lower.parameterEntries captures.length modes parameterRemaining)
      parameterSources.reverse
      (rootsForWorlds (modes.map worldOfUses) parameterArgs).reverse := by
    have htransport := hparameter₀.of_depth_eq (Δ := Γ) (by simp [Γ])
    have henv : args.reverse =
        parameterArgs.reverse ++ captureArgs.reverse := by
      simp [args, List.reverse_append]
    simpa [henv] using htransport
  have hall : ValuesAt sourceEnv (List.range entryCount) sourceEnv := by
    rw [← hsourceLength]
    exact ValuesAt.range_self sourceEnv
  have hcaptureWorlds : ∀ value, value ∈ captureArgs →
      HasWorld store .shared value := by
    intro value hvalue
    apply hown.roots_world ⟨.shared, value⟩
    rw [hrootShape]
    apply List.mem_append_left rest
    exact List.mem_append_left _ (by simpa [rootsFor] using hvalue)
  have hcaptureEntries : EntriesValueGraph funRel recSelfRel store Γ
      args.reverse
      (selectedEntriesFrom selected captureRemaining
        (List.range entryCount) 0)
      sourceEnv (rootsFor .shared captureArgs) := by
    apply selectedEntriesFrom_entriesValueGraph selected captureRemaining
      (sourceEnv := sourceEnv)
    · exact hall
    · exact hselected
    · exact hcaptures
    · dsimp [Γ]
      exact Nat.add_pos_right captures.length hpositive
    · simp [Γ, hcaptureLength']
    · intro index hindex
      have hindexArgs : index < args.length := by omega
      have hindexTotal : index < captures.length + modes.length := by omega
      have hreverse := getElem?_reverse_at_absolute
        (values := args) htotal hindexTotal
      have happend : args[index]? = captureArgs[index]? := by
        exact List.getElem?_append_left
          (by simpa [hcaptureLength'] using hindex)
      simpa [Γ, VEnv.rel, htotal] using hreverse.trans happend
    · exact hcaptureWorlds
  refine ⟨?_, ?_⟩
  · simpa [Γ, args, Nat.add_comm] using htotal
  · simpa [Γ, args] using hparameter.append hcaptureEntries

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
  intro indices next depth
  exact selectedEntriesFrom_traverse selected remaining
    (Result := fun _ _ entries => NoRecSelf ⟨entries, depth⟩)
    (hnil := fun _ => NoRecSelf.empty)
    (hfalse := by
      intro index rest current tail hselected htail
      exact htail.consSlot 0 0 .many false)
    (htrue := by
      intro index rest current tail hselected htail
      exact htail.consSlot current (remaining index) .many true)
    indices next

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
      ⟨captures.length + modes.length, .shared, true, code⟩
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
      (cur :=
        (⟨captures.length + modes.length, .shared, true, code⟩ : FnDef))
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
      (⟨captures.length + modes.length, .shared, true, code⟩ : FnDef)
      limit input output .shared (plannedEmit ∘ emit) av :=
    hbodySound.afterRelease hplan.soundBelow
  apply hfull.fnOwnershipPreservesAt
    (FnEntryRealizes.lifted entryCount modes parameterRemaining selected
      captureRemaining hpositive hshared)
  · simp [captures]
  · exact hreleased
  · exact hcode

/-- Semantic execution of one generated lifted body at an exact target
fuel.  The stored capture prefix and the remaining lambda parameters are
separated explicitly: selected outer values populate the framed source
environment, while the complete supplied-parameter vector is reversed in
front of it, exactly as in the source evaluator. -/
theorem lowerFnBody_liftedEntries_run_value_within_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {limit compilerFuel targetFuel : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    (entryCount : Nat) (modes : List Uses) (body : IxIR0.Expr)
    (selected : Nat → Bool)
    {state finalState : LowSt} {code : Code}
    (hadmissible : ParameterDropsAdmissible modes
      (fun index => countUses index body))
    (hselectDef : ∀ index, index < entryCount →
      selected index = (countUses (modes.length + index) body != 0))
    (hpositive : 0 < modes.length)
    (hshared : modes.map worldOfUses =
      List.replicate modes.length .shared)
    (hrun : (lowerFnBody src (compilerFuel + 1)
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
    (hextends : ExtraExtends finalState ambient)
    {sourceEnv selectedSources parameterSources : List IxIR0.Value}
    {sourceResult : IxIR0.Value}
    {store store' : Store} {captureArgs parameterArgs : List RVal}
    {value : RVal} {sourceRest : List (Owned × IxIR0.Value)}
    {rest : List Root}
    (hsourceLength : sourceEnv.length = entryCount)
    (hselectedValues : ValuesAt sourceEnv
      ((List.range entryCount).filter selected) selectedSources)
    (hcaptureLength : captureArgs.length =
      ((List.range entryCount).filter selected).length)
    (hparameterLength : parameterArgs.length = modes.length)
    (hcaptureGraph : Sim.ValuesGraph
      (CompilerFunctionRel sourceCtx src ambient) store selectedSources
      captureArgs)
    (hparameterGraph : Sim.ValuesGraph
      (CompilerFunctionRel sourceCtx src ambient) store parameterSources
      parameterArgs)
    (hsource : ∃ sourceFuel, IxIR0.eval sourceCtx sourceFuel
      (parameterSources.reverse ++ sourceEnv) body = .ok sourceResult)
    (hframe : Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient)
      store sourceRest rest)
    (hown : RootOwnership store
      (rootsFor .shared (captureArgs ++ parameterArgs) ++ rest))
    (htarget : targetFuel ≤ limit)
    (hcodeRun : runCode ctx targetFuel
      ⟨((List.range entryCount).filter selected).length + modes.length,
        .shared, true, code⟩ store (captureArgs ++ parameterArgs).reverse code =
      .ok (store', value)) :
    Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceResult value ∧
      Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceRest rest := by
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
      (lowerFnBody src (compilerFuel + 1) input drops .shared body).run state =
        .ok code finalState := by
    simpa [input, drops, outerEntries, parameterRemaining, captureRemaining,
      captures] using hrun
  simp only [lowerFnBody] at hrun'
  obtain ⟨releaseResult, releaseState, hreleaseRun, hafterRelease⟩ :=
    trackedBindRun_ok_inv hrun'
  rcases releaseResult with ⟨middle, releaseEmit⟩
  obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
    trackedBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, emit, av⟩
  have hpure :
      (releaseEmit ∘ emit) (.ret (av.toAtom output)) = code ∧
        bodyState = finalState := by
    simpa using hafterBody
  obtain ⟨hcode, hbodyState⟩ := hpure
  subst bodyState
  have hinputNo : NoRecSelf input := by
    apply NoRecSelf.appendEntries
    · exact parameterEntries_noRecSelf captures.length modes
        parameterRemaining (captures.length + modes.length)
    · simpa [outerEntries] using
        selectedEntriesFrom_noRecSelf selected captureRemaining
          (List.range entryCount) 0 (captures.length + modes.length)
  have hmiddleNo : NoRecSelf middle :=
    releaseSlots_noRecSelf input hreleaseRun hinputNo
  obtain ⟨parameterOutput, plannedEmit, hparameterPlan,
      hparameterTracks⟩ :=
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
  cases heq.2
  have hparameterOutputLength : parameterOutput.entries.length =
      modes.length := by
    calc
      parameterOutput.entries.length =
          (parameterEntries captures.length modes parameterRemaining).length :=
        hparameterPlan.entries_length
      _ = modes.length := parameterEntries_length _ _ _
  have htracks : EntriesTrackCounts plannedMiddle
      (modes.length + entryCount) (fun index => countUses index body) := by
    have hframed := hparameterTracks.frameSelectedRange
      hparameterOutputLength selected captureRemaining 0 entryCount 0
      (fun offset hoffset => by
        simpa [captureRemaining] using hselectDef offset hoffset)
      (fun offset hoffset => by
        simp [captureRemaining, parameterRemaining])
    simpa [plannedMiddle, outerEntries, List.range_eq_range'] using hframed
  have hconsume := lowerE_consumesEntries hbodyRun
  have hcount := lowerE_preservesEntryCount hbodyRun
  have hmiddleLength : plannedMiddle.entries.length =
      modes.length + entryCount := by
    calc
      plannedMiddle.entries.length = input.entries.length :=
        hplan.entries_length
      _ = modes.length + entryCount := by
        simp [input, outerEntries, parameterRemaining, captureRemaining]
  have hreleased : EntriesReleased output.entries :=
    hconsume.entriesReleased htracks (Eq.trans hcount hmiddleLength)
  obtain ⟨sourceFuel, hsourceEval⟩ := hsource
  have hbodySound : LowerResultValueSoundBelow
      (CompilerFunctionRel sourceCtx src ambient) (fun _ _ => False) ctx
      ⟨captures.length + modes.length, .shared, true, code⟩
        limit plannedMiddle
      output (parameterSources.reverse ++ sourceEnv)
      (parameterSources.reverse ++ sourceEnv) sourceResult .shared emit av :=
    lowerE_run_value_sound_within_noRecSelf_below
      (recSelfRel := fun _ _ => False)
      (cur :=
        (⟨captures.length + modes.length, .shared, true, code⟩ : FnDef))
      henv hrepresented hcontracts hvalues hsourceEval hbodyRun hextends
      hmiddleNo
  have hfull : LowerResultValueSoundBelow
      (CompilerFunctionRel sourceCtx src ambient) (fun _ _ => False) ctx
      ⟨captures.length + modes.length, .shared, true, code⟩
        limit input output
      (parameterSources.reverse ++ sourceEnv)
      (parameterSources.reverse ++ sourceEnv) sourceResult .shared
      (plannedEmit ∘ emit) av :=
    hbodySound.afterRelease
      (hplan.valueSoundBelow (parameterSources.reverse ++ sourceEnv))
  have hentryGraph : VEnvValueGraph
      (CompilerFunctionRel sourceCtx src ambient) (fun _ _ => False) store
      input (parameterSources.reverse ++ sourceEnv)
      (captureArgs ++ parameterArgs).reverse
      ((rootsForWorlds (modes.map worldOfUses) parameterArgs).reverse ++
        rootsFor .shared captureArgs) := by
    simpa [input, outerEntries, parameterRemaining, captureRemaining,
      captures] using
      VEnvValueGraph.lifted (recSelfRel := fun _ _ => False)
        entryCount modes parameterRemaining selected captureRemaining
        hsourceLength hselectedValues hcaptureLength hparameterLength
        hcaptureGraph hparameterGraph hpositive hshared hown
  have hparameterRoots :
      rootsForWorlds (modes.map worldOfUses) parameterArgs =
        rootsFor .shared parameterArgs := by
    rw [hshared]
    exact rootsForWorlds_replicate_eq_rootsFor .shared hparameterLength
  have hpre : GraphOwnsVEnv
      (CompilerFunctionRel sourceCtx src ambient) (fun _ _ => False) input
      (parameterSources.reverse ++ sourceEnv) sourceRest rest store
      (captureArgs ++ parameterArgs).reverse := by
    refine ⟨(rootsForWorlds
        (modes.map worldOfUses) parameterArgs).reverse ++
          rootsFor .shared captureArgs, hentryGraph, hframe, ?_⟩
    have hrootPerm :
        (rootsFor .shared (captureArgs ++ parameterArgs) ++ rest).Perm
          (((rootsForWorlds (modes.map worldOfUses) parameterArgs).reverse ++
              rootsFor .shared captureArgs) ++ rest) := by
      rw [hparameterRoots]
      simp only [rootsFor, List.map_append]
      exact (List.perm_append_comm.trans
        ((List.reverse_perm
          (parameterArgs.map fun value => (⟨.shared, value⟩ : Root))).symm
            |>.append_right (captureArgs.map fun value =>
              (⟨.shared, value⟩ : Root)))).append_right rest
    exact hown.perm hrootPerm
  have hcodeRun' : runCode ctx targetFuel
      ⟨captures.length + modes.length, .shared, true, code⟩ store
      (captureArgs ++ parameterArgs).reverse
      ((plannedEmit ∘ emit) (.ret (av.toAtom output))) =
        .ok (store', value) := by
    rw [hcode]
    simpa [captures] using hcodeRun
  exact hfull.closeGraph hreleased sourceRest rest htarget hpre hcodeRun'

/-- A compiler-provenanced lifted pap computes its residual source closure
when the stored prefix plus the newly supplied arguments saturate the
generated declaration.  This is the generated-function branch needed by
the semantic `applyGo` proof; unlike `FnValuePreservesAt`, selected outer
captures are target calling arguments but are not source applications. -/
theorem invoke_lifted_value_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {limit fuel : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    {sourceFunction sourceResult : IxIR0.Value}
    {address : Ixon.Address} {arity : Nat}
    {captures sourceArgs : List IxIR0.Value}
    {store store' : Store} {got args : List RVal} {value : RVal}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hlifted : CompilerLiftedFunctionRel src ambient sourceFunction address
      arity captures)
    (hgot : Sim.ValuesGraph (CompilerFunctionRel sourceCtx src ambient)
      store captures got)
    (hargs : Sim.ValuesGraph (CompilerFunctionRel sourceCtx src ambient)
      store sourceArgs args)
    (happlies : SourceApplies sourceCtx sourceFunction sourceArgs
      sourceResult)
    (hframe : Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient)
      store sourceRest rest)
    (hown : RootOwnership store
      (rootsFor .shared (got ++ args) ++ rest))
    (hfuel : fuel ≤ limit)
    (hinvoke : invoke ctx fuel address (got ++ args) store =
      .ok (store', value)) :
    Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceResult value ∧
      Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceRest rest := by
  obtain ⟨sourceEnv, expr, selectedSources, suppliedSources, hliftCode,
      hselectedValues, hcaptures, harity, hprefix⟩ := hlifted
  subst captures
  subst arity
  obtain ⟨bodyCompilerFuel, bodyInitial, bodyFinal, code, hsafe,
      hbodyRun, hbodyExtends, hmember⟩ := hliftCode
  have hselectedLength := hselectedValues.length
  rw [← hselectedLength] at hmember
  have hdecl : ctx.decls address = some (.fn
      ⟨selectedSources.length + lamArity expr, .shared, true, code⟩) :=
    hrepresented.decl hmember
  have hmodes := papSafe_lamUses_eq_replicate hsafe
  have hadmissible : ParameterDropsAdmissible (lamUses expr)
      (fun index => countUses index (stripLams expr)) := by
    rw [hmodes]
    exact parameterDropsAdmissible_replicate_many _ _
  have hselectDef : ∀ index, index < sourceEnv.length →
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
  have hpositive : 0 < (lamUses expr).length := by
    have hunder := hprefix.length_lt_lamArity
    rw [lamUses_length]
    omega
  cases bodyCompilerFuel with
  | zero =>
      exact (trackedThrowRun_not_ok
        (by simpa [lowerFnBody] using hbodyRun)).elim
  | succ compilerFuel =>
    let selectedArgs := got.take selectedSources.length
    let suppliedArgs := got.drop selectedSources.length
    have hgotSplit : selectedArgs ++ suppliedArgs = got := by
      exact List.take_append_drop selectedSources.length got
    have hselectedGraph : Sim.ValuesGraph
        (CompilerFunctionRel sourceCtx src ambient) store selectedSources
        selectedArgs := by
      simpa [selectedArgs] using hgot.take selectedSources.length
    have hsuppliedGraph : Sim.ValuesGraph
        (CompilerFunctionRel sourceCtx src ambient) store suppliedSources
        suppliedArgs := by
      simpa [suppliedArgs] using hgot.drop selectedSources.length
    have hparameterGraph : Sim.ValuesGraph
        (CompilerFunctionRel sourceCtx src ambient) store
        (suppliedSources ++ sourceArgs) (suppliedArgs ++ args) :=
      hsuppliedGraph.append hargs
    have hselectedArgsLength : selectedArgs.length =
        (liftCaptureIndices sourceEnv.length expr).length := by
      calc
        selectedArgs.length = selectedSources.length := by
          simpa [selectedArgs] using hselectedGraph.length.symm
        _ = (liftCaptureIndices sourceEnv.length expr).length :=
          hselectedValues.length
    have htotalSplit : selectedArgs ++ (suppliedArgs ++ args) =
        got ++ args := by
      rw [← List.append_assoc, hgotSplit]
    have hownSplit : RootOwnership store
        (rootsFor .shared (selectedArgs ++ (suppliedArgs ++ args)) ++
          rest) := by
      rw [htotalSplit]
      exact hown
    have hbodyRun' :
        (lowerFnBody src (compilerFuel + 1)
          (liftedBodyVEnv sourceEnv.length expr)
          (liftedBodyDrops sourceEnv.length expr) .shared
          (stripLams expr)).run bodyInitial = .ok code bodyFinal := by
      simpa using hbodyRun
    cases fuel with
    | zero => simp [invoke] at hinvoke
    | succ innerFuel =>
      simp only [invoke, hdecl] at hinvoke
      split at hinvoke
      · contradiction
      next hlength =>
        have htotalLength : (got ++ args).length =
            selectedSources.length + lamArity expr := by
          simpa using hlength
        have hparameterLength : (suppliedArgs ++ args).length =
            (lamUses expr).length := by
          have hgotLength : got.length =
              selectedSources.length + suppliedSources.length := by
            simpa using hgot.length.symm
          have hsuppliedLength : suppliedArgs.length =
              suppliedSources.length := hsuppliedGraph.length.symm
          simp only [List.length_append] at htotalLength ⊢
          rw [lamUses_length]
          omega
        have hlambdaLength : (suppliedSources ++ sourceArgs).length =
            lamArity expr := by
          calc
            (suppliedSources ++ sourceArgs).length =
                (suppliedArgs ++ args).length := hparameterGraph.length
            _ = (lamUses expr).length := hparameterLength
            _ = lamArity expr := lamUses_length expr
        obtain ⟨sourceFuel, hsourceEval⟩ :=
          hprefix.saturate hlambdaLength happlies
        cases hcodeEval : runCode ctx innerFuel
            ⟨selectedSources.length + lamArity expr, .shared, true, code⟩
            store
            (got ++ args).reverse code with
        | error error =>
            rw [hcodeEval] at hinvoke
            change (.error error : Except Err (Store × RVal)) =
              .ok (store', value) at hinvoke
            contradiction
        | ok out =>
            rw [hcodeEval] at hinvoke
            change checkResultWorld .shared out = .ok (store', value) at hinvoke
            obtain ⟨hpair, _⟩ := checkResultWorld_ok hinvoke
            subst out
            have hcodeEval' : runCode ctx innerFuel
                ⟨(liftCaptureIndices sourceEnv.length expr).length +
                    (lamUses expr).length,
                  .shared, true, code⟩ store
                (selectedArgs ++ (suppliedArgs ++ args)).reverse code =
                .ok (store', value) := by
              rw [htotalSplit, ← hselectedLength, lamUses_length]
              exact hcodeEval
            exact lowerFnBody_liftedEntries_run_value_within_below
              (compilerFuel := compilerFuel) (targetFuel := innerFuel)
              henv hrepresented hcontracts hvalues sourceEnv.length
              (lamUses expr) (stripLams expr)
              (fun index => countUses index expr > 0)
              hadmissible hselectDef hpositive hshared
              (by simpa [liftedBodyVEnv, liftedBodyDrops,
                liftCaptureIndices] using hbodyRun')
              hbodyExtends (sourceEnv := sourceEnv)
              (selectedSources := selectedSources)
              (parameterSources := suppliedSources ++ sourceArgs)
              (captureArgs := selectedArgs)
              (parameterArgs := suppliedArgs ++ args)
              (sourceResult := sourceResult) rfl
              (by simpa [liftCaptureIndices] using hselectedValues)
              (by simpa [liftCaptureIndices] using hselectedArgsLength)
              hparameterLength hselectedGraph hparameterGraph
              ⟨sourceFuel, hsourceEval⟩ hframe hownSplit (by omega)
              hcodeEval'

/-- Semantic companion of `applyGo_preparePap_owned`.  Retaining the stored
pap values is a graph extension; consuming the old pap is a restriction, and
the exact post-state ownership roots keep every stored argument, new
argument, and caller-frame graph live across both steps. -/
theorem applyGo_preparePap_valueGraphs
    {funRel : Sim.FunctionRel} {ctx : Ctx} {fuel : Nat}
    {store dupStore readyStore : Store} {loc rc : Nat}
    {address : Ixon.Address} {arity : Nat} {got : Array RVal}
    {args : List RVal} {captures sourceArgs : List IxIR0.Value}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hget : store.get? loc = some
      ⟨.shared, rc, .papN address arity got⟩)
    (hcaptures : Sim.ValuesGraph funRel store captures got.toList)
    (hargs : Sim.ValuesGraph funRel store sourceArgs args)
    (hframe : Sim.RootsGraph funRel store sourceRest rest)
    (hown : RootOwnership store
      (⟨.shared, .loc loc⟩ :: rootsFor .shared args ++ rest))
    (hdup : dupVals store got.toList = .ok dupStore)
    (hdrop : dropVal ctx fuel dupStore (.loc loc) = .ok readyStore) :
    Sim.ValuesGraph funRel readyStore captures got.toList ∧
      Sim.ValuesGraph funRel readyStore sourceArgs args ∧
      Sim.RootsGraph funRel readyStore sourceRest rest ∧
      RootOwnership readyStore
        (rootsFor .shared (got.toList ++ args) ++ rest) := by
  have hready : RootOwnership readyStore
      (rootsFor .shared (got.toList ++ args) ++ rest) :=
    applyGo_preparePap_owned hget hown hdup hdrop
  have hextends : StoreGraphExtends store dupStore := dupVals_extends hdup
  have hrestricts : StoreGraphRestricts dupStore readyStore :=
    dropVal_restricts hdrop
  have hcombined : Sim.ValuesGraph funRel dupStore
      (captures ++ sourceArgs) (got.toList ++ args) :=
    (hcaptures.append hargs).monoStore hextends
  have hcombinedReady : Sim.ValuesGraph funRel readyStore
      (captures ++ sourceArgs) (got.toList ++ args) := by
    apply hcombined.ofRestrictsIn hrestricts hready
    intro runtime hmember
    exact ⟨.shared, List.mem_append_left rest (by
      simpa [rootsFor] using hmember)⟩
  obtain ⟨hcapturesReady, hargsReady⟩ :=
    hcombinedReady.splitAppend hcaptures.length
  have hframeReady : Sim.RootsGraph funRel readyStore sourceRest rest := by
    apply hframe.monoStore hextends |>.ofRestrictsIn hrestricts hready
    intro root hmember
    exact List.mem_append_right _ hmember
  exact ⟨hcapturesReady, hargsReady, hframeReady, hready⟩

/-- Ownership half of lifted-function invocation, recovered directly from
the same exact generated-body provenance used by
`invoke_lifted_value_below`. -/
theorem invoke_lifted_owned_below
    {src : IxIR0.Env} {ambient : LowSt} {ctx : Ctx} {fuel : Nat}
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    {sourceFunction : IxIR0.Value} {address : Ixon.Address} {arity : Nat}
    {captures : List IxIR0.Value} {runtimeArgs : List RVal}
    {store store' : Store} {value : RVal} {rest : List Root}
    (hlifted : CompilerLiftedFunctionRel src ambient sourceFunction address
      arity captures)
    (hown : RootOwnership store
      (rootsFor .shared runtimeArgs ++ rest))
    (hinvoke : invoke ctx fuel address runtimeArgs store =
      .ok (store', value)) :
    RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  obtain ⟨sourceEnv, expr, selectedSources, suppliedSources, hliftCode,
      hselectedValues, _, _, hprefix⟩ := hlifted
  obtain ⟨bodyCompilerFuel, bodyInitial, bodyFinal, code, hsafe,
      hbodyRun, hbodyExtends, hmember⟩ := hliftCode
  have hdecl : ctx.decls address = some (.fn
      ⟨(liftCaptureIndices sourceEnv.length expr).length + lamArity expr,
        .shared, true, code⟩) := hrepresented.decl hmember
  have hmodes := papSafe_lamUses_eq_replicate hsafe
  have hadmissible : ParameterDropsAdmissible (lamUses expr)
      (fun index => countUses index (stripLams expr)) := by
    rw [hmodes]
    exact parameterDropsAdmissible_replicate_many _ _
  have hselectDef : ∀ index, index < sourceEnv.length →
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
  have hpositive : 0 < (lamUses expr).length := by
    have hunder := hprefix.length_lt_lamArity
    rw [lamUses_length]
    omega
  cases bodyCompilerFuel with
  | zero =>
      exact (trackedThrowRun_not_ok
        (by simpa [lowerFnBody] using hbodyRun)).elim
  | succ compilerFuel =>
    have hbodyRun' :
        (lowerFnBody src (compilerFuel + 1)
          (liftedBodyVEnv sourceEnv.length expr)
          (liftedBodyDrops sourceEnv.length expr) .shared
          (stripLams expr)).run bodyInitial = .ok code bodyFinal := by
      simpa using hbodyRun
    have hbodyRepresented : ExtraRepresented ctx bodyFinal :=
      hrepresented.of_extends hbodyExtends
    have hownership : FnOwnershipContractBelow ctx
        ⟨(liftCaptureIndices sourceEnv.length expr).length + lamArity expr,
          .shared, true, code⟩
        (List.replicate
          ((liftCaptureIndices sourceEnv.length expr).length +
            lamArity expr) .shared) fuel := by
      constructor
      · simp
      · intro smaller hsmaller
        have hpreserves : FnOwnershipPreservesAt ctx
            ⟨(liftCaptureIndices sourceEnv.length expr).length +
                (lamUses expr).length,
              .shared, true, code⟩
            (List.replicate
              ((liftCaptureIndices sourceEnv.length expr).length +
                (lamUses expr).length) .shared) smaller :=
          lowerFnBody_liftedEntries_preservesAt
          (limit := smaller) (fuel := compilerFuel)
          (state := bodyInitial) (finalState := bodyFinal) (code := code)
          (hcontracts.apply.below smaller)
          (hcontracts.decls.below smaller) sourceEnv.length
          (lamUses expr) (stripLams expr)
          (fun index => countUses index expr > 0)
          hadmissible hselectDef hpositive hshared
          (by simpa [liftedBodyVEnv, liftedBodyDrops,
            liftCaptureIndices] using hbodyRun') hbodyRepresented
        intro callStore callStore' callArgs callValue callRest hlength
          hcallOwn hcallRun
        exact hpreserves
          (by simpa [lamUses_length] using hlength)
          (by simpa [lamUses_length] using hcallOwn)
          (by simpa [lamUses_length] using hcallRun)
    have hargsLength : runtimeArgs.length =
        (liftCaptureIndices sourceEnv.length expr).length +
          lamArity expr := by
      simpa [declArity] using invoke_success_length hdecl hinvoke
    have hroots : rootsForWorlds
        (List.replicate
          ((liftCaptureIndices sourceEnv.length expr).length +
            lamArity expr) .shared) runtimeArgs =
        rootsFor .shared runtimeArgs :=
      rootsForWorlds_replicate_eq_rootsFor .shared hargsLength
    have hown' : RootOwnership store
        (rootsForWorlds
          (List.replicate
            ((liftCaptureIndices sourceEnv.length expr).length +
              lamArity expr) .shared) runtimeArgs ++ rest) := by
      rwa [hroots]
    exact invoke_fn_owned_below hdecl hownership hown' hinvoke

/-- Saturating invocation for every origin admitted by
`CompilerFunctionRel`.  Besides source-result and caller-frame graphs, the
paired ownership conclusion is retained for an over-application tail. -/
theorem invoke_compilerFunction_value_owned_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {limit fuel : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit)
    (hwrapperValue : ∀ (memo : WrapperMemo)
        (baseFunction : IxIR0.Value),
      sourceCtx.env memo.source = some (.ctor memo.tag memo.arity) →
      SourceRefValue sourceCtx memo.source baseFunction →
      FnValueContract (CompilerFunctionRel sourceCtx src ambient)
        sourceCtx ctx
        ⟨memo.arity, .shared, true,
          .letOp (.alloc .shared (ctorIdOf memo.source memo.tag)
            (descendingVars memo.arity).toArray) (.ret (.var 0))⟩
        (List.replicate memo.arity .shared) baseFunction)
    (hwrapperOwnership : ∀ memo : WrapperMemo,
      FnOwnershipContract ctx
        ⟨memo.arity, .shared, true,
          .letOp (.alloc .shared (ctorIdOf memo.source memo.tag)
            (descendingVars memo.arity).toArray) (.ret (.var 0))⟩
        (List.replicate memo.arity .shared))
    {sourceFunction sourceResult : IxIR0.Value}
    {address : Ixon.Address} {arity : Nat}
    {captures sourceArgs : List IxIR0.Value}
    {store store' : Store} {got args : List RVal} {value : RVal}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hrel : CompilerFunctionRel sourceCtx src ambient sourceFunction address
      arity captures)
    (hcaptures : Sim.ValuesGraph
      (CompilerFunctionRel sourceCtx src ambient) store captures got)
    (hargs : Sim.ValuesGraph (CompilerFunctionRel sourceCtx src ambient)
      store sourceArgs args)
    (happlies : SourceApplies sourceCtx sourceFunction sourceArgs
      sourceResult)
    (hframe : Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient)
      store sourceRest rest)
    (hown : RootOwnership store
      (rootsFor .shared (got ++ args) ++ rest))
    (hfuel : fuel ≤ limit)
    (hinvoke : invoke ctx fuel address (got ++ args) store =
      .ok (store', value)) :
    Sim.ValueGraph (CompilerFunctionRel sourceCtx src ambient) store'
        sourceResult value ∧
      Sim.RootsGraph (CompilerFunctionRel sourceCtx src ambient) store'
          sourceRest rest ∧
        RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  cases hrel with
  | @source relatedFunction baseFunction targetAddress targetArity
      storedSources source hsrc heligible harity href hprefix hunder =>
    have hfullGraph : Sim.ValuesGraph
        (CompilerFunctionRel sourceCtx src ambient) store
        (captures ++ sourceArgs) (got ++ args) :=
      hcaptures.append hargs
    have hfullApply : SourceApplies sourceCtx baseFunction
        (captures ++ sourceArgs) sourceResult :=
      hprefix.append happlies
    cases source with
    | defn result body =>
      obtain ⟨hresultShared, hsafe⟩ := heligible
      subst result
      obtain ⟨d, hdecl, harityDef, hresultDef, hownership⟩ :=
        hcontracts.decls.defn hsrc
      have hvalueContract : FnValueContractBelow
          (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx d
          ((lamUses body).map worldOfUses) baseFunction limit := by
        apply hvalues.decls.fnContract hsrc (by rfl) hdecl href
        simpa using harityDef.symm
      have hmodes := papSafe_lamUses_eq_replicate hsafe
      have hworlds : (lamUses body).map worldOfUses =
          List.replicate (lamUses body).length .shared := by
        rw [hmodes]
        simp [worldOfUses]
      have htotalLength : (got ++ args).length =
          (lamUses body).length := by
        have hinvokeLength := invoke_success_length hdecl hinvoke
        simpa [declArity, harityDef] using hinvokeLength
      have hroots : rootsForWorlds
          ((lamUses body).map worldOfUses) (got ++ args) =
          rootsFor .shared (got ++ args) := by
        rw [hworlds]
        exact rootsForWorlds_replicate_eq_rootsFor .shared htotalLength
      have hown' : RootOwnership store
          (rootsForWorlds ((lamUses body).map worldOfUses)
            (got ++ args) ++ rest) := by
        rwa [hroots]
      have hsemantic := invoke_fn_value_below hdecl
        hvalueContract.arity_eq
        (fun {smaller} hsmaller => hvalueContract.preserves
          (Nat.lt_of_lt_of_le hsmaller hfuel))
        hfullGraph hfullApply hframe hown' hinvoke
      have howned := invoke_fn_owned hdecl hownership hown' hinvoke
      rw [hresultDef] at howned
      exact ⟨hsemantic.1, hsemantic.2, howned⟩
    | ctor tag ctorArity => exact heligible.elim
    | recursor numArgs natLit rules =>
      obtain ⟨d, hdecl, harityRec, hresultRec, hownership⟩ :=
        hcontracts.decls.recursor hsrc
      have hvalueContract : FnValueContractBelow
          (CompilerFunctionRel sourceCtx src ambient) sourceCtx ctx d
          (List.replicate (numArgs + 1) .shared) baseFunction limit := by
        apply hvalues.decls.fnContract hsrc (by rfl) hdecl href
        simpa using harityRec.symm
      have htotalLength : (got ++ args).length = numArgs + 1 := by
        have hinvokeLength := invoke_success_length hdecl hinvoke
        simpa [declArity, harityRec] using hinvokeLength
      have hroots : rootsForWorlds
          (List.replicate (numArgs + 1) .shared) (got ++ args) =
          rootsFor .shared (got ++ args) :=
        rootsForWorlds_replicate_eq_rootsFor .shared htotalLength
      have hown' : RootOwnership store
          (rootsForWorlds (List.replicate (numArgs + 1) .shared)
            (got ++ args) ++ rest) := by
        rwa [hroots]
      have hsemantic := invoke_fn_value_below hdecl
        hvalueContract.arity_eq
        (fun {smaller} hsmaller => hvalueContract.preserves
          (Nat.lt_of_lt_of_le hsmaller hfuel))
        hfullGraph hfullApply hframe hown' hinvoke
      have howned := invoke_fn_owned hdecl hownership hown' hinvoke
      rw [hresultRec] at howned
      exact ⟨hsemantic.1, hsemantic.2, howned⟩
    | extern externArity =>
      have hdecl := hcontracts.decls.extern hsrc
      have hlookup : sourceCtx.env address =
          some (.extern externArity) := by
        rw [henv]
        exact hsrc
      have hsourceLength : (captures ++ sourceArgs).length =
          externArity := by
        have hinvokeLength := invoke_success_length hdecl hinvoke
        have hgraphLength := hfullGraph.length
        simpa [declArity] using hgraphLength.trans hinvokeLength
      cases fuel with
      | zero => simp [invoke] at hinvoke
      | succ innerFuel =>
        simp only [invoke, hdecl] at hinvoke
        split at hinvoke
        · contradiction
        next _ =>
          cases horacle : callScalarOracle ctx address (got ++ args) with
          | error error =>
              rw [horacle] at hinvoke
              contradiction
          | ok runtimeResult =>
              rw [horacle] at hinvoke
              have hpair : (store, runtimeResult) = (store', value) :=
                Except.ok.inj hinvoke
              cases hpair
              have hvalueGraph := hvalues.extern.preserves hlookup href
                hsourceLength hfullApply hfullGraph horacle
              have hscalar := callScalarOracle_ok horacle
              have howned : RootOwnership store
                  (⟨.shared, value⟩ :: rest) :=
                (hown.dropScalars hscalar.1).addNoLocation
                  (RVal.rvalLocation?_eq_none_of_isScalar hscalar.2)
              exact ⟨hvalueGraph, hframe, howned⟩
  | @wrapper relatedFunction baseFunction storedSources memo hmember hsrc
      href hprefix hunder =>
    let wrapperDef : FnDef :=
      ⟨memo.arity, .shared, true,
        .letOp (.alloc .shared (ctorIdOf memo.source memo.tag)
          (descendingVars memo.arity).toArray) (.ret (.var 0))⟩
    have hdecl : ctx.decls memo.wrapper = some (.fn wrapperDef) := by
      simpa [wrapperDef, ctorWrapperDecl] using
        hrepresented.wrapper hmember
    have hlookup : sourceCtx.env memo.source =
        some (.ctor memo.tag memo.arity) := by
      rw [henv]
      exact hsrc
    have hfullGraph : Sim.ValuesGraph
        (CompilerFunctionRel sourceCtx src ambient) store
        (captures ++ sourceArgs) (got ++ args) :=
      hcaptures.append hargs
    have hfullApply : SourceApplies sourceCtx baseFunction
        (captures ++ sourceArgs) sourceResult :=
      hprefix.append happlies
    have hvalueContract := hwrapperValue memo baseFunction hlookup href
    have hownership := hwrapperOwnership memo
    have htotalLength : (got ++ args).length = memo.arity := by
      have hinvokeLength := invoke_success_length hdecl hinvoke
      simpa [wrapperDef, declArity] using hinvokeLength
    have hroots : rootsForWorlds
        (List.replicate memo.arity .shared) (got ++ args) =
        rootsFor .shared (got ++ args) :=
      rootsForWorlds_replicate_eq_rootsFor .shared htotalLength
    have hown' : RootOwnership store
        (rootsForWorlds (List.replicate memo.arity .shared)
          (got ++ args) ++ rest) := by
      rwa [hroots]
    have hsemantic := invoke_fn_value_below hdecl hvalueContract.arity_eq
      (fun {_} _ => hvalueContract.preserves) hfullGraph hfullApply hframe
      hown' hinvoke
    have howned := invoke_fn_owned hdecl hownership hown' hinvoke
    exact ⟨hsemantic.1, hsemantic.2, howned⟩
  | lifted hlifted =>
    have hsemantic := invoke_lifted_value_below henv hrepresented
      hcontracts hvalues hlifted hcaptures hargs happlies hframe hown hfuel
      hinvoke
    have howned := invoke_lifted_owned_below hrepresented hcontracts
      hlifted hown hinvoke
    exact ⟨hsemantic.1, hsemantic.2, howned⟩

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
        ⟨captures.length + lamArity expr, .shared, true, code⟩) ∈
          finalState.extra ∧
      ctx.decls address = some (.fn
        ⟨captures.length + lamArity expr, .shared, true, code⟩) ∧
      FnOwnershipPreservesAt ctx
        ⟨captures.length + lamArity expr, .shared, true, code⟩
        (List.replicate (captures.length + lamArity expr) .shared) limit := by
  let captures := liftCaptureIndices input.entries.length expr
  change ∃ address code,
    (address, .fn
      ⟨captures.length + lamArity expr, .shared, true, code⟩) ∈
        finalState.extra ∧
    ctx.decls address = some (.fn
      ⟨captures.length + lamArity expr, .shared, true, code⟩) ∧
    FnOwnershipPreservesAt ctx
      ⟨captures.length + lamArity expr, .shared, true, code⟩
      (List.replicate (captures.length + lamArity expr) .shared) limit
  refine lowerLam_run_core
    (Result := fun finalState _ _ _ =>
      ExtraRepresented ctx finalState →
      ∃ address code,
        (address, .fn
          ⟨captures.length + lamArity expr, .shared, true, code⟩) ∈
            finalState.extra ∧
        ctx.decls address = some (.fn
          ⟨captures.length + lamArity expr, .shared, true, code⟩) ∧
        FnOwnershipPreservesAt ctx
          ⟨captures.length + lamArity expr, .shared, true, code⟩
          (List.replicate
            (captures.length + lamArity expr) .shared) limit)
    ?_ hrun hrepresented
  intro bodyFuel _captureOutput _captureEmit _captureValues _captureState
    fnAddr addressState code bodyState _hfuel hp _hcaptureRun _hfreshRun hbodyRun
    hrepresented
  let ambient : LowSt :=
    { bodyState with
      extra := (fnAddr, .fn
        ⟨captures.length + lamArity expr, .shared, true, code⟩) ::
          bodyState.extra }
  change ExtraRepresented ctx ambient at hrepresented
  have hextends : ExtraExtends bodyState ambient := by
    refine ⟨[(fnAddr, .fn
      ⟨captures.length + lamArity expr, .shared, true, code⟩)],
      [], ?_, ?_, ?_⟩
    · simp [ambient]
    · simp [ambient]
    · simp
  have hbodyRepresented : ExtraRepresented ctx bodyState :=
    hrepresented.of_extends hextends
  have hmember :
      (fnAddr, .fn
        ⟨captures.length + lamArity expr, .shared, true, code⟩) ∈
          ambient.extra := by
    simp [ambient]
  have hdecl := hrepresented.decl hmember
  have hmodes := papSafe_lamUses_eq_replicate hp
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
  cases bodyFuel with
  | zero =>
    exact (trackedThrowRun_not_ok
      (by simpa [lowerFnBody] using hbodyRun)).elim
  | succ innerFuel =>
    have hbodyRun' :
        (lowerFnBody src (innerFuel + 1)
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
      simpa [liftedBodyVEnv, liftedBodyDrops, liftCaptureIndices,
        lamUses_length] using hbodyRun
    have hpreserves : FnOwnershipPreservesAt ctx
        ⟨captures.length + (lamUses expr).length, .shared, true, code⟩
        (List.replicate
          (captures.length + (lamUses expr).length) .shared) limit := by
      exact lowerFnBody_liftedEntries_preservesAt
        (fuel := innerFuel) (state := addressState)
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
      ⟨arity, .shared, true,
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

/-- A constructor eta-wrapper has the corresponding source semantics at
every target evaluator index.  The wrapper's allocation is fresh, so the
argument graphs become constructor-field graphs while the caller frame is
transported through the one-node store extension. -/
theorem ctorWrapper_fnValueContract
    {funRel : Sim.FunctionRel} (sourceCtx : IxIR0.Ctx) (ctx : Ctx)
    (source : Ixon.Address) (tag arity : Nat)
    (sourceFunction : IxIR0.Value)
    (hlookup : sourceCtx.env source = some (.ctor tag arity))
    (href : SourceRefValue sourceCtx source sourceFunction) :
    FnValueContract funRel sourceCtx ctx
      ⟨arity, .shared, true,
        .letOp (.alloc .shared (ctorIdOf source tag)
          (descendingVars arity).toArray)
          (.ret (.var 0))⟩
      (List.replicate arity .shared) sourceFunction := by
  constructor
  · simp
  · intro fuel store store' args value sourceArgs sourceResult
      sourceRest rest hlength hargs hsource hframe hown hrun
    have hargsLength : args.length = arity := by simpa using hlength
    have hsourceArgsLength : sourceArgs.length = arity := by
      simpa [hargsLength] using hargs.length
    have hcanonical : SourceApplies sourceCtx sourceFunction sourceArgs
        (.ctor source tag sourceArgs) :=
      sourceCtorRef_saturates hlookup href hsourceArgsLength
    have hsourceResult : sourceResult = .ctor source tag sourceArgs :=
      hsource.deterministic hcanonical
    subst sourceResult
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
        let node : Node :=
          .ctorN (ctorIdOf source tag) args.toArray
        let allocated := store.allocNode .shared node
        have hextends : Sim.StoreGraphExtends store allocated.1 :=
          Sim.StoreGraphExtends.allocNode store .shared node
        have hfields : Sim.ValuesGraph funRel allocated.1 sourceArgs args :=
          hargs.monoStore hextends
        have hresultGraph : Sim.ValueGraph funRel allocated.1
            (.ctor source tag sourceArgs) (.loc allocated.2) := by
          apply Sim.ValueGraph.ctor
          · exact Sim.HeapIso.get?_allocNode_new store .shared node
          · rfl
          · rfl
          · simpa [node] using hfields
        have hframeAfter : Sim.RootsGraph funRel allocated.1
            sourceRest rest := hframe.monoStore hextends
        simpa [allocated, node] using And.intro hresultGraph hframeAfter

/-- Exact semantic preservation for `applyGo` at the current evaluator
index.  Declaration and recursive-application semantics are required only
strictly below this index through `hvalues`; generated lifted bodies are
recovered from their compiler provenance. -/
theorem applyValuePreservesAt_within_below
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ambient : LowSt}
    {ctx : Ctx} {limit : Nat}
    (henv : sourceCtx.env = src)
    (hrepresented : ExtraRepresented ctx ambient)
    (hcontracts : CompilerContracts src ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx src ambient) sourceCtx src ctx limit) :
    ApplyValuePreservesAt (CompilerFunctionRel sourceCtx src ambient)
      sourceCtx ctx limit := by
  intro store store' function args value sourceFunction sourceArgs
    sourceResult sourceRest rest hfunction hargs happlies hframe hown hrun
  cases limit with
  | zero => simp [applyGo] at hrun
  | succ fuel =>
    cases hfunction with
    | lit => simp [applyGo] at hrun
    | erased =>
      have hsourceResult : sourceResult = .erased :=
        happlies.deterministic (SourceApplies.erased sourceCtx sourceArgs)
      subst sourceResult
      have hargsOwn : RootOwnership store
          (rootsFor .shared args ++ rest) :=
        hown.dropNoLocation rfl
      simp only [applyGo] at hrun
      cases hdrop : dropMany ctx fuel store args with
      | error error =>
        rw [hdrop, wrapperBindErr] at hrun
        contradiction
      | ok dropped =>
        rw [hdrop, wrapperBindOk] at hrun
        have hrestOwn : RootOwnership dropped rest :=
          dropMany_preserves hargsOwn hdrop
        have hrestrict : StoreGraphRestricts store dropped :=
          dropMany_restricts hdrop
        injection hrun with hpair
        cases hpair
        exact ⟨.erased,
          hframe.ofRestricts hrestrict hrestOwn⟩
    | @ctor sourceAddress sourceTag sourceFields loc boxWorld rc cid fields
        hget haddress htag hfields =>
      simp [applyGo, hget] at hrun
    | @function relatedFunction address arity captures loc rc got hget hfun
        hgot =>
      simp only [applyGo] at hrun
      rw [hget] at hrun
      dsimp only at hrun
      cases hdup : dupVals store got.toList with
      | error error =>
        rw [hdup, wrapperBindErr] at hrun
        contradiction
      | ok dupStore =>
        rw [hdup, wrapperBindOk] at hrun
        cases hdrop : dropVal ctx fuel dupStore (.loc loc) with
        | error error =>
          rw [hdrop, wrapperBindErr] at hrun
          contradiction
        | ok readyStore =>
          rw [hdrop, wrapperBindOk] at hrun
          let total := got.toList ++ args
          obtain ⟨hgotReady, hargsReady, hframeReady, hready⟩ :=
            applyGo_preparePap_valueGraphs hget hgot hargs hframe hown
              hdup hdrop
          split at hrun
          next hunder =>
            have hsourceUnder : (captures ++ sourceArgs).length < arity := by
              have htotalGraph := hgotReady.append hargsReady
              have hlength := htotalGraph.length
              rw [hlength]
              simpa [total] using hunder
            have hnewRel := hfun.underfilledApply happlies hsourceUnder
            injection hrun with hpair
            cases hpair
            let node : Node := .papN address arity total.toArray
            let allocated := readyStore.allocNode .shared node
            have hextends : StoreGraphExtends readyStore allocated.1 :=
              StoreGraphExtends.allocNode readyStore .shared node
            have htotalGraph : Sim.ValuesGraph
                (CompilerFunctionRel sourceCtx src ambient) allocated.1
                (captures ++ sourceArgs) total := by
              exact (hgotReady.append hargsReady).monoStore hextends
            have hresultGraph : Sim.ValueGraph
                (CompilerFunctionRel sourceCtx src ambient) allocated.1
                sourceResult (.loc allocated.2) := by
              apply Sim.ValueGraph.function
              · exact Sim.HeapIso.get?_allocNode_new readyStore .shared node
              · exact hnewRel
              · simpa [node] using htotalGraph
            have hframeAfter := hframeReady.monoStore hextends
            simpa [allocated, node, total] using
              And.intro hresultGraph hframeAfter
          next hnotUnder =>
            split at hrun
            next hexact =>
              have hsafety : ∃ declaration,
                  ctx.decls address = some declaration ∧
                    declPapSafe declaration = true := by
                cases hdecl : ctx.decls address with
                | none => simp [hdecl] at hrun
                | some declaration =>
                  cases hpapsafe : declPapSafe declaration with
                  | false => simp [hdecl, hpapsafe] at hrun
                  | true => exact ⟨declaration, rfl, hpapsafe⟩
              obtain ⟨declaration, hdecl, hpapsafe⟩ := hsafety
              simp only [hdecl, hpapsafe, if_true] at hrun
              have hcalled := invoke_compilerFunction_value_owned_below
                henv hrepresented hcontracts hvalues
                (fun memo baseFunction hlookup href =>
                  ctorWrapper_fnValueContract
                    (funRel := CompilerFunctionRel sourceCtx src ambient)
                    sourceCtx ctx memo.source memo.tag memo.arity
                    baseFunction hlookup href)
                (fun memo => ctorWrapper_fnOwnershipContract ctx memo.source
                  memo.tag memo.arity)
                hfun hgotReady hargsReady happlies hframeReady hready
                (Nat.le_succ fuel) hrun
              exact ⟨hcalled.1, hcalled.2.1⟩
            next hover =>
              have hsafety : ∃ declaration,
                  ctx.decls address = some declaration ∧
                    declPapSafe declaration = true := by
                cases hdecl : ctx.decls address with
                | none => simp [hdecl] at hrun
                | some declaration =>
                  cases hpapsafe : declPapSafe declaration with
                  | false => simp [hdecl, hpapsafe] at hrun
                  | true => exact ⟨declaration, rfl, hpapsafe⟩
              obtain ⟨declaration, hdecl, hpapsafe⟩ := hsafety
              simp only [hdecl, hpapsafe, if_true] at hrun
              have hfunUnder := hfun.underfilled
              have hgotUnder : got.toList.length < arity := by
                have hlength := hgotReady.length
                omega
              have hgotLe : got.toList.length ≤ arity :=
                Nat.le_of_lt hgotUnder
              have hoverLength : arity < total.length := by
                have hnotExact : total.length ≠ arity := by
                  intro heq
                  apply hover
                  simpa [total] using heq
                have hle : arity ≤ total.length :=
                  Nat.le_of_not_gt hnotUnder
                omega
              let missing := arity - got.toList.length
              have hmissing : got.toList.length + missing = arity := by
                exact Nat.add_sub_of_le hgotLe
              have hmissingLe : missing ≤ args.length := by
                simp only [total, List.length_append] at hoverLength
                omega
              have htakeTotal : total.take arity =
                  got.toList ++ args.take missing := by
                rw [List.take_append]
                rw [List.take_of_length_le hgotLe]
              have hdropTotal : total.drop arity = args.drop missing := by
                rw [List.drop_append]
                rw [List.drop_eq_nil_of_le hgotLe]
                rfl
              have hsourceWhole : SourceApplies sourceCtx sourceFunction
                  (sourceArgs.take missing ++ sourceArgs.drop missing)
                  sourceResult := by
                rw [List.take_append_drop]
                exact happlies
              obtain ⟨middleSource, hprefixApply, htailApply⟩ :=
                hsourceWhole.split
              have hprefixGraph := hargsReady.take missing
              have htailGraph := hargsReady.drop missing
              have htailWorld : ∀ runtime,
                  runtime ∈ args.drop missing →
                  HasWorld readyStore .shared runtime := by
                intro runtime hmember
                apply hready.roots_world ⟨.shared, runtime⟩
                apply List.mem_append_left rest
                have hmemberArgs : runtime ∈ args :=
                  List.mem_of_mem_drop hmember
                have hmemberTotal : runtime ∈ total := by
                  exact List.mem_append_right got.toList hmemberArgs
                simpa [total, rootsFor] using hmemberTotal
              let tailSourceRest : List (Owned × IxIR0.Value) :=
                (sourceArgs.drop missing).map
                  (fun source => (.shared, source))
              let tailRoots : List Root :=
                rootsFor .shared (args.drop missing)
              have htailFrame : Sim.RootsGraph
                  (CompilerFunctionRel sourceCtx src ambient) readyStore
                  tailSourceRest tailRoots := by
                exact htailGraph.rootsGraph .shared htailWorld
              have hcombinedFrame : Sim.RootsGraph
                  (CompilerFunctionRel sourceCtx src ambient) readyStore
                  (tailSourceRest ++ sourceRest) (tailRoots ++ rest) :=
                htailFrame.append hframeReady
              have hrootsSplit : rootsFor .shared total =
                  rootsFor .shared (total.take arity) ++
                    rootsFor .shared (total.drop arity) := by
                unfold rootsFor
                rw [← List.map_append]
                exact congrArg _ (List.take_append_drop arity total).symm
              have hpartition : RootOwnership readyStore
                  (rootsFor .shared (got.toList ++ args.take missing) ++
                    (tailRoots ++ rest)) := by
                have hsplit := hready
                rw [hrootsSplit] at hsplit
                rw [htakeTotal, hdropTotal] at hsplit
                simpa [tailRoots, List.append_assoc] using hsplit
              cases hinvoke : invoke ctx fuel address
                  (total.take arity) readyStore with
              | error error =>
                  rw [hinvoke, wrapperBindErr] at hrun
                  contradiction
              | ok called =>
                rcases called with ⟨calledStore, calledValue⟩
                rw [hinvoke, wrapperBindOk] at hrun
                have hinvokePrefix : invoke ctx fuel address
                    (got.toList ++ args.take missing) readyStore =
                    .ok (calledStore, calledValue) := by
                  rw [← htakeTotal]
                  exact hinvoke
                have hcalled := invoke_compilerFunction_value_owned_below
                  henv hrepresented hcontracts hvalues
                  (fun memo baseFunction hlookup href =>
                    ctorWrapper_fnValueContract
                      (funRel := CompilerFunctionRel sourceCtx src ambient)
                      sourceCtx ctx memo.source memo.tag memo.arity
                      baseFunction hlookup href)
                  (fun memo => ctorWrapper_fnOwnershipContract ctx
                    memo.source memo.tag memo.arity)
                  hfun hgotReady hprefixGraph hprefixApply hcombinedFrame
                  hpartition (Nat.le_succ fuel) hinvokePrefix
                have htailLength : tailSourceRest.length = tailRoots.length := by
                  simp [tailSourceRest, tailRoots, rootsFor,
                    hargsReady.length]
                obtain ⟨htailFrameAfter, hframeAfter⟩ :=
                  hcalled.2.1.splitAppend htailLength
                have htailGraphAfter : Sim.ValuesGraph
                    (CompilerFunctionRel sourceCtx src ambient) calledStore
                    (sourceArgs.drop missing) (args.drop missing) := by
                  exact htailFrameAfter.valuesGraph
                have hrecursiveRun : applyGo ctx fuel calledStore calledValue
                    (args.drop missing) = .ok (store', value) := by
                  change applyGo ctx fuel calledStore calledValue
                    (total.drop arity) = .ok (store', value) at hrun
                  rw [hdropTotal] at hrun
                  exact hrun
                exact hvalues.apply.preserves (Nat.lt_succ_self fuel)
                  hcalled.1 htailGraphAfter htailApply hframeAfter
                  hcalled.2.2 hrecursiveRun

/-! ### Whole-pass semantic contract sealing -/

/-- A successful lookup in the source list environment identifies the exact
source declaration occurrence traversed by `lowerAllAction`.  No no-duplicate
assumption is needed in this direction: `Env.ofList` returns an actual
`find?` member. -/
theorem sourceEnv_ofList_lookup_mem
    {decls : List (Ixon.Address × IxIR0.Decl)}
    {address : Ixon.Address} {source : IxIR0.Decl}
    (hlookup : IxIR0.Env.ofList decls address = some source) :
    (address, source) ∈ decls := by
  unfold IxIR0.Env.ofList at hlookup
  obtain ⟨item, hfind, hvalue⟩ :=
    Option.map_eq_some_iff.mp hlookup
  rcases item with ⟨itemAddress, itemSource⟩
  have hbeq : itemAddress == address :=
    List.find?_some
      (p := fun item : Ixon.Address × IxIR0.Decl =>
        item.1 == address) hfind
  have haddress : itemAddress = address :=
    Ixon.Address.eq_of_beq hbeq
  have hsource : itemSource = source := by
    simpa using hvalue
  subst itemAddress
  subst itemSource
  exact List.mem_of_find?_eq_some hfind

/-- The IxIR₁ list environment likewise returns an actual declaration
occurrence.  This reverse lookup is the bridge from an exact raw target
context to the whole-pass declaration list. -/
theorem targetEnv_ofList_lookup_mem
    {decls : List (Ixon.Address × Decl)}
    {address : Ixon.Address} {declaration : Decl}
    (hlookup : Env.ofList decls address = some declaration) :
    (address, declaration) ∈ decls := by
  unfold Env.ofList at hlookup
  obtain ⟨item, hfind, hvalue⟩ :=
    Option.map_eq_some_iff.mp hlookup
  rcases item with ⟨itemAddress, itemDeclaration⟩
  have hbeq : itemAddress == address :=
    List.find?_some
      (p := fun item : Ixon.Address × Decl =>
        item.1 == address) hfind
  have haddress : itemAddress = address :=
    Ixon.Address.eq_of_beq hbeq
  have hdeclaration : itemDeclaration = declaration := by
    simpa using hvalue
  subst itemAddress
  subst itemDeclaration
  exact List.mem_of_find?_eq_some hfind

/-- Every callable source row traversed by the whole pass is the row selected
by its list environment.  Validated addressed erasure supplies this premise
from its collision-free producer namespace. -/
def SourceCallableRowsSelected
    (decls : List (Ixon.Address × IxIR0.Decl)) : Prop :=
  ∀ {address source worlds result},
    (address, source) ∈ decls →
    sourceCallableSignature source = some (worlds, result) →
    IxIR0.Env.ofList decls address = some source

/-- Recover the exact same-address callable declaration run selected by the
final target context.  This is the semantic counterpart of the concrete
fixture's `addLowerDecl_run`, generalized to any successful whole pass. -/
theorem lowerAllAction_callable_decl_trace
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx} {address : Ixon.Address} {source : IxIR0.Decl}
    {worlds : List Owned} {result : Owned} {d : FnDef}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hsrc : IxIR0.Env.ofList decls address = some source)
    (hsignature : sourceCallableSignature source = some (worlds, result))
    (hdecl : ctx.decls address = some (.fn d)) :
    ∃ itemInitial itemFinal,
      (lowerDecl (IxIR0.Env.ofList decls) compilerFuel
        (address, source)).run itemInitial =
          .ok (some (address, .fn d)) itemFinal ∧
      ExtraExtends itemFinal finalState := by
  obtain ⟨itemInitial, itemFinal, output, hrun, hextends, houtput⟩ :=
    lowerAllAction_decl_trace hlower (sourceEnv_ofList_lookup_mem hsrc)
  obtain ⟨generated, hgenerated⟩ :=
    lowerDecl_output_fn_of_callable hsignature hrun
  have hgeneratedDecl : ctx.decls address = some (.fn generated) :=
    htarget (houtput _ hgenerated)
  have hd : generated = d := by
    have heq : some (Decl.fn generated) = some (Decl.fn d) :=
      hgeneratedDecl.symm.trans hdecl
    exact Decl.fn.inj (Option.some.inj heq)
  subst generated
  rw [hgenerated] at hrun
  exact ⟨itemInitial, itemFinal, hrun, hextends⟩

/-- A successful whole pass determines the complete same-address layout of
every callable source declaration represented by its returned raw target
list. -/
theorem lowerAllAction_sourceDeclLayout
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl) :
    SourceDeclLayout (IxIR0.Env.ofList decls) ctx := by
  constructor
  · intro address source worlds result hsrc hsignature
    obtain ⟨itemInitial, itemFinal, output, hrun, _, houtput⟩ :=
      lowerAllAction_decl_trace hlower
        (sourceEnv_ofList_lookup_mem hsrc)
    obtain ⟨d, hemitted, harity, hresult⟩ :=
      lowerDecl_output_fn_layout_of_callable hsignature hrun
    exact ⟨d, htarget (houtput _ hemitted), harity, hresult⟩
  · intro address arity hsrc
    obtain ⟨itemInitial, itemFinal, output, hrun, _, houtput⟩ :=
      lowerAllAction_decl_trace hlower
        (sourceEnv_ofList_lookup_mem hsrc)
    have hemitted : output = some (address, .extern arity) := by
      symm
      simpa [lowerDecl] using congrArg
        (fun result : EStateM.Result String LowSt
            (Option (Ixon.Address × Decl)) =>
          match result with
          | .ok value _ => value
          | .error _ _ => none) hrun
    exact htarget (houtput _ hemitted)

/-- A successful ordinary-definition lowering run exposes the PAP-safety bit
computed from the source result world and body. -/
theorem lowerDecl_defn_papSafe_of_run
    {src : IxIR0.Env} {fuel : Nat} {address : Ixon.Address}
    {result : Owned} {body : IxIR0.Expr} {initial final : LowSt}
    {d : FnDef}
    (hrun : (lowerDecl src fuel (address, .defn result body)).run initial =
      .ok (some (address, .fn d)) final)
    (hresult : result = .shared) (hbody : papSafe body = true) :
    d.papSafe = true := by
  simp only [lowerDecl] at hrun
  obtain ⟨code, bodyState, _, hpureRun⟩ := trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn ⟨lamArity body, result,
        result == .shared && papSafe body, code⟩) =
          some (address, Decl.fn d) ∧ bodyState = final := by
    simpa using hpureRun
  have hd : d = ⟨lamArity body, result,
      result == .shared && papSafe body, code⟩ := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2.symm
  subst d
  simp [hresult, hbody]

/-- Generated recursor declarations always permit dynamic PAP entry. -/
theorem lowerDecl_recursor_papSafe_of_run
    {src : IxIR0.Env} {fuel numArgs : Nat} {address : Ixon.Address}
    {natLit : Bool} {rules : Array IxIR0.RecRule}
    {initial final : LowSt} {d : FnDef}
    (hrun : (lowerDecl src fuel
      (address, .recursor numArgs natLit rules)).run initial =
        .ok (some (address, .fn d)) final) :
    d.papSafe = true := by
  simp only [lowerDecl] at hrun
  obtain ⟨actual, recursorState, hrecursorRun, hafterRecursor⟩ :=
    trackedBindRun_ok_inv hrun
  have hpure :
      some (address, Decl.fn actual) = some (address, Decl.fn d) ∧
        recursorState = final := by
    simpa using hafterRecursor
  have hd : actual = d := by
    have hp := Option.some.inj hpure.1
    exact Decl.fn.inj (Prod.mk.inj hp).2
  subst actual
  simp only [lowerRecursor] at hrecursorRun
  obtain ⟨alts, rulesState, _, hafterRules⟩ :=
    trackedBindRun_ok_inv hrecursorRun
  have hshape :
      (⟨numArgs + 1, .shared, true,
        .case (.var 0) natLit alts.toArray⟩ : FnDef) = d ∧
        rulesState = recursorState := by
    simpa using hafterRules
  rw [← hshape.1]

/-- If the emitted function admits dynamic PAP entry, its source signature is
homogeneously shared.  Definitions recover both facts from the committed
`papSafe` bit; recursors have that signature by construction. -/
theorem lowerDecl_callable_signature_of_papSafe_run
    {src : IxIR0.Env} {fuel : Nat} {address : Ixon.Address}
    {source : IxIR0.Decl} {worlds : List Owned} {result : Owned}
    {initial final : LowSt} {d : FnDef}
    (hsignature : sourceCallableSignature source = some (worlds, result))
    (hrun : (lowerDecl src fuel (address, source)).run initial =
      .ok (some (address, .fn d)) final)
    (hsafe : d.papSafe = true) :
    result = .shared ∧
      worlds = List.replicate worlds.length .shared := by
  cases source with
  | defn sourceResult body =>
      simp only [sourceCallableSignature, Option.some.injEq,
        Prod.mk.injEq] at hsignature
      obtain ⟨rfl, rfl⟩ := hsignature
      simp only [lowerDecl] at hrun
      obtain ⟨code, bodyState, _, hpureRun⟩ :=
        trackedBindRun_ok_inv hrun
      have hpure :
          some (address, Decl.fn
            ⟨lamArity body, sourceResult,
              sourceResult == .shared && papSafe body, code⟩) =
              some (address, .fn d) ∧ bodyState = final := by
        simpa using hpureRun
      have hd : d =
          ⟨lamArity body, sourceResult,
            sourceResult == .shared && papSafe body, code⟩ := by
        have hp := Option.some.inj hpure.1
        exact Decl.fn.inj (Prod.mk.inj hp).2.symm
      subst d
      change (sourceResult == .shared && papSafe body) = true at hsafe
      simp only [Bool.and_eq_true] at hsafe
      obtain ⟨hresultBeq, hbody⟩ := hsafe
      have hresult : sourceResult = .shared := by
        cases sourceResult <;> simp_all
      have hmodes := papSafe_lamUses_eq_replicate hbody
      refine ⟨hresult, ?_⟩
      rw [hmodes]
      simp [worldOfUses]
  | ctor tag arity => simp [sourceCallableSignature] at hsignature
  | recursor numArgs natLit rules =>
      simp only [sourceCallableSignature, Option.some.injEq,
        Prod.mk.injEq] at hsignature
      obtain ⟨rfl, rfl⟩ := hsignature
      refine ⟨rfl, ?_⟩
      simp
  | extern arity => simp [sourceCallableSignature] at hsignature

/-- Owner-sensitive PAP safety is a theorem of the concrete whole-pass
declaration trace, not an all-shared source-environment assumption. -/
theorem lowerAllAction_sourcePapSafe
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl) :
    SourcePapSafe (IxIR0.Env.ofList decls) ctx := by
  intro address source worlds result d hsrc hsignature hdecl hsafe
  obtain ⟨itemInitial, itemFinal, hrun, _⟩ :=
    lowerAllAction_callable_decl_trace hlower htarget hsrc hsignature hdecl
  exact lowerDecl_callable_signature_of_papSafe_run
    hsignature hrun hsafe

/-- Every raw function returned by the whole pass came either from a selected
same-address callable source row or from the final generated-declaration
accumulator.  This is the exact declaration partition consumed by
`FnDeclCovered`. -/
theorem lowerAllAction_fn_mem_source_or_extra
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (hselected : SourceCallableRowsSelected decls)
    {address : Ixon.Address} {d : FnDef}
    (hmember : (address, .fn d) ∈ targetDecls) :
    (∃ source worlds result,
      IxIR0.Env.ofList decls address = some source ∧
      sourceCallableSignature source = some (worlds, result)) ∨
    (address, .fn d) ∈ finalState.extra := by
  let src := IxIR0.Env.ofList decls
  simp only [lowerAllAction] at hlower
  obtain ⟨base, baseState, hbase, hafterBase⟩ :=
    trackedBindRun_ok_inv hlower
  obtain ⟨compiledMain, mainState, hmain, hafterMain⟩ :=
    trackedBindRun_ok_inv hafterBase
  obtain ⟨observed, getState, hget, hpure⟩ :=
    trackedBindRun_ok_inv hafterMain
  have hget' : mainState = observed ∧ mainState = getState := by
    simpa using hget
  obtain ⟨hobserved, hgetState⟩ := hget'
  subst observed
  subst getState
  have hpure' :
      (base ++ mainState.extra, compiledMain) =
          (targetDecls, mainCode) ∧ mainState = finalState := by
    simpa using hpure
  obtain ⟨hresult, hstate⟩ := hpure'
  subst finalState
  have hdecls : base ++ mainState.extra = targetDecls :=
    congrArg Prod.fst hresult
  rw [← hdecls, List.mem_append] at hmember
  cases hmember with
  | inl hbaseMember =>
      obtain ⟨item, itemInitial, itemFinal, hitem, hitemRun⟩ :=
        listFilterMapM_result_trace (lowerDecl src compilerFuel)
          decls hbase hbaseMember
      rcases item with ⟨sourceAddress, source⟩
      obtain ⟨haddress, worlds, result, hsignature⟩ :=
        lowerDecl_fn_output_input_callable hitemRun
      subst sourceAddress
      exact Or.inl ⟨source, worlds, result,
        hselected hitem hsignature, hsignature⟩
  | inr hextra => exact Or.inr hextra

/-- With an exact raw target context, the whole-pass source/generated
partition closes declaration coverage without admitting synthetic aliases. -/
theorem lowerAllAction_fnDeclCovered
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (hselected : SourceCallableRowsSelected decls)
    (hctx : ctx.decls = Env.ofList targetDecls) :
    FnDeclCovered (IxIR0.Env.ofList decls) ctx finalState := by
  intro address d hdecl
  have hlookup : Env.ofList targetDecls address = some (.fn d) := by
    rw [← hctx]
    exact hdecl
  exact lowerAllAction_fn_mem_source_or_extra hlower hselected
    (targetEnv_ofList_lookup_mem hlookup)

/-- Every PAP admitted by the whole-pass compiler relation resolves to a
declaration whose content-addressed metadata permits dynamic PAP entry.  The
proof is origin-sensitive: source definitions expose the computed bit,
recursors and generated functions are safe by construction, and externs are
scalar-only. -/
theorem lowerAllAction_compilerFunction_declPapSafe
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    {sourceFunction : IxIR0.Value} {address : Ixon.Address}
    {arity : Nat} {captures : List IxIR0.Value}
    (hrel : CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls)
      finalState sourceFunction address arity captures) :
    ∃ declaration, ctx.decls address = some declaration ∧
      declPapSafe declaration = true := by
  cases hrel with
  | @source relatedFunction baseFunction targetAddress targetArity
      storedSources source hsrc heligible harity href happly hunder =>
    cases source with
    | defn result body =>
      obtain ⟨hresult, hbody⟩ := heligible
      obtain ⟨d, hdecl, _, _, _⟩ := hcontracts.decls.defn hsrc
      obtain ⟨itemInitial, itemFinal, hrun, _⟩ :=
        lowerAllAction_callable_decl_trace hlower htarget hsrc (by rfl)
          hdecl
      refine ⟨.fn d, hdecl, ?_⟩
      exact lowerDecl_defn_papSafe_of_run hrun hresult hbody
    | ctor tag ctorArity => exact heligible.elim
    | recursor numArgs natLit rules =>
      obtain ⟨d, hdecl, _, _, _⟩ := hcontracts.decls.recursor hsrc
      obtain ⟨itemInitial, itemFinal, hrun, _⟩ :=
        lowerAllAction_callable_decl_trace hlower htarget hsrc (by rfl)
          hdecl
      refine ⟨.fn d, hdecl, ?_⟩
      exact lowerDecl_recursor_papSafe_of_run hrun
    | extern externArity =>
      have hdecl := hcontracts.decls.extern hsrc
      exact ⟨.extern externArity, hdecl, rfl⟩
  | @wrapper relatedFunction baseFunction storedSources memo hmember hsrc
      href happly hunder =>
    refine ⟨ctorWrapperDecl memo.source memo.tag memo.arity,
      hrepresented.wrapper hmember, ?_⟩
    simp [ctorWrapperDecl, declPapSafe]
  | lifted hlifted =>
    obtain ⟨sourceEnv, expr, selected, supplied, hliftCode, _, _, _, _⟩ :=
      hlifted
    obtain ⟨fuel, bodyInitial, generated, code, _, _, _, hmember⟩ :=
      hliftCode
    refine ⟨.fn
        ⟨(liftCaptureIndices sourceEnv.length expr).length + lamArity expr,
          .shared, true, code⟩,
      hrepresented.decl hmember, rfl⟩

/-- At one evaluator index, every source-backed callable emitted by an
actual whole-pass run satisfies its semantic function contract using only
the mutually recursive semantic contracts below that index. -/
theorem lowerAllAction_sourceFnValuePreservesAt_within_below
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel limit : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (henv : sourceCtx.env = IxIR0.Env.ofList decls)
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (hvalues : CompilerValueContractsBelow
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx (IxIR0.Env.ofList decls) ctx limit) :
    SourceFnValuePreservesAt
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx (IxIR0.Env.ofList decls) ctx limit := by
  intro address source worlds result d sourceFunction
    hsrc hsignature hdecl href
  obtain ⟨itemInitial, itemFinal, hrun, hextends⟩ :=
    lowerAllAction_callable_decl_trace hlower htarget hsrc hsignature hdecl
  cases source with
  | defn sourceResult body =>
    simp only [sourceCallableSignature, Option.some.injEq,
      Prod.mk.injEq] at hsignature
    obtain ⟨rfl, rfl⟩ := hsignature
    cases compilerFuel with
    | zero =>
      simp only [lowerDecl] at hrun
      obtain ⟨code, bodyState, hbodyRun, _⟩ :=
        trackedBindRun_ok_inv hrun
      exact (trackedThrowRun_not_ok (by
        simpa [lowerFnBody] using hbodyRun)).elim
    | succ bodyFuel =>
      have hadmissible := lowerDecl_defn_parameterDropsAdmissible hrun
      intro store store' args value sourceArgs sourceValue sourceRest rest
        hlength hargs happlies hframe hown hcodeRun
      exact lowerDecl_defn_valuePreservesAt_within_below
        (compilerFuel := bodyFuel) (limit := limit)
        henv hrepresented hcontracts hvalues hsrc href hadmissible
        (by simpa [Nat.succ_eq_add_one] using hrun) hextends
        hlength hargs happlies hframe hown hcodeRun
  | ctor tag arity =>
    simp [sourceCallableSignature] at hsignature
  | recursor numArgs natLit rules =>
    simp only [sourceCallableSignature, Option.some.injEq,
      Prod.mk.injEq] at hsignature
    obtain ⟨rfl, rfl⟩ := hsignature
    intro store store' args value sourceArgs sourceValue sourceRest rest
      hlength hargs happlies hframe hown hcodeRun
    exact lowerDecl_recursor_valuePreservesAt_within_below
      (compilerFuel := compilerFuel) (limit := limit)
      henv hrepresented hcontracts hvalues hsrc hdecl href hrun hextends
      hlength hargs happlies hframe hown hcodeRun
  | extern arity =>
    simp [sourceCallableSignature] at hsignature

/-- Seal the actual whole-pass declaration and `applyGo` producers by strong
evaluator-fuel induction.  Generated lifted functions and constructor
wrappers need no separate semantic environment: their exact compiler
provenance is reconstructed inside the application producer. -/
theorem lowerAllAction_compilerValueContracts
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (henv : sourceCtx.env = IxIR0.Env.ofList decls)
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (hextern : ExternValueContract
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx ctx) :
    CompilerValueContracts
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx (IxIR0.Env.ofList decls) ctx := by
  apply compilerValueContracts_of_below_step hextern
  intro limit hvalues
  constructor
  · exact lowerAllAction_sourceFnValuePreservesAt_within_below
      henv hlower htarget hrepresented hcontracts hvalues
  · exact applyValuePreservesAt_within_below
      henv hrepresented hcontracts hvalues

/-- Whole-main value agreement with semantic compiler contracts constructed
from this very whole-pass output.  Only ownership contracts and the explicit
extern-oracle compatibility boundary remain as semantic premises. -/
theorem lowerAllAction_main_value_graph_sealed
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx} {sourceFuel targetFuel : Nat}
    {sourceValue : IxIR0.Value} {targetStore : Store}
    {targetValue : RVal}
    (henv : sourceCtx.env = IxIR0.Env.ofList decls)
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htargetDecls : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (hextern : ExternValueContract
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx ctx)
    (hsource : IxIR0.eval sourceCtx sourceFuel [] main = .ok sourceValue)
    (htargetRun : runMain ctx mainCode targetFuel =
      .ok (targetStore, targetValue)) :
    Sim.ValueGraph
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      targetStore sourceValue targetValue := by
  have hvalues := lowerAllAction_compilerValueContracts
    henv hlower htargetDecls hrepresented hcontracts hextern
  exact lowerAllAction_main_value_graph henv hlower hrepresented
    hcontracts hvalues hsource htargetRun

/-- Public semantic forward simulation after the semantic contract seal.
Target-run existence remains deliberately separate as the progress premise;
all value-agreement contracts now come from the actual compiler output. -/
theorem lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (henv : sourceCtx.env = IxIR0.Env.ofList decls)
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (targetDecls, mainCode) finalState)
    (htargetDecls : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented ctx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList decls) ctx)
    (hextern : ExternValueContract
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls) finalState)
      sourceCtx ctx)
    (hprogress : ∀ {sourceFuel sourceValue},
      IxIR0.eval sourceCtx sourceFuel [] main = .ok sourceValue →
      ∃ targetFuel targetStore targetValue,
        runMain ctx mainCode targetFuel = .ok (targetStore, targetValue)) :
    SemanticForwardSimulation sourceCtx ctx main mainCode
      (CompilerFunctionRel sourceCtx (IxIR0.Env.ofList decls)
        finalState) := by
  have hvalues := lowerAllAction_compilerValueContracts
    henv hlower htargetDecls hrepresented hcontracts hextern
  intro sourceFuel sourceValue hsource
  exact lowerAllAction_semanticForwardSimulation_of_targetProgress
    henv hlower hrepresented hcontracts hvalues hprogress hsource

/-- Package the exact declaration shape and callable contract of a generated
constructor wrapper. -/
theorem ctorWrapper_ownershipContract (ctx : Ctx)
    (source : Ixon.Address) (tag arity : Nat) :
    ∃ d, ctorWrapperDecl source tag arity = .fn d ∧
      d.result = .shared ∧
      FnOwnershipContract ctx d (List.replicate d.arity .shared) := by
  refine ⟨⟨arity, .shared, true,
      .letOp (.alloc .shared (ctorIdOf source tag)
        (descendingVars arity).toArray) (.ret (.var 0))⟩, rfl, rfl, ?_⟩
  exact ctorWrapper_fnOwnershipContract ctx source tag arity

/-! ### Ownership from generated-declaration provenance -/

/-- Every operationally provenanced generated function satisfies its exact
all-shared ownership transformer at the current evaluator index. -/
theorem GeneratedDeclProvenance.fnPreservesAt
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env}
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {state : LowSt} (hrepresented : ExtraRepresented ctx state)
    {address : Ixon.Address} {d : FnDef}
    (hprovenance : GeneratedDeclProvenance src state (address, .fn d)) :
    d.result = .shared ∧
      FnOwnershipPreservesAt ctx d
        (List.replicate d.arity .shared) limit := by
  cases hprovenance with
  | inl hwrapper =>
    obtain ⟨wrapperAddress, source, tag, arity, hitem⟩ := hwrapper
    have haddress : address = wrapperAddress := congrArg Prod.fst hitem
    have hdecl : (Decl.fn d) = ctorWrapperDecl source tag arity :=
      congrArg Prod.snd hitem
    subst address
    simp only [ctorWrapperDecl] at hdecl
    have hd : d =
        ⟨arity, .shared, true,
          .letOp (.alloc .shared (ctorIdOf source tag)
            (descendingVars arity).toArray) (.ret (.var 0))⟩ :=
      Decl.fn.inj hdecl
    subst d
    exact ⟨rfl,
      (ctorWrapper_fnOwnershipContract ctx source tag arity).preserves⟩
  | inr hlifted =>
    obtain ⟨generatedAddress, entryCount, expr, bodyFuel, bodyInitial,
      generated, code, hitem, hpositive, hsafe, hbodyRun, hgenerated,
      hmember⟩ := hlifted
    have haddress : address = generatedAddress := congrArg Prod.fst hitem
    have hdecl : Decl.fn d = .fn
        ⟨(liftCaptureIndices entryCount expr).length + lamArity expr,
          .shared, true, code⟩ := congrArg Prod.snd hitem
    subst address
    have hd : d =
        ⟨(liftCaptureIndices entryCount expr).length + lamArity expr,
          .shared, true, code⟩ := Decl.fn.inj hdecl
    subst d
    have hbodyRepresented : ExtraRepresented ctx generated :=
      hrepresented.of_extends hgenerated
    have hmodes := papSafe_lamUses_eq_replicate hsafe
    have hadmissible : ParameterDropsAdmissible (lamUses expr)
        (fun index => countUses index (stripLams expr)) := by
      rw [hmodes]
      exact parameterDropsAdmissible_replicate_many _ _
    have hselected : ∀ index, index < entryCount →
        decide (0 < countUses index expr) =
          (countUses ((lamUses expr).length + index)
            (stripLams expr) != 0) := by
      intro index _
      rw [lamUses_length]
      rw [← countUses_eq_stripLams_shift expr index]
      cases countUses index expr <;> rfl
    have hshared : (lamUses expr).map worldOfUses =
        List.replicate (lamUses expr).length .shared := by
      rw [hmodes]
      simp [worldOfUses]
    cases bodyFuel with
    | zero =>
      exact (trackedThrowRun_not_ok
        (by simpa [lowerFnBody] using hbodyRun)).elim
    | succ innerFuel =>
      have hbodyRun' :
          (lowerFnBody src (innerFuel + 1)
            (let captures := (List.range entryCount).filter
                (fun index => countUses index expr > 0)
             ⟨parameterEntries captures.length (lamUses expr)
                  (fun index => countUses index (stripLams expr)) ++
                selectedEntriesFrom
                  (fun index => countUses index expr > 0)
                  (fun index => countUses ((lamUses expr).length + index)
                    (stripLams expr))
                  (List.range entryCount) 0,
              captures.length + (lamUses expr).length⟩)
            (let captures := (List.range entryCount).filter
                (fun index => countUses index expr > 0)
             parameterDrops captures.length (lamUses expr)
                (fun index => countUses index (stripLams expr)))
            .shared (stripLams expr)).run bodyInitial =
              .ok code generated := by
        simpa [liftedBodyVEnv, liftedBodyDrops, liftCaptureIndices,
          lamUses_length] using hbodyRun
      have hpreserves : FnOwnershipPreservesAt ctx
          ⟨(liftCaptureIndices entryCount expr).length +
              (lamUses expr).length,
            .shared, true, code⟩
          (List.replicate
            ((liftCaptureIndices entryCount expr).length +
              (lamUses expr).length) .shared) limit := by
        exact lowerFnBody_liftedEntries_preservesAt
          (fuel := innerFuel) (state := bodyInitial)
          (finalState := generated) (code := code)
          happly hdecls entryCount (lamUses expr) (stripLams expr)
          (fun index => countUses index expr > 0)
          hadmissible hselected (by simpa [lamUses_length] using hpositive)
          hshared hbodyRun' hbodyRepresented
      refine ⟨rfl, ?_⟩
      rw [lamUses_length] at hpreserves
      exact hpreserves

/-- A provenanced extension from the empty compiler state supplies the
generated-function half of one contractive compiler step. -/
theorem ExtraProvenanceExtends.extraFnPreservesAt_of_empty
    {ctx : Ctx} {limit : Nat} {src : IxIR0.Env} {state : LowSt}
    (hprovenance : ExtraProvenanceExtends src ({} : LowSt) state)
    (hrepresented : ExtraRepresented ctx state)
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow src ctx limit) :
    ExtraFnPreservesAt ctx state limit := by
  intro address d hmember
  exact (hprovenance.provenance_of_empty hmember).fnPreservesAt
    happly hdecls hrepresented

/-- Generated result worlds are fixed by provenance alone, independently of
the semantic evaluator index. -/
theorem ExtraProvenanceExtends.extraFnResultsShared_of_empty
    {src : IxIR0.Env} {state : LowSt}
    (hprovenance : ExtraProvenanceExtends src ({} : LowSt) state) :
    ExtraFnResultsShared state := by
  intro address d hmember
  have horigin := hprovenance.provenance_of_empty hmember
  cases horigin with
  | inl hwrapper =>
    obtain ⟨wrapperAddress, source, tag, arity, hitem⟩ := hwrapper
    have hdecl : Decl.fn d = ctorWrapperDecl source tag arity :=
      congrArg Prod.snd hitem
    simp only [ctorWrapperDecl] at hdecl
    exact congrArg FnDef.result (Decl.fn.inj hdecl)
  | inr hlifted =>
    obtain ⟨generatedAddress, entryCount, expr, bodyFuel, bodyInitial,
      generated, code, hitem, _⟩ := hlifted
    have hdecl : Decl.fn d = .fn
        ⟨(liftCaptureIndices entryCount expr).length + lamArity expr,
          .shared, true, code⟩ := congrArg Prod.snd hitem
    exact congrArg FnDef.result (Decl.fn.inj hdecl)

/-- At one evaluator index, every source-backed function emitted by an
actual whole-program lowering run satisfies its ownership transformer from
the three strictly-smaller contract environments. -/
theorem lowerAllAction_sourceFnPreservesAt
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel limit : Nat}
    {finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented ctx finalState)
    (happly : ApplyOwnershipContractBelow ctx limit)
    (hdecls : SourceDeclContractsBelow
      (IxIR0.Env.ofList decls) ctx limit) :
    SourceFnPreservesAt (IxIR0.Env.ofList decls) ctx limit := by
  intro address source worlds result d hsrc hsignature hdecl
  obtain ⟨itemInitial, itemFinal, hrun, hextends⟩ :=
    lowerAllAction_callable_decl_trace hlower htarget
      hsrc hsignature hdecl
  have hitemRepresented : ExtraRepresented ctx itemFinal :=
    hrepresented.of_extends hextends
  cases source with
  | defn sourceResult body =>
      simp only [sourceCallableSignature, Option.some.injEq,
        Prod.mk.injEq] at hsignature
      obtain ⟨rfl, rfl⟩ := hsignature
      cases compilerFuel with
      | zero =>
          simp only [lowerDecl] at hrun
          obtain ⟨code, bodyState, hbodyRun, _⟩ :=
            trackedBindRun_ok_inv hrun
          exact (trackedThrowRun_not_ok (by
            simpa [lowerFnBody] using hbodyRun)).elim
      | succ bodyFuel =>
          intro store store' args value rest hlength hown hcodeRun
          exact lowerDecl_defn_preservesAt
            (fuel := bodyFuel) happly hdecls
            (lowerDecl_defn_parameterDropsAdmissible hrun)
            (by simpa [Nat.succ_eq_add_one] using hrun)
            hitemRepresented hlength hown hcodeRun
  | ctor tag arity =>
      simp [sourceCallableSignature] at hsignature
  | recursor numArgs natLit rules =>
      simp only [sourceCallableSignature, Option.some.injEq,
        Prod.mk.injEq] at hsignature
      obtain ⟨rfl, rfl⟩ := hsignature
      obtain ⟨self, hselfDecl, _, hself⟩ :=
        hdecls.recursorCurrentSelf hsrc
      have hsame : self = d := by
        have heq : some (Decl.fn self) = some (Decl.fn d) :=
          hselfDecl.symm.trans hdecl
        exact Decl.fn.inj (Option.some.inj heq)
      subst self
      intro store store' args value rest hlength hown hcodeRun
      exact lowerDecl_recursor_preservesAt
        happly hdecls hself hrun hitemRepresented
        hlength hown hcodeRun
  | extern arity =>
      simp [sourceCallableSignature] at hsignature

/-- A successful whole-program lowering from the empty compiler state seals
all ownership contracts of its exact raw target context. Source declarations,
lifted functions, constructor wrappers, and dynamic PAP entry are closed by
one evaluator-fuel induction; no generated-function contract is assumed. -/
theorem lowerAllAction_compilerContracts
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat} {finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    {ctx : Ctx}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (targetDecls, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ targetDecls →
      ctx.decls targetAddress = some targetDecl)
    (hselected : SourceCallableRowsSelected decls)
    (hctx : ctx.decls = Env.ofList targetDecls) :
    CompilerContracts (IxIR0.Env.ofList decls) ctx ∧
      ExtraFnContracts ctx finalState := by
  have hprovenance := lowerAllAction_extraProvenance_empty hlower
  have hrepresented : ExtraRepresented ctx finalState :=
    lowerAllAction_extraRepresented hlower fun hmember =>
      htarget (lowerAllAction_extra_mem_result hlower hmember)
  apply compilerContracts_of_source_extra_below_step
    (lowerAllAction_sourceDeclLayout hlower htarget)
    (lowerAllAction_sourcePapSafe hlower htarget)
    hprovenance.extraFnResultsShared_of_empty
    (lowerAllAction_fnDeclCovered hlower hselected hctx)
  intro limit hdecls _ happly
  exact ⟨lowerAllAction_sourceFnPreservesAt
      hlower htarget hrepresented happly hdecls,
    hprovenance.extraFnPreservesAt_of_empty
      hrepresented happly hdecls⟩

end Ix.Compiler.IxIR1.LowerSim
