import Ix.Cert.Composition

/-! # Every state of the fold's run owns the artifact's resolution

The ownership obligation (`Obligation.ScheduleOwnership`) asks that every state the fold of
a compile passes through (`Resolution.OnRun`) owns the artifact's resolution and store
(`Owned`). This module proves it from one fact about a single driver step
(`StepKeeps`): applying a block's outcome keeps every name the state resolves at its
address, or records the name as failed.

* `Persists`: a later state keeps an earlier one's resolution (or its failures), its
  stored records and its failures (`Mono`); it composes (`Persists.trans`);
* `step_persists`, `applySeqList_persists`, `foldWaveSeq_persists`,
  `foldWavesSeq_persists`: a step, a wave's sequential apply, a wave and the waves
  persist, given `StepKeeps` (the stored records and `Mono` are `Resolution.Step`'s);
* `waveStart_reaches`, `onRun_persists`: the run passes through every wave start, so a
  state of the run persists into the run's final state;
* `scheduleOwnership_of_stepKeeps`: the final state's resolution is the compile's
  (`Resolution.FoldRun`), published at its addresses (`resolvedPublished`), and its
  records are the compile's, stored in the artifact (`compileEnvFold_final`); a name the
  final state records as failed is reported failed (`compileUnchecked_ungrounded`). -/

namespace Ix.Cert.RunOwnership

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Compile.ExactKey (ExactName)

/-- **`c'` keeps `c`'s resolution**: every name `c` resolves, `c'` resolves to the same
address, or records as failed. -/
def Keeps (c c' : CompileEnv) : Prop :=
  ∀ (n : ExactName) (a : Address), c.nameToAddr.get? n = some a →
    c'.nameToAddr.get? n = some a ∨ c'.ungrounded.contains n = true

/-- **One driver step keeps a resolution**: applying a block's outcome to a state keeps
every name the state resolves at its address, or records the name as failed. -/
def StepKeeps : Prop :=
  ∀ (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name) (o : AuxBlockOutcome),
    Keeps acc.cenv (applyAuxBlockOutcome acc lo all o).1.cenv

/-- **`c` persists into `c'`**: `c'` keeps `c`'s resolution, its stored records with their
bytes, and its failures (`Mono`). -/
structure Persists (c c' : CompileEnv) : Prop where
  names : Keeps c c'
  consts : ∀ (a : Address) (b : ByteArray), c.constants.get? a = some b → c'.constants.get? a = some b
  mono : Mono c c'

theorem Persists.refl (c : CompileEnv) : Persists c c :=
  ⟨fun _ _ h => .inl h, fun _ _ h => h, Mono.refl c⟩

theorem Persists.trans {c₁ c₂ c₃ : CompileEnv} (h₁ : Persists c₁ c₂) (h₂ : Persists c₂ c₃) :
    Persists c₁ c₃ :=
  ⟨fun n a h => (h₁.names n a h).elim (fun h => h₂.names n a h) (fun f => .inr (h₂.mono n f)),
    fun a b h => h₂.consts a b (h₁.consts a b h), h₁.mono.trans h₂.mono⟩

/-- **A step persists**, given `StepKeeps`: its stored records and failures are
`Resolution.Step`'s. -/
theorem step_persists (hk : StepKeeps) (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (o : AuxBlockOutcome) : Persists acc.cenv (applyAuxBlockOutcome acc lo all o).1.cenv :=
  ⟨hk acc lo all o, (applyAuxBlockOutcome_step acc lo all o).1.1, applyAuxBlockOutcome_mono acc lo all o⟩

/-- **A wave's sequential apply persists**, block by block. -/
theorem applySeqList_persists (hk : StepKeeps) (snapshot : CompileEnv) :
    ∀ (l : List (Ix.Name × Ix.Name × Ix.Set Ix.Name)) (acc : DriverAcc),
      Persists acc.cenv (applySeqList snapshot l acc).cenv
  | [], acc => Persists.refl acc.cenv
  | x :: l, acc => by
    obtain ⟨key, rep, all⟩ := x
    exact (step_persists hk acc key all _).trans (applySeqList_persists hk snapshot l _)

/-- **A wave persists.** -/
theorem foldWaveSeq_persists (hk : StepKeeps) {blocks : Ix.CondensedBlocks} {sched : FoldSchedule}
    {st st' : FoldState} (h : foldWaveSeq blocks sched st = .ok st') : Persists st.acc.cenv st'.acc.cenv := by
  obtain ⟨ready, -, hacc⟩ := foldWaveWith_ready applySeq blocks sched st st' h
  rw [hacc, applySeq_eq_list]
  exact applySeqList_persists hk _ _ _

/-- **The waves persist**: the state they start from persists into the state they end in. -/
theorem foldWavesSeq_persists (hk : StepKeeps) {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} :
    ∀ fuel (st fin : FoldState), foldWavesSeq blocks sched fuel st = .ok fin →
      Persists st.acc.cenv fin.acc.cenv := by
  intro fuel
  induction fuel with
  | zero =>
    intro st fin h
    unfold foldWavesSeq at h
    split at h
    · cases h; exact Persists.refl _
    · cases h
  | succ fuel ih =>
    intro st fin h
    unfold foldWavesSeq at h
    split at h
    · cases h; exact Persists.refl _
    · split at h
      · cases h
      · rename_i st₁ h₁
        exact (foldWaveSeq_persists hk h₁).trans (ih st₁ fin h)

/-- **The run passes through every wave start**: from a wave start of a run that ends, the
waves end in the same state. -/
theorem waveStart_reaches {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {st₀ st fin : FoldState}
    {fuel : Nat} (hrun : foldWavesSeq blocks sched fuel st₀ = .ok fin)
    (h : WaveStart blocks sched st₀ st) : ∃ fuel', foldWavesSeq blocks sched fuel' st = .ok fin := by
  induction h with
  | start => exact ⟨fuel, hrun⟩
  | @wave st st' _ hr hw ih =>
    obtain ⟨fuel', h'⟩ := ih
    cases fuel' with
    | zero =>
      unfold foldWavesSeq at h'
      split at h'
      · rename_i hz
        exact absurd (by simpa using hz) hr
      · cases h'
    | succ fuel' =>
      unfold foldWavesSeq at h'
      split at h'
      · rename_i hz
        exact absurd (by simpa using hz) hr
      · rw [hw] at h'
        exact ⟨fuel', h'⟩

/-- **A state of the run persists into the run's final state.** -/
theorem onRun_persists (hk : StepKeeps) {blocks : Ix.CondensedBlocks} {sched : FoldSchedule}
    {st₀ fin : FoldState} {fuel : Nat} {acc : DriverAcc}
    (hrun : foldWavesSeq blocks sched fuel st₀ = .ok fin) (h : OnRun blocks sched st₀ acc) :
    Persists acc.cenv fin.acc.cenv := by
  obtain ⟨st, hst, rfl | ⟨st', ready, pre, post, hr, hw, -, hacc, e, rfl⟩⟩ := h
  · obtain ⟨fuel', h'⟩ := waveStart_reaches hrun hst
    exact foldWavesSeq_persists hk fuel' st fin h'
  · obtain ⟨fuel', h'⟩ := waveStart_reaches hrun hst
    have rest : ∃ fuel'', foldWavesSeq blocks sched fuel'' st' = .ok fin := by
      cases fuel' with
      | zero =>
        unfold foldWavesSeq at h'
        split at h'
        · rename_i hz
          exact absurd (by simpa using hz) hr
        · cases h'
      | succ fuel' =>
        unfold foldWavesSeq at h'
        split at h'
        · rename_i hz
          exact absurd (by simpa using hz) hr
        · rw [hw] at h'
          exact ⟨fuel', h'⟩
    obtain ⟨fuel'', h''⟩ := rest
    have wave : Persists (applySeqList st.acc.cenv pre st.acc).cenv st'.acc.cenv := by
      rw [hacc, applySeq_eq_list, e, applySeqList_append]
      exact applySeqList_persists hk _ _ _
    exact wave.trans (foldWavesSeq_persists hk fuel'' st' fin h'')

/-- **Schedule ownership, from one step's.** Every state of the fold's run persists into
the run's final state, whose resolution map is the compile's and whose records the compile
stores (`Resolution.FoldRun`); the compile publishes every name it resolves at its address
(`resolvedPublished`) and stores its records in the artifact (`compileEnvFold_final`); and
a name the final state records as failed is reported failed. -/
theorem scheduleOwnership_of_stepKeeps (hk : StepKeeps) : Obligation.ScheduleOwnership := by
  intro env ixe failures cenv cenv₀ sched hrep hu hrun snap hsnap
  obtain ⟨st, -, -, hst, hmap, hconsts, hm⟩ := hrun
  have p := onRun_persists hk hst hsnap
  obtain ⟨cenv', hu', pub⟩ := resolvedPublished hrep
  rw [hu] at hu'
  cases hu'
  obtain ⟨bytes, hf⟩ := compileUnchecked_fold hu
  obtain ⟨-, -, st₁, -, -, -, finalized, -, hconsts₁, -⟩ := compileEnvFold_final hf
  refine ⟨fun n a hn hnf => ?_, fun a b hb => ?_⟩
  · rcases p.names n a hn with h | h
    · rw [← hmap] at h
      exact pub n a h
    · have failed := compileUnchecked_ungrounded hu (hm n h)
      rw [hnf] at failed
      cases failed
  · have stored := hconsts a b (p.consts a b hb)
    rw [hconsts₁] at stored
    rw [← finalized]
    exact assembleEnv_consts _ stored

/-- info: 'Ix.Cert.RunOwnership.scheduleOwnership_of_stepKeeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scheduleOwnership_of_stepKeeps

end Ix.Cert.RunOwnership
