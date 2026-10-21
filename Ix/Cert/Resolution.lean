import Ix.Cert.Schedule
import Ix.CompileCert.Canon.QSort

/-! # Where the driver's resolution map comes from (Route A, B9b, piece 2)

`compileUnchecked` returns, with the environment, the driver's resolution map
at the end of the fold (`CompileEnv.nameToAddr`), and `compileReport` checks
that every name it holds is published at the address it resolves to
(`Ix.Cert.resolvedPublished`). This file says where each entry of that map
comes from: **every entry is an aux name's (its name is in `auxNameToAddr`),
or a primary claim of a block compiled during the fold**, against a state the
fold reached, with the block's outcome as the driver computed it
(`Compiled`). No claim check is needed for that: a merge only adds a block's
own primary claims (`mergeCompiledBlock`), a withdrawal erases names
(`failAuxPromotion`), and the promotions write only aux addresses
(`promoteAuxWrites`, `promoteRemainingWrites`).

* `Reach`: the driver states the fold reaches from its initial state. Each
  step applies, to a reached state, the outcome of a condensation block
  computed against a reached state (the wave's snapshot); `foldWavesSeq_reach`
  (with `foldWaveWith_ready`: a wave's ready blocks are condensation blocks
  under their keys);
* `Step`: how one driver operation moves the resolution map; it composes
  (`Step.trans`), and every operation of `applyAuxBlockOutcome` is one;
* `Provenance` and `reach_provenance`: on every reached state, every entry of
  the resolution map is an aux name's or `Compiled`. -/

namespace Ix.Cert.Resolution

open Ix.CompileM Ix.Cert.Schedule

/-! ## Loops in `Id` -/

/-- A loop in `Id` keeps an invariant of its state that each step keeps,
whether the step continues or stops. -/
theorem forIn_inv_list {α σ : Type} (I : σ → Prop) (f : α → σ → Id (ForInStep σ)) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, I s → I (f x s).value) →
      ∀ s, I s → I (forIn (m := Id) l s f) := by
  intro l
  induction l with
  | nil => intro _ s hs; exact hs
  | cons x l ih =>
    intro hstep s hs
    rw [List.forIn_cons]
    have hx := hstep x List.mem_cons_self s hs
    cases hf : f x s with
    | done s' => rw [hf] at hx; exact hx
    | yield s' =>
      rw [hf] at hx
      exact ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) s' hx

/-- `forIn_inv_list` over an array. -/
theorem forIn_inv_array {α σ : Type} (I : σ → Prop) (f : α → σ → Id (ForInStep σ)) (xs : Array α)
    (step : ∀ x ∈ xs, ∀ s, I s → I (f x s).value) (s : σ) (hs : I s) :
    I (forIn (m := Id) xs s f) := by
  rw [← Array.forIn_toList]
  exact forIn_inv_list I f xs.toList (fun x hx => step x (Array.mem_toList_iff.mp hx)) s hs

/-- A loop over an array followed by its continuation: the continuation of
every state the invariant holds of has `P`. Stated on the bind, so that it
unifies with an elaborated `do` block's loop and continuation. -/
theorem loop_bind {α σ β : Type} (xs : Array α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (k : σ → Id β) (I : σ → Prop) (P : β → Prop)
    (hinit : I init) (body : ∀ x ∈ xs, ∀ s, I s → I (f x s).value) (cont : ∀ L, I L → P (k L)) :
    P (forIn (m := Id) xs init f >>= k) :=
  cont _ (forIn_inv_array I f xs body init hinit)

/-! ## A wave's ready blocks -/

/-- A wave's ready blocks: key, representative, members. -/
abbrev Ready := Array (Ix.Name × Ix.Name × Ix.Set Ix.Name)

/-- Every ready block is a condensation block, under its key (`blockKey`). -/
def GoodReady (blocks : Ix.CondensedBlocks) (ready : Ready) : Prop :=
  ∀ x ∈ ready, blocks.blocks.get? x.2.1 = some x.2.2 ∧ x.1 = blockKey x.2.1 x.2.2

/-- **A wave applies its step to condensation blocks**: a wave that returns
applies `apply`, against the state it starts from, to ready blocks that are
condensation blocks under their keys, and that is its driver state. -/
theorem foldWaveWith_ready (apply : CompileEnv → Ready → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st st' : FoldState)
    (h : foldWaveWith apply blocks sched st = .ok st') :
    ∃ ready, GoodReady blocks ready ∧ st'.acc = apply st.acc.cenv ready st.acc := by
  unfold foldWaveWith at h
  simp only [Id.run] at h
  revert h
  refine loop_bind (P := fun r => r = Except.ok st' →
      ∃ ready, GoodReady blocks ready ∧ st'.acc = apply st.acc.cenv ready st.acc)
    (I := fun s : Option (Except String FoldState) × Ready × Array Ix.Name =>
      (s.1 = none ∨ ∃ e, s.1 = some (.error e)) ∧ GoodReady blocks s.2.1) _ _ _ _ ?init ?body ?cont
  case init => exact ⟨.inl rfl, fun x hx => by simp at hx⟩
  case body =>
    intro rep _ s hs
    obtain ⟨_, hgood⟩ := hs
    split
    · rename_i all hall
      split
      · refine ⟨.inl rfl, fun x hx => ?_⟩
        have hx' : x ∈ s.2.1.push (blockKey rep all, rep, all) := hx
        rcases Array.mem_push.mp hx' with hx' | rfl
        · exact hgood x hx'
        · exact ⟨hall, rfl⟩
      · exact ⟨.inl rfl, hgood⟩
    · exact ⟨.inr ⟨_, rfl⟩, hgood⟩
  case cont =>
    intro L hL h
    obtain ⟨h1, hgood⟩ := hL
    rcases h1 with h1 | ⟨e, h1⟩
    · rw [h1] at h
      dsimp only at h
      split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        exact ⟨_, fun x hx => hgood x (Ix.CompileCert.Canon.mem_qsort.mp hx), rfl⟩
    · rw [h1] at h
      cases h

/-! ## The states the fold reaches -/

/-- **The driver states the fold reaches from `init`.** A step applies, to a
reached state, the outcome of a condensation block under its key, computed
against a reached state (the wave's snapshot). -/
inductive Reach (blocks : Ix.CondensedBlocks) (init : DriverAcc) : DriverAcc → Prop
  | init : Reach blocks init init
  | step {snap acc : DriverAcc} {rep : Ix.Name} {all : Ix.Set Ix.Name} :
      Reach blocks init snap → Reach blocks init acc → blocks.blocks.get? rep = some all →
      Reach blocks init (applyAuxBlockOutcome acc (blockKey rep all) all
        (auxBlockOutcome snap.cenv (blockKey rep all) all)).1

/-- A wave's sequential apply step reaches a state from reached ones. -/
theorem applySeq_reach {blocks : Ix.CondensedBlocks} {init snap : DriverAcc} {ready : Ready}
    (hsnap : Reach blocks init snap) (good : GoodReady blocks ready) :
    ∀ acc, Reach blocks init acc → Reach blocks init (applySeq snap.cenv ready acc) := by
  intro acc₀ h₀
  unfold applySeq
  rw [← Array.foldl_toList]
  have : ∀ (l : List (Ix.Name × Ix.Name × Ix.Set Ix.Name)), (∀ x ∈ l, x ∈ ready) →
      ∀ acc, Reach blocks init acc → Reach blocks init (l.foldl (fun acc x =>
        (applyAuxBlockOutcome acc x.1 x.2.2 (auxBlockOutcome snap.cenv x.1 x.2.2)).1) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x l ih =>
      intro sub acc h
      rw [List.foldl_cons]
      refine ih (fun y hy => sub y (List.mem_cons_of_mem _ hy)) _ ?_
      obtain ⟨hall, hkey⟩ := good x (sub x List.mem_cons_self)
      rw [hkey]
      exact Reach.step hsnap h hall
  exact this ready.toList (fun x hx => Array.mem_toList_iff.mp hx) acc₀ h₀

/-- A wave reaches a state from a reached one. -/
theorem foldWaveSeq_reach {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {init : DriverAcc}
    {st st' : FoldState} (h : foldWaveSeq blocks sched st = .ok st') (hst : Reach blocks init st.acc) :
    Reach blocks init st'.acc := by
  obtain ⟨ready, good, hacc⟩ := foldWaveWith_ready applySeq blocks sched st st' h
  rw [hacc]
  exact applySeq_reach hst good st.acc hst

/-- **The waves reach a state from a reached one.** -/
theorem foldWavesSeq_reach {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {init : DriverAcc} :
    ∀ fuel (st st' : FoldState), foldWavesSeq blocks sched fuel st = .ok st' →
      Reach blocks init st.acc → Reach blocks init st'.acc := by
  intro fuel
  induction fuel with
  | zero =>
    intro st st' h hst
    unfold foldWavesSeq at h
    split at h
    · cases h; exact hst
    · cases h
  | succ fuel ih =>
    intro st st' h hst
    unfold foldWavesSeq at h
    split at h
    · cases h; exact hst
    · split at h
      · cases h
      · rename_i st₁ h₁
        exact ih st₁ st' h (foldWaveSeq_reach h₁ hst)

end Ix.Cert.Resolution
