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
  the resolution map is an aux name's or `Compiled`;
* `compileEnvFold_final`, `compileEnvFold_provenance`, `compileUnchecked_fold`
  and `compileUnchecked_provenance`: the fold starts from an empty map, and
  `compileUnchecked`'s resolution map is the final state's, so every entry of
  it is an aux name's (in the final aux map) or `Compiled`. -/

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

/-! ## How an operation moves the resolution map -/

open Ix.Compile.ExactKey (ExactName)

/-- **One driver operation's effect on the resolution map**, from `c` to `c'`:
every entry of `c'`'s resolution map is one of `c`'s, whose name keeps its
aux address if it had one, or its name has an aux address in `c'`, or it is
one of the operation's own claims (`F`). -/
def Step (c c' : CompileEnv) (F : Ix.Name → Address → Prop) : Prop :=
  ∀ (n : ExactName) (a : Address), c'.nameToAddr.get? n = some a →
    (c.nameToAddr.get? n = some a ∧ (c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)) ∨
      c'.auxNameToAddr.contains n = true ∨ F n a

theorem Step.refl (c : CompileEnv) (F : Ix.Name → Address → Prop) : Step c c F :=
  fun _ _ h => .inl ⟨h, id⟩

theorem Step.mono {c c' : CompileEnv} {F G : Ix.Name → Address → Prop} (h : Step c c' F)
    (FG : ∀ n a, F n a → G n a) : Step c c' G := by
  intro n a hn
  rcases h n a hn with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (FG n a h))

theorem Step.trans {c₁ c₂ c₃ : CompileEnv} {F : Ix.Name → Address → Prop} (h₁ : Step c₁ c₂ F)
    (h₂ : Step c₂ c₃ F) : Step c₁ c₃ F := by
  intro n a hn
  rcases h₂ n a hn with ⟨h, keep₂⟩ | h | h
  · rcases h₁ n a h with ⟨h, keep₁⟩ | h | h
    · exact .inl ⟨h, fun k => keep₂ (keep₁ k)⟩
    · exact .inr (.inl (keep₂ h))
    · exact .inr (.inr h)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- An operation that leaves the resolution map and keeps every aux name. -/
theorem Step.keep {c c' : CompileEnv} {F : Ix.Name → Address → Prop}
    (h₁ : c'.nameToAddr = c.nameToAddr)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true) :
    Step c c' F := by
  intro n a hn
  rw [h₁] at hn
  exact .inl ⟨hn, h₂ n⟩

/-- An operation that erases one name from the resolution map and the aux map. -/
theorem Step.erase {c c' : CompileEnv} {F : Ix.Name → Address → Prop} {m : ExactName}
    (h₁ : c'.nameToAddr = c.nameToAddr.erase m) (h₂ : c'.auxNameToAddr = c.auxNameToAddr.erase m) :
    Step c c' F := by
  intro n a hn
  rw [h₁, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase] at hn
  split at hn
  · cases hn
  · rename_i ne
    refine .inl ⟨by rw [Std.HashMap.get?_eq_getElem?]; exact hn, fun k => ?_⟩
    rw [h₂, Std.HashMap.contains_erase]
    simp [ne, k]

/-- An operation that writes one entry of the resolution map: one of its own
claims (`F`), or an aux name's. -/
theorem Step.insert {c c' : CompileEnv} {F : Ix.Name → Address → Prop} {m : ExactName} {b : Address}
    (h₁ : c'.nameToAddr = c.nameToAddr.insert m b)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (hm : F m b ∨ c'.auxNameToAddr.contains m = true) : Step c c' F := by
  intro n a hn
  rw [h₁, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hn
  split at hn
  · rename_i same
    have e : m = n := beq_iff_eq.mp same
    subst e
    cases hn
    rcases hm with hm | hm
    · exact .inr (.inr hm)
    · exact .inr (.inl hm)
  · exact .inl ⟨by rw [Std.HashMap.get?_eq_getElem?]; exact hn, h₂ n⟩

theorem contains_of_get {m : Std.HashMap ExactName Address} {n : ExactName} {a : Address}
    (h : m.get? n = some a) : m.contains n = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, h]; rfl

/-- `loop_bind` over a hash set. -/
theorem loop_bind_set {α σ β : Type} [BEq α] [Hashable α] (xs : Std.HashSet α) (init : σ)
    (f : α → σ → Id (ForInStep σ)) (k : σ → Id β) (I : σ → Prop) (P : β → Prop)
    (hinit : I init) (body : ∀ x, ∀ s, I s → I (f x s).value) (cont : ∀ L, I L → P (k L)) :
    P (forIn (m := Id) xs init f >>= k) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact cont _ (forIn_inv_list I f xs.toList (fun x _ => body x) init hinit)

/-- **A withdrawal only erases**: `failAuxPromotion` erases each member from
the resolution map and the aux map. -/
theorem failAuxPromotion_step (acc : DriverAcc) (all : Ix.Set Ix.Name) (msg : String)
    (F : Ix.Name → Address → Prop) : Step acc.cenv (failAuxPromotion acc all msg).cenv F := by
  unfold failAuxPromotion
  simp only [Id.run]
  refine loop_bind_set (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
    (I := fun s : DriverAcc => Step acc.cenv s.cenv F) _ _ _ _ (Step.refl _ _) ?_ ?_
  · intro m s hs
    exact hs.trans (Step.erase rfl rfl)
  · intro L hL
    exact hL

/-- **An aux promotion writes an aux address**: `promoteAuxWrites` writes a
name's resolution entry only from its aux entry. -/
theorem promoteAuxWrites_step (cenv : CompileEnv) (name : Ix.Name) (origAddr : Address)
    (origMeta : Ixon.ConstantMeta) (F : Ix.Name → Address → Prop) :
    Step cenv (promoteAuxWrites cenv name origAddr origMeta) F := by
  unfold promoteAuxWrites
  simp only [Id.run]
  split
  · rename_i auxAddr found
    have hm := contains_of_get found
    split
    · exact Step.insert rfl (fun _ h => h) (.inr hm)
    · exact Step.insert rfl (fun _ h => h) (.inr hm)
  · split
    · exact Step.keep rfl (fun _ h => h)
    · exact Step.keep rfl (fun _ h => h)

/-- The original-form promotion's writes (`promoteOriginalWrites`) write only
aux addresses. -/
theorem promoteOriginalWrites_step (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult)
    (cache : BlockState) (F : Ix.Name → Address → Prop) :
    Step acc.cenv (promoteOriginalWrites acc lo result cache).cenv F := by
  unfold promoteOriginalWrites
  simp only [Id.run]
  refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
    (I := fun s : DriverAcc => Step acc.cenv s.cenv F) _ _ _ _ (Step.refl _ _) ?_ ?_
  · intro x _ s hs
    exact hs.trans (promoteAuxWrites_step _ _ _ _ _)
  · intro L hL
    exact hL.trans (Step.keep rfl (fun _ h => h))

/-- The remaining members' writes (`promoteRemainingWrites`) write only names
not yet resolved, at their aux addresses. -/
theorem promoteRemainingWrites_step (acc : DriverAcc) (all : Ix.Set Ix.Name)
    (F : Ix.Name → Address → Prop) : Step acc.cenv (promoteRemainingWrites acc all).1.cenv F := by
  unfold promoteRemainingWrites
  simp only [Id.run]
  refine loop_bind_set (P := fun d : DriverAcc × Array Ix.Name => Step acc.cenv d.1.cenv F)
    (I := fun s : DriverAcc × Array Ix.Name => Step acc.cenv s.1.cenv F) _ _ _ _ (Step.refl _ _) ?_ ?_
  · intro name s hs
    split
    · exact hs
    · rename_i none'
      split
      · rename_i addr found
        unfold resolveAddrPure at found
        rw [none'] at found
        exact hs.trans (Step.insert rfl (fun _ h => h) (.inr (contains_of_get found)))
      · exact hs
  · intro L hL
    exact hL

/-- **A promotion writes only aux addresses**: `finishAuxPromotion` withdraws
the block, or writes the original-form promotion and the remaining members. -/
theorem finishAuxPromotion_step (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (original : Option (BlockResult × BlockState)) (F : Ix.Name → Address → Prop) :
    Step acc.cenv (finishAuxPromotion acc lo all original).1.cenv F := by
  have tail : ∀ (o : Option (BlockResult × BlockState)), Step acc.cenv
      (promoteRemainingWrites (match o with
        | some (result, cache) => promoteOriginalWrites acc lo result cache
        | none => acc) all).1.cenv F := by
    intro o
    cases o with
    | none => exact promoteRemainingWrites_step acc all F
    | some p =>
      obtain ⟨result, cache⟩ := p
      exact (promoteOriginalWrites_step acc lo result cache F).trans
        (promoteRemainingWrites_step _ all F)
  unfold finishAuxPromotion
  simp only [Id.run]
  split
  · split
    · exact failAuxPromotion_step acc all _ F
    · split
      · exact failAuxPromotion_step acc all _ F
      · refine loop_bind (P := fun r : DriverAcc × Array Ix.Name × Bool => Step acc.cenv r.1.cenv F)
          (I := fun s : Option (DriverAcc × Array Ix.Name × Bool) × PUnit =>
            s.1 = none ∨ ∃ msg, s.1 = some (failAuxPromotion acc all msg, #[], true))
          _ _ _ _ (.inl rfl) ?_ ?_
        · intro name _ s _
          split
          · exact .inr ⟨_, rfl⟩
          · exact .inl rfl
        · intro L hL
          rcases hL with h | ⟨msg, h⟩
          · simp only [h]
            exact (promoteOriginalWrites_step acc lo _ _ F).trans (promoteRemainingWrites_step _ all F)
          · simp only [h]
            exact failAuxPromotion_step acc all msg F
  · split
    · exact failAuxPromotion_step acc all _ F
    · refine loop_bind (P := fun r : DriverAcc × Array Ix.Name × Bool => Step acc.cenv r.1.cenv F)
        (I := fun s : Option (DriverAcc × Array Ix.Name × Bool) × PUnit =>
          s.1 = none ∨ ∃ msg, s.1 = some (failAuxPromotion acc all msg, #[], true))
        _ _ _ _ (.inl rfl) ?_ ?_
      · intro name _ s _
        split
        · exact .inr ⟨_, rfl⟩
        · exact .inl rfl
      · intro L hL
        rcases hL with h | ⟨msg, h⟩
        · simp only [h]
          exact tail original
        · simp only [h]
          exact failAuxPromotion_step acc all msg F

/-- Merging a map of inserts into a map keeps every name it holds. -/
theorem fold_insert_contains {m src : Std.HashMap ExactName Address} {n : ExactName}
    (h : m.contains n = true) : (src.fold (fun m k v => m.insert k v) m).contains n = true := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  suffices ∀ (l : List (ExactName × Address)) (m : Std.HashMap ExactName Address), m.contains n = true →
      (l.foldl (fun m x => m.insert x.1 x.2) m).contains n = true from this _ m h
  intro l
  induction l with
  | nil => intro m h; exact h
  | cons x l ih =>
    intro m h
    rw [List.foldl_cons]
    exact ih _ (by rw [Std.HashMap.contains_insert]; simp [h])

/-- A lone constant's primary claim. -/
theorem claim_of_empty {lo : Ix.Name} {result : BlockResult} (h : result.projections.isEmpty = true) :
    (lo, result.blockAddr) ∈ primaryClaims lo result := by
  simp [primaryClaims, h]

/-- A member projection's primary claim. -/
theorem claim_of_projection {lo : Ix.Name} {result : BlockResult}
    (h : ¬result.projections.isEmpty = true) {x : Ix.Name × Ixon.Constant × Ixon.ConstantMeta}
    (hx : x ∈ result.projections) :
    (x.1, Address.admissionHash (Ixon.ser x.2.1)) ∈ primaryClaims lo result := by
  unfold primaryClaims
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  exact Array.mem_map.mpr ⟨x, hx, rfl⟩

set_option hygiene false in
/-- `mergeCompiledBlock`'s loops after its primary registrations, which change
only the stored records, the `Named` table, the aux map (it grows), the
extra names, Pass 3's records, the class registry and the pending names. -/
local macro "merge_tail" init:term : tactic => `(tactic| (
  refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
    (I := fun c : CompileEnv => Step acc.cenv c F) _ _ _ _ ?_ ?_ ?_
  · exact $init
  · intro _ _ s hs; exact hs
  · intro L₂ hL₂
    refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
      (I := fun c : CompileEnv => Step acc.cenv c F) _ _ _ _ hL₂ ?_ ?_
    · intro _ _ s hs; split <;> exact hs
    · intro L₃ hL₃
      split
      · refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
          (I := fun c : CompileEnv => Step acc.cenv c F) _ _ _ _ ?_ ?_ ?_
        · exact hL₃.trans (Step.keep rfl fun _ h => fold_insert_contains h)
        · intro cls _ s hs
          exact forIn_inv_array (fun c : CompileEnv => Step acc.cenv c F) _ cls (by intro _ _ s hs; exact hs) s hs
        · intro L₄ hL₄
          refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
            (I := fun _ : Array Ix.Name => True) _ _ _ _ trivial (fun _ _ _ _ => trivial) ?_
          intro _ _; exact hL₄
      · refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
          (I := fun _ : Array Ix.Name => True) _ _ _ _ trivial (fun _ _ _ _ => trivial) ?_
        intro _ _; exact hL₃.trans (Step.keep rfl fun _ h => fold_insert_contains h)))

/-- **A merge adds only the block's own primary claims** to the resolution
map, and only grows the aux map. -/
theorem mergeCompiledBlock_step (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult)
    (cache : BlockState) (published : Ix.Compile.Pass.Published) :
    Step acc.cenv (mergeCompiledBlock acc lo result cache published).cenv
      (fun n a => (n, a) ∈ primaryClaims lo result) := by
  generalize hF : (fun n a => (n, a) ∈ primaryClaims lo result) = F
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · rename_i hempty
    have claim : F lo result.blockAddr := by rw [← hF]; exact claim_of_empty hempty
    split
    · merge_tail (Step.insert rfl (fun _ h => h) (.inl claim))
    · merge_tail (Step.insert rfl (fun _ h => h) (.inl claim))
  · rename_i hne
    refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
      (I := fun c : CompileEnv => Step acc.cenv c F) _ _ _ _ ?_ ?_ ?_
    · exact Step.keep rfl fun _ h => h
    · intro x hx s hs
      have claim : F x.1 (Address.admissionHash (Ixon.ser x.2.1)) := by
        rw [← hF]; exact claim_of_projection hne hx
      split
      · exact hs.trans (Step.insert rfl (fun _ h => h) (.inl claim))
      · exact hs.trans (Step.insert rfl (fun _ h => h) (.inl claim))
    · intro L hL
      merge_tail hL

/-- The primary claims a block outcome merges: a compiled block's, at its
key; a promoted block's cross-SCC subset's, at its own key; none otherwise. -/
def outcomeClaims (lo : Ix.Name) : AuxBlockOutcome → Ix.Name → Address → Prop
  | .compiled result _ _ => fun n a => (n, a) ∈ primaryClaims lo result
  | .promoted (some (clo, result, _, _)) _ _ _ _ _ => fun n a => (n, a) ∈ primaryClaims clo result
  | _ => fun _ _ => False

theorem fst_pure {G : Ix.Name → Address → Prop} {c : CompileEnv} {d : DriverAcc} {x : Array Ix.Name}
    {y : Bool} (h : Step c d.cenv G) :
    Step c (pure (d, x, y) : Id (DriverAcc × Array Ix.Name × Bool)).1.cenv G := h

/-- A loop over registered names, then a return. -/
theorem loopNames {G : Ix.Name → Address → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
    (init : Array Ix.Name) (f : α → Array Ix.Name → Id (ForInStep (Array Ix.Name)))
    (k : Array Ix.Name → Id (DriverAcc × Array Ix.Name × Bool)) (cont : ∀ L, Step c (k L).1.cenv G) :
    Step c (forIn (m := Id) xs init f >>= k).1.cenv G :=
  loop_bind xs init f k (fun _ => True) (fun r => Step c r.1.cenv G) trivial (fun _ _ _ _ => trivial)
    fun L _ => cont L

/-- A loop over the driver state, then its continuation. -/
theorem loopAcc {G : Ix.Name → Address → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
    (init : DriverAcc) (f : α → DriverAcc → Id (ForInStep DriverAcc)) (k : DriverAcc → Id DriverAcc)
    (hinit : Step c init.cenv G) (body : ∀ x ∈ xs, ∀ s, Step c s.cenv G → Step c (f x s).value.cenv G)
    (cont : ∀ L, Step c L.cenv G → Step c (k L).cenv G) : Step c (forIn (m := Id) xs init f >>= k).cenv G :=
  loop_bind xs init f k (fun d => Step c d.cenv G) (fun d => Step c d.cenv G) hinit body cont


/-- **Applying a compiled block adds only its primary claims** to the
resolution map (or, when its claims or payloads conflict, records its
failures and changes nothing else). -/
theorem applyAuxBlockOutcome_compiled_step (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (r : BlockResult) (c : BlockState) (p : Ix.Compile.Pass.Published) :
    Step acc.cenv (applyAuxBlockOutcome acc lo all (.compiled r c p)).1.cenv
      (outcomeClaims lo (.compiled r c p)) := by
    unfold applyAuxBlockOutcome; simp only [Id.run]
    have merged := (mergeCompiledBlock_step acc lo r c p).mono (G := outcomeClaims lo (.compiled r c p))
      fun _ _ h => h
    split
    · refine fst_pure ?_
      refine loopAcc _ _ _ _ ?_ ?_ ?_
      · exact Step.refl _ _
      · intro _ _ s hs
        exact hs.trans (Step.keep rfl fun _ h => h)
      · intro L hL
        exact hL
    · split
      · refine loopNames _ _ _ _ ?_
        intro L
        exact fst_pure merged
      · refine loopNames _ _ _ _ ?_
        intro L
        refine loopNames _ _ _ _ ?_
        intro L
        exact fst_pure merged

/-- **Applying a failed block only records its failures.** -/
theorem applyAuxBlockOutcome_failed_step (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (msg : String) :
    Step acc.cenv (applyAuxBlockOutcome acc lo all (.failed msg)).1.cenv (outcomeClaims lo (.failed msg)) := by
    unfold applyAuxBlockOutcome; simp only [Id.run]
    refine fst_pure ?_
    refine loopAcc _ _ _ _ ?_ ?_ ?_
    · exact Step.refl _ _
    · intro _ _ s hs
      exact hs.trans (Step.keep rfl fun _ h => h)
    · intro L hL
      exact hL

/-- A loop over the driver state, then a continuation that returns. -/
theorem loopAccRet {G : Ix.Name → Address → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
    (init : DriverAcc) (f : α → DriverAcc → Id (ForInStep DriverAcc))
    (k : DriverAcc → Id (DriverAcc × Array Ix.Name × Bool)) (hinit : Step c init.cenv G)
    (body : ∀ x ∈ xs, ∀ s, Step c s.cenv G → Step c (f x s).value.cenv G)
    (cont : ∀ L, Step c L.cenv G → Step c (k L).1.cenv G) : Step c (forIn (m := Id) xs init f >>= k).1.cenv G :=
  loop_bind xs init f k (fun d => Step c d.cenv G) (fun r => Step c r.1.cenv G) hinit body cont

/-- A loop body that changes only fields `Step` ignores. -/
local macro "keep_body" : tactic => `(tactic| (intro _ _ s hs; exact hs.trans (Step.keep rfl fun _ h => h)))

/-- A loop over the driver state that changes only fields `Step` ignores,
then a return; the step to the loop's initial state is left. -/
local macro "keep_loop" : tactic => `(tactic| refine loopAcc _ _ _ _ ?_ (by keep_body) fun _ h => h)

/-- The promotion's tail, from a driver state `X` already reached by a step:
an incomplete or failed original form withdraws the promotion, otherwise it
finishes. `x` proves the step to `X`. -/
local macro "prom_tail" x:tactic : tactic => `(tactic| (
  split
  · refine fst_pure (Step.trans ?_ (failAuxPromotion_step _ _ _ _)); $x
  · split
    · refine fst_pure (Step.trans ?_ (failAuxPromotion_step _ _ _ _)); $x
    · split
      · refine fst_pure (Step.trans ?_ (finishAuxPromotion_step _ _ _ _ _)); $x
      · refine fst_pure (Step.trans ?_ (finishAuxPromotion_step _ _ _ _ _)); $x))

/-- **Applying a promoted block adds only its cross-SCC subset's primary
claims** (the original-form promotion and the remaining claims write aux
addresses, a withdrawal only erases, and recorded failures leave the map). -/
theorem applyAuxBlockOutcome_promoted_step (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (cs : Option (Ix.Name × BlockResult × BlockState × Ix.Compile.Pass.Published)) (cn : Array Ix.Name)
    (cf : Option (Array Ix.Name × String)) (im : Option String) (na : Option (BlockResult × BlockState))
    (nf : Option String) :
    Step acc.cenv (applyAuxBlockOutcome acc lo all (.promoted cs cn cf im na nf)).1.cenv
      (outcomeClaims lo (.promoted cs cn cf im na nf)) := by
  rcases cs with _ | ⟨clo, result, cache, published⟩
  · rcases cf with _ | ⟨names, msg⟩
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      prom_tail (exact Step.refl _ _)
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      prom_tail (keep_loop; exact Step.refl _ _)
  · have merged : ∀ X : DriverAcc, Step acc.cenv X.cenv
        (outcomeClaims lo (.promoted (some (clo, result, cache, published)) cn cf im na nf)) →
        Step acc.cenv (mergeCompiledBlock X clo result cache published).cenv
          (outcomeClaims lo (.promoted (some (clo, result, cache, published)) cn cf im na nf)) :=
      fun X hX => hX.trans ((mergeCompiledBlock_step X clo result cache published).mono fun _ _ h => h)
    rcases cf with _ | ⟨names, msg⟩
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      split
      · prom_tail (keep_loop; exact Step.refl _ _)
      · split
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ (Step.refl _ _)) (by keep_body) fun L hL => ?_
          prom_tail (exact hL)
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ (Step.refl _ _)) (by keep_body) fun L hL => ?_
          prom_tail (exact hL)
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      split
      · prom_tail (keep_loop; keep_loop; exact Step.refl _ _)
      · split
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ ?_) (by keep_body) fun L hL => ?_
          · keep_loop; exact Step.refl _ _
          · prom_tail (exact hL)
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ ?_) (by keep_body) fun L hL => ?_
          · keep_loop; exact Step.refl _ _
          · prom_tail (exact hL)

/-- **Applying a block's outcome adds only the outcome's primary claims** to
the resolution map, besides aux names' entries. -/
theorem applyAuxBlockOutcome_step (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (o : AuxBlockOutcome) :
    Step acc.cenv (applyAuxBlockOutcome acc lo all o).1.cenv (outcomeClaims lo o) := by
  cases o with
  | compiled r c p => exact applyAuxBlockOutcome_compiled_step acc lo all r c p
  | promoted cs cn cf im na nf => exact applyAuxBlockOutcome_promoted_step acc lo all cs cn cf im na nf
  | failed msg => exact applyAuxBlockOutcome_failed_step acc lo all msg

/-! ## Where the final resolution map's entries come from -/

/-- **A primary claim of a block compiled during the fold**: `n ↦ a` is one
of the claims (`outcomeClaims`) of a condensation block's outcome, under its
key, computed against a state the fold reached. -/
def Compiled (blocks : Ix.CondensedBlocks) (init : DriverAcc) (n : Ix.Name) (a : Address) : Prop :=
  ∃ snap rep all, Reach blocks init snap ∧ blocks.blocks.get? rep = some all ∧
    outcomeClaims (blockKey rep all) (auxBlockOutcome snap.cenv (blockKey rep all) all) n a

/-- Every entry of a driver state's resolution map is an aux name's, or
`Compiled`. -/
def Provenance (blocks : Ix.CondensedBlocks) (init acc : DriverAcc) : Prop :=
  ∀ (n : ExactName) (a : Address), acc.cenv.nameToAddr.get? n = some a →
    acc.cenv.auxNameToAddr.contains n = true ∨ Compiled blocks init n a

theorem provenance_of_empty {blocks : Ix.CondensedBlocks} {init : DriverAcc}
    (h : init.cenv.nameToAddr = {}) : Provenance blocks init init := by
  intro n a hn
  rw [h, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hn
  cases hn

/-- **Every reached state's resolution map has provenance**, when the
initial one has: each entry is an aux name's, or a primary claim of a block
compiled during the fold. -/
theorem reach_provenance {blocks : Ix.CondensedBlocks} {init acc : DriverAcc}
    (h₀ : Provenance blocks init init) (h : Reach blocks init acc) : Provenance blocks init acc := by
  induction h with
  | init => exact h₀
  | @step snap acc rep all hsnap _ hall _ ih =>
    intro n a hn
    rcases applyAuxBlockOutcome_step acc _ all _ n a hn with ⟨hold, keep⟩ | haux | hclaim
    · rcases ih n a hold with haux | hc
      · exact .inl (keep haux)
      · exact .inr hc
    · exact .inl haux
    · exact .inr ⟨snap, rep, all, hsnap, hall, hclaim⟩

/-- The fold's initial state keeps its compile environment's resolution map. -/
theorem init_nameToAddr (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) :
    (FoldState.init cenv blocks sched).acc.cenv.nameToAddr = cenv.nameToAddr := rfl

/-- Assembling the environment returns the driver's compile environment. -/
theorem assembleEnv_cenv (acc : DriverAcc) : (assembleEnv acc).2.2 = acc.cenv := rfl

/-- **The driver's final state**: a fold that returns ran its waves from an
initial state whose resolution map is empty, and returns the resolution map
and the aux map of the state the waves reached. -/
theorem compileEnvFold_final {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState),
      cenv₀.nameToAddr = {} ∧
      foldWavesSeq blocks sched (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched) = .ok st ∧
      cenv.nameToAddr = st.acc.cenv.nameToAddr ∧ cenv.auxNameToAddr = st.acc.cenv.auxNameToAddr := by
  rw [compileEnvFold_eq_seq] at h
  unfold compileEnvFoldSeq compileEnvFoldWithSourceSeq at h
  generalize missingBlockRefs? blocks = missing at h
  generalize validateInductiveFlags env = flags at h
  generalize validateMutualSafety env blocks = safety at h
  cases missing <;> cases flags <;> cases safety <;>
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h <;> try cases h
  generalize hr : foldWavesSeq _ _ _ _ = r at h
  cases r with
  | error => cases h
  | ok st =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact ⟨_, _, st, rfl, hr, rfl, rfl⟩

/-- **The driver's final resolution map has provenance**: every entry is an
aux name's, or a primary claim of a condensation block compiled during the
fold, against a state the fold reached. -/
theorem compileEnvFold_provenance {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ init : DriverAcc, ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
      cenv.auxNameToAddr.contains n = true ∨ Compiled blocks init n a := by
  obtain ⟨cenv₀, sched, st, h₀, hst, hmap, haux⟩ := compileEnvFold_final h
  refine ⟨(FoldState.init cenv₀ blocks sched).acc, fun n a hn => ?_⟩
  rw [hmap] at hn
  rw [haux]
  exact reach_provenance (provenance_of_empty ((init_nameToAddr _ _ _).trans h₀))
    (foldWavesSeq_reach _ _ _ hst Reach.init) n a hn

/-- **`compileUnchecked`'s resolution map is the driver's final one**: a
`compileUnchecked` that returns ran the fold on the ground part's
condensation, and returns the resolution map of the fold's final compile
environment. -/
theorem compileUnchecked_fold {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {resolved : Std.HashMap ExactName Address}
    (h : compileUnchecked env = .ok (ixe, failures, resolved)) :
    ∃ (bytes : Nat) (cenv : CompileEnv),
      compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) = .ok (ixe, bytes, cenv) ∧
      resolved = cenv.nameToAddr := by
  unfold compileUnchecked at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      obtain ⟨ixe', bytes, cenv⟩ := r
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨bytes, cenv, hr, rfl⟩

/-- **Where `compileUnchecked`'s resolution map comes from**: every entry is
an aux name's, in the fold's final compile environment, or a primary claim
of a condensation block compiled during the fold. -/
theorem compileUnchecked_provenance {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {resolved : Std.HashMap ExactName Address}
    (h : compileUnchecked env = .ok (ixe, failures, resolved)) :
    ∃ (bytes : Nat) (cenv : CompileEnv) (init : DriverAcc),
      compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) = .ok (ixe, bytes, cenv) ∧
      resolved = cenv.nameToAddr ∧
      ∀ (n : ExactName) (a : Address), resolved.get? n = some a →
        cenv.auxNameToAddr.contains n = true ∨
          Compiled (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) init n a := by
  obtain ⟨bytes, cenv, hf, rfl⟩ := compileUnchecked_fold h
  obtain ⟨init, hp⟩ := compileEnvFold_provenance hf
  exact ⟨bytes, cenv, init, hf, rfl, hp⟩

end Ix.Cert.Resolution
