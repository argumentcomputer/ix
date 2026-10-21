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
(`promoteAuxWrites`, `promoteRemainingWrites`). **The environment stores the
claimed record's bytes at its address**: only a merge stores records, after
the content check (`checkCompiledBlock`, `checkAnonymousWrites`: each write
agrees with the store and with the block's other writes), so a stored record
never changes, and `assembleEnv` copies the store. No digest injectivity is
assumed.

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

/-- **One driver operation's effect on the resolution map and the stored
records**, from `c` to `c'`: a stored record stays stored, with the same
bytes; and every entry of `c'`'s resolution map is one of `c`'s, whose name
keeps its aux address if it had one, or its name has an aux address in `c'`,
or it is one of the operation's own claims (`F`), with the claimed bytes
stored at its address. -/
def Step (c c' : CompileEnv) (F : Ix.Name → Address → ByteArray → Prop) : Prop :=
  (∀ (a : Address) (b : ByteArray), c.constants.get? a = some b → c'.constants.get? a = some b) ∧
  ∀ (n : ExactName) (a : Address), c'.nameToAddr.get? n = some a →
    (c.nameToAddr.get? n = some a ∧ (c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)) ∨
      c'.auxNameToAddr.contains n = true ∨ ∃ b, F n a b ∧ c'.constants.get? a = some b

theorem Step.refl (c : CompileEnv) (F : Ix.Name → Address → ByteArray → Prop) : Step c c F :=
  ⟨fun _ _ h => h, fun _ _ h => .inl ⟨h, id⟩⟩

theorem Step.mono {c c' : CompileEnv} {F G : Ix.Name → Address → ByteArray → Prop} (h : Step c c' F)
    (FG : ∀ n a b, F n a b → G n a b) : Step c c' G := by
  refine ⟨h.1, fun n a hn => ?_⟩
  rcases h.2 n a hn with h | h | ⟨b, hF, hb⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨b, FG n a b hF, hb⟩)

theorem Step.trans {c₁ c₂ c₃ : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} (h₁ : Step c₁ c₂ F)
    (h₂ : Step c₂ c₃ F) : Step c₁ c₃ F := by
  refine ⟨fun a b h => h₂.1 a b (h₁.1 a b h), fun n a hn => ?_⟩
  rcases h₂.2 n a hn with ⟨h, keep₂⟩ | h | h
  · rcases h₁.2 n a h with ⟨h, keep₁⟩ | h | ⟨b, hF, hb⟩
    · exact .inl ⟨h, fun k => keep₂ (keep₁ k)⟩
    · exact .inr (.inl (keep₂ h))
    · exact .inr (.inr ⟨b, hF, h₂.1 a b hb⟩)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- An operation that leaves the resolution map and the stored records, and
keeps every aux name. -/
theorem Step.keep {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop}
    (h₁ : c'.nameToAddr = c.nameToAddr)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (h₃ : c'.constants = c.constants := by rfl) :
    Step c c' F := by
  refine ⟨fun a b h => by rw [h₃]; exact h, fun n a hn => ?_⟩
  rw [h₁] at hn
  exact .inl ⟨hn, h₂ n⟩

/-- An operation that erases one name from the resolution map and the aux map. -/
theorem Step.erase {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} {m : ExactName}
    (h₁ : c'.nameToAddr = c.nameToAddr.erase m) (h₂ : c'.auxNameToAddr = c.auxNameToAddr.erase m)
    (h₃ : c'.constants = c.constants := by rfl) :
    Step c c' F := by
  refine ⟨fun a b h => by rw [h₃]; exact h, fun n a hn => ?_⟩
  rw [h₁, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase] at hn
  split at hn
  · cases hn
  · rename_i ne
    refine .inl ⟨by rw [Std.HashMap.get?_eq_getElem?]; exact hn, fun k => ?_⟩
    rw [h₂, Std.HashMap.contains_erase]
    simp [ne, k]

/-- An operation that writes one entry of the resolution map: one of its own
claims (`F`), with the claimed bytes stored, or an aux name's. -/
theorem Step.insert {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} {m : ExactName}
    {b : Address} (h₁ : c'.nameToAddr = c.nameToAddr.insert m b)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (hm : (∃ bytes, F m b bytes ∧ c'.constants.get? b = some bytes) ∨ c'.auxNameToAddr.contains m = true)
    (h₃ : c'.constants = c.constants := by rfl) : Step c c' F := by
  refine ⟨fun a b h => by rw [h₃]; exact h, fun n a hn => ?_⟩
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

/-- A write that agrees with what is stored at its address changes no stored
record. -/
theorem grow_insert {s s' : Std.HashMap Address ByteArray} {k : Address} {v : ByteArray}
    (h₃ : s' = s.insert k v) (agree : ∀ v₀, s.get? k = some v₀ → v₀ = v) :
    ∀ a b, s.get? a = some b → s'.get? a = some b := by
  intro a b h
  rw [h₃, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  split
  · rename_i same
    have e : k = a := beq_iff_eq.mp same
    subst e
    rw [agree b h]
  · rw [← Std.HashMap.get?_eq_getElem?]; exact h

/-- Storing a record: a write that agrees with what is stored at its address. -/
theorem Step.write {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} {k : Address}
    {v : ByteArray} (h₁ : c'.nameToAddr = c.nameToAddr)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (h₃ : c'.constants = c.constants.insert k v) (agree : ∀ v₀, c.constants.get? k = some v₀ → v₀ = v) :
    Step c c' F := by
  refine ⟨grow_insert h₃ agree, fun n a hn => ?_⟩
  rw [h₁] at hn
  exact .inl ⟨hn, h₂ n⟩

/-- Storing a claimed record and claiming it: a write that agrees with what is
stored at its address, and the resolution entry of one of the operation's
claims (`F`) at that address. -/
theorem Step.claim {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} {m : ExactName}
    {k : Address} {v : ByteArray} (h₁ : c'.nameToAddr = c.nameToAddr.insert m k)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (h₃ : c'.constants = c.constants.insert k v) (agree : ∀ v₀, c.constants.get? k = some v₀ → v₀ = v)
    (hF : F m k v) : Step c c' F := by
  have stored : c'.constants.get? k = some v := by
    rw [h₃, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
  refine ⟨grow_insert h₃ agree, fun n a hn => ?_⟩
  rw [h₁, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hn
  split at hn
  · rename_i same
    have e : m = n := beq_iff_eq.mp same
    subst e
    cases hn
    exact .inr (.inr ⟨v, hF, stored⟩)
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
    (F : Ix.Name → Address → ByteArray → Prop) : Step acc.cenv (failAuxPromotion acc all msg).cenv F := by
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
    (origMeta : Ixon.ConstantMeta) (F : Ix.Name → Address → ByteArray → Prop) :
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
    (cache : BlockState) (F : Ix.Name → Address → ByteArray → Prop) :
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
    (F : Ix.Name → Address → ByteArray → Prop) : Step acc.cenv (promoteRemainingWrites acc all).1.cenv F := by
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
    (original : Option (BlockResult × BlockState)) (F : Ix.Name → Address → ByteArray → Prop) :
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

/-- The primary claims of a compiled block, with the bytes of the records they
claim: the lone constant's, else each member projection's. -/
def claimWrites (lo : Ix.Name) (result : BlockResult) : Array (Ix.Name × Address × ByteArray) :=
  if result.projections.isEmpty then
    #[(lo, result.blockAddr, result.blockBytes)]
  else
    result.projections.map fun (name, proj, _) =>
      (name, Address.admissionHash (Ixon.ser proj), Ixon.ser proj)

/-- A lone constant's primary claim. -/
theorem claim_of_empty {lo : Ix.Name} {result : BlockResult} (h : result.projections.isEmpty = true) :
    (lo, result.blockAddr, result.blockBytes) ∈ claimWrites lo result := by
  simp [claimWrites, h]

/-- A member projection's primary claim. -/
theorem claim_of_projection {lo : Ix.Name} {result : BlockResult}
    (h : ¬result.projections.isEmpty = true) {x : Ix.Name × Ixon.Constant × Ixon.ConstantMeta}
    (hx : x ∈ result.projections) :
    (x.1, Address.admissionHash (Ixon.ser x.2.1), Ixon.ser x.2.1) ∈ claimWrites lo result := by
  unfold claimWrites
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  exact Array.mem_map.mpr ⟨x, hx, rfl⟩

/-! ### The content check -/

/-- What a passed content check says about a block's record writes: each
agrees with the store before the block, and two writes at one address agree. -/
structure Agrees (before : Std.HashMap Address ByteArray) (W : List (Address × ByteArray)) : Prop where
  old : ∀ k v, (k, v) ∈ W → ∀ v₀, before.get? k = some v₀ → v₀ = v
  own : ∀ k v v', (k, v) ∈ W → (k, v') ∈ W → v = v'

theorem contentMatches_eq {store : Std.HashMap Address ByteArray} {k : Address} {v v₀ : ByteArray}
    (h : contentMatches store k v = true) (h₀ : store.get? k = some v₀) : v₀ = v := by
  unfold contentMatches at h
  rw [← Std.HashMap.get?_eq_getElem?, h₀] at h
  exact of_decide_eq_true h

theorem checkContentWrites_agrees : ∀ (W : List (Address × ByteArray)) (seen : Std.HashMap Address ByteArray),
    checkContentWrites seen W = true →
      (∀ k v v', seen.get? k = some v → (k, v') ∈ W → v = v') ∧
        ∀ k v v', (k, v) ∈ W → (k, v') ∈ W → v = v' := by
  intro W
  induction W with
  | nil => intro _ _; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩
  | cons x rest ih =>
    obtain ⟨k₀, v₀⟩ := x
    intro seen h
    unfold checkContentWrites at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hm, hrest⟩ := h
    obtain ⟨ihA, ihB⟩ := ih _ hrest
    have seen' : ∀ k v, seen.get? k = some v → (seen.insert k₀ v₀).get? k = some v := by
      intro k v hk
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      split
      · rename_i same
        have e : k₀ = k := beq_iff_eq.mp same
        subst e
        rw [contentMatches_eq hm hk]
      · rw [← Std.HashMap.get?_eq_getElem?]; exact hk
    have self : (seen.insert k₀ v₀).get? k₀ = some v₀ := by
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
    refine ⟨fun k v v' hk hv' => ?_, fun k v v' hv hv' => ?_⟩
    · rcases List.mem_cons.mp hv' with e | hv'
      · cases e; exact contentMatches_eq hm hk
      · exact ihA k v v' (seen' k v hk) hv'
    · rcases List.mem_cons.mp hv with e | hv <;> rcases List.mem_cons.mp hv' with e' | hv'
      · cases e; cases e'; rfl
      · cases e; exact ihA _ _ _ self hv'
      · cases e'; exact (ihA _ _ _ self hv).symm
      · exact ihB k v v' hv hv'

theorem checkAnonymousWrites_agrees {before : Std.HashMap Address ByteArray} {W : List (Address × ByteArray)}
    (h : checkAnonymousWrites before W = true) : Agrees before W := by
  unfold checkAnonymousWrites at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hown⟩ := h
  exact ⟨fun k v hk v₀ h₀ => contentMatches_eq (hall (k, v) hk) h₀,
    (checkContentWrites_agrees W {} hown).2⟩

/-- A merge runs only after `checkCompiledBlock`, whose content check covers
exactly the merge's record writes (`blockRecordWrites`). -/
theorem checkCompiledBlock_content {cenv : CompileEnv} {lo : Ix.Name} {result : BlockResult}
    {cache : BlockState} {published : Ix.Compile.Pass.Published}
    (h : checkCompiledBlock cenv lo result cache published = .ok ()) :
    checkAnonymousWrites cenv.constants (blockRecordWrites result cache) = true := by
  unfold checkCompiledBlock at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · unfold checkBlockContent at h
    split at h
    · assumption
    · cases h

/-- Every record stored during a merge was stored before it, or is one of
the merge's writes. -/
def Stored (before : Std.HashMap Address ByteArray) (W : List (Address × ByteArray)) (c : CompileEnv) : Prop :=
  ∀ a v, c.constants.get? a = some v → before.get? a = some v ∨ (a, v) ∈ W

theorem Stored.agree {before : Std.HashMap Address ByteArray} {W : List (Address × ByteArray)}
    {c : CompileEnv} {k : Address} {v : ByteArray} (hs : Stored before W c) (ag : Agrees before W)
    (hk : (k, v) ∈ W) : ∀ v₀, c.constants.get? k = some v₀ → v₀ = v := by
  intro v₀ h
  rcases hs k v₀ h with h | h
  · exact ag.old k v hk v₀ h
  · exact ag.own k v₀ v h hk

theorem Stored.insert {before : Std.HashMap Address ByteArray} {W : List (Address × ByteArray)}
    {c c' : CompileEnv} {k : Address} {v : ByteArray} (hs : Stored before W c) (hk : (k, v) ∈ W)
    (h₃ : c'.constants = c.constants.insert k v) : Stored before W c' := by
  intro a v' h
  rw [h₃, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i same
    have e : k = a := beq_iff_eq.mp same
    subst e
    cases h
    exact .inr hk
  · exact hs a v' (by rw [Std.HashMap.get?_eq_getElem?]; exact h)

theorem write_block {result : BlockResult} {cache : BlockState} :
    (result.blockAddr, result.blockBytes) ∈ blockRecordWrites result cache := List.mem_cons_self

theorem write_projection {result : BlockResult} {cache : BlockState}
    {x : Ix.Name × Ixon.Constant × Ixon.ConstantMeta} (hx : x ∈ result.projections) :
    (Address.admissionHash (Ixon.ser x.2.1), Ixon.ser x.2.1) ∈ blockRecordWrites result cache :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨x, Array.mem_toList_iff.mpr hx, rfl⟩))

theorem write_aux {result : BlockResult} {cache : BlockState} {x : Address × Ixon.Constant}
    (hx : x ∈ cache.auxConsts) : (x.1, Ixon.ser x.2) ∈ blockRecordWrites result cache :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨x, Array.mem_toList_iff.mpr hx, rfl⟩))

set_option hygiene false in
/-- `mergeCompiledBlock`'s loops after its primary registrations, which change
only the stored records (each write checked), the `Named` table, the aux map
(it grows), the extra names, Pass 3's records, the class registry and the
pending names. -/
local macro "merge_tail" init:term : tactic => `(tactic| (
  refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
    (I := fun c : CompileEnv => Step acc.cenv c F ∧ Stored acc.cenv.constants (blockRecordWrites result cache) c)
    _ _ _ _ ?_ ?_ ?_
  · exact $init
  · intro x hx s hs
    exact ⟨hs.1.trans (Step.write rfl (fun _ h => h) rfl (hs.2.agree ag (write_aux hx))),
      hs.2.insert (write_aux hx) rfl⟩
  · intro L₂ hL₂'
    have hL₂ := hL₂'.1
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
map, each with its record's bytes stored at its address, only grows the aux
map, and changes no stored record (its writes passed the content check). -/
theorem mergeCompiledBlock_step (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult)
    (cache : BlockState) (published : Ix.Compile.Pass.Published)
    (hchk : checkAnonymousWrites acc.cenv.constants (blockRecordWrites result cache) = true) :
    Step acc.cenv (mergeCompiledBlock acc lo result cache published).cenv
      (fun n a b => (n, a, b) ∈ claimWrites lo result) := by
  have ag := checkAnonymousWrites_agrees hchk
  have st₀ : Stored acc.cenv.constants (blockRecordWrites result cache) acc.cenv := fun _ _ h => .inl h
  generalize hF : (fun n a b => (n, a, b) ∈ claimWrites lo result) = F
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · rename_i hempty
    have claim : F lo result.blockAddr result.blockBytes := by rw [← hF]; exact claim_of_empty hempty
    split
    · merge_tail ⟨Step.claim rfl (fun _ h => h) rfl (st₀.agree ag write_block) claim,
        st₀.insert write_block rfl⟩
    · merge_tail ⟨Step.claim rfl (fun _ h => h) rfl (st₀.agree ag write_block) claim,
        st₀.insert write_block rfl⟩
  · rename_i hne
    refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
      (I := fun c : CompileEnv => Step acc.cenv c F ∧ Stored acc.cenv.constants (blockRecordWrites result cache) c)
      _ _ _ _ ?_ ?_ ?_
    · exact ⟨Step.write rfl (fun _ h => h) rfl (st₀.agree ag write_block), st₀.insert write_block rfl⟩
    · intro x hx s hs
      have claim : F x.1 (Address.admissionHash (Ixon.ser x.2.1)) (Ixon.ser x.2.1) := by
        rw [← hF]; exact claim_of_projection hne hx
      split
      · exact ⟨hs.1.trans (Step.claim rfl (fun _ h => h) rfl (hs.2.agree ag (write_projection hx)) claim),
          hs.2.insert (write_projection hx) rfl⟩
      · exact ⟨hs.1.trans (Step.claim rfl (fun _ h => h) rfl (hs.2.agree ag (write_projection hx)) claim),
          hs.2.insert (write_projection hx) rfl⟩
    · intro L hL
      merge_tail hL

/-- The primary claims a block outcome merges, with their records' bytes: a
compiled block's, at its key; a promoted block's cross-SCC subset's, at its
own key; none otherwise. -/
def outcomeClaims (lo : Ix.Name) : AuxBlockOutcome → Ix.Name → Address → ByteArray → Prop
  | .compiled result _ _ => fun n a b => (n, a, b) ∈ claimWrites lo result
  | .promoted (some (clo, result, _, _)) _ _ _ _ _ => fun n a b => (n, a, b) ∈ claimWrites clo result
  | _ => fun _ _ _ => False

theorem fst_pure {G : Ix.Name → Address → ByteArray → Prop} {c : CompileEnv} {d : DriverAcc} {x : Array Ix.Name}
    {y : Bool} (h : Step c d.cenv G) :
    Step c (pure (d, x, y) : Id (DriverAcc × Array Ix.Name × Bool)).1.cenv G := h

/-- A loop over registered names, then a return. -/
theorem loopNames {G : Ix.Name → Address → ByteArray → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
    (init : Array Ix.Name) (f : α → Array Ix.Name → Id (ForInStep (Array Ix.Name)))
    (k : Array Ix.Name → Id (DriverAcc × Array Ix.Name × Bool)) (cont : ∀ L, Step c (k L).1.cenv G) :
    Step c (forIn (m := Id) xs init f >>= k).1.cenv G :=
  loop_bind xs init f k (fun _ => True) (fun r => Step c r.1.cenv G) trivial (fun _ _ _ _ => trivial)
    fun L _ => cont L

/-- A loop over the driver state, then its continuation. -/
theorem loopAcc {G : Ix.Name → Address → ByteArray → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
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
    split
    · refine fst_pure ?_
      refine loopAcc _ _ _ _ ?_ ?_ ?_
      · exact Step.refl _ _
      · intro _ _ s hs
        exact hs.trans (Step.keep rfl fun _ h => h)
      · intro L hL
        exact hL
    · rename_i hc
      have merged := (mergeCompiledBlock_step acc lo r c p (checkCompiledBlock_content hc)).mono
        (G := outcomeClaims lo (.compiled r c p)) fun _ _ _ h => h
      split
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
theorem loopAccRet {G : Ix.Name → Address → ByteArray → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
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
  · have merged : ∀ X : DriverAcc, checkCompiledBlock X.cenv clo result cache published = .ok () →
        Step acc.cenv X.cenv
        (outcomeClaims lo (.promoted (some (clo, result, cache, published)) cn cf im na nf)) →
        Step acc.cenv (mergeCompiledBlock X clo result cache published).cenv
          (outcomeClaims lo (.promoted (some (clo, result, cache, published)) cn cf im na nf)) :=
      fun X hc hX => hX.trans ((mergeCompiledBlock_step X clo result cache published
        (checkCompiledBlock_content hc)).mono fun _ _ _ h => h)
    rcases cf with _ | ⟨names, msg⟩
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      split
      · prom_tail (keep_loop; exact Step.refl _ _)
      · rename_i hc
        split
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ hc (Step.refl _ _)) (by keep_body) fun L hL => ?_
          prom_tail (exact hL)
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ hc (Step.refl _ _)) (by keep_body) fun L hL => ?_
          prom_tail (exact hL)
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      split
      · prom_tail (keep_loop; keep_loop; exact Step.refl _ _)
      · rename_i hc
        split
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ hc ?_) (by keep_body) fun L hL => ?_
          · keep_loop; exact Step.refl _ _
          · prom_tail (exact hL)
        · refine loopNames _ _ _ _ fun _ => ?_
          refine loopNames _ _ _ _ fun _ => ?_
          refine loopAccRet _ _ _ _ (merged _ hc ?_) (by keep_body) fun L hL => ?_
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

/-- **A primary claim of a block compiled during the fold**: `n ↦ a`, with
the claimed record's bytes `b`, is one of the claims (`outcomeClaims`) of a
condensation block's outcome, under its key, computed against a state the
fold reached. -/
def Compiled (blocks : Ix.CondensedBlocks) (init : DriverAcc) (n : Ix.Name) (a : Address)
    (b : ByteArray) : Prop :=
  ∃ snap rep all, Reach blocks init snap ∧ blocks.blocks.get? rep = some all ∧
    outcomeClaims (blockKey rep all) (auxBlockOutcome snap.cenv (blockKey rep all) all) n a b

/-- Every entry of a driver state's resolution map is an aux name's, or
`Compiled` with the claimed record's bytes stored at its address. -/
def Provenance (blocks : Ix.CondensedBlocks) (init acc : DriverAcc) : Prop :=
  ∀ (n : ExactName) (a : Address), acc.cenv.nameToAddr.get? n = some a →
    acc.cenv.auxNameToAddr.contains n = true ∨
      ∃ b, Compiled blocks init n a b ∧ acc.cenv.constants.get? a = some b

theorem provenance_of_empty {blocks : Ix.CondensedBlocks} {init : DriverAcc}
    (h : init.cenv.nameToAddr = {}) : Provenance blocks init init := by
  intro n a hn
  rw [h, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hn
  cases hn

/-- **Every reached state's resolution map has provenance**, when the
initial one has: each entry is an aux name's, or a primary claim of a block
compiled during the fold, whose record's bytes are stored at its address. -/
theorem reach_provenance {blocks : Ix.CondensedBlocks} {init acc : DriverAcc}
    (h₀ : Provenance blocks init init) (h : Reach blocks init acc) : Provenance blocks init acc := by
  induction h with
  | init => exact h₀
  | @step snap acc rep all hsnap _ hall _ ih =>
    intro n a hn
    have st := applyAuxBlockOutcome_step acc (blockKey rep all) all
      (auxBlockOutcome snap.cenv (blockKey rep all) all)
    rcases st.2 n a hn with ⟨hold, keep⟩ | haux | ⟨b, hclaim, hb⟩
    · rcases ih n a hold with haux | ⟨b, hc, hb⟩
      · exact .inl (keep haux)
      · exact .inr ⟨b, hc, st.1 a b hb⟩
    · exact .inl haux
    · exact .inr ⟨b, ⟨snap, rep, all, hsnap, hall, hclaim⟩, hb⟩

/-- The fold's initial state keeps its compile environment's resolution map. -/
theorem init_nameToAddr (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) :
    (FoldState.init cenv blocks sched).acc.cenv.nameToAddr = cenv.nameToAddr := rfl

/-- Assembling the environment returns the driver's compile environment. -/
theorem assembleEnv_cenv (acc : DriverAcc) : (assembleEnv acc).2.2 = acc.cenv := rfl

/-- Inserting a list of entries with distinct keys: an entry's key ends with
its value. -/
theorem foldl_insert_get {β γ : Type} (g : β → γ) {a : Address} {b : β} :
    ∀ (l : List (Address × β)) (m : Std.HashMap Address γ),
      l.Pairwise (fun x y => (x.1 == y.1) = false) → (a, b) ∈ l →
        (l.foldl (fun m x => m.insert x.1 (g x.2)) m).get? a = some (g b) := by
  have keep : ∀ (l : List (Address × β)) (m : Std.HashMap Address γ), (∀ x ∈ l, (a == x.1) = false) →
      (l.foldl (fun m x => m.insert x.1 (g x.2)) m).get? a = m.get? a := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons x l ih =>
      intro m hl
      rw [List.foldl_cons, ih _ fun y hy => hl y (List.mem_cons_of_mem _ hy),
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, BEq.comm, hl x List.mem_cons_self]
      rfl
  intro l
  induction l with
  | nil => intro _ _ h; cases h
  | cons x l ih =>
    intro m hd hm
    rw [List.pairwise_cons] at hd
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with e | hm
    · subst e
      rw [keep _ _ hd.1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
    · exact ih _ hd.2 hm

/-- **The environment stores the driver's records**, each as its own buffer. -/
theorem assembleEnv_consts (acc : DriverAcc) {a : Address} {b : ByteArray}
    (h : acc.cenv.constants.get? a = some b) :
    (assembleEnv acc).1.consts.get? a = some { buf := b, len := b.size } := by
  show (acc.cenv.constants.fold (init := {}) fun (m : Std.HashMap Address Ixon.LazyConstant) a bytes =>
    m.insert a ({ buf := bytes, len := bytes.size } : Ixon.LazyConstant)).get? a = _
  rw [Std.HashMap.fold_eq_foldl_toList]
  refine foldl_insert_get (fun bytes => ({ buf := bytes, len := bytes.size } : Ixon.LazyConstant))
    _ _ Std.HashMap.distinct_keys_toList ?_
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
  exact h

/-- **The driver's final state**: a fold that returns ran its waves from an
initial state whose resolution map is empty, and returns the environment
assembled from the state the waves reached, with that state's resolution
map, aux map and stored records. -/
theorem compileEnvFold_final {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState),
      cenv₀.nameToAddr = {} ∧
      foldWavesSeq blocks sched (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched) = .ok st ∧
      ixe = (assembleEnv st.acc).1 ∧
      cenv.nameToAddr = st.acc.cenv.nameToAddr ∧ cenv.auxNameToAddr = st.acc.cenv.auxNameToAddr ∧
      cenv.constants = st.acc.cenv.constants := by
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
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨_, _, st, rfl, hr, rfl, rfl, rfl, rfl⟩

/-- **The driver's final resolution map has provenance**: every entry is an
aux name's, or a primary claim of a condensation block compiled during the
fold, against a state the fold reached, whose record's bytes the assembled
environment stores at its address. -/
theorem compileEnvFold_provenance {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ init : DriverAcc, ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
      cenv.auxNameToAddr.contains n = true ∨
        ∃ b, Compiled blocks init n a b ∧ ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨cenv₀, sched, st, h₀, hst, rfl, hmap, haux, -⟩ := compileEnvFold_final h
  refine ⟨(FoldState.init cenv₀ blocks sched).acc, fun n a hn => ?_⟩
  rw [hmap] at hn
  rw [haux]
  rcases reach_provenance (provenance_of_empty ((init_nameToAddr _ _ _).trans h₀))
    (foldWavesSeq_reach _ _ _ hst Reach.init) n a hn with haux | ⟨b, hc, hb⟩
  · exact .inl haux
  · exact .inr ⟨b, hc, assembleEnv_consts _ hb⟩

/-- **`compileUnchecked`'s resolution map is the driver's final one**: a
`compileUnchecked` that returns ran the fold on the ground part's
condensation, and returns the resolution map of the fold's final compile
environment, with its aux map. -/
theorem compileUnchecked_fold {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {resolved aux : Std.HashMap ExactName Address}
    (h : compileUnchecked env = .ok (ixe, failures, resolved, aux)) :
    ∃ (bytes : Nat) (cenv : CompileEnv),
      compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) = .ok (ixe, bytes, cenv) ∧
      resolved = cenv.nameToAddr ∧ aux = cenv.auxNameToAddr := by
  unfold compileUnchecked at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      obtain ⟨ixe', bytes, cenv⟩ := r
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl, rfl⟩ := h
      exact ⟨bytes, cenv, hr, rfl, rfl⟩

/-- **Where `compileUnchecked`'s resolution map comes from**: every entry is
an aux name's (in the fold's final aux map, which `compileUnchecked` returns),
or a primary claim of a condensation block compiled during the fold, whose
record's bytes the environment stores at its address. -/
theorem compileUnchecked_provenance {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {resolved aux : Std.HashMap ExactName Address}
    (h : compileUnchecked env = .ok (ixe, failures, resolved, aux)) :
    ∃ (bytes : Nat) (cenv : CompileEnv) (init : DriverAcc),
      compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) = .ok (ixe, bytes, cenv) ∧
      resolved = cenv.nameToAddr ∧ aux = cenv.auxNameToAddr ∧
      ∀ (n : ExactName) (a : Address), resolved.get? n = some a →
        aux.contains n = true ∨
          ∃ b, Compiled (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) init n a b ∧
            ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨bytes, cenv, hf, rfl, rfl⟩ := compileUnchecked_fold h
  obtain ⟨init, hp⟩ := compileEnvFold_provenance hf
  exact ⟨bytes, cenv, init, hf, rfl, rfl, hp⟩


/-! ## The block compile behind a claim -/

/-- **A compiled outcome is its block's compile**: `auxBlockOutcome` returns
`.compiled` only from `runBlock` on the block itself (a block whose key does
not resolve yet). -/
theorem auxBlockOutcome_compiled {cenv : CompileEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {r : BlockResult} {c : BlockState} {p : Ix.Compile.Pass.Published}
    (h : auxBlockOutcome cenv lo all = .compiled r c p) :
    ∃ layout, runBlock cenv all lo = .ok (r, c, layout, p) := by
  unfold auxBlockOutcome at h
  simp only [Id.run] at h
  split at h
  · refine absurd h (loop_bind_set _ _ _ _ (fun _ => True) (fun o : AuxBlockOutcome => o ≠ .compiled r c p) trivial
      (fun _ _ _ => trivial) fun L _ => ?_)
    intro h'
    repeat (first | (split at h') | cases h')
  · split at h
    · cases h
    · rename_i x result cache layout published hr
      cases h
      exact ⟨layout, hr⟩

/-- **The compile behind a claim**: a `Compiled` claim is one of the
`claimWrites` of a condensation block's own compile (`runBlock`, against a
state the fold reached), or of the cross-SCC subset of a promoted block. -/
theorem compiled_cases {blocks : Ix.CondensedBlocks} {init : DriverAcc} {n : Ix.Name} {a : Address}
    {b : ByteArray} (h : Compiled blocks init n a b) :
    ∃ snap rep all, Reach blocks init snap ∧ blocks.blocks.get? rep = some all ∧
      ((∃ r c p layout, runBlock snap.cenv all (blockKey rep all) = .ok (r, c, layout, p) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r) ∨
        ∃ clo r c p cn cf im na nf,
          auxBlockOutcome snap.cenv (blockKey rep all) all = .promoted (some (clo, r, c, p)) cn cf im na nf ∧
          (n, a, b) ∈ claimWrites clo r) := by
  obtain ⟨snap, rep, all, hsnap, hall, hclaim⟩ := h
  refine ⟨snap, rep, all, hsnap, hall, ?_⟩
  generalize ho : auxBlockOutcome snap.cenv (blockKey rep all) all = o at hclaim
  cases o with
  | compiled r c p =>
    obtain ⟨layout, hr⟩ := auxBlockOutcome_compiled ho
    exact .inl ⟨r, c, p, layout, hr, hclaim⟩
  | promoted cs cn cf im na nf =>
    cases cs with
    | none => exact hclaim.elim
    | some x =>
      obtain ⟨clo, r, c, p⟩ := x
      exact .inr ⟨clo, r, c, p, cn, cf, im, na, nf, rfl, hclaim⟩
  | failed msg => exact hclaim.elim

end Ix.Cert.Resolution
