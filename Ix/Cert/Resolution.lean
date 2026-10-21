import Ix.Cert.Schedule
import Ix.Cert.PassHooks
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
  computed against a reached state (the wave's snapshot) that it follows
  (`Mono`); `foldWavesSeq_reach` (with `foldWaveWith_ready`: a wave's ready
  blocks are condensation blocks under their keys);
* `Mono`: from one state to a later one, a recorded failure (`ungrounded`)
  stays recorded, and a Pass 3 head or an extra name stays one or is recorded
  as a failure (only `failAuxPromotion` removes them, recording each);
  `compileUnchecked_ungrounded`: a failure recorded at the end is reported;
* `Step`: how one driver operation moves the resolution map (and, by `Mono`,
  the failures, heads and extra names); it composes (`Step.trans`), and every
  operation of `applyAuxBlockOutcome` is one;
* `Provenance` and `reach_provenance`: on every reached state, every entry of
  the resolution map is an aux name's or `Compiled`;
* `compileEnvFold_final`, `compileEnvFold_provenance`, `compileUnchecked_fold`
  and `compileUnchecked_provenance`: the fold starts from an empty map, and
  `compileUnchecked`'s resolution map is the final state's, so every entry of
  it is an aux name's (in the final aux map) or `Compiled`;
* `compiled_runBlock` (with `auxBlockOutcome_cross`): a `Compiled` claim is a
  claim of `runBlock` on a subset of a condensation block's members, under a
  key, against a reached state that the final one follows (`Mono`);
  `reach_p3BlockRefs`: the block references never change during the fold;
* `HookFree` and `hookFree_compiled`: where Pass 3's hooks are identities at
  that compile, the claim is one of the block compile's (`BlockCompiled`,
  via `Ix.Cert.PassHooks.runBlockWithAux_records`);
* `compileReport_claim` (B9b): a resolved name outside the aux map is
  published at its address, its record's bytes are stored there, and it is a
  claim of its block's compile, the block compile's under `HookFree`. -/

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

/-! ## How an operation moves the resolution map -/

open Ix.Compile.ExactKey (ExactName)

/-- **Failures stay, and a head or an extra name leaves only as a failure**,
from `c` to `c'`: a recorded failure (`ungrounded`) stays recorded, and a
Pass 3 head (`p3Heads`) or an extra name (`auxGenExtraNames`) stays one or
is recorded as a failure. Only a withdrawal (`failAuxPromotion`) removes
heads and extra names, each while recording it as a failure. -/
def Mono (c c' : CompileEnv) : Prop :=
  (∀ x : Ix.Name, c.ungrounded.contains x = true → c'.ungrounded.contains x = true) ∧
  (∀ x : ExactName, c.p3Heads.contains x = true →
    c'.p3Heads.contains x = true ∨ c'.ungrounded.contains x = true) ∧
  (∀ x : Ix.Name, c.auxGenExtraNames.contains x = true →
    c'.auxGenExtraNames.contains x = true ∨ c'.ungrounded.contains x = true)

theorem Mono.refl (c : CompileEnv) : Mono c c :=
  ⟨fun _ h => h, fun _ h => .inl h, fun _ h => .inl h⟩

theorem Mono.trans {c₁ c₂ c₃ : CompileEnv} (h₁ : Mono c₁ c₂) (h₂ : Mono c₂ c₃) : Mono c₁ c₃ := by
  refine ⟨fun x h => h₂.1 x (h₁.1 x h), fun x h => ?_, fun x h => ?_⟩
  · rcases h₁.2.1 x h with h | h
    · exact h₂.2.1 x h
    · exact .inr (h₂.1 x h)
  · rcases h₁.2.2 x h with h | h
    · exact h₂.2.2 x h
    · exact .inr (h₂.1 x h)

/-- An operation that only grows the failures, the heads and the extra names. -/
theorem Mono.grow {c c' : CompileEnv}
    (hu : ∀ x : Ix.Name, c.ungrounded.contains x = true → c'.ungrounded.contains x = true)
    (hh : ∀ x : ExactName, c.p3Heads.contains x = true → c'.p3Heads.contains x = true)
    (he : ∀ x : Ix.Name, c.auxGenExtraNames.contains x = true → c'.auxGenExtraNames.contains x = true) :
    Mono c c' :=
  ⟨hu, fun x h => .inl (hh x h), fun x h => .inl (he x h)⟩

/-- An operation that leaves the failures, the heads and the extra names. -/
theorem Mono.of_eq {c c' : CompileEnv} (hu : c'.ungrounded = c.ungrounded) (hh : c'.p3Heads = c.p3Heads)
    (he : c'.auxGenExtraNames = c.auxGenExtraNames) : Mono c c' :=
  Mono.grow (fun _ h => by rw [hu]; exact h) (fun _ h => by rw [hh]; exact h) (fun _ h => by rw [he]; exact h)

/-- Recording a failure. -/
theorem Mono.fail {c c' : CompileEnv} {m : Ix.Name} {msg : String}
    (hu : c'.ungrounded = c.ungrounded.insert m msg) (hh : c'.p3Heads = c.p3Heads := by rfl)
    (he : c'.auxGenExtraNames = c.auxGenExtraNames := by rfl) : Mono c c' :=
  Mono.grow (fun _ h => by rw [hu, Std.HashMap.contains_insert, h, Bool.or_true])
    (fun _ h => by rw [hh]; exact h) (fun _ h => by rw [he]; exact h)

/-- Adding an extra name. -/
theorem Mono.extra {c c' : CompileEnv} {m : Ix.Name}
    (he : c'.auxGenExtraNames = c.auxGenExtraNames.insert m) (hu : c'.ungrounded = c.ungrounded := by rfl)
    (hh : c'.p3Heads = c.p3Heads := by rfl) : Mono c c' :=
  Mono.grow (fun _ h => by rw [hu]; exact h) (fun _ h => by rw [hh]; exact h)
    (fun _ h => by rw [he, Std.HashSet.contains_insert, h, Bool.or_true])

/-- Erasing a head keeps every other head (the keys compared exactly). -/
theorem erase_contains_or {M : Std.HashMap ExactName Ix.Name} {k y : ExactName} (h : M.contains y = true) :
    (M.erase k).contains y = true ∨ k = y := by
  rw [Std.HashMap.contains_erase]
  cases e : (k == y)
  · exact .inl (by rw [h]; rfl)
  · exact .inr (beq_iff_eq.mp e)

/-- Publishing a head keeps every head. -/
theorem insert_contains {M : Std.HashMap ExactName Ix.Name} {k y : ExactName} {v : Ix.Name}
    (h : M.contains y = true) : (M.insert k v).contains y = true := by
  rw [Std.HashMap.contains_insert, h, Bool.or_true]

/-- Withdrawing a name: it leaves the heads and the extra names and is
recorded as a failure. -/
theorem Mono.withdraw {c c' : CompileEnv} {m : Ix.Name} {msg : String}
    (hu : c'.ungrounded = c.ungrounded.insert m msg) (hh : c'.p3Heads = c.p3Heads.erase m)
    (he : c'.auxGenExtraNames = c.auxGenExtraNames.erase m) : Mono c c' := by
  refine ⟨fun _ h => by rw [hu, Std.HashMap.contains_insert, h, Bool.or_true], fun x h => ?_, fun x h => ?_⟩
  · rcases erase_contains_or (k := m) h with h' | same
    · exact .inl ((congrArg (·.contains x) hh).trans h')
    · subst same
      exact .inr ((congrArg (·.contains m) hu).trans Std.HashMap.contains_insert_self)
  · rw [he, Std.HashSet.contains_erase]
    cases e : (m == x)
    · exact .inl (by rw [h]; rfl)
    · exact .inr (by rw [hu, Std.HashMap.contains_insert, e]; rfl)

/-- **One driver operation's effect on the resolution map and the stored
records**, from `c` to `c'`: a stored record stays stored, with the same
bytes, the block references (`p3BlockRefs`) and the input environment (`env`)
stay as they are, and failures, heads and extra names move as `Mono` says;
and every entry of `c'`'s resolution map is one of `c`'s, whose name keeps its
aux address if it had one, or its name has an aux address in `c'`, or it is
one of the operation's own claims (`F`), with the claimed bytes stored at its
address. -/
def Step (c c' : CompileEnv) (F : Ix.Name → Address → ByteArray → Prop) : Prop :=
  ((∀ (a : Address) (b : ByteArray), c.constants.get? a = some b → c'.constants.get? a = some b) ∧
    (c'.p3BlockRefs = c.p3BlockRefs ∧ c'.env = c.env) ∧ Mono c c') ∧
  ∀ (n : ExactName) (a : Address), c'.nameToAddr.get? n = some a →
    (c.nameToAddr.get? n = some a ∧ (c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)) ∨
      c'.auxNameToAddr.contains n = true ∨ ∃ b, F n a b ∧ c'.constants.get? a = some b

theorem Step.refl (c : CompileEnv) (F : Ix.Name → Address → ByteArray → Prop) : Step c c F :=
  ⟨⟨fun _ _ h => h, ⟨rfl, rfl⟩, Mono.refl c⟩, fun _ _ h => .inl ⟨h, id⟩⟩

theorem Step.mono {c c' : CompileEnv} {F G : Ix.Name → Address → ByteArray → Prop} (h : Step c c' F)
    (FG : ∀ n a b, F n a b → G n a b) : Step c c' G := by
  refine ⟨h.1, fun n a hn => ?_⟩
  rcases h.2 n a hn with h | h | ⟨b, hF, hb⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨b, FG n a b hF, hb⟩)

theorem Step.trans {c₁ c₂ c₃ : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} (h₁ : Step c₁ c₂ F)
    (h₂ : Step c₂ c₃ F) : Step c₁ c₃ F := by
  refine ⟨⟨fun a b h => h₂.1.1 a b (h₁.1.1 a b h),
    ⟨h₂.1.2.1.1.trans h₁.1.2.1.1, h₂.1.2.1.2.trans h₁.1.2.1.2⟩, h₁.1.2.2.trans h₂.1.2.2⟩,
    fun n a hn => ?_⟩
  rcases h₂.2 n a hn with ⟨h, keep₂⟩ | h | h
  · rcases h₁.2 n a h with ⟨h, keep₁⟩ | h | ⟨b, hF, hb⟩
    · exact .inl ⟨h, fun k => keep₂ (keep₁ k)⟩
    · exact .inr (.inl (keep₂ h))
    · exact .inr (.inr ⟨b, hF, h₂.1.1 a b hb⟩)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- An operation that leaves the resolution map and the stored records, and
keeps every aux name. -/
theorem Step.keep {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop}
    (h₁ : c'.nameToAddr = c.nameToAddr)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (h₃ : c'.constants = c.constants := by rfl) (h₄ : c'.p3BlockRefs = c.p3BlockRefs := by rfl) (h₆ : c'.env = c.env := by rfl)
    (h₅ : Mono c c' := by exact Mono.of_eq rfl rfl rfl) :
    Step c c' F := by
  refine ⟨⟨fun a b h => by rw [h₃]; exact h, ⟨h₄, h₆⟩, h₅⟩, fun n a hn => ?_⟩
  rw [h₁] at hn
  exact .inl ⟨hn, h₂ n⟩

/-- An operation that erases one name from the resolution map and the aux map. -/
theorem Step.erase {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} {m : ExactName}
    (h₁ : c'.nameToAddr = c.nameToAddr.erase m) (h₂ : c'.auxNameToAddr = c.auxNameToAddr.erase m)
    (h₃ : c'.constants = c.constants := by rfl) (h₄ : c'.p3BlockRefs = c.p3BlockRefs := by rfl) (h₆ : c'.env = c.env := by rfl)
    (h₅ : Mono c c' := by exact Mono.of_eq rfl rfl rfl) :
    Step c c' F := by
  refine ⟨⟨fun a b h => by rw [h₃]; exact h, ⟨h₄, h₆⟩, h₅⟩, fun n a hn => ?_⟩
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
    (h₃ : c'.constants = c.constants := by rfl) (h₄ : c'.p3BlockRefs = c.p3BlockRefs := by rfl) (h₆ : c'.env = c.env := by rfl)
    (h₅ : Mono c c' := by exact Mono.of_eq rfl rfl rfl) :
    Step c c' F := by
  refine ⟨⟨fun a b h => by rw [h₃]; exact h, ⟨h₄, h₆⟩, h₅⟩, fun n a hn => ?_⟩
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
    (h₃ : c'.constants = c.constants.insert k v) (agree : ∀ v₀, c.constants.get? k = some v₀ → v₀ = v)
    (h₄ : c'.p3BlockRefs = c.p3BlockRefs := by rfl) (h₆ : c'.env = c.env := by rfl)
    (h₅ : Mono c c' := by exact Mono.of_eq rfl rfl rfl) : Step c c' F := by
  refine ⟨⟨grow_insert h₃ agree, ⟨h₄, h₆⟩, h₅⟩, fun n a hn => ?_⟩
  rw [h₁] at hn
  exact .inl ⟨hn, h₂ n⟩

/-- Storing a claimed record and claiming it: a write that agrees with what is
stored at its address, and the resolution entry of one of the operation's
claims (`F`) at that address. -/
theorem Step.claim {c c' : CompileEnv} {F : Ix.Name → Address → ByteArray → Prop} {m : ExactName}
    {k : Address} {v : ByteArray} (h₁ : c'.nameToAddr = c.nameToAddr.insert m k)
    (h₂ : ∀ n : ExactName, c.auxNameToAddr.contains n = true → c'.auxNameToAddr.contains n = true)
    (h₃ : c'.constants = c.constants.insert k v) (agree : ∀ v₀, c.constants.get? k = some v₀ → v₀ = v)
    (hF : F m k v) (h₄ : c'.p3BlockRefs = c.p3BlockRefs := by rfl) (h₆ : c'.env = c.env := by rfl)
    (h₅ : Mono c c' := by exact Mono.of_eq rfl rfl rfl) : Step c c' F := by
  have stored : c'.constants.get? k = some v := by
    rw [h₃, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
  refine ⟨⟨grow_insert h₃ agree, ⟨h₄, h₆⟩, h₅⟩, fun n a hn => ?_⟩
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
    exact hs.trans (Step.erase rfl rfl (h₅ := Mono.withdraw rfl rfl rfl))
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

/-- Publishing heads keeps every head. -/
theorem heads_insert_contains {hs : Array (Ix.Name × Ix.Name)} {m : Std.HashMap ExactName Ix.Name}
    {x : ExactName} (h : m.contains x = true) :
    (hs.foldl (fun m (k, v) => m.insert k v) m).contains x = true := by
  rw [← Array.foldl_toList]
  generalize hs.toList = l
  induction l generalizing m with
  | nil => exact h
  | cons y l ih =>
    rw [List.foldl_cons]
    exact ih (by obtain ⟨k, v⟩ := y; exact insert_contains h)

/-- Adding extra names keeps every extra name. -/
theorem extras_insert_contains {s src : Std.HashSet Ix.Name} {x : Ix.Name} (h : s.contains x = true) :
    (src.fold (fun s n => s.insert n) s).contains x = true := by
  rw [Std.HashSet.fold_eq_foldl_toList]
  generalize src.toList = l
  induction l generalizing s with
  | nil => exact h
  | cons y l ih =>
    rw [List.foldl_cons]
    exact ih (by rw [Std.HashSet.contains_insert, h, Bool.or_true])

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
        · exact hL₃.trans (Step.keep rfl (fun _ h => fold_insert_contains h)
              (h₅ := Mono.grow (fun _ h => h) (fun _ h => heads_insert_contains h) (fun _ h => extras_insert_contains h)))
        · intro cls _ s hs
          exact forIn_inv_array (fun c : CompileEnv => Step acc.cenv c F) _ cls (by intro _ _ s hs; exact hs) s hs
        · intro L₄ hL₄
          refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
            (I := fun _ : Array Ix.Name => True) _ _ _ _ trivial (fun _ _ _ _ => trivial) ?_
          intro _ _; exact hL₄
      · refine loop_bind (P := fun d : DriverAcc => Step acc.cenv d.cenv F)
          (I := fun _ : Array Ix.Name => True) _ _ _ _ trivial (fun _ _ _ _ => trivial) ?_
        intro _ _; exact hL₃.trans (Step.keep rfl (fun _ h => fold_insert_contains h)
              (h₅ := Mono.grow (fun _ h => h) (fun _ h => heads_insert_contains h) (fun _ h => extras_insert_contains h)))))

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
        exact hs.trans (Step.keep rfl (fun _ h => h) (h₅ := Mono.fail rfl))
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
      exact hs.trans (Step.keep rfl (fun _ h => h) (h₅ := Mono.fail rfl))
    · intro L hL
      exact hL

/-- A loop over the driver state, then a continuation that returns. -/
theorem loopAccRet {G : Ix.Name → Address → ByteArray → Prop} {c : CompileEnv} {α : Type} (xs : Array α)
    (init : DriverAcc) (f : α → DriverAcc → Id (ForInStep DriverAcc))
    (k : DriverAcc → Id (DriverAcc × Array Ix.Name × Bool)) (hinit : Step c init.cenv G)
    (body : ∀ x ∈ xs, ∀ s, Step c s.cenv G → Step c (f x s).value.cenv G)
    (cont : ∀ L, Step c L.cenv G → Step c (k L).1.cenv G) : Step c (forIn (m := Id) xs init f >>= k).1.cenv G :=
  loop_bind xs init f k (fun d => Step c d.cenv G) (fun r => Step c r.1.cenv G) hinit body cont

/-- A loop body that records a failure, adds an extra name, or changes only
fields `Step` ignores. -/
local macro "keep_body" : tactic => `(tactic| (intro _ _ s hs; first
  | exact hs.trans (Step.keep rfl (fun _ h => h) (h₅ := Mono.fail rfl))
  | exact hs.trans (Step.keep rfl (fun _ h => h) (h₅ := Mono.extra rfl))
  | exact hs.trans (Step.keep rfl fun _ h => h)))

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

/-! ## The states the fold reaches -/

/-- **The driver states the fold reaches from `init`.** A step applies, to a
reached state, the outcome of a condensation block under its key, computed
against a reached state (the wave's snapshot) that it follows: from the
snapshot to the state, failures, heads and extra names moved as `Mono` says. -/
inductive Reach (blocks : Ix.CondensedBlocks) (init : DriverAcc) : DriverAcc → Prop
  | init : Reach blocks init init
  | step {snap acc : DriverAcc} {rep : Ix.Name} {all : Ix.Set Ix.Name} :
      Reach blocks init snap → Reach blocks init acc → Mono snap.cenv acc.cenv →
      blocks.blocks.get? rep = some all →
      Reach blocks init (applyAuxBlockOutcome acc (blockKey rep all) all
        (auxBlockOutcome snap.cenv (blockKey rep all) all)).1

/-- Applying an outcome moves failures, heads and extra names as `Mono` says. -/
theorem applyAuxBlockOutcome_mono (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (o : AuxBlockOutcome) : Mono acc.cenv (applyAuxBlockOutcome acc lo all o).1.cenv :=
  (applyAuxBlockOutcome_step acc lo all o).1.2.2

/-- A wave's sequential apply step reaches a state from reached ones, and
follows its snapshot. -/
theorem applySeq_reach {blocks : Ix.CondensedBlocks} {init snap : DriverAcc} {ready : Ready}
    (hsnap : Reach blocks init snap) (good : GoodReady blocks ready) :
    ∀ acc, Reach blocks init acc → Mono snap.cenv acc.cenv →
      Reach blocks init (applySeq snap.cenv ready acc) ∧ Mono snap.cenv (applySeq snap.cenv ready acc).cenv := by
  intro acc₀ h₀ m₀
  unfold applySeq
  rw [← Array.foldl_toList]
  have : ∀ (l : List (Ix.Name × Ix.Name × Ix.Set Ix.Name)), (∀ x ∈ l, x ∈ ready) →
      ∀ acc, Reach blocks init acc → Mono snap.cenv acc.cenv →
        Reach blocks init (l.foldl (fun acc x =>
          (applyAuxBlockOutcome acc x.1 x.2.2 (auxBlockOutcome snap.cenv x.1 x.2.2)).1) acc) ∧
        Mono snap.cenv (l.foldl (fun acc x =>
          (applyAuxBlockOutcome acc x.1 x.2.2 (auxBlockOutcome snap.cenv x.1 x.2.2)).1) acc).cenv := by
    intro l
    induction l with
    | nil => intro _ acc h m; exact ⟨h, m⟩
    | cons x l ih =>
      intro sub acc h m
      rw [List.foldl_cons]
      refine ih (fun y hy => sub y (List.mem_cons_of_mem _ hy)) _ ?_
        (m.trans (applyAuxBlockOutcome_mono _ _ _ _))
      obtain ⟨hall, hkey⟩ := good x (sub x List.mem_cons_self)
      rw [hkey]
      exact Reach.step hsnap h m hall
  exact this ready.toList (fun x hx => Array.mem_toList_iff.mp hx) acc₀ h₀ m₀

/-- A wave reaches a state from a reached one. -/
theorem foldWaveSeq_reach {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {init : DriverAcc}
    {st st' : FoldState} (h : foldWaveSeq blocks sched st = .ok st') (hst : Reach blocks init st.acc) :
    Reach blocks init st'.acc := by
  obtain ⟨ready, good, hacc⟩ := foldWaveWith_ready applySeq blocks sched st st' h
  rw [hacc]
  exact (applySeq_reach hst good st.acc hst (Mono.refl _)).1

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

/-! ## Where the final resolution map's entries come from -/

/-- **A primary claim of a block compiled during the fold**: `n ↦ a`, with
the claimed record's bytes `b`, is one of the claims (`outcomeClaims`) of a
condensation block's outcome, under its key, computed against a state the
fold reached (`snap`) and applied to a reached state (`pre`) that follows it;
the compile environment `c` follows the state the application made. -/
def Compiled (blocks : Ix.CondensedBlocks) (init : DriverAcc) (c : CompileEnv) (n : Ix.Name)
    (a : Address) (b : ByteArray) : Prop :=
  ∃ (snap pre : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name),
    Reach blocks init snap ∧ Reach blocks init pre ∧ Mono snap.cenv pre.cenv ∧
    blocks.blocks.get? rep = some all ∧
    Mono (applyAuxBlockOutcome pre (blockKey rep all) all
      (auxBlockOutcome snap.cenv (blockKey rep all) all)).1.cenv c ∧
    outcomeClaims (blockKey rep all) (auxBlockOutcome snap.cenv (blockKey rep all) all) n a b

theorem Compiled.mono {blocks : Ix.CondensedBlocks} {init : DriverAcc} {c c' : CompileEnv} {n : Ix.Name}
    {a : Address} {b : ByteArray} (h : Compiled blocks init c n a b) (m : Mono c c') :
    Compiled blocks init c' n a b := by
  obtain ⟨snap, pre, rep, all, hsnap, hpre, hm, hall, hpost, hclaim⟩ := h
  exact ⟨snap, pre, rep, all, hsnap, hpre, hm, hall, hpost.trans m, hclaim⟩

/-- Every entry of a driver state's resolution map is an aux name's, or
`Compiled` with the claimed record's bytes stored at its address. -/
def Provenance (blocks : Ix.CondensedBlocks) (init acc : DriverAcc) : Prop :=
  ∀ (n : ExactName) (a : Address), acc.cenv.nameToAddr.get? n = some a →
    acc.cenv.auxNameToAddr.contains n = true ∨
      ∃ b, Compiled blocks init acc.cenv n a b ∧ acc.cenv.constants.get? a = some b

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
  | @step snap acc rep all hsnap hacc hm hall _ ih =>
    intro n a hn
    have st := applyAuxBlockOutcome_step acc (blockKey rep all) all
      (auxBlockOutcome snap.cenv (blockKey rep all) all)
    rcases st.2 n a hn with ⟨hold, keep⟩ | haux | ⟨b, hclaim, hb⟩
    · rcases ih n a hold with haux | ⟨b, hc, hb⟩
      · exact .inl (keep haux)
      · exact .inr ⟨b, hc.mono st.1.2.2, st.1.1 a b hb⟩
    · exact .inl haux
    · exact .inr ⟨b, ⟨snap, acc, rep, all, hsnap, hacc, hm, hall, Mono.refl _, hclaim⟩, hb⟩

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
      (FoldState.init cenv₀ blocks sched).acc.cenv.env = { consts := {}, fallback? := some env.get? } ∧
      foldWavesSeq blocks sched (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched) = .ok st ∧
      ixe = (assembleEnv st.acc).1 ∧
      cenv.nameToAddr = st.acc.cenv.nameToAddr ∧ cenv.auxNameToAddr = st.acc.cenv.auxNameToAddr ∧
      cenv.constants = st.acc.cenv.constants ∧ Mono st.acc.cenv cenv := by
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
    exact ⟨_, _, st, rfl, rfl, hr, rfl, rfl, rfl, rfl, Mono.of_eq rfl rfl rfl⟩

/-- **The driver's final resolution map has provenance**: every entry is an
aux name's, or a primary claim of a condensation block compiled during the
fold, against a state the fold reached, whose record's bytes the assembled
environment stores at its address. -/
theorem compileEnvFold_provenance {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule),
      (FoldState.init cenv₀ blocks sched).acc.cenv.env = { consts := {}, fallback? := some env.get? } ∧
      ∀ (n : ExactName) (a : Address),
        cenv.nameToAddr.get? n = some a → cenv.auxNameToAddr.contains n = true ∨
          ∃ b, Compiled blocks (FoldState.init cenv₀ blocks sched).acc cenv n a b ∧
            ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨cenv₀, sched, st, h₀, henv, hst, rfl, hmap, haux, -, hm⟩ := compileEnvFold_final h
  refine ⟨cenv₀, sched, henv, fun n a hn => ?_⟩
  rw [hmap] at hn
  rw [haux]
  rcases reach_provenance (provenance_of_empty ((init_nameToAddr _ _ _).trans h₀))
    (foldWavesSeq_reach _ _ _ hst Reach.init) n a hn with haux | ⟨b, hc, hb⟩
  · exact .inl haux
  · exact .inr ⟨b, hc.mono hm, assembleEnv_consts _ hb⟩

/-- **`compileUnchecked` returns the driver's final environment**: a
`compileUnchecked` that returns ran the fold on the ground part's
condensation, and returns the fold's final compile environment. -/
theorem compileUnchecked_fold {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {cenv : CompileEnv} (h : compileUnchecked env = .ok (ixe, failures, cenv)) :
    ∃ bytes : Nat, compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) = .ok (ixe, bytes, cenv) := by
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
      exact ⟨bytes, hr⟩

/-- **A failure recorded in the driver's final environment is reported**:
`compileUnchecked`'s block failures are the final environment's `ungrounded`. -/
theorem compileUnchecked_ungrounded {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {cenv : CompileEnv} (h : compileUnchecked env = .ok (ixe, failures, cenv)) {x : Ix.Name}
    (hx : cenv.ungrounded.contains x = true) : failures.failed x = true := by
  unfold compileUnchecked at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      obtain ⟨ixe', bytes, cenv'⟩ := r
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      simp only [Failures.failed, hx, Bool.or_true]

/-- **Where the resolution map of `compileUnchecked`'s environment comes
from**: every entry is an aux name's (in the same environment's aux map),
or a primary claim of a condensation block compiled during the fold, whose
record's bytes the environment stores at its address. -/
theorem compileUnchecked_provenance {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {cenv : CompileEnv} (h : compileUnchecked env = .ok (ixe, failures, cenv)) :
    ∃ (bytes : Nat) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) = .ok (ixe, bytes, cenv) ∧
      (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched).acc.cenv.env =
        { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) } ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = true ∨
          ∃ b, Compiled (Ix.CondenseM.run (groundSplit { consts := env.consts }).1)
              (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched).acc
              cenv n a b ∧
            ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨bytes, hf⟩ := compileUnchecked_fold h
  obtain ⟨cenv₀, sched, henv, hp⟩ := compileEnvFold_provenance hf
  exact ⟨bytes, cenv₀, sched, hf, henv, hp⟩


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
state the fold reached, which `fin` follows), or of the cross-SCC subset of a
promoted block. -/
theorem compiled_cases {blocks : Ix.CondensedBlocks} {init : DriverAcc} {fin : CompileEnv} {n : Ix.Name}
    {a : Address} {b : ByteArray} (h : Compiled blocks init fin n a b) :
    ∃ snap rep all, Reach blocks init snap ∧ blocks.blocks.get? rep = some all ∧ Mono snap.cenv fin ∧
      ((∃ r c p layout, runBlock snap.cenv all (blockKey rep all) = .ok (r, c, layout, p) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r) ∨
        ∃ clo r c p cn cf im na nf,
          auxBlockOutcome snap.cenv (blockKey rep all) all = .promoted (some (clo, r, c, p)) cn cf im na nf ∧
          (n, a, b) ∈ claimWrites clo r) := by
  obtain ⟨snap, pre, rep, all, hsnap, -, hm, hall, hpost, hclaim⟩ := h
  refine ⟨snap, rep, all, hsnap, hall, hm.trans ((applyAuxBlockOutcome_mono _ _ _ _).trans hpost), ?_⟩
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


/-! ## The cross-SCC subset's compile -/

/-- `loop_bind_set`, with each step on a member of the set. -/
theorem loop_bind_mem {α σ β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (xs : Std.HashSet α) (init : σ)
    (f : α → σ → Id (ForInStep σ)) (k : σ → Id β) (I : σ → Prop) (P : β → Prop)
    (hinit : I init) (body : ∀ x, xs.contains x = true → ∀ s, I s → I (f x s).value)
    (cont : ∀ L, I L → P (k L)) :
    P (forIn (m := Id) xs init f >>= k) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine cont _ (forIn_inv_list I f xs.toList (fun x hx => body x ?_) init hinit)
  rw [← Std.HashSet.contains_toList]
  exact List.contains_iff_exists_mem_beq.mpr ⟨x, hx, BEq.rfl⟩

/-- A set built from an array's names holds only names of a set that holds
each of them. -/
theorem foldl_insert_sub {L : Array Ix.Name} {all : Ix.Set Ix.Name}
    (hL : ∀ x ∈ L, all.contains x = true) :
    ∀ x, (L.foldl (fun s n => s.insert n) ({} : Ix.Set Ix.Name)).contains x = true →
      all.contains x = true := by
  rw [← Array.foldl_toList]
  suffices key : ∀ (l : List Ix.Name) (s : Ix.Set Ix.Name), (∀ x ∈ l, all.contains x = true) →
      (∀ x, s.contains x = true → all.contains x = true) →
      ∀ x, (l.foldl (fun s n => s.insert n) s).contains x = true → all.contains x = true from
    key L.toList {} (fun x hx => hL x (Array.mem_toList_iff.mp hx)) (fun x h => by simp at h)
  intro l
  induction l with
  | nil => intro s _ hs; exact hs
  | cons y l ih =>
    intro s hl hs
    rw [List.foldl_cons]
    refine ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) fun x hx => ?_
    rw [Std.HashSet.contains_insert] at hx
    rcases Bool.or_eq_true_iff.mp hx with h | h
    · rw [← Std.HashSet.contains_congr h]; exact hl y List.mem_cons_self
    · exact hs x h

/-- **A promoted block's cross-SCC subset is `runBlock`'s compile** of a
subset of the block's members, under the subset's own key. -/
theorem auxBlockOutcome_cross {cenv : CompileEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {clo : Ix.Name} {r : BlockResult} {c : BlockState} {p : Ix.Compile.Pass.Published}
    {cn : Array Ix.Name} {cf : Option (Array Ix.Name × String)} {im : Option String}
    {na : Option (BlockResult × BlockState)} {nf : Option String}
    (h : auxBlockOutcome cenv lo all = .promoted (some (clo, r, c, p)) cn cf im na nf) :
    ∃ (A : Ix.Set Ix.Name) (layout : Option Ixon.AuxLayout), (∀ x, A.contains x = true → all.contains x = true) ∧
      runBlock cenv A clo = .ok (r, c, layout, p) := by
  unfold auxBlockOutcome at h
  simp only [Id.run] at h
  split at h
  · revert h
    refine loop_bind_mem _ _ _ _ (fun L : Array Ix.Name => ∀ x ∈ L, all.contains x = true)
      (fun o : AuxBlockOutcome => o = .promoted (some (clo, r, c, p)) cn cf im na nf →
        ∃ (A : Ix.Set Ix.Name) (layout : Option Ixon.AuxLayout), (∀ x, A.contains x = true → all.contains x = true) ∧
          runBlock cenv A clo = .ok (r, c, layout, p)) (fun _ h => by simp at h) ?_ ?_
    · intro x hx s hs
      split
      · exact hs
      · split
        · exact hs
        · intro y hy
          rcases Array.mem_push.mp hy with hy | hy
          · exact hs y hy
          · exact hy ▸ hx
    · intro L hL h'
      repeat' (first | (focus (cases h'; done)) | split at h')
      all_goals (cases h'; exact ⟨_, _, foldl_insert_sub hL, ‹_›⟩)
  · split at h <;> cases h

/-! ## Where Pass 3's hooks are identities -/

/-- Off an image block, `runBlock` is `runBlockWithAux`. -/
theorem runBlock_of_not_image {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name}
    (h : Ix.Compile.Pass.isImageBlock cenv all = false) :
    runBlock cenv all lo = runBlockWithAux cenv all lo := by
  simp [runBlock, h]

/-- Two results with the same records make the same primary claims. -/
theorem claimWrites_records {k : Ix.Name} {r r' : BlockResult}
    (h : Ix.Cert.PassHooks.recordsOf r = Ix.Cert.PassHooks.recordsOf r') :
    claimWrites k r = claimWrites k r' := by
  unfold Ix.Cert.PassHooks.recordsOf at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, hbytes, haddr, hproj⟩ := h
  have e₁ : r.projections.isEmpty = r'.projections.isEmpty := by
    have hs : r.projections.size = r'.projections.size := by simpa using congrArg Array.size hproj
    unfold Array.isEmpty
    rw [hs]
  have e₂ : r.projections.map (fun x : Ix.Name × Ixon.Constant × Ixon.ConstantMeta =>
        (x.1, Address.admissionHash (Ixon.ser x.2.1), Ixon.ser x.2.1)) =
      r'.projections.map (fun x : Ix.Name × Ixon.Constant × Ixon.ConstantMeta =>
        (x.1, Address.admissionHash (Ixon.ser x.2.1), Ixon.ser x.2.1)) := by
    have := congrArg (Array.map fun q : Ix.Name × Ixon.Constant =>
      (q.1, Address.admissionHash (Ixon.ser q.2), Ixon.ser q.2)) hproj
    simpa [Array.map_map, Function.comp_def] using this
  unfold claimWrites
  rw [e₁, hbytes, haddr]
  split
  · rfl
  · exact e₂

/-- **Pass 3's hooks are identities at a compile** of the members `A` under
the key `k`: hook 2 returns the compile environment as it is and publishes
nothing, `A` is not an image block, and the clique step returns the compile
environment as it is, the empty block state and nothing published
(`Ix.Cert.PassHooks.cliqueStep_inert` gives it from `cliqueInert`). -/
def HookFree (cenv : CompileEnv) (A : Ix.Set Ix.Name) (k : Ix.Name) : Prop :=
  Ix.Compile.Pass.prepareBlock cenv A k = .ok (cenv, {}) ∧ Ix.Compile.Pass.isImageBlock cenv A = false ∧
    Ix.Compile.Pass.cliqueStep cenv A k = .ok (cenv, {}, {})

/-- **Where the hooks are identities, a block's claims are the block
compile's**: the lone constant's `compileConstantInfo`, or `sortConsts` then
`compileMutualBlock` over the members, run from the empty block state
(`Ix.Cert.PassHooks.runBlockWithAux_records`). -/
theorem hookFree_claims {cenv : CompileEnv} {A : Ix.Set Ix.Name} {k : Ix.Name} {r : BlockResult}
    {c : BlockState} {layout : Option Ixon.AuxLayout} {p : Ix.Compile.Pass.Published}
    (hf : HookFree cenv A k) (h : runBlock cenv A k = .ok (r, c, layout, p)) :
    ∃ const, cenv.env.get? k = some const ∧
      ((∃ (r' : BlockResult) (s₂ : BlockState), Ix.CompileCert.rawRun (compileConstantInfo const)
          (cenv, { all := A, current := k, mutCtx := default, univCtx := [] }) {} = (.ok r', s₂) ∧
          claimWrites k r = claimWrites k r') ∨
        ∃ (cs : Array Ix.MutConst) (out : BlockResult) (s₄ : BlockState),
          Ix.CompileCert.rawRun (sortConsts cs.toList >>= fun sorted =>
              compileMutualBlock (orderRecursorFamily sorted))
            (cenv, { all := A, current := k, mutCtx := default, univCtx := [] }) {} = (.ok out, s₄) ∧
          claimWrites k r = claimWrites k out) := by
  rw [runBlock_of_not_image hf.2.1] at h
  obtain ⟨const, found, rest⟩ := Ix.Cert.PassHooks.runBlockWithAux_records hf.2.2 hf.1 h
  refine ⟨const, found, ?_⟩
  rcases rest with ⟨r', s₂, run, same⟩ | ⟨cs, out, s₄, run, same⟩
  · exact .inl ⟨r', s₂, run, claimWrites_records same⟩
  · exact .inr ⟨cs, out, s₄, run, claimWrites_records same⟩

/-- **`(n, a, b)` is a primary claim of the block compile** of the members
`A` under the key `k`, run from the empty block state in `cenv`: the lone
constant's `compileConstantInfo`, or `sortConsts` then `compileMutualBlock`
over the members (the form the reading theorems, N-READS, take). -/
def BlockCompiled (cenv : CompileEnv) (A : Ix.Set Ix.Name) (k n : Ix.Name) (a : Address)
    (b : ByteArray) : Prop :=
  ∃ const, cenv.env.get? k = some const ∧
    ((∃ (r : BlockResult) (s : BlockState), Ix.CompileCert.rawRun (compileConstantInfo const)
        (cenv, { all := A, current := k, mutCtx := default, univCtx := [] }) {} = (.ok r, s) ∧
        (n, a, b) ∈ claimWrites k r) ∨
      ∃ (cs : Array Ix.MutConst) (out : BlockResult) (s : BlockState),
        Ix.CompileCert.rawRun (sortConsts cs.toList >>= fun sorted =>
            compileMutualBlock (orderRecursorFamily sorted))
          (cenv, { all := A, current := k, mutCtx := default, univCtx := [] }) {} = (.ok out, s) ∧
        (n, a, b) ∈ claimWrites k out)

/-- A claim of a compile whose hooks are identities is a claim of the block
compile. -/
theorem hookFree_compiled {cenv : CompileEnv} {A : Ix.Set Ix.Name} {k n : Ix.Name} {a : Address}
    {b : ByteArray} {r : BlockResult} {c : BlockState} {layout : Option Ixon.AuxLayout}
    {p : Ix.Compile.Pass.Published} (hf : HookFree cenv A k) (h : runBlock cenv A k = .ok (r, c, layout, p))
    (hc : (n, a, b) ∈ claimWrites k r) : BlockCompiled cenv A k n a b := by
  obtain ⟨const, found, rest⟩ := hookFree_claims hf h
  refine ⟨const, found, ?_⟩
  rcases rest with ⟨r', s₂, run, same⟩ | ⟨cs, out, s₄, run, same⟩
  · exact .inl ⟨r', s₂, run, by rw [← same]; exact hc⟩
  · exact .inr ⟨cs, out, s₄, run, by rw [← same]; exact hc⟩

/-- **The compile behind a claim, under its own key**: a `Compiled` claim is
one of the `claimWrites` of `runBlock` on a subset `A` of a condensation
block's members (all of them, or a promoted block's cross-SCC subset), under
a key `k`, against a state the fold reached, which `fin` follows. -/
theorem compiled_runBlock {blocks : Ix.CondensedBlocks} {init : DriverAcc} {fin : CompileEnv} {n : Ix.Name}
    {a : Address} {b : ByteArray} (h : Compiled blocks init fin n a b) :
    ∃ (snap : DriverAcc) (rep : Ix.Name) (all A : Ix.Set Ix.Name) (k : Ix.Name) (r : BlockResult)
      (c : BlockState) (layout : Option Ixon.AuxLayout) (p : Ix.Compile.Pass.Published),
      Reach blocks init snap ∧ blocks.blocks.get? rep = some all ∧ Mono snap.cenv fin ∧
      (∀ x, A.contains x = true → all.contains x = true) ∧
      runBlock snap.cenv A k = .ok (r, c, layout, p) ∧ (n, a, b) ∈ claimWrites k r := by
  obtain ⟨snap, rep, all, hsnap, hall, hm, rest⟩ := compiled_cases h
  rcases rest with ⟨r, c, p, layout, hr, hclaim⟩ | ⟨clo, r, c, p, cn, cf, im, na, nf, ho, hclaim⟩
  · exact ⟨snap, rep, all, all, _, r, c, layout, p, hsnap, hall, hm, fun _ h => h, hr, hclaim⟩
  · obtain ⟨A, layout, sub, hr⟩ := auxBlockOutcome_cross ho
    exact ⟨snap, rep, all, A, clo, r, c, layout, p, hsnap, hall, hm, sub, hr, hclaim⟩

/-- **The block references never change during the fold**: every reached
state has its initial state's (`FoldState.init` sets them). -/
theorem reach_p3BlockRefs {blocks : Ix.CondensedBlocks} {init acc : DriverAcc}
    (h : Reach blocks init acc) : acc.cenv.p3BlockRefs = init.cenv.p3BlockRefs := by
  induction h with
  | init => rfl
  | step _ _ _ _ _ ih => exact (applyAuxBlockOutcome_step _ _ _ _).1.2.1.1.trans ih

/-- **The input environment never changes during the fold**: every reached
state has its initial state's. -/
theorem reach_env {blocks : Ix.CondensedBlocks} {init acc : DriverAcc}
    (h : Reach blocks init acc) : acc.cenv.env = init.cenv.env := by
  induction h with
  | init => rfl
  | step _ _ _ _ _ ih => exact (applyAuxBlockOutcome_step _ _ _ _).1.2.1.2.trans ih

/-! ## Block keys -/

/-- A canonical key of a nonempty array is one of its names. -/
theorem canonicalKey_mem {dflt : Ix.Name} {names : Array Ix.Name} (h : names ≠ #[]) :
    canonicalKey dflt names ∈ names := by
  unfold canonicalKey
  have h0 : names[0]?.getD dflt ∈ names := by
    obtain ⟨x, xs, hx⟩ : ∃ x xs, names.toList = x :: xs := by
      cases hl : names.toList with
      | nil => exact absurd (Array.toList_eq_nil_iff.mp hl) h
      | cons x xs => exact ⟨x, xs, rfl⟩
    have : names[0]? = some x := by
      rw [← Array.getElem?_toList, hx]; rfl
    rw [this]
    exact Array.mem_toList_iff.mp (by rw [hx]; exact List.mem_cons_self)
  rw [← Array.foldl_toList]
  suffices key : ∀ (l : List Ix.Name) (k : Ix.Name), (∀ x ∈ l, x ∈ names) → k ∈ names →
      l.foldl (fun k n => if aliasPrecedes n k then n else k) k ∈ names from
    key _ _ (fun x hx => Array.mem_toList_iff.mp hx) h0
  intro l
  induction l with
  | nil => intro k _ hk; exact hk
  | cons y l ih =>
    intro k hl hk
    rw [List.foldl_cons]
    refine ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_
    split
    · exact hl y List.mem_cons_self
    · exact hk

/-- The key of a nonempty block is one of its members. -/
theorem blockKey_mem {lo : Ix.Name} {all : Ix.Set Ix.Name} (h : all.isEmpty = false) :
    all.contains (blockKey lo all) = true := by
  have ne : all.toArray ≠ #[] := by
    intro e
    have := congrArg Array.size e
    rw [Std.HashSet.size_toArray] at this
    rw [Std.HashSet.isEmpty_eq_size_eq_zero] at h
    simp [this] at h
  have hm := canonicalKey_mem (dflt := lo) ne
  rw [← Std.HashSet.contains_toArray]
  exact Array.contains_iff_exists_mem_beq.mpr ⟨_, hm, BEq.rfl⟩

/-- The key of a nonempty block does not depend on its default. -/
theorem blockKey_indep {a b : Ix.Name} {all : Ix.Set Ix.Name} (h : all.isEmpty = false) :
    blockKey a all = blockKey b all := by
  have ne : 0 < all.toArray.size := by
    rw [Std.HashSet.size_toArray]
    rw [Std.HashSet.isEmpty_eq_size_eq_zero] at h
    simp only [beq_eq_false_iff_ne] at h
    omega
  unfold blockKey canonicalKey
  rw [Array.getElem?_eq_getElem ne]
  rfl

/-- `FoldState.init`'s loop state: the unmet counts, the candidates, the
block references. -/
abbrev InitState := Std.HashMap Ix.Name Nat × Array Ix.Name × Std.HashMap Ix.Name (Ix.Set Ix.Name)

/-- `FoldState.init`'s loop, as far as the block references go: each step
continues, and installs a block's references under its key when it has some. -/
def InitStep (blocks : Ix.CondensedBlocks) (f : Ix.Name × Ix.Set Ix.Name → InitState → Id (ForInStep InitState)) :
    Prop :=
  ∀ x s, ∃ u v, f x s = .yield (u, v, match blocks.blockRefs.get? x.1 with
    | some refs => s.2.2.insert (blockKey x.1 x.2) refs
    | none => s.2.2)

theorem initStep_refs {blocks : Ix.CondensedBlocks}
    {f : Ix.Name × Ix.Set Ix.Name → InitState → Id (ForInStep InitState)} (hf : InitStep blocks f)
    (P : Ix.Name → Ix.Set Ix.Name → Prop)
    (hP : ∀ x ∈ blocks.blocks.toList, ∀ refs, blocks.blockRefs.get? x.1 = some refs →
      ∀ key, (blockKey x.1 x.2 == key) = true → P key refs) :
    ∀ (l : List (Ix.Name × Ix.Set Ix.Name)), (∀ x ∈ l, x ∈ blocks.blocks.toList) → ∀ s : InitState,
      (∀ key refs, s.2.2.get? key = some refs → P key refs) →
      ∀ key refs, (forIn (m := Id) l s f).2.2.get? key = some refs → P key refs := by
  intro l
  induction l with
  | nil => intro _ s hs; exact hs
  | cons x l ih =>
    intro hl s hs
    rw [List.forIn_cons]
    obtain ⟨u, v, hu⟩ := hf x s
    rw [hu]
    refine ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ fun key refs h => ?_
    dsimp only at h
    split at h
    · rename_i r hr
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i same
        cases h
        exact hP x (hl x List.mem_cons_self) _ hr key same
      · rw [← Std.HashMap.get?_eq_getElem?] at h; exact hs key refs h
    · exact hs key refs h

theorem initStep_contains {blocks : Ix.CondensedBlocks}
    {f : Ix.Name × Ix.Set Ix.Name → InitState → Id (ForInStep InitState)} (hf : InitStep blocks f)
    {key : Ix.Name} {x : Ix.Name × Ix.Set Ix.Name} (hx : (blocks.blockRefs.get? x.1).isSome = true)
    (hk : blockKey x.1 x.2 = key) :
    ∀ (l : List (Ix.Name × Ix.Set Ix.Name)) (s : InitState), x ∈ l →
      (forIn (m := Id) l s f).2.2.contains key = true := by
  have keep : ∀ (l : List (Ix.Name × Ix.Set Ix.Name)) (s : InitState), s.2.2.contains key = true →
      (forIn (m := Id) l s f).2.2.contains key = true := by
    intro l
    induction l with
    | nil => intro s h; exact h
    | cons y l ih =>
      intro s h
      rw [List.forIn_cons]
      obtain ⟨u, v, hu⟩ := hf y s
      rw [hu]
      refine ih _ ?_
      dsimp only
      split
      · rw [Std.HashMap.contains_insert, h, Bool.or_true]
      · exact h
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons y l ih =>
    intro s h
    rw [List.forIn_cons]
    obtain ⟨u, v, hu⟩ := hf y s
    rw [hu]
    rcases List.mem_cons.mp h with rfl | h
    · refine keep _ _ ?_
      dsimp only
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hx
      rw [hr]
      dsimp only
      rw [Std.HashMap.contains_insert, hk, BEq.rfl, Bool.true_or]
    · exact ih _ h

/-- **The block references `FoldState.init` installs**: under the key of a
condensation block with references, the initial state holds the references of
a condensation block (with references) whose members contain that key, when
every condensation block is nonempty. -/
theorem init_p3BlockRefs {cenv : CompileEnv} {blocks : Ix.CondensedBlocks} {sched : FoldSchedule}
    {rep : Ix.Name} {all rs : Ix.Set Ix.Name} (hb : blocks.blocks.get? rep = some all)
    (hrs : blocks.blockRefs.get? rep = some rs)
    (nonempty : ∀ rep all, blocks.blocks.get? rep = some all → all.isEmpty = false) :
    ∃ (refs : Ix.Set Ix.Name) (rep' : Ix.Name) (all' : Ix.Set Ix.Name),
      (FoldState.init cenv blocks sched).acc.cenv.p3BlockRefs.get? (blockKey rep all) = some refs ∧
      blocks.blocks.get? rep' = some all' ∧ blocks.blockRefs.get? rep' = some refs ∧
      all'.contains (blockKey rep all) = true := by
  have hb' := hb
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hb'
  obtain ⟨k, rk, hk⟩ := hb'
  have get_of : ∀ e ∈ blocks.blocks.toList, blocks.blocks.get? e.1 = some e.2 := fun e he => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList]
    exact ⟨e.1, BEq.rfl, he⟩
  have hrk : blocks.blockRefs.get? k = some rs := by
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.getElem?_congr rk, ← Std.HashMap.get?_eq_getElem?]
    exact hrs
  have hkey : blockKey k all = blockKey rep all := blockKey_indep (nonempty rep all hb)
  unfold FoldState.init
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList]
  generalize hR : forIn (m := Id) blocks.blocks.toList ((∅, #[], ∅) : InitState) _ = R
  have contains : R.2.2.contains (blockKey rep all) = true := by
    rw [← hR]
    refine initStep_contains ?_ (x := (k, all)) (by rw [hrk]; rfl) hkey _ _ hk
    intro x s
    dsimp only
    cases hg : blocks.blockRefs.get? x.fst <;> split <;> exact ⟨_, _, rfl⟩
  have values : ∀ key refs, R.2.2.get? key = some refs → ∃ rep' all', blocks.blocks.get? rep' = some all' ∧
      blocks.blockRefs.get? rep' = some refs ∧ all'.contains key = true := by
    rw [← hR]
    refine initStep_refs ?_ _ (fun x hx refs h key same => ⟨x.1, x.2, get_of x hx, h, ?_⟩)
      blocks.blocks.toList (fun x hx => hx) _ (fun key refs h => by
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    · intro x s
      dsimp only
      cases hg : blocks.blockRefs.get? x.fst <;> split <;> exact ⟨_, _, rfl⟩
    · rw [← Std.HashSet.contains_congr same]
      exact blockKey_mem (nonempty _ _ (get_of x hx))
  obtain ⟨refs, hrefs⟩ := Option.isSome_iff_exists.mp
    (show (R.2.2.get? (blockKey rep all)).isSome = true by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact contains)
  obtain ⟨rep', all', h₁, h₂, h₃⟩ := values _ refs hrefs
  exact ⟨refs, rep', all', hrefs, h₁, h₂, h₃⟩
/-! ## B9b: a resolved primary name's record -/

/-- **B9b, a resolved primary name's record.** For `compileReport env =
.ok (ixe, failures)`, a name `n` of the driver's final resolution map, at
`a`, that is not in its final aux map (so not an aux name, B9d's):
* `ixe.named` publishes `n` at `a` (`Ix.Cert.resolvedPublished`);
* `n ↦ a`, with the bytes `b` of its record, is a primary claim of
  `runBlock` on a subset `A` of a condensation block's members (all of them,
  or a promoted block's cross-SCC subset) under a key `k`, against a state
  `snap` the fold reached from its initial state, which the final environment
  follows (`Mono`: a head of `snap` is a final head or a recorded failure);
* `ixe.consts` stores `b` at `a`;
* where Pass 3's hooks are identities at that compile (`HookFree`), the claim
  is one of the block compile's (`BlockCompiled`), the form N-READS takes.

`HookFree` is this lemma's premise; `Ix.Cert.HookFree.compileReport_hookFree`
discharges it for a closure that avoids the changed set and has no failure,
from `Avoids`, `NoFailure` and the decided checks of the discharge. -/
theorem compileReport_claim {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileUnchecked env = .ok (ixe, failures, cenv) ∧
      blocks = Ix.CondenseM.run (groundSplit { consts := env.consts }).1 ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = false →
        (ixe.named.get? n).map (·.addr) = some a ∧
        ∃ (snap : DriverAcc) (rep : Ix.Name) (all A : Ix.Set Ix.Name) (k : Ix.Name) (r : BlockResult)
          (c : BlockState) (layout : Option Ixon.AuxLayout) (p : Ix.Compile.Pass.Published) (b : ByteArray),
          Reach blocks (FoldState.init cenv₀ blocks sched).acc snap ∧ blocks.blocks.get? rep = some all ∧
          Mono snap.cenv cenv ∧
          (∀ x, A.contains x = true → all.contains x = true) ∧
          runBlock snap.cenv A k = .ok (r, c, layout, p) ∧ (n, a, b) ∈ claimWrites k r ∧
          ixe.consts.get? a = some { buf := b, len := b.size } ∧
          (HookFree snap.cenv A k → BlockCompiled snap.cenv A k n a b) := by
  obtain ⟨cenv, hu, pub⟩ := Ix.Cert.resolvedPublished h
  obtain ⟨bytes, cenv₀, sched, -, -, prov⟩ := compileUnchecked_provenance hu
  refine ⟨cenv, _, cenv₀, sched, hu, rfl, fun n a hn hnaux => ⟨pub n a hn, ?_⟩⟩
  rcases prov n a hn with hx | ⟨b, hc, hb⟩
  · rw [hnaux] at hx; cases hx
  · obtain ⟨snap, rep, all, A, k, r, c, layout, p, hsnap, hall, hm, sub, hr, hclaim⟩ := compiled_runBlock hc
    exact ⟨snap, rep, all, A, k, r, c, layout, p, b, hsnap, hall, hm, sub, hr, hclaim, hb,
      fun hf => hookFree_compiled hf hr hclaim⟩

end Ix.Cert.Resolution
