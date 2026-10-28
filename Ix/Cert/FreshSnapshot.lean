import Ix.Cert.ClosureClaims

/-! # A block's members are unresolved at its own snapshot

The fold computes each wave's ready blocks against the wave's start (the snapshot) and then
applies them. This module shows that a block's members are not in the snapshot's resolution
map, except as aux names: outside the aux map, a block member is resolved only by a claim of
its own block (a block's claims name its members, and the constructors its inductives list,
which are in the block too), and a block is applied once, after its snapshot.

* `blocks_disjoint`: two condensation blocks with a common member have the same
  representative;
* `foldWaveWith_spec`: what one wave does to the fold state;
* `WaveInv`: at each wave start, the candidates and waiting blocks have no settled member,
  and every resolved block member outside the aux map is settled;
* `ctorsInBlock`: an inductive and the constructors it lists share a block, since they
  reference each other;
* `Ix.Cert.compileReport_owned_fresh`: `ClosureClaims.compileReport_owned`, and a member of
  the claim's block is resolved at the block's snapshot only through the aux map. -/

namespace Ix.Cert.FreshSnapshot

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Compile.ExactKey (ExactName)

/-! ## Condensation blocks are disjoint -/

/-- **Two blocks of a condensation with a common member are one block.** -/
theorem blocks_disjoint {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {r₁ r₂ x : Ix.Name}
    {a₁ a₂ : Ix.Set Ix.Name} (h₁ : (Ix.CondenseM.run refs).blocks.get? r₁ = some a₁)
    (h₂ : (Ix.CondenseM.run refs).blocks.get? r₂ = some a₂) (hx₁ : a₁.contains x = true)
    (hx₂ : a₂.contains x = true) : (r₁ == r₂) = true := by
  obtain ⟨hr, hv, e⟩ := Condense.blocks_eq refs
  rw [e] at h₁ h₂
  obtain ⟨_, _, hb₁, hrep₁, hn₁⟩ := Condense.blocksOfDisc_mem h₁ hx₁
  obtain ⟨v₁, hv₁, rfl⟩ := Condense.discOf_get hb₁
  obtain ⟨_, _, hb₂, hrep₂, hn₂⟩ := Condense.blocksOfDisc_mem h₂ hx₂
  obtain ⟨v₂, hv₂, rfl⟩ := Condense.discOf_get hb₂
  dsimp only at hrep₁ hn₁ hrep₂ hn₂
  obtain rfl := Condense.namesOf_inj hv₁ hv₂ (BEq.trans hn₁ (BEq.symm hn₂))
  exact BEq.trans (BEq.symm hrep₁) hrep₂

/-- Blocks with a common member have the same representative. -/
def Disjoint (blocks : Ix.CondensedBlocks) : Prop :=
  ∀ (r₁ r₂ x : Ix.Name) (a₁ a₂ : Ix.Set Ix.Name), blocks.blocks.get? r₁ = some a₁ →
    blocks.blocks.get? r₂ = some a₂ → a₁.contains x = true → a₂.contains x = true → (r₁ == r₂) = true

theorem disjoint_run (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) : Disjoint (Ix.CondenseM.run refs) :=
  fun _ _ _ _ _ h₁ h₂ hx₁ hx₂ => blocks_disjoint h₁ h₂ hx₁ hx₂

/-- A name is a member of a block. -/
def Member (blocks : Ix.CondensedBlocks) (x : Ix.Name) : Prop :=
  ∃ rep all, blocks.blocks.get? rep = some all ∧ all.contains x = true

/-! ## Loops -/

/-- The readiness loop of a wave, as the driver writes it. -/
def depsOkOf (p : Ix.Name → Bool) (deps : Ix.Set Ix.Name) : Bool := Id.run do
  for d in deps do
    if !p d then return false
  return true

theorem depsLoop_list (p : Ix.Name → Bool) : ∀ (l : List Ix.Name),
    (forIn (m := Id) l ((none : Option Bool), PUnit.unit) fun d (_ : Option Bool × PUnit) =>
      if (!p d) = true then pure (ForInStep.done (some false, PUnit.unit))
      else pure (ForInStep.yield (none, PUnit.unit))).1 = if l.all p then none else some false
  | [] => rfl
  | d :: l => by
    rw [List.forIn_cons]
    cases hd : p d
    · simp [hd]
      rfl
    · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.all_cons, Bool.true_and]
      exact depsLoop_list p l

/-- **The readiness loop accepts exactly when every dependency is ready.** -/
theorem depsOkOf_eq (p : Ix.Name → Bool) (deps : Ix.Set Ix.Name) :
    depsOkOf p deps = deps.toList.all p := by
  unfold depsOkOf
  simp only [Id.run, Std.HashSet.forIn_eq_forIn_toList]
  have h := depsLoop_list p deps.toList
  generalize hs : forIn (m := Id) deps.toList ((none : Option Bool), PUnit.unit) _ = s at h
  obtain ⟨o, u⟩ := s
  dsimp only at h
  subst h
  split
  · rename_i hc; rw [hc]; rfl
  · rename_i hc; rw [Bool.not_eq_true] at hc; rw [hc]; rfl

/-- A loop whose every step continues, grows its set and adds some names. -/
theorem forIn_grow {α : Type} (f : α → Ix.Set Ix.Name → Id (ForInStep (Ix.Set Ix.Name)))
    (mem : α → Ix.Name → Prop) (hy : ∀ x s, f x s = .yield (f x s).value)
    (grow : ∀ x s y, s.contains y = true → (f x s).value.contains y = true)
    (adds : ∀ x s y, mem x y → (f x s).value.contains y = true) :
    ∀ (l : List α) (s : Ix.Set Ix.Name),
      (∀ y, s.contains y = true → (forIn (m := Id) l s f).contains y = true) ∧
      ∀ x ∈ l, ∀ y, mem x y → (forIn (m := Id) l s f).contains y = true
  | [], s => ⟨fun _ h => h, fun _ h => by cases h⟩
  | x :: l, s => by
    rw [List.forIn_cons, hy x s]
    obtain ⟨ih₁, ih₂⟩ := forIn_grow f mem hy grow adds l (f x s).value
    refine ⟨fun y h => ih₁ y (grow x s y h), fun z hz y hy' => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ih₁ y (adds z s y hy')
    · exact ih₂ z hz y hy'

/-- The inner settling loop: a block's members join the settled set. -/
theorem settle_one (all s : Ix.Set Ix.Name) :
    (∀ y, s.contains y = true →
      (forIn (m := Id) all s fun m s => pure (ForInStep.yield (s.insert m))).contains y = true) ∧
    (∀ y, all.contains y = true →
      (forIn (m := Id) all s fun m s => pure (ForInStep.yield (s.insert m))).contains y = true) ∧
    (∀ y, (forIn (m := Id) all s fun m s => pure (ForInStep.yield (s.insert m))).contains y = true →
      s.contains y = true ∨ all.contains y = true) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  obtain ⟨g, a⟩ := forIn_grow (α := Ix.Name) (fun m (s : Ix.Set Ix.Name) => (pure (ForInStep.yield (s.insert m)) : Id _))
    (fun m y => (m == y) = true) (fun _ _ => rfl)
    (fun m s y h => by show (s.insert m).contains y = true; rw [Std.HashSet.contains_insert, h, Bool.or_true])
    (fun m s y h => by show (s.insert m).contains y = true; rw [Std.HashSet.contains_insert, h, Bool.true_or])
    all.toList s
  refine ⟨g, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨m, hm, e⟩ := List.contains_iff_exists_mem_beq.mp
      (show all.toList.contains y = true by rw [Std.HashSet.contains_toList]; exact hy)
    exact a m hm y (BEq.symm e)
  · refine forIn_inv_list (fun t : Ix.Set Ix.Name => ∀ y, t.contains y = true →
        s.contains y = true ∨ all.contains y = true) _ all.toList (fun m hm t ht y hy => ?_) s
      (fun y h => .inl h) y hy
    change (t.insert m).contains y = true at hy
    rw [Std.HashSet.contains_insert] at hy
    rcases Bool.or_eq_true_iff.mp hy with e | hy
    · right
      rw [← Std.HashSet.contains_congr e]
      exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_of_mem_toList hm)
    · exact ht y hy

/-- A loop over a set keeps an invariant that each step keeps. -/
theorem forIn_inv_set {σ : Type} (I : σ → Prop) (f : Ix.Name → σ → Id (ForInStep σ))
    (xs : Ix.Set Ix.Name) (step : ∀ x s, I s → I (f x s).value) (s : σ) (hs : I s) :
    I (forIn (m := Id) xs s f) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact forIn_inv_list I f xs.toList (fun x _ => step x) s hs

/-- A wave's settling loop, as the driver writes it: the ready blocks' members join the
settled set. -/
def settleLoop (ready : Ready) (s₀ : Ix.Set Ix.Name) : Ix.Set Ix.Name :=
  forIn (m := Id) ready s₀ fun x s => do
    let s ← forIn (m := Id) x.2.2 s fun m s => pure (ForInStep.yield (s.insert m))
    pure (ForInStep.yield s)

theorem settleLoop_spec (ready : Ready) (s₀ : Ix.Set Ix.Name) :
    (∀ y, s₀.contains y = true → (settleLoop ready s₀).contains y = true) ∧
    (∀ x ∈ ready, ∀ y, x.2.2.contains y = true → (settleLoop ready s₀).contains y = true) ∧
    (∀ y, (settleLoop ready s₀).contains y = true →
      s₀.contains y = true ∨ ∃ x ∈ ready, x.2.2.contains y = true) := by
  unfold settleLoop
  rw [← Array.forIn_toList]
  obtain ⟨g, a⟩ := forIn_grow (α := Ix.Name × Ix.Name × Ix.Set Ix.Name)
    (fun x (s : Ix.Set Ix.Name) => (do
      let s ← forIn (m := Id) x.2.2 s fun m s => pure (ForInStep.yield (s.insert m))
      pure (ForInStep.yield s) : Id _))
    (fun x y => x.2.2.contains y = true) (fun _ _ => rfl)
    (fun x s y h => (settle_one x.2.2 s).1 y h) (fun x s y h => (settle_one x.2.2 s).2.1 y h)
    ready.toList s₀
  refine ⟨g, fun x hx y hy => a x (Array.mem_toList_iff.mpr hx) y hy, fun y hy => ?_⟩
  refine forIn_inv_list (fun t : Ix.Set Ix.Name => ∀ y, t.contains y = true →
      s₀.contains y = true ∨ ∃ x ∈ ready, x.2.2.contains y = true) _ ready.toList
      (fun x hx t ht y hy => ?_) s₀ (fun y h => .inl h) y hy
  rcases (settle_one x.2.2 t).2.2 y hy with h | h
  · exact ht y h
  · exact .inr ⟨x, Array.mem_toList_iff.mp hx, h⟩

/-- A wave's release loop, as the driver writes it: each settled member's waiting blocks
count it, and a block whose last unsettled dependency it was becomes a candidate. -/
def releaseLoop (sched : FoldSchedule) (ready : Ready)
    (init : Std.HashMap Ix.Name Nat × Array Ix.Name) : Std.HashMap Ix.Name Nat × Array Ix.Name :=
  forIn (m := Id) ready init fun x s => do
    let s ← forIn (m := Id) x.2.2 (s.1, s.2) fun m s => do
      let s ← forIn (m := Id) ((sched.waiters.get? m).getD #[]) (s.1, s.2) fun w s =>
        match s.1.get? w with
        | some 1 => pure (ForInStep.yield (s.1.erase w, s.2.push w))
        | some k => pure (ForInStep.yield (s.1.insert w (k - 1), s.2))
        | none => pure (ForInStep.yield (s.1, s.2))
      pure (ForInStep.yield (s.1, s.2))
    pure (ForInStep.yield (s.1, s.2))

/-- **The release loop only shrinks the waiting map, and releases blocks that no longer
wait**: each next candidate is a parked block or was waiting. -/
theorem releaseLoop_spec (sched : FoldSchedule) (ready : Ready) (u₀ : Std.HashMap Ix.Name Nat)
    (parked : Array Ix.Name) (hp : ∀ p ∈ parked, u₀.contains p = false) :
    (∀ y, (releaseLoop sched ready (u₀, parked)).1.contains y = true → u₀.contains y = true) ∧
    ∀ y ∈ (releaseLoop sched ready (u₀, parked)).2,
      (releaseLoop sched ready (u₀, parked)).1.contains y = false ∧ (y ∈ parked ∨ u₀.contains y = true) := by
  let J : Std.HashMap Ix.Name Nat × Array Ix.Name → Prop := fun s =>
    (∀ y, s.1.contains y = true → u₀.contains y = true) ∧
    ∀ y ∈ s.2, s.1.contains y = false ∧ (y ∈ parked ∨ u₀.contains y = true)
  suffices h : J (releaseLoop sched ready (u₀, parked)) from h
  unfold releaseLoop
  refine forIn_inv_array J _ ready (fun x _ s hs => ?_) _ ⟨fun _ h => h, fun y hy => ⟨hp y hy, .inl hy⟩⟩
  refine forIn_inv_set J _ x.2.2 (fun m t ht => ?_) (s.1, s.2) hs
  refine forIn_inv_array J _ _ (fun w _ u hu => ?_) (t.1, t.2) ht
  obtain ⟨keys, next⟩ := hu
  split
  · rename_i hw
    change J (u.1.erase w, u.2.push w)
    have hc : u.1.contains w = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hw]; rfl
    refine ⟨fun y hy => keys y ?_, fun y hy => ?_⟩
    · rw [Std.HashMap.contains_erase] at hy
      exact (Bool.and_eq_true_iff.mp hy).2
    · rcases Array.mem_push.mp hy with hy | rfl
      · refine ⟨?_, (next y hy).2⟩
        rw [Std.HashMap.contains_erase, (next y hy).1, Bool.and_false]
      · exact ⟨by rw [Std.HashMap.contains_erase, BEq.rfl]; rfl, .inr (keys _ hc)⟩
  · rename_i k _ hw
    change J (u.1.insert w (k - 1), u.2)
    have hc : u.1.contains w = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hw]; rfl
    refine ⟨fun y hy => ?_, fun y hy => ⟨?_, (next y hy).2⟩⟩
    · rw [Std.HashMap.contains_insert] at hy
      rcases Bool.or_eq_true_iff.mp hy with e | hy
      · exact keys y (by rw [← Std.HashMap.contains_congr e]; exact hc)
      · exact keys y hy
    · rw [Std.HashMap.contains_insert, (next y hy).1, Bool.or_false]
      cases e : (w == y)
      · rfl
      · have := (next y hy).1
        rw [← Std.HashMap.contains_congr e, hc] at this
        cases this
  · exact ⟨keys, next⟩

/-! ## One wave -/

/-- **A ready block of a wave**: a candidate at the wave's start, a block of the
condensation under its key, whose scheduling dependencies are all ready. -/
def ReadyIn (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState)
    (x : Ix.Name × Ix.Name × Ix.Set Ix.Name) : Prop :=
  x.2.1 ∈ st.candidates ∧ blocks.blocks.get? x.2.1 = some x.2.2 ∧ x.1 = blockKey x.2.1 x.2.2 ∧
    ∀ d ∈ ((sched.deps.get? x.2.1).getD ∅).toList,
      auxDependencyReady blocks.lowLinks.contains st.acc.cenv st.settled d = true

/-- **One wave**: its ready blocks, applied against the wave's start; the blocks it parks,
candidates distinct from every ready block; the settled set grown by the ready blocks'
members; the waiting map shrunk; and the next candidates, the parked blocks and released
waiting blocks, none of them waiting. -/
theorem foldWaveWith_spec (apply : CompileEnv → Ready → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st st' : FoldState)
    (hcand : ∀ p ∈ st.candidates, st.unmet.contains p = false)
    (h : foldWaveWith apply blocks sched st = .ok st') :
    ∃ (ready : Ready) (parked : Array Ix.Name),
      (∀ x ∈ ready, ReadyIn blocks sched st x) ∧
      (∀ p ∈ parked, p ∈ st.candidates ∧ ∀ x ∈ ready, (p == x.2.1) = false) ∧
      st'.acc = apply st.acc.cenv ready st.acc ∧
      (∀ y, st.settled.contains y = true → st'.settled.contains y = true) ∧
      (∀ x ∈ ready, ∀ y, x.2.2.contains y = true → st'.settled.contains y = true) ∧
      (∀ y, st'.settled.contains y = true →
        st.settled.contains y = true ∨ ∃ x ∈ ready, x.2.2.contains y = true) ∧
      (∀ y, st'.unmet.contains y = true → st.unmet.contains y = true) ∧
      (∀ y ∈ st'.candidates, st'.unmet.contains y = false ∧ (y ∈ parked ∨ st.unmet.contains y = true)) := by
  unfold foldWaveWith at h
  simp only [Id.run] at h
  revert h
  let ok : Ix.Name → Prop := fun rep => ∀ d ∈ ((sched.deps.get? rep).getD ∅).toList,
    auxDependencyReady blocks.lowLinks.contains st.acc.cenv st.settled d = true
  refine loop_bind (P := fun r => r = Except.ok st' → _)
    (I := fun s : Option (Except String FoldState) × Ready × Array Ix.Name =>
      (s.1 = none ∨ ∃ e, s.1 = some (.error e)) ∧ (∀ x ∈ s.2.1, ReadyIn blocks sched st x) ∧
        ∀ p ∈ s.2.2, p ∈ st.candidates ∧ ¬ ok p) _ _ _ _ ?init ?body ?cont
  case init => exact ⟨.inl rfl, fun x hx => by simp at hx, fun p hp => by simp at hp⟩
  case body =>
    intro rep hrep s hs
    obtain ⟨_, hready, hparked⟩ := hs
    split
    · rename_i all hall
      split
      · rename_i hok
        have hok' : depsOkOf (auxDependencyReady blocks.lowLinks.contains st.acc.cenv st.settled)
            ((sched.deps.get? rep).getD ∅) = true := hok
        rw [depsOkOf_eq, List.all_eq_true] at hok'
        refine ⟨.inl rfl, fun x hx => ?_, hparked⟩
        rcases Array.mem_push.mp hx with hx | rfl
        · exact hready x hx
        · exact ⟨hrep, hall, rfl, hok'⟩
      · rename_i hok
        refine ⟨.inl rfl, hready, fun p hp => ?_⟩
        rcases Array.mem_push.mp hp with hp | rfl
        · exact hparked p hp
        · refine ⟨hrep, fun hall' => hok ?_⟩
          show depsOkOf (auxDependencyReady blocks.lowLinks.contains st.acc.cenv st.settled)
            ((sched.deps.get? p).getD ∅) = true
          rw [depsOkOf_eq, List.all_eq_true]
          exact hall'
    · exact ⟨.inr ⟨_, rfl⟩, hready, hparked⟩
  case cont =>
    intro L hL h
    obtain ⟨h1, hready, hparked⟩ := hL
    rcases h1 with h1 | ⟨e, h1⟩
    · rw [h1] at h
      dsimp only at h
      split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        have rdy : ∀ x ∈ L.2.1.qsort (fun a b => Ix.nameCompare a.fst b.fst == Ordering.lt),
            ReadyIn blocks sched st x :=
          fun x hx => hready x (Ix.CompileCert.Canon.mem_qsort.mp hx)
        generalize L.2.1.qsort (fun a b => Ix.nameCompare a.fst b.fst == Ordering.lt) = ready at rdy ⊢
        have distinct : ∀ p ∈ L.2.2, p ∈ st.candidates ∧ ∀ x ∈ ready, (p == x.2.1) = false := by
          intro p hp
          obtain ⟨hpc, hnok⟩ := hparked p hp
          refine ⟨hpc, fun x hx => ?_⟩
          cases e : (p == x.2.1)
          · rfl
          · refine absurd ?_ hnok
            have hd : sched.deps.get? p = sched.deps.get? x.2.1 := by
              rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?]
              exact Std.HashMap.getElem?_congr e
            show ∀ d ∈ ((sched.deps.get? p).getD ∅).toList,
              auxDependencyReady blocks.lowLinks.contains st.acc.cenv st.settled d = true
            rw [hd]
            exact (rdy x hx).2.2.2
        obtain ⟨s0, s1, s2⟩ := settleLoop_spec ready st.settled
        exact ⟨ready, L.2.2, rdy, distinct, rfl, s0, s1, s2,
          releaseLoop_spec sched ready st.unmet L.2.2 fun p hp => hcand p (hparked p hp).1⟩
    · rw [h1] at h
      cases h

/-! ## The wave-start invariant -/

/-- No member of block `rep` is settled. -/
def Unsettled (blocks : Ix.CondensedBlocks) (settled : Ix.Set Ix.Name) (rep : Ix.Name) : Prop :=
  ∀ all, blocks.blocks.get? rep = some all → ∀ x, all.contains x = true → settled.contains x = false

/-- **The invariant of a wave start**: a candidate block has no settled member and is not
waiting; a waiting block has no settled member; and a block member resolved outside the aux
map is settled. -/
structure WaveInv (blocks : Ix.CondensedBlocks) (st : FoldState) : Prop where
  cand : ∀ p ∈ st.candidates, Unsettled blocks st.settled p ∧ st.unmet.contains p = false
  waiting : ∀ p, st.unmet.contains p = true → Unsettled blocks st.settled p
  resolved : ∀ (n : ExactName) (a : Address), st.acc.cenv.nameToAddr.get? n = some a →
    st.acc.cenv.auxNameToAddr.contains n = true ∨ (Member blocks n → st.settled.contains n = true)

/-- **A ready block's outcome claims, among block members, only its own members.** -/
def ClaimsOwn (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) : Prop :=
  ∀ x, ReadyIn blocks sched st x → ∀ (n : Ix.Name) (a : Address) (b : ByteArray),
    outcomeClaims x.1 (auxBlockOutcome st.acc.cenv x.1 x.2.2) n a b → Member blocks n →
      x.2.2.contains n = true

/-- The fold's first loop, as the driver writes it: blocks without source dependencies are
the first candidates, the others wait. -/
def initLoop (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) :
    Std.HashMap Ix.Name Nat × Array Ix.Name :=
  forIn (m := Id) blocks.blocks ((∅ : Std.HashMap Ix.Name Nat), (#[] : Array Ix.Name)) fun x s =>
    if ((sched.sourceDeps.get? x.1).getD 0 == 0) = true then pure (ForInStep.yield (s.1, s.2.push x.1))
    else pure (ForInStep.yield (s.1.insert x.1 ((sched.sourceDeps.get? x.1).getD 0), s.2))

/-- **The fold's start satisfies the invariant** when it resolves nothing. -/
theorem waveInv_init {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {cenv : CompileEnv}
    (h₀ : cenv.nameToAddr = {}) : WaveInv blocks (FoldState.init cenv blocks sched) := by
  have settled : (FoldState.init cenv blocks sched).settled = ∅ := rfl
  have none : ∀ p, Unsettled blocks (FoldState.init cenv blocks sched).settled p := by
    intro p all _ x _
    rw [settled]
    exact Std.HashSet.contains_empty
  let k : Ix.Name → Nat := fun y => (sched.sourceDeps.get? y).getD 0
  have loop : (∀ p ∈ (initLoop blocks sched).2, k p = 0) ∧
      ∀ y, (initLoop blocks sched).1.contains y = true → k y ≠ 0 := by
    unfold initLoop
    rw [Std.HashMap.forIn_eq_forIn_toList]
    refine forIn_inv_list (fun s : Std.HashMap Ix.Name Nat × Array Ix.Name =>
        (∀ p ∈ s.2, k p = 0) ∧ ∀ y, s.1.contains y = true → k y ≠ 0) _ _ (fun x _ s hs => ?_) _
        ⟨fun p hp => by simp at hp, fun y hy => by simp at hy⟩
    split
    · rename_i hk
      refine ⟨fun p hp => ?_, hs.2⟩
      rcases Array.mem_push.mp hp with hp | rfl
      · exact hs.1 p hp
      · exact beq_iff_eq.mp hk
    · rename_i hk
      refine ⟨hs.1, fun y hy => ?_⟩
      change (s.1.insert x.1 ((sched.sourceDeps.get? x.1).getD 0)).contains y = true at hy
      rw [Std.HashMap.contains_insert] at hy
      rcases Bool.or_eq_true_iff.mp hy with e | hy
      · have same : k y = k x.1 := by
          show (sched.sourceDeps.get? y).getD 0 = (sched.sourceDeps.get? x.1).getD 0
          rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr e]
        rw [same]
        intro h0
        exact hk (by show ((sched.sourceDeps.get? x.1).getD 0 == 0) = true; exact beq_iff_eq.mpr h0)
      · exact hs.2 y hy
  have hc : (FoldState.init cenv blocks sched).candidates = (initLoop blocks sched).2 := rfl
  have hu : (FoldState.init cenv blocks sched).unmet = (initLoop blocks sched).1 := rfl
  refine ⟨fun p hp => ⟨none p, ?_⟩, fun p _ => none p, fun n a hn => ?_⟩
  · rw [hc] at hp
    rw [hu]
    cases e : (initLoop blocks sched).1.contains p
    · rfl
    · exact absurd (loop.1 p hp) (loop.2 p e)
  · rw [init_nameToAddr, h₀, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hn
    cases hn

/-- **The invariant survives a wave** whose ready blocks claim, among block members, only
their own. -/
theorem applySeqList_resolved {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {st : FoldState}
    (claims : ClaimsOwn blocks sched st) (Q : Ix.Name → Prop) :
    ∀ (l : List (Ix.Name × Ix.Name × Ix.Set Ix.Name)) (acc : DriverAcc),
      (∀ x ∈ l, ReadyIn blocks sched st x ∧ ∀ y, x.2.2.contains y = true → Q y) →
      (∀ (n : ExactName) (a : Address), acc.cenv.nameToAddr.get? n = some a →
        acc.cenv.auxNameToAddr.contains n = true ∨ (Member blocks n → Q n)) →
      ∀ (n : ExactName) (a : Address), (applySeqList st.acc.cenv l acc).cenv.nameToAddr.get? n = some a →
        (applySeqList st.acc.cenv l acc).cenv.auxNameToAddr.contains n = true ∨ (Member blocks n → Q n)
  | [], _, _, h => h
  | x :: l, acc, hl, h => by
    obtain ⟨key, rep, all⟩ := x
    have hx := hl (key, rep, all) List.mem_cons_self
    refine applySeqList_resolved claims Q l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_
    intro n a hn
    have st' := applyAuxBlockOutcome_step acc key all (auxBlockOutcome st.acc.cenv key all)
    rcases st'.2 n a hn with ⟨hold, keep⟩ | haux | ⟨b, hclaim, -⟩
    · rcases h n a hold with h | h
      · exact .inl (keep h)
      · exact .inr h
    · exact .inl haux
    · exact .inr fun hm => hx.2 n (claims _ hx.1 n a b hclaim hm)

theorem waveInv_step {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {st st' : FoldState}
    (hd : Disjoint blocks) (inv : WaveInv blocks st) (claims : ClaimsOwn blocks sched st)
    (h : foldWaveSeq blocks sched st = .ok st') : WaveInv blocks st' := by
  obtain ⟨ready, parked, hready, hparked, hacc, s0, s1, s2, u1, u2⟩ :=
    foldWaveWith_spec applySeq blocks sched st st' (fun p hp => (inv.cand p hp).2) h
  have keep : ∀ p, Unsettled blocks st.settled p → (∀ x ∈ ready, (p == x.2.1) = false) →
      Unsettled blocks st'.settled p := by
    intro p hu hne all hall y hy
    cases e : st'.settled.contains y
    · rfl
    · rcases s2 y e with h | ⟨x, hx, hxy⟩
      · rw [hu all hall y hy] at h; cases h
      · have := hd p x.2.1 y all x.2.2 hall (hready x hx).2.1 hy hxy
        rw [hne x hx] at this; cases this
  have waitNe : ∀ p, st.unmet.contains p = true → ∀ x ∈ ready, (p == x.2.1) = false := by
    intro p hp x hx
    cases e : (p == x.2.1)
    · rfl
    · have := (inv.cand x.2.1 (hready x hx).1).2
      rw [← Std.HashMap.contains_congr e, hp] at this; cases this
  refine ⟨fun p hp => ?_, fun p hp => ?_, ?_⟩
  · obtain ⟨hnot, hsrc⟩ := u2 p hp
    refine ⟨?_, hnot⟩
    rcases hsrc with hp' | hp'
    · obtain ⟨hc, hne⟩ := hparked p hp'
      exact keep p (inv.cand p hc).1 hne
    · exact keep p (inv.waiting p hp') (waitNe p hp')
  · have hp' := u1 p hp
    exact keep p (inv.waiting p hp') (waitNe p hp')
  · intro n a hn
    rw [hacc, applySeq_eq_list] at hn ⊢
    rcases applySeqList_resolved claims
        (fun y => st.settled.contains y = true ∨ ∃ x ∈ ready, x.2.2.contains y = true)
        ready.toList st.acc (fun x hx => ⟨hready x (Array.mem_toList_iff.mp hx),
          fun y hy => .inr ⟨x, Array.mem_toList_iff.mp hx, hy⟩⟩)
        (fun n a hn => (inv.resolved n a hn).imp id fun h hm => .inl (h hm)) n a hn with h | h
    · exact .inl h
    · refine .inr fun hm => ?_
      rcases h hm with h | ⟨x, hx, hy⟩
      · exact s0 n h
      · exact s1 x hx n hy

/-! ## Freshness of the snapshots -/

/-- **`c` resolves the block's members only as aux names.** -/
def FreshFor (c : CompileEnv) (all : Ix.Set Ix.Name) : Prop :=
  ∀ x, all.contains x = true → ∀ a', c.nameToAddr.get? x = some a' → c.auxNameToAddr.contains x = true

/-- **A ready block is fresh at its wave's start.** -/
theorem ready_fresh {blocks : Ix.CondensedBlocks} {sched : FoldSchedule} {st : FoldState}
    {x : Ix.Name × Ix.Name × Ix.Set Ix.Name} (inv : WaveInv blocks st) (hx : ReadyIn blocks sched st x) :
    FreshFor st.acc.cenv x.2.2 := by
  intro y hy a' ha
  rcases inv.resolved y a' ha with h | h
  · exact h
  · have hs := h ⟨x.2.1, x.2.2, hx.2.1, hy⟩
    rw [(inv.cand x.2.1 hx.1).1 x.2.2 hx.2.1 y hy] at hs
    cases hs

/-- `Resolution.CompiledIn`, with the block fresh at the snapshot its outcome was computed
against. -/
def CompiledFresh (blocks : Ix.CondensedBlocks) (R : DriverAcc → Prop) (c : CompileEnv) (n : Ix.Name)
    (a : Address) (b : ByteArray) : Prop :=
  ∃ (snap pre : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name),
    R snap ∧ R pre ∧ Mono snap.cenv pre.cenv ∧ blocks.blocks.get? rep = some all ∧
    Mono (applyAuxBlockOutcome pre (blockKey rep all) all
      (auxBlockOutcome snap.cenv (blockKey rep all) all)).1.cenv c ∧
    outcomeClaims (blockKey rep all) (auxBlockOutcome snap.cenv (blockKey rep all) all) n a b ∧
    FreshFor snap.cenv all

theorem CompiledFresh.mono {blocks : Ix.CondensedBlocks} {R : DriverAcc → Prop} {c c' : CompileEnv}
    {n : Ix.Name} {a : Address} {b : ByteArray} (h : CompiledFresh blocks R c n a b) (m : Mono c c') :
    CompiledFresh blocks R c' n a b := by
  obtain ⟨snap, pre, rep, all, hsnap, hpre, hm, hall, hpost, hclaim, fresh⟩ := h
  exact ⟨snap, pre, rep, all, hsnap, hpre, hm, hall, hpost.trans m, hclaim, fresh⟩

/-- `Resolution.ProvenanceIn`, with fresh snapshots. -/
def ProvenanceFresh (blocks : Ix.CondensedBlocks) (R : DriverAcc → Prop) (acc : DriverAcc) : Prop :=
  ∀ (n : ExactName) (a : Address), acc.cenv.nameToAddr.get? n = some a →
    acc.cenv.auxNameToAddr.contains n = true ∨
      ∃ b, CompiledFresh blocks R acc.cenv n a b ∧ acc.cenv.constants.get? a = some b

theorem provenanceFresh_of_empty {blocks : Ix.CondensedBlocks} {R : DriverAcc → Prop} {acc : DriverAcc}
    (h : acc.cenv.nameToAddr = {}) : ProvenanceFresh blocks R acc := by
  intro n a hn
  rw [h, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hn
  cases hn

theorem provenanceFresh_step {blocks : Ix.CondensedBlocks} {R : DriverAcc → Prop} {snap acc : DriverAcc}
    {rep : Ix.Name} {all : Ix.Set Ix.Name} (hsnap : R snap) (hacc : R acc) (hm : Mono snap.cenv acc.cenv)
    (hall : blocks.blocks.get? rep = some all) (fresh : FreshFor snap.cenv all)
    (ih : ProvenanceFresh blocks R acc) :
    ProvenanceFresh blocks R (applyAuxBlockOutcome acc (blockKey rep all) all
      (auxBlockOutcome snap.cenv (blockKey rep all) all)).1 := by
  intro n a hn
  have st := applyAuxBlockOutcome_step acc (blockKey rep all) all
    (auxBlockOutcome snap.cenv (blockKey rep all) all)
  rcases st.2 n a hn with ⟨hold, keep⟩ | haux | ⟨b, hclaim, hb⟩
  · rcases ih n a hold with haux | ⟨b, hc, hb⟩
    · exact .inl (keep haux)
    · exact .inr ⟨b, hc.mono st.1.2.2, st.1.1 a b hb⟩
  · exact .inl haux
  · exact .inr ⟨b, ⟨snap, acc, rep, all, hsnap, hacc, hm, hall, Mono.refl _, hclaim, fresh⟩, hb⟩

theorem applySeqList_provenanceFresh {blocks : Ix.CondensedBlocks} {R : DriverAcc → Prop}
    {snap : DriverAcc} (hsnap : R snap) :
    ∀ (l : List (Ix.Name × Ix.Name × Ix.Set Ix.Name)) (acc : DriverAcc),
      (∀ x ∈ l, blocks.blocks.get? x.2.1 = some x.2.2 ∧ x.1 = blockKey x.2.1 x.2.2 ∧
        FreshFor snap.cenv x.2.2) →
      (∀ pre post, l = pre ++ post → R (applySeqList snap.cenv pre acc)) →
      Mono snap.cenv acc.cenv → ProvenanceFresh blocks R acc →
      ProvenanceFresh blocks R (applySeqList snap.cenv l acc)
  | [], _, _, _, _, h => h
  | x :: l, acc, good, hR, hm, h => by
    obtain ⟨key, rep, all⟩ := x
    obtain ⟨hall, hkey, fresh⟩ := good (key, rep, all) List.mem_cons_self
    simp only at hall hkey fresh
    subst hkey
    have hacc : R acc := by simpa [applySeqList] using hR [] ((blockKey rep all, rep, all) :: l) rfl
    have step := provenanceFresh_step hsnap hacc hm hall fresh h
    exact applySeqList_provenanceFresh hsnap l _ (fun y hy => good y (List.mem_cons_of_mem _ hy))
      (fun pre post e => by
        have := hR ((blockKey rep all, rep, all) :: pre) post (by rw [e]; rfl)
        simpa [applySeqList] using this)
      (hm.trans (applyAuxBlockOutcome_mono _ _ _ _)) step

/-- **Every wave start of the run satisfies the invariant and has fresh provenance.** -/
theorem waveStart_provenanceFresh {blocks : Ix.CondensedBlocks} {sched : FoldSchedule}
    {st₀ st : FoldState} (hd : Disjoint blocks) (inv₀ : WaveInv blocks st₀)
    (claimsAt : ∀ st, WaveStart blocks sched st₀ st → ClaimsOwn blocks sched st)
    (h₀ : ProvenanceFresh blocks (OnRun blocks sched st₀) st₀.acc) (h : WaveStart blocks sched st₀ st) :
    WaveInv blocks st ∧ ProvenanceFresh blocks (OnRun blocks sched st₀) st.acc := by
  induction h with
  | start => exact ⟨inv₀, h₀⟩
  | @wave st st' hst hr hw ih =>
    obtain ⟨inv, prov⟩ := ih
    refine ⟨waveInv_step hd inv (claimsAt st hst) hw, ?_⟩
    obtain ⟨ready, -, hready, -, hacc, -⟩ :=
      foldWaveWith_spec applySeq blocks sched st st' (fun p hp => (inv.cand p hp).2) hw
    have good : GoodReady blocks ready := fun x hx => ⟨(hready x hx).2.1, (hready x hx).2.2.1⟩
    rw [hacc, applySeq_eq_list]
    refine applySeqList_provenanceFresh (R := OnRun blocks sched st₀) ⟨st, hst, .inl rfl⟩ _ _
      (fun x hx => ⟨(hready x (Array.mem_toList_iff.mp hx)).2.1,
        (hready x (Array.mem_toList_iff.mp hx)).2.2.1,
        ready_fresh inv (hready x (Array.mem_toList_iff.mp hx))⟩) (fun pre post e => ?_) (Mono.refl _) prov
    exact ⟨st, hst, .inr ⟨st', ready, pre, post, hr, hw, good, hacc, e, rfl⟩⟩

/-- **The fold's final resolution map has fresh provenance**: `Resolution.compileEnvFold_provenance`,
with each claim's block fresh at its snapshot, when the condensation's blocks are disjoint
and every wave's ready blocks claim, among block members, only their own. -/
theorem compileEnvFold_provenanceFresh {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv))
    (hd : Disjoint blocks)
    (claimsAt : ∀ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState),
      (FoldState.init cenv₀ blocks sched).acc.cenv.env = { consts := {}, fallback? := some env.get? } →
      WaveStart blocks sched (FoldState.init cenv₀ blocks sched) st → ClaimsOwn blocks sched st) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule), FoldRun env blocks cenv cenv₀ sched ∧
      (FoldState.init cenv₀ blocks sched).acc.cenv.env = { consts := {}, fallback? := some env.get? } ∧
      ∀ (n : ExactName) (a : Address),
        cenv.nameToAddr.get? n = some a → cenv.auxNameToAddr.contains n = true ∨
          ∃ b, CompiledFresh blocks (OnRun blocks sched (FoldState.init cenv₀ blocks sched)) cenv n a b ∧
            ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨cenv₀, sched, st, h₀, henv, hst, finalized, hmap, haux, hconsts, hm⟩ :=
    compileEnvFold_final h
  have kept : ∀ a b, st.acc.cenv.constants.get? a = some b → cenv.constants.get? a = some b :=
    fun a b hb => by rw [hconsts]; exact hb
  refine ⟨cenv₀, sched, ⟨st, h₀, henv, hst, hmap, kept, hm⟩, henv, fun n a hn => ?_⟩
  rw [hmap] at hn
  rw [haux]
  rcases (waveStart_provenanceFresh hd (waveInv_init h₀) (fun st' hst' => claimsAt cenv₀ sched st' henv hst')
    (provenanceFresh_of_empty ((init_nameToAddr _ _ _).trans h₀))
    (foldWavesSeq_waveStart _ _ _ hst)).2 n a hn with haux | ⟨b, hc, hb⟩
  · exact .inl haux
  · rw [← finalized]
    exact .inr ⟨b, hc.mono hm, assembleEnv_consts _ hb⟩

/-! ## A block's claims name its own members -/

/-- **An inductive's constructors are in its block**: a constructor an inductive member of
a block lists, if it is a block member at all, is a member of that block. -/
def CtorsInBlock (blocks : Ix.CondensedBlocks) (E : Ix.Environment) : Prop :=
  ∀ (rep : Ix.Name) (all : Ix.Set Ix.Name) (I : Ix.Name) (iv : Ix.InductiveVal) (c : Ix.Name),
    blocks.blocks.get? rep = some all → all.contains I = true → E.get? I = some (.inductInfo iv) →
    c ∈ iv.ctors → Member blocks c → all.contains c = true

/-- A promoted block's cross-SCC names are members of the block. -/
theorem auxBlockOutcome_cross_sub {cenv : CompileEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {clo : Ix.Name} {r : BlockResult} {c : BlockState}
    {cn : Array Ix.Name} {cf : Option (Array Ix.Name × String)} {im : Option String}
    {na : Option (BlockResult × BlockState)} {nf : Option String}
    (h : auxBlockOutcome cenv lo all = .promoted (some (clo, r, c)) cn cf im na nf) :
    ∀ y ∈ cn, all.contains y = true := by
  unfold auxBlockOutcome at h
  simp only [Id.run] at h
  split at h
  · revert h
    refine loop_bind_mem _ _ _ _ (fun L : Array Ix.Name => ∀ x ∈ L, all.contains x = true)
      (fun o : AuxBlockOutcome => o = .promoted (some (clo, r, c)) cn cf im na nf →
        ∀ y ∈ cn, all.contains y = true) (fun _ h => by simp at h) ?_ ?_
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
      all_goals (cases h'; exact hL)
  · split at h <;> cases h

/-- **A ready block's claims name, among block members, only its own members**, when an
inductive's constructors are in its block. -/
theorem claims_members {blocks : Ix.CondensedBlocks} {cenv : CompileEnv}
    (hn : Ix.Cert.Claims.NamedEnv cenv.env) (hctor : CtorsInBlock blocks cenv.env)
    {rep : Ix.Name} {all : Ix.Set Ix.Name} (hall : blocks.blocks.get? rep = some all)
    (hne : all.isEmpty = false) {n : Ix.Name} {a : Address} {b : ByteArray}
    (h : outcomeClaims (blockKey rep all) (auxBlockOutcome cenv (blockKey rep all) all) n a b)
    (hm : Member blocks n) : all.contains n = true := by
  have owned : ∀ (A : Ix.Set Ix.Name), (∀ x, A.contains x = true → all.contains x = true) →
      ∀ x, Ix.Cert.Claims.Owned cenv.env A x → Member blocks x → all.contains x = true := by
    intro A sub x hx hmx
    rcases hx with ⟨m, hm', em⟩ | ⟨I, iv, c', hI, hiv, hc, ec⟩
    · rw [Std.HashSet.contains_congr em]; exact sub m hm'
    · have hmc : Member blocks c' := by
        obtain ⟨r', a', hr', ha'⟩ := hmx
        exact ⟨r', a', hr', by rw [← Std.HashSet.contains_congr ec]; exact ha'⟩
      rw [Std.HashSet.contains_congr ec]
      exact hctor rep all I iv c' hall (sub I hI) hiv hc hmc
  generalize ho : auxBlockOutcome cenv (blockKey rep all) all = o at h
  cases o with
  | compiled r c =>
    obtain ⟨layout, hr⟩ := auxBlockOutcome_compiled ho
    rcases ClosureClaims.claim_name h with e | ⟨row, hrow, e⟩
    · rw [e]; exact blockKey_mem hne
    · rw [← e]
      exact owned all (fun _ h => h) row.1 (Ix.Cert.Claims.runBlock_owned hn hr row hrow) (e ▸ hm)
  | promoted cs cn cf im na nf =>
    cases cs with
    | none => exact h.elim
    | some x =>
      obtain ⟨clo, r, c⟩ := x
      obtain ⟨layout, hclo, hr⟩ := ClosureClaims.auxBlockOutcome_cross_names ho
      have sub := auxBlockOutcome_cross_sub ho
      rcases ClosureClaims.claim_name h with e | ⟨row, hrow, e⟩
      · rw [e]; exact sub clo hclo
      · rw [← e]
        refine owned _ (fun x hx => ?_) row.1 (Ix.Cert.Claims.runBlock_owned hn hr row hrow) (e ▸ hm)
        obtain ⟨y, hy, ey⟩ := ClosureClaims.foldl_insert_mem hx
        rw [← Std.HashSet.contains_congr ey]
        exact sub y hy
  | failed msg => exact h.elim

/-! ## An inductive and its constructors share a block

An inductive references its constructors and a constructor its inductive
(`Ix.graphConst`), so where both are grounded they are one strongly connected component of
the ground graph, and the condensation (`Ix.CompileCert.Canon.condensation_scc`) makes them
one block. -/

/-- A loop whose every step continues, keeps what holds and adds some facts. -/
theorem forIn_grows {α σ β : Type} (f : α → σ → Id (ForInStep σ)) (mem : σ → β → Prop)
    (adds : α → β → Prop) (hy : ∀ x s, f x s = .yield (f x s).value)
    (grow : ∀ x s y, mem s y → mem (f x s).value y) (add : ∀ x s y, adds x y → mem (f x s).value y) :
    ∀ (l : List α) (s : σ), (∀ y, mem s y → mem (forIn (m := Id) l s f) y) ∧
      ∀ x ∈ l, ∀ y, adds x y → mem (forIn (m := Id) l s f) y
  | [], _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | x :: l, s => by
    rw [List.forIn_cons, hy x s]
    obtain ⟨ih₁, ih₂⟩ := forIn_grows f mem adds hy grow add l (f x s).value
    refine ⟨fun y h => ih₁ y (grow x s y h), fun z hz y hy' => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ih₁ y (add z s y hy')
    · exact ih₂ z hz y hy'

/-- A fold that keeps what a set holds. -/
theorem foldl_keep (g : Ix.Set Ix.Name → Ix.Name → Ix.Set Ix.Name)
    (hg : ∀ s n y, s.contains y = true → (g s n).contains y = true) :
    ∀ (l : List Ix.Name) (s : Ix.Set Ix.Name) (y : Ix.Name), s.contains y = true →
      (l.foldl g s).contains y = true
  | [], _, _, h => h
  | n :: l, s, y, h => foldl_keep g hg l (g s n) y (hg s n y h)

/-- An inserting fold holds each name it inserts. -/
theorem foldl_insert_has : ∀ (l : List Ix.Name) (s : Ix.Set Ix.Name) (y : Ix.Name), y ∈ l →
    (l.foldl (fun s n => s.insert n) s).contains y = true
  | [], _, _, h => by cases h
  | n :: l, s, y, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_keep _ (fun s n y h => by rw [Std.HashSet.contains_insert, h, Bool.or_true]) l _ _
        Std.HashSet.contains_insert_self
    · exact foldl_insert_has l _ y h

/-- **An inductive references its constructors** (`Ix.graphConst`). -/
theorem refsOf_induct (iv : Ix.InductiveVal) {c : Ix.Name} (hc : c ∈ iv.ctors) :
    (refsOf (.inductInfo iv)).contains c = true := by
  unfold refsOf Ix.GraphM.run
  simp only [Ix.graphConst]
  generalize hS : Array.foldl (fun s n => if (n == iv.cnst.name) = true then s else Std.HashSet.insert s n)
      (Array.foldl (fun s n => Std.HashSet.insert s n) ∅ iv.ctors) iv.all = S
  have hcS : S.contains c = true := by
    rw [← hS, ← Array.foldl_toList]
    refine foldl_keep _ (fun s n y h => ?_) _ _ _ ?_
    · split
      · exact h
      · rw [Std.HashSet.contains_insert, h, Bool.or_true]
    · rw [← Array.foldl_toList]
      exact foldl_insert_has _ _ _ (Array.mem_toList_iff.mpr hc)
  change ((_ : Ix.Set Ix.Name) ∪ S).contains c = true
  rw [Std.HashSet.contains_union, hcS, Bool.or_true]

/-- A filtering fold keeps an element the filter does not drop. -/
theorem filterFold_keep {β : Type} {rs : Ix.Set Ix.Name} {U : Std.HashMap Ix.Name β} {r : Ix.Name} (hr : rs.contains r = true)
    (hu : U.contains r = false) :
    (rs.fold (init := ({} : Ix.Set Ix.Name)) fun s r => if U.contains r then s else s.insert r).contains r = true := by
  rw [Std.HashSet.fold_eq_foldl_toList]
  obtain ⟨r', hr', e⟩ := List.contains_iff_exists_mem_beq.mp
    (show rs.toList.contains r = true by rw [Std.HashSet.contains_toList]; exact hr)
  have keep := foldl_keep (fun s r => if U.contains r = true then s else s.insert r) (fun s n y h => by
    split
    · exact h
    · rw [Std.HashSet.contains_insert, h, Bool.or_true])
  suffices key : ∀ (l : List Ix.Name) (s : Ix.Set Ix.Name), r' ∈ l →
      (l.foldl (fun s r => if U.contains r = true then s else s.insert r) s).contains r = true from
    key _ _ hr'
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons y l ih =>
    intro s h
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine keep l _ r ?_
      have hu' : U.contains r' = false := by rw [← Std.HashMap.contains_congr e]; exact hu
      simp only [hu', Bool.false_eq_true, ↓reduceIte]
      rw [Std.HashSet.contains_insert, BEq.symm e, Bool.true_or]
    · exact ih _ h

/-- **The ground graph keeps a constant's references to grounded constants.** -/
theorem groundSplit_keep {env : Ix.Environment} {n r : Ix.Name} {rs rs₀ : Ix.Set Ix.Name}
    (h : (groundSplit env).1.get? n = some rs) (h₀ : (Ix.GraphM.envSerial env).get? n = some rs₀)
    (hr : rs₀.contains r = true) (hk : (groundSplit env).1.contains r = true) : rs.contains r = true := by
  unfold groundSplit at h hk
  dsimp only at h hk
  split at h
  · rw [h₀] at h
    cases h
    exact hr
  · rename_i hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hk
    generalize Ix.groundConsts _ _ = U at h hk
    rw [Std.HashMap.fold_eq_foldl_toList] at h hk
    have keys := Condense.foldl_inv (fun m : Ix.Map Ix.Name (Ix.Set Ix.Name) =>
        ∀ y, m.contains y = true → U.contains y = false) _ _ {}
      (fun y h => by simp at h) (fun m x _ hm y hy => by
        split at hy
        · exact hm y hy
        · rename_i hx
          rw [Std.HashMap.contains_insert] at hy
          rcases Bool.or_eq_true_iff.mp hy with e | hy
          · rw [← Std.HashMap.contains_congr e]
            simpa using hx
          · exact hm y hy) r hk
    have vals := Condense.foldl_inv (fun m : Ix.Map Ix.Name (Ix.Set Ix.Name) =>
        ∀ y v, m.get? y = some v → ∃ x ∈ (Ix.GraphM.envSerial env).toList, (x.1 == y) = true ∧
          v = (x.2.fold (init := ({} : Ix.Set Ix.Name)) fun s r => if U.contains r then s else s.insert r))
        _ _ {}
      (fun y v h => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
      (fun m x hx hm y v hy => by
        split at hy
        · exact hm y v hy
        · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hy
          split at hy
          · rename_i same
            cases hy
            exact ⟨x, hx, same, rfl⟩
          · rw [← Std.HashMap.get?_eq_getElem?] at hy
            exact hm y v hy) n rs h
    obtain ⟨x, hx, e, rfl⟩ := vals
    have hx₀ := Condense.get_of_mem_toList hx e
    rw [h₀] at hx₀
    cases hx₀
    exact filterFold_keep hr keys

/-- An edge of the condensation's graph: a reference of node `i`'s entry at node `j`. -/
theorem adjOf_of_mem {E : Array (Ix.Name × Ix.Set Ix.Name)} {I : Std.HashMap Ix.Name Nat} {i j : Nat}
    {ref : Ix.Name} (hi : i < E.size) (href : E[i].2.contains ref = true) (hj : I.get? ref = some j) :
    j ∈ (Condense.adjOf E I)[i]?.getD #[] := by
  unfold Condense.adjOf
  rw [Array.getElem?_map, Array.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some, Id.run, Std.HashSet.forIn_eq_forIn_toList]
  obtain ⟨r, hr, e⟩ := List.contains_iff_exists_mem_beq.mp
    (show E[i].2.toList.contains ref = true by rw [Std.HashSet.contains_toList]; exact href)
  have hjr : I.get? r = some j := by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr (BEq.symm e), ← Std.HashMap.get?_eq_getElem?]
    exact hj
  refine (forIn_grows (β := Nat) _ (fun (s : Array Nat) j => j ∈ s) (fun r j => I.get? r = some j)
    ?_ ?_ ?_ E[i].2.toList #[]).2 r hr j hjr
  · intro x s
    split <;> rfl
  · intro x s y h
    split
    · exact Array.mem_push.mpr (.inl h)
    · exact h
  · intro x s y h
    split
    · rename_i k hk
      rw [hk] at h
      cases h
      exact Array.mem_push.mpr (.inr rfl)
    · rename_i hk
      exact (hk y h).elim

/-- Every name of the graph has a position. -/
theorem nodesOf_idx (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) {k : Ix.Name} (hk : refs.contains k = true) :
    ∃ j, (Condense.nodesOf refs).2.get? k = some j := by
  have e : Condense.nodesOf refs = ((refs.toList.foldl Condense.nodeStep (#[], ∅, 0)).1,
      (refs.toList.foldl Condense.nodeStep (#[], ∅, 0)).2.1) := by
    unfold Condense.nodesOf
    simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  have grow : ∀ (l : List (Ix.Name × Ix.Set Ix.Name)) b,
      (∀ y, b.2.1.contains y = true → (l.foldl Condense.nodeStep b).2.1.contains y = true) ∧
      ∀ x ∈ l, (l.foldl Condense.nodeStep b).2.1.contains x.1 = true := by
    intro l
    induction l with
    | nil => intro b; exact ⟨fun _ h => h, fun _ h => by cases h⟩
    | cons a l ih =>
      intro b
      rw [List.foldl_cons]
      obtain ⟨g, a'⟩ := ih (Condense.nodeStep b a)
      refine ⟨fun y h => g y ?_, fun x hx => ?_⟩
      · show (b.2.1.insert a.1 b.1.size).contains y = true
        rw [Std.HashMap.contains_insert, h, Bool.or_true]
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact g _ (by show (b.2.1.insert x.1 b.1.size).contains x.1 = true; exact Std.HashMap.contains_insert_self)
        · exact a' x hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    (show (refs.get? k).isSome = true by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hk)
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hv
  obtain ⟨k', ek, hm⟩ := hv
  have hc := (grow refs.toList (#[], ∅, 0)).2 (k', v) hm
  rw [e]
  refine Option.isSome_iff_exists.mp ?_
  rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_congr ek]
  exact hc

/-- **An edge of the condensation's graph from a reference**: where node `u`'s entry
references a name of the graph at node `w`, the filtered graph has the edge `u → w`. -/
theorem edge_of_ref {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {u w : Nat} {x : Ix.Name}
    (hu : u < (Condense.nodesOf refs).1.size) (hw : w < (Condense.nodesOf refs).1.size)
    (hx : (Condense.nodesOf refs).1[u].2.contains x = true)
    (hxw : ((Condense.nodesOf refs).1[w].1 == x) = true) :
    Ix.CompileCert.Canon.Edge (Ix.CompileCert.Canon.filt (Condense.edgesOf refs)) u w := by
  have hkey : refs.contains x = true := by
    rw [← Std.HashMap.contains_congr hxw, Std.HashMap.contains_eq_isSome_getElem?,
      ← Std.HashMap.get?_eq_getElem?, Condense.node_get hw]
    rfl
  obtain ⟨j, hj⟩ := nodesOf_idx refs hkey
  obtain ⟨hj', hname⟩ := (Condense.nodesOf_spec refs).2 x j hj
  have hjw : j = w := Condense.namesOf_inj (by simpa [Condense.namesOf] using hj')
    (by simpa [Condense.namesOf] using hw)
    (by simp only [Condense.namesOf, Array.getElem_map]; exact BEq.trans hname (BEq.symm hxw))
  subst hjw
  refine Ix.CompileCert.Canon.edge_filt.mpr ⟨adjOf_of_mem hu hx hj, ?_⟩
  rw [← Condense.namesOf_size]
  simpa [Condense.namesOf] using hw

/-- **Two nodes on a cycle of two edges have the same representative.** -/
theorem root_of_cycle {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {u w : Nat}
    (hr : ∀ p ∈ (Condense.compsOf refs).comps.zip (Condense.compsOf refs).roots, p.2 < (Condense.namesOf refs).size)
    (hu : u < (Condense.namesOf refs).size) (hw : w < (Condense.namesOf refs).size)
    (e₁ : Ix.CompileCert.Canon.Edge (Ix.CompileCert.Canon.filt (Condense.edgesOf refs)) u w)
    (e₂ : Ix.CompileCert.Canon.Edge (Ix.CompileCert.Canon.filt (Condense.edgesOf refs)) w u) :
    (Condense.rootNames (Condense.namesOf refs) (Condense.compsOf refs) hr)[u] =
      (Condense.rootNames (Condense.namesOf refs) (Condense.compsOf refs) hr)[w] := by
  have hc := Condense.compsOf_eq refs
  obtain ⟨cm, hcm, hum, hwm⟩ := (Ix.CompileCert.Canon.condensation_scc hc u w).mpr
    ⟨by rw [← Condense.namesOf_size]; exact hu, by rw [← Condense.namesOf_size]; exact hw,
      .tail (.refl u) e₁, .tail (.refl w) e₂⟩
  obtain ⟨k, hk, ek⟩ := Array.mem_iff_getElem.mp hcm
  have hkr : k < (Condense.compsOf refs).roots.size := by
    rw [(CondenseRoots.condensation_roots_mem hc).1]; exact hk
  have hrn : (Condense.compsOf refs).roots[k] < (Condense.namesOf refs).size := by
    rw [Condense.namesOf_size]
    exact Ix.CompileCert.Canon.condensation_roots_lt hc (Array.getElem_mem hkr)
  have uniq := Ix.CompileCert.Canon.condensation_unique hc
  rw [Condense.rootNames_get uniq (by rw [Array.getElem?_eq_getElem hk, ek]) (Array.getElem?_eq_getElem hkr) hum hu hrn,
    Condense.rootNames_get uniq (by rw [Array.getElem?_eq_getElem hk, ek]) (Array.getElem?_eq_getElem hkr) hwm hw hrn]

/-- **A constructor an inductive lists is in the inductive's block**, in a compile that
returns. -/
theorem ctorsInBlock {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) {E : Ix.Environment}
    (hE : ∀ x, E.get? x = env.consts.get? x) :
    CtorsInBlock (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) E := by
  intro rep all I iv c hall hI hiv hc hmc
  rw [hE] at hiv
  obtain ⟨cv, hcv, hind⟩ := ctorsBelong h I iv hiv c hc
  obtain ⟨repc, allc, hrc, hcc⟩ := hmc
  generalize hrefs : (groundSplit { consts := env.consts }).1 = refs at hall hrc
  obtain ⟨hr, hv, e⟩ := Condense.blocks_eq refs
  rw [e] at hall hrc
  obtain ⟨_, _, hbI, hrepI, hnI⟩ := Condense.blocksOfDisc_mem hall hI
  obtain ⟨vI, hvI, rfl⟩ := Condense.discOf_get hbI
  obtain ⟨_, _, hbc, hrepc, hnc⟩ := Condense.blocksOfDisc_mem hrc hcc
  obtain ⟨vc, hvc, rfl⟩ := Condense.discOf_get hbc
  dsimp only at hrepI hnI hrepc hnc
  have hvI' : vI < (Condense.nodesOf refs).1.size := by simpa [Condense.namesOf] using hvI
  have hvc' : vc < (Condense.nodesOf refs).1.size := by simpa [Condense.namesOf] using hvc
  simp only [Condense.namesOf, Array.getElem_map] at hnI hnc
  -- the references of a node's entry, from the input
  have refsAt : ∀ (v : Nat) (hv : v < (Condense.nodesOf refs).1.size) (x : Ix.Name) (ci : Ix.ConstantInfo)
      (y : Ix.Name), ((Condense.nodesOf refs).1[v].1 == x) = true → env.consts.get? x = some ci →
      (refsOf ci).contains y = true → refs.contains y = true →
      (Condense.nodesOf refs).1[v].2.contains y = true := by
    intro v hv x ci y ex hx hy hky
    have hget' := Condense.node_get hv
    have hget : (groundSplit { consts := env.consts }).1.get? (Condense.nodesOf refs).1[v].1 =
        some (Condense.nodesOf refs).1[v].2 := by rw [hrefs]; exact hget'
    have hky' : (groundSplit { consts := env.consts }).1.contains y = true := by rw [hrefs]; exact hky
    obtain ⟨rs₀, h₀, -⟩ := Condense.groundSplit_get hget
    obtain ⟨ci', hci', rfl⟩ := Condense.envSerial_get h₀
    have : ci' = ci := by
      have e' : ({ consts := env.consts } : Ix.Environment).consts.get? (Condense.nodesOf refs).1[v].1 =
          env.consts.get? x := by
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr ex]
      rw [e', hx] at hci'
      exact (Option.some.inj hci').symm
    subst this
    exact groundSplit_keep hget h₀ hy hky'
  have keyOf : ∀ (v : Nat) (hv : v < (Condense.nodesOf refs).1.size) (x : Ix.Name),
      ((Condense.nodesOf refs).1[v].1 == x) = true → refs.contains x = true := by
    intro v hv x ex
    rw [← Std.HashMap.contains_congr ex, Std.HashMap.contains_eq_isSome_getElem?,
      ← Std.HashMap.get?_eq_getElem?, Condense.node_get hv]
    rfl
  have e₁ := edge_of_ref hvI' hvc' (refsAt vI hvI' I _ c hnI hiv (refsOf_induct iv hc) (keyOf vc hvc' c hnc)) hnc
  have hIc : (refsOf (.ctorInfo cv)).contains I = true := by
    rw [← Std.HashSet.contains_congr hind]; exact ClosureClaims.refsOf_ctor cv
  have e₂ := edge_of_ref hvc' hvI' (refsAt vc hvc' c _ I hnc hcv hIc (keyOf vI hvI' I hnI)) hnI
  have same := root_of_cycle hr hvI hvc e₁ e₂
  have hrr : (repc == rep) = true := BEq.trans (BEq.symm hrepc) (same ▸ hrepI)
  have hg : (Condense.blocksOfDisc (Condense.discOf (Condense.namesOf refs) (Condense.compsOf refs)
      (Condense.rootNames (Condense.namesOf refs) (Condense.compsOf refs) hr) hv)).get? repc =
      (Condense.blocksOfDisc (Condense.discOf (Condense.namesOf refs) (Condense.compsOf refs)
      (Condense.rootNames (Condense.namesOf refs) (Condense.compsOf refs) hr) hv)).get? rep := by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hrr]
  rw [hg, hall] at hrc
  cases hrc
  exact hcc

/-! ## The closure's claims, with fresh snapshots -/

/-- `ClosureClaims.compileReport_owned`, with the claim's block fresh at its snapshot,
given that an inductive's constructors are in its block. -/
theorem compileReport_owned_fresh_of {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {roots : List Ix.Name} {sub : Ix.Environment}
    (h : compileReport env = .ok (ixe, failures)) (hcl : IsClosure env roots sub)
    (nofail : NoFailure failures sub)
    (hctor : ∀ E : Ix.Environment, (∀ x, E.get? x = env.consts.get? x) →
      CtorsInBlock (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) E) :
    ∃ (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileUnchecked env = .ok (ixe, failures, cenv) ∧
      blocks = Ix.CondenseM.run (groundSplit { consts := env.consts }).1 ∧
      FoldRun { consts := env.consts } blocks cenv cenv₀ sched ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = false → (sub.consts.get? n).isSome = true →
        (ixe.named.get? n).map (·.addr) = some a ∧
        ∃ (snap : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult)
          (c : BlockState) (layout : Option Ixon.AuxLayout) (b : ByteArray),
          OnRun blocks sched (FoldState.init cenv₀ blocks sched) snap ∧
          blocks.blocks.get? rep = some all ∧
          Mono snap.cenv cenv ∧ (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
          runBlock snap.cenv all (blockKey rep all) = .ok (r, c, layout) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r ∧
          ixe.consts.get? a = some { buf := b, len := b.size } ∧
          BlockCompiled snap.cenv all (blockKey rep all) n a b ∧
          (∀ x, all.contains x = true → ∀ a', snap.cenv.nameToAddr.get? x = some a' →
            snap.cenv.auxNameToAddr.contains x = true) := by
  obtain ⟨cenv, hu, pub⟩ := Ix.Cert.resolvedPublished h
  obtain ⟨bytes, hf⟩ := compileUnchecked_fold hu
  have claimsAt : ∀ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState),
      (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched).acc.cenv.env =
        { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) } →
      WaveStart (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched
        (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched) st →
      ClaimsOwn (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched st := by
    intro cenv₀ sched st henv hst x hx n a b hclaim hm
    have he := (reach_env (waveStart_reach hst)).trans henv
    have hE : ∀ y, st.acc.cenv.env.get? y = env.consts.get? y := fun y => by
      rw [he, ClosureClaims.view_get, ClosureClaims.input_get]
    have hnamed : Ix.Cert.Claims.NamedEnv st.acc.cenv.env := by
      rw [he]
      exact ClosureClaims.namedEnv_view h
    obtain ⟨-, hall, hkey, -⟩ := hx
    rw [hkey] at hclaim
    exact claims_members hnamed (hctor _ hE) hall (Condense.condense_nonempty hall) hclaim hm
  obtain ⟨cenv₀, sched, hrun, henv, prov⟩ :=
    compileEnvFold_provenanceFresh hf (disjoint_run _) claimsAt
  refine ⟨cenv, _, cenv₀, sched, hu, rfl, hrun, fun n a hn hnaux hs => ⟨pub n a hn, ?_⟩⟩
  rcases prov n a hn with hx | ⟨b, hc, hb⟩
  · rw [hnaux] at hx; cases hx
  obtain ⟨snap, pre, rep, all, hrun_snap, -, hm, hall, hpost, hclaim, fresh⟩ := hc
  have hsnap := onRun_reach hrun_snap
  have hE : ∀ x, snap.cenv.env.get? x = env.consts.get? x := fun x => by
    rw [reach_env hsnap, henv, ClosureClaims.view_get, ClosureClaims.input_get]
  have hnamed : Ix.Cert.Claims.NamedEnv snap.cenv.env := by
    rw [reach_env hsnap, henv]
    exact ClosureClaims.namedEnv_view h
  have hfinal : Mono snap.cenv cenv := hm.trans ((applyAuxBlockOutcome_mono _ _ _ _).trans hpost)
  generalize ho : auxBlockOutcome snap.cenv (blockKey rep all) all = o at hclaim hpost
  cases o with
  | compiled r c =>
    obtain ⟨layout, hr⟩ := auxBlockOutcome_compiled ho
    obtain ⟨m, hmA, hms⟩ : ∃ m, all.contains m = true ∧ ClosureClaims.InSub sub m := by
      rcases ClosureClaims.claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact ⟨_, blockKey_mem (Condense.condense_nonempty hall), e ▸ hs⟩
      · obtain ⟨m, hm, hms, -⟩ := ClosureClaims.owned_sub h hcl hE (e ▸ hs)
          (Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
        exact ⟨m, hm, hms⟩
    have hsub : ∀ x, all.contains x = true → ClosureClaims.InSub sub x := fun x hx =>
      Condense.closure_path hcl (Condense.condense_scc hall hmA hx) hms
    exact ⟨snap, rep, all, r, c, layout, b, hrun_snap, hall, hfinal, hsub, hr, hclaim, hb,
      runBlock_compiled hr hclaim, fresh⟩
  | promoted cs cn cf im na nf =>
    rcases cs with _ | ⟨clo, r, c⟩
    · exact False.elim hclaim
    · exfalso
      obtain ⟨layout, hclo, hr⟩ := ClosureClaims.auxBlockOutcome_cross_names ho
      have marks : ∀ y ∈ cn, ClosureClaims.ExtraOrFail cenv y := fun y hy =>
        (ClosureClaims.applyAuxBlockOutcome_cross_extras pre _ all clo r c cn cf im na nf hy).mono hpost
      refine ClosureClaims.cross_refuted h hu hcl nofail hE marks hn hnaux hs ?_
      rcases ClosureClaims.claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact .inl (e ▸ hclo)
      · exact .inr (e ▸ Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
  | failed msg => exact False.elim hclaim

end Ix.Cert.FreshSnapshot

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Compile.ExactKey (ExactName)

/-- **The closure's claims, with fresh snapshots**: `ClosureClaims.compileReport_owned`, and
a member of the claim's block is resolved at the block's snapshot (the start of the wave
that applied it) only through the aux map. -/
theorem Ix.Cert.compileReport_owned_fresh {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {roots : List Ix.Name} {sub : Ix.Environment}
    (h : compileReport env = .ok (ixe, failures)) (hcl : IsClosure env roots sub)
    (nofail : NoFailure failures sub) :
    ∃ (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileUnchecked env = .ok (ixe, failures, cenv) ∧
      blocks = Ix.CondenseM.run (groundSplit { consts := env.consts }).1 ∧
      FoldRun { consts := env.consts } blocks cenv cenv₀ sched ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = false → (sub.consts.get? n).isSome = true →
        (ixe.named.get? n).map (·.addr) = some a ∧
        ∃ (snap : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult)
          (c : BlockState) (layout : Option Ixon.AuxLayout) (b : ByteArray),
          OnRun blocks sched (FoldState.init cenv₀ blocks sched) snap ∧
          blocks.blocks.get? rep = some all ∧
          Mono snap.cenv cenv ∧ (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
          runBlock snap.cenv all (blockKey rep all) = .ok (r, c, layout) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r ∧
          ixe.consts.get? a = some { buf := b, len := b.size } ∧
          BlockCompiled snap.cenv all (blockKey rep all) n a b ∧
          (∀ x, all.contains x = true → ∀ a', snap.cenv.nameToAddr.get? x = some a' →
            snap.cenv.auxNameToAddr.contains x = true) :=
  FreshSnapshot.compileReport_owned_fresh_of h hcl nofail fun _ hE => FreshSnapshot.ctorsInBlock h hE

/-- info: 'Ix.Cert.compileReport_owned_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.compileReport_owned_fresh
