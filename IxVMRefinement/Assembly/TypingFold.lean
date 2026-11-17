/-! # A fold over units ordered by rank

The typing theorem installs the constants of a run unit by unit. A unit owns some addresses
and needs others. This module proves the one fact about the order: if every address a unit
needs is stored at the start, owned by the unit itself, or owned by a unit of strictly smaller
rank, then every unit can be stepped at a state in which what it needs is stored and what it
owns is not, and the final state stores what every unit owns.

The lemma knows nothing of records, checks or environments. A `UnitFold` names a state, an
invariant, an extension order, what is stored, what a unit owns and needs, its rank, and a
postcondition per unit that extension keeps. `UnitFold.run` takes a step for each unit as a
hypothesis: from the invariant, with the unit's needs stored and its own addresses fresh, to
a state that keeps the invariant, stores the unit's addresses and nothing else, and
establishes its postcondition.

No order on the list of units is assumed, and the list is not sorted: the proof runs through
the ranks from zero, and within a rank through the list. A unit met twice is stepped once.

`toy_run` is an instance with every hypothesis discharged: three units on the addresses
`0`, `1`, `2`, listed out of order, over a start state that stores the address `7`. Its
invariant (the stored addresses are distinct and closed under the needs) holds after a step
only because the fold steps a unit when its needs are stored and its address is fresh.
-/

namespace IxVM.Refinement.Typing

universe u v w

/-- **A system of units to fold**: a state with an invariant and an extension order, the
addresses a state stores, the addresses a unit owns and needs, a unit's rank, and a
postcondition per unit. Extension is reflexive and transitive and keeps what is stored and
every postcondition. -/
structure UnitFold (σ : Type u) (α : Type v) (κ : Type w) where
  /-- The invariant of a state. -/
  Inv : σ → Prop
  /-- The second state extends the first. -/
  Ext : σ → σ → Prop
  /-- The state stores the address. -/
  Stored : σ → κ → Prop
  /-- What the fold establishes of a unit. -/
  Post : α → σ → Prop
  /-- The unit stores the address. -/
  owns : α → κ → Prop
  /-- The unit's step reads the address. -/
  needs : α → κ → Prop
  /-- The unit's position. -/
  rank : α → Nat
  ext_refl : ∀ s, Ext s s
  ext_trans : ∀ {s₁ s₂ s₃ : σ}, Ext s₁ s₂ → Ext s₂ s₃ → Ext s₁ s₃
  stored_mono : ∀ {s s' : σ} (x : κ), Ext s s' → Stored s x → Stored s' x
  post_mono : ∀ {s s' : σ} (a : α), Ext s s' → Post a s → Post a s'

namespace UnitFold

variable {σ : Type u} {α : Type v} {κ : Type w}

/-- Some rank is above the rank of every unit of a list. -/
theorem exists_rank_bound (rank : α → Nat) (us : List α) : ∃ N, ∀ a ∈ us, rank a < N := by
  induction us with
  | nil => exact ⟨0, fun _ h => nomatch h⟩
  | cons b us ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + rank b + 1, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with h | h
    · rw [h]
      omega
    · have := hN a h
      omega

/-- **The fold's running invariant**: the state `s` extends the start, keeps the invariant,
and the units of `D` are done: each is a unit of the list, its addresses are stored and its
postcondition holds; and nothing is stored but what the start stored and what a done unit
owns. -/
def Running (F : UnitFold σ α κ) (s₀ : σ) (us : List α) (s : σ) (D : α → Prop) : Prop :=
  F.Inv s ∧ F.Ext s₀ s ∧
    (∀ a, D a → a ∈ us ∧ (∀ x, F.owns a x → F.Stored s x) ∧ F.Post a s) ∧
    ∀ x, F.Stored s x → F.Stored s₀ x ∨ ∃ a, D a ∧ F.owns a x

/-- The step hypothesis of the fold: a unit of the list steps from any state that extends
the start, keeps the invariant, stores what the unit needs outside itself and stores nothing
the unit owns. The step keeps the invariant, extends the state, stores what the unit owns,
establishes its postcondition, and stores nothing else. -/
def Steps (F : UnitFold σ α κ) (s₀ : σ) (us : List α) : Prop :=
  ∀ s, ∀ a ∈ us, F.Inv s → F.Ext s₀ s →
    (∀ x, F.needs a x → F.Stored s x ∨ F.owns a x) →
    (∀ x, F.owns a x → ¬ F.Stored s x) →
    ∃ s', F.Inv s' ∧ F.Ext s s' ∧ (∀ x, F.owns a x → F.Stored s' x) ∧ F.Post a s' ∧
      ∀ x, F.Stored s' x → F.Stored s x ∨ F.owns a x

/-- Distinct units of the list own no address in common. -/
def OwnsApart (F : UnitFold σ α κ) (us : List α) : Prop :=
  ∀ a ∈ us, ∀ b ∈ us, ∀ x, F.owns a x → F.owns b x → a = b

/-- The start stores nothing a unit of the list owns. -/
def FreshAt (F : UnitFold σ α κ) (s₀ : σ) (us : List α) : Prop :=
  ∀ a ∈ us, ∀ x, F.owns a x → ¬ F.Stored s₀ x

/-- **The order condition**: an address a unit needs is stored at the start, owned by the
unit, or owned by a unit of strictly smaller rank. -/
def NeedsEarlier (F : UnitFold σ α κ) (s₀ : σ) (us : List α) : Prop :=
  ∀ a ∈ us, ∀ x, F.needs a x →
    F.Stored s₀ x ∨ F.owns a x ∨ ∃ b ∈ us, F.owns b x ∧ F.rank b < F.rank a

/-- The units of rank `n` in a part of the list, after the units of smaller rank. -/
theorem run_rank (F : UnitFold σ α κ) {s₀ : σ} {us : List α} (hown : F.OwnsApart us)
    (hfresh : F.FreshAt s₀ us) (hneeds : F.NeedsEarlier s₀ us) (hstep : F.Steps s₀ us)
    (n : Nat) (l : List α) (hl : ∀ a ∈ l, a ∈ us)
    (hstart : ∃ s D, F.Running s₀ us s D ∧ ∀ a ∈ us, F.rank a < n → D a) :
    ∃ s D, F.Running s₀ us s D ∧ (∀ a ∈ us, F.rank a < n → D a) ∧
      ∀ a ∈ l, F.rank a = n → D a := by
  induction l with
  | nil =>
    obtain ⟨s, D, hr, hlt⟩ := hstart
    exact ⟨s, D, hr, hlt, fun _ h => nomatch h⟩
  | cons b l ih =>
    obtain ⟨s, D, hr, hlt, heq⟩ := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    have hb : b ∈ us := hl b (List.mem_cons.mpr (Or.inl rfl))
    by_cases hD : D b
    · refine ⟨s, D, hr, hlt, fun a ha han => ?_⟩
      rcases List.mem_cons.mp ha with h | h
      · rw [h]
        exact hD
      · exact heq a h han
    · by_cases hn : F.rank b = n
      · obtain ⟨hinv, hext, hdone, hframe⟩ := hr
        have hneed : ∀ x, F.needs b x → F.Stored s x ∨ F.owns b x := by
          intro x hx
          rcases hneeds b hb x hx with h0 | hself | ⟨c, hc, hcx, hcr⟩
          · exact Or.inl (F.stored_mono x hext h0)
          · exact Or.inr hself
          · have hcn : F.rank c < n := by omega
            exact Or.inl ((hdone c (hlt c hc hcn)).2.1 x hcx)
        have hfr : ∀ x, F.owns b x → ¬ F.Stored s x := by
          intro x hx hst
          rcases hframe x hst with h0 | ⟨c, hDc, hcx⟩
          · exact hfresh b hb x hx h0
          · have hbc : b = c := hown b hb c (hdone c hDc).1 x hx hcx
            rw [← hbc] at hDc
            exact hD hDc
        obtain ⟨s', hinv', hext', hown', hpost', hframe'⟩ := hstep s b hb hinv hext hneed hfr
        refine ⟨s', fun a => D a ∨ a = b, ⟨hinv', F.ext_trans hext hext', ?_, ?_⟩, ?_, ?_⟩
        · intro a ha
          rcases ha with ha | ha
          · obtain ⟨h1, h2, h3⟩ := hdone a ha
            exact ⟨h1, fun x hx => F.stored_mono x hext' (h2 x hx), F.post_mono a hext' h3⟩
          · rw [ha]
            exact ⟨hb, hown', hpost'⟩
        · intro x hx
          rcases hframe' x hx with h | h
          · rcases hframe x h with h0 | ⟨c, hDc, hcx⟩
            · exact Or.inl h0
            · exact Or.inr ⟨c, Or.inl hDc, hcx⟩
          · exact Or.inr ⟨b, Or.inr rfl, h⟩
        · exact fun a ha han => Or.inl (hlt a ha han)
        · intro a ha han
          rcases List.mem_cons.mp ha with h | h
          · exact Or.inr h
          · exact Or.inl (heq a h han)
      · refine ⟨s, D, hr, hlt, fun a ha han => ?_⟩
        rcases List.mem_cons.mp ha with h | h
        · rw [h] at han
          exact absurd han hn
        · exact heq a h han

/-- The units of rank below `n`. -/
theorem run_below (F : UnitFold σ α κ) {s₀ : σ} {us : List α} (h₀ : F.Inv s₀)
    (hown : F.OwnsApart us) (hfresh : F.FreshAt s₀ us) (hneeds : F.NeedsEarlier s₀ us)
    (hstep : F.Steps s₀ us) (n : Nat) :
    ∃ s D, F.Running s₀ us s D ∧ ∀ a ∈ us, F.rank a < n → D a := by
  induction n with
  | zero =>
    exact ⟨s₀, fun _ => False,
      ⟨h₀, F.ext_refl s₀, fun _ h => h.elim, fun _ hx => Or.inl hx⟩,
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨s, D, hr, hlt, heq⟩ :=
      F.run_rank hown hfresh hneeds hstep n us (fun _ h => h) ih
    refine ⟨s, D, hr, fun a ha han => ?_⟩
    rcases Nat.lt_or_ge (F.rank a) n with h | h
    · exact hlt a ha h
    · have he : F.rank a = n := by omega
      exact heq a ha he

/-- **The fold.** From a start state with the invariant, for a list of units that own
disjoint addresses, none stored at the start, whose needs are stored at the start, their own,
or owned by a unit of strictly smaller rank (`NeedsEarlier`), and that can each be stepped
(`Steps`): some state extends the start, keeps the invariant, stores what every unit owns,
satisfies every unit's postcondition, and stores nothing but what the start stored and what
a unit owns. -/
theorem run (F : UnitFold σ α κ) {s₀ : σ} {us : List α} (h₀ : F.Inv s₀)
    (hown : F.OwnsApart us) (hfresh : F.FreshAt s₀ us) (hneeds : F.NeedsEarlier s₀ us)
    (hstep : F.Steps s₀ us) :
    ∃ s, F.Inv s ∧ F.Ext s₀ s ∧
      (∀ a ∈ us, (∀ x, F.owns a x → F.Stored s x) ∧ F.Post a s) ∧
      ∀ x, F.Stored s x → F.Stored s₀ x ∨ ∃ a ∈ us, F.owns a x := by
  obtain ⟨N, hN⟩ := exists_rank_bound F.rank us
  obtain ⟨s, D, ⟨hinv, hext, hdone, hframe⟩, hlt⟩ := F.run_below h₀ hown hfresh hneeds hstep N
  refine ⟨s, hinv, hext, fun a ha => (hdone a (hlt a ha (hN a ha))).2, fun x hx => ?_⟩
  rcases hframe x hx with h | ⟨a, hDa, hax⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, (hdone a hDa).1, hax⟩

end UnitFold

/-! ## A toy instance

Addresses are naturals. Unit `a` owns the address `a` and needs the addresses `toyNeeds a`:
unit `1` needs `0` and the address `7` the start stores; unit `2` needs `1`, `0` and itself.
The state is the list of stored addresses. Its invariant is that they are distinct and closed
under the needs, which a step keeps only if the unit's needs are stored and its address is
not. The units are listed as `2, 0, 1`. -/

/-- The addresses a toy unit needs. -/
def toyNeeds : Nat → List Nat
  | 1 => [0, 7]
  | 2 => [1, 2, 0]
  | _ => []

/-- The toy system. -/
def toyFold : UnitFold (List Nat) Nat Nat where
  Inv := fun s => s.Nodup ∧ ∀ a ∈ s, ∀ x ∈ toyNeeds a, x ∈ s
  Ext := fun s s' => ∀ x ∈ s, x ∈ s'
  Stored := fun s x => x ∈ s
  Post := fun a s => a ∈ s
  owns := fun a x => x = a
  needs := fun a x => x ∈ toyNeeds a
  rank := fun a => a
  ext_refl := fun _ _ h => h
  ext_trans := fun h₁ h₂ x hx => h₂ x (h₁ x hx)
  stored_mono := fun x h hx => h x hx
  post_mono := fun a h ha => h a ha

/-- A toy unit steps by storing its address. -/
theorem toy_steps : toyFold.Steps [7] [2, 0, 1] := by
  intro s a _ hinv _ hneed hfr
  have hfresh : a ∉ s := hfr a rfl
  refine ⟨a :: s, ⟨List.nodup_cons.mpr ⟨hfresh, hinv.1⟩, ?_⟩,
    fun x hx => List.mem_cons_of_mem _ hx, ?_, List.mem_cons.mpr (Or.inl rfl), ?_⟩
  · intro b hb x hx
    rcases List.mem_cons.mp hb with h | h
    · rw [h] at hx
      rcases hneed x hx with h1 | h1
      · exact List.mem_cons_of_mem _ h1
      · exact List.mem_cons.mpr (Or.inl h1)
    · exact List.mem_cons_of_mem _ (hinv.2 b h x hx)
  · intro x hx
    exact List.mem_cons.mpr (Or.inl hx)
  · intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- The start state of the toy keeps the invariant. -/
theorem toy_start : toyFold.Inv [7] := by
  have hclosed : ∀ a ∈ [7], ∀ x ∈ toyNeeds a, x ∈ [7] := by decide
  exact ⟨List.nodup_cons.mpr ⟨(fun h => nomatch h), List.nodup_nil⟩, hclosed⟩

/-- The toy units need only what the start stores, themselves, or a unit of smaller rank. -/
theorem toy_needs : toyFold.NeedsEarlier [7] [2, 0, 1] := by
  have h : ∀ a ∈ [2, 0, 1], ∀ x ∈ toyNeeds a,
      x ∈ [7] ∨ x = a ∨ ∃ b ∈ [2, 0, 1], x = b ∧ b < a := by decide
  exact fun a ha x hx => h a ha x hx

/-- No toy unit's address is stored at the start. -/
theorem toy_fresh : toyFold.FreshAt [7] [2, 0, 1] := by
  have h : ∀ a ∈ [2, 0, 1], a ∉ [7] := by decide
  intro a ha x hx hst
  have hx' : x = a := hx
  rw [hx'] at hst
  exact h a ha hst

/-- **The fold on the toy**, with no hypothesis left: some list of distinct addresses, closed
under the needs, holds `7`, `0`, `1` and `2` and nothing else. -/
theorem toy_run : ∃ s : List Nat, s.Nodup ∧ (∀ a ∈ s, ∀ x ∈ toyNeeds a, x ∈ s) ∧
    7 ∈ s ∧ 0 ∈ s ∧ 1 ∈ s ∧ 2 ∈ s ∧ ∀ x ∈ s, x = 7 ∨ x = 2 ∨ x = 0 ∨ x = 1 := by
  have hown : toyFold.OwnsApart [2, 0, 1] := by
    intro a _ b _ x ha hb
    have ha' : x = a := ha
    have hb' : x = b := hb
    exact ha'.symm.trans hb'
  obtain ⟨s, hinv, hext, hdone, hframe⟩ :=
    toyFold.run toy_start hown toy_fresh toy_needs toy_steps
  have hmem : ∀ a ∈ [2, 0, 1], a ∈ s := fun a ha => (hdone a ha).2
  refine ⟨s, hinv.1, hinv.2, hext 7 (List.mem_singleton.mpr rfl), hmem 0 (by decide),
    hmem 1 (by decide), hmem 2 (by decide), fun x hx => ?_⟩
  rcases hframe x hx with h | ⟨a, ha, hax⟩
  · exact Or.inl (List.mem_singleton.mp h)
  · have hx' : x = a := hax
    rw [hx']
    have hcases : ∀ b ∈ [2, 0, 1], b = 2 ∨ b = 0 ∨ b = 1 := by decide
    exact Or.inr (hcases a ha)

end IxVM.Refinement.Typing
