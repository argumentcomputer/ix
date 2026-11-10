import IxCC.Lam.Erase
import IxCC.Src.Proof.NatMap
import IxCC.Lam.Erase.Proof.Rel

/-! # Reasoning about the erasure monad

Erasure runs in `StateT St (Except EraseError)`. Its key table only grows:
a key, once given an id, keeps it. So a result can be specified against
any key relation `G` that contains the table at the end of the run
(`Sound x Q`): every id erasure hands out for a key is related to it by
`G`, whatever keys are added later. The combinators follow the monad's
`pure`, `bind`, `throw`, conditionals and `mapM`. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels NatMap)

/-- The id a key has in the erasure state. -/
def keyOf (s : St) (key : Key.GKey) : Option GlobalId :=
  ((s.ids.get? key.bucket).getD []).lookup key

/-- The ids lie below `next`, and each names one key. -/
def IdsOk (s : St) : Prop :=
  (∀ key g, keyOf s key = some g → g < s.next) ∧
    ∀ key key' g, keyOf s key = some g → keyOf s key' = some g → key = key'

/-- The key table only grows, new keys join the back of the queue, the
front of the queue and the erased globals stay, and ids stay unique. -/
structure Grows (s s' : St) : Prop where
  keys : ∀ key g, keyOf s key = some g → keyOf s' key = some g
  front : s'.front = s.front
  globals : s'.globals = s.globals
  back : ∀ p ∈ s.back, p ∈ s'.back
  fresh : ∀ key g, keyOf s' key = some g → keyOf s key = some g ∨ (key, g) ∈ s'.back
  ids : IdsOk s → IdsOk s'
  backKeys : ∀ p ∈ s'.back, p ∈ s.back ∨ keyOf s' p.1 = some p.2

theorem Grows.refl (s : St) : Grows s s :=
  ⟨fun _ _ h => h, rfl, rfl, fun _ h => h, fun _ _ h => .inl h, id, fun _ h => .inl h⟩

theorem Grows.trans {s₁ s₂ s₃ : St} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ where
  keys key g h := h₂.keys key g (h₁.keys key g h)
  front := h₂.front.trans h₁.front
  globals := h₂.globals.trans h₁.globals
  back p hp := h₂.back p (h₁.back p hp)
  fresh key g h := (h₂.fresh key g h).elim
    (fun h' => (h₁.fresh key g h').elim .inl fun hb => .inr (h₂.back _ hb)) .inr
  ids h := h₂.ids (h₁.ids h)
  backKeys p hp := (h₂.backKeys p hp).elim
    (fun h' => (h₁.backKeys p h').elim .inl fun hk => .inr (h₂.keys _ _ hk)) .inr

/-- A step that keeps the table, the queue, the globals and `next`. -/
theorem Grows.frame {s s' : St} (hids : s'.ids = s.ids) (hn : s'.next = s.next)
    (hf : s'.front = s.front) (hb : s'.back = s.back) (hg : s'.globals = s.globals) :
    Grows s s' where
  keys key g h := by unfold keyOf at h ⊢; rw [hids]; exact h
  front := hf
  globals := hg
  back p hp := by rw [hb]; exact hp
  fresh key g h := .inl (by unfold keyOf at h ⊢; rw [← hids]; exact h)
  ids h := by
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨fun key g hk => ?_, fun key key' g hk hk' => ?_⟩
    · unfold keyOf at hk; rw [hids] at hk; rw [hn]; exact h₁ key g hk
    · unfold keyOf at hk hk'; rw [hids] at hk hk'; exact h₂ key key' g hk hk'
  backKeys p hp := .inl (by rw [← hb]; exact hp)

/-- A key relation containing the state's table. -/
def Covers (G : Key.GKey → GlobalId → Prop) (s : St) : Prop :=
  ∀ key g, keyOf s key = some g → G key g

theorem Covers.of_grows {G : Key.GKey → GlobalId → Prop} {s s' : St} (h : Covers G s')
    (hg : Grows s s') : Covers G s := fun key g hk => h key g (hg.keys key g hk)

/-- `x` succeeds only growing the key table, with `Q` of its result under
every key relation that contains the final table. -/
def Sound {α : Type} (x : M α) (Q : α → (Key.GKey → GlobalId → Prop) → Prop) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → Grows s s' ∧ ∀ G, Covers G s' → Q a G

namespace Sound

variable {α β : Type} {Q Q' : α → (Key.GKey → GlobalId → Prop) → Prop}

theorem imp {x : M α} (h : Sound x Q) (hq : ∀ a G, Q a G → Q' a G) : Sound x Q' :=
  fun s a s' e => ⟨(h s a s' e).1, fun G hG => hq a G ((h s a s' e).2 G hG)⟩

theorem pure {a : α} (h : ∀ G, Q a G) : Sound (Pure.pure a : M α) Q := fun s b s' e => by
  simp only [StateT.run_pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Grows.refl _, fun G _ => h G⟩

theorem bind_run {x : M α} {f : α → M β} {s : St} {b : β} {s'' : St}
    (e : (x >>= f).run s = .ok (b, s'')) :
    ∃ a s', x.run s = .ok (a, s') ∧ (f a).run s' = .ok (b, s'') := by
  rw [StateT.run_bind] at e
  cases hx : x.run s with
  | error err => rw [hx] at e; cases e
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hx] at e
    exact ⟨a, s', rfl, e⟩

theorem bind {Q₁ : α → (Key.GKey → GlobalId → Prop) → Prop}
    {Q : β → (Key.GKey → GlobalId → Prop) → Prop} {x : M α} {f : α → M β} (hx : Sound x Q₁)
    (hf : ∀ a, Sound (f a) fun b G => Q₁ a G → Q b G) : Sound (x >>= f) Q := by
  intro s b s'' e
  obtain ⟨a, s', ex, ef⟩ := bind_run e
  obtain ⟨g₁, h₁⟩ := hx s a s' ex
  obtain ⟨g₂, h₂⟩ := hf a s' b s'' ef
  exact ⟨g₁.trans g₂, fun G hG => h₂ G hG (h₁ G (hG.of_grows g₂))⟩

theorem throw {e : EraseError} : Sound (MonadExcept.throw e : M α) Q := fun s a s' h => by
  simp [MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift,
    ExceptT.lift] at h
  cases h

theorem decline {code message : String} {c : Option CId} :
    Sound (Erase.decline code message c : M α) Q := by
  unfold Erase.decline
  exact bind (Q₁ := fun _ _ => True) (fun s a s' e => by
      simp only [StateT.run_get, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨Grows.refl _, fun _ _ => trivial⟩)
    fun _ => throw

theorem ite {c : Prop} [Decidable c] {x y : M α} (h₁ : c → Sound x Q) (h₂ : ¬ c → Sound y Q) :
    Sound (if c then x else y) Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

/-- `unless c do decline …`: afterwards `c` holds. -/
theorem unless_decline {c : Bool} {code message : String} {k : Option CId} :
    Sound (if c then Pure.pure PUnit.unit else Erase.decline code message k : M Unit)
      fun _ _ => c = true := by
  cases c with
  | true => exact pure fun _ => rfl
  | false => exact decline

theorem mapM {γ : Type} {f : γ → M β} {P : γ → β → (Key.GKey → GlobalId → Prop) → Prop} :
    ∀ {xs : List γ}, (∀ x ∈ xs, Sound (f x) (P x)) →
      Sound (xs.mapM f) fun ys G => Forall2 (fun x y => P x y G) xs ys
  | [], _ => pure fun _ => .nil
  | x :: xs, h => by
    rw [List.mapM_cons]
    exact bind (h x List.mem_cons_self) fun y =>
      bind (mapM fun z hz => h z (List.mem_cons_of_mem _ hz)) fun ys =>
        pure fun G hys hy => .cons hy hys

end Sound

/-! ## The key table -/

theorem keyOf_globalId_new (s : St) (key : Key.GKey) (key' : Key.GKey)
    (hnone : ((s.ids.get? key.bucket).getD []).lookup key = none) :
    keyOf { s with ids := s.ids.insert key.bucket ((key, s.next) :: (s.ids.get? key.bucket).getD []),
                   next := s.next + 1, back := (key, s.next) :: s.back } key' =
      if key' = key then some s.next else keyOf s key' := by
  unfold keyOf
  dsimp only
  rw [NatMap.get?_insert]
  by_cases hb : key'.bucket = key.bucket
  · simp only [hb, ↓reduceIte, Option.getD_some, List.lookup]
    by_cases hk : key' = key
    · subst hk; simp
    · have : (key' == key) = false := beq_false_of_ne hk
      simp [this, hk]
  · have hk : key' ≠ key := fun e => hb (by rw [e])
    simp [hb, hk]

theorem sound_globalId (key : Key.GKey) :
    Sound (globalId key) fun g G => G key g := by
  intro s g s' e
  unfold globalId at e
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at e
  cases hl : ((s.ids.get? key.bucket).getD []).lookup key with
  | some g₀ =>
    rw [hl] at e
    simp only [StateT.run_pure] at e
    cases e
    exact ⟨Grows.refl _, fun G hG => hG key _ hl⟩
  | none =>
    rw [hl] at e
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] at e
    cases e
    have hnew := fun key' => keyOf_globalId_new s key key' hl
    have hold : ∀ key' g', keyOf s key' = some g' → key' ≠ key := fun key' g' hk e => by
      subst e
      unfold keyOf at hk
      rw [hl] at hk
      cases hk
    refine ⟨⟨fun key' g' hk => ?_, rfl, rfl, fun p hp => List.mem_cons_of_mem _ hp,
      fun key' g' hk => ?_, fun ⟨h₁, h₂⟩ => ⟨fun key' g' hk => ?_, fun k₁ k₂ g' hk₁ hk₂ => ?_⟩,
      fun p hp => ?_⟩,
      fun G hG => hG key _ ?_⟩
    · rw [hnew key']
      simp [hold key' g' hk, hk]
    · rw [hnew key'] at hk
      by_cases e : key' = key
      · subst e
        simp only [↓reduceIte, Option.some.injEq] at hk
        subst hk
        exact .inr List.mem_cons_self
      · simp only [e, ↓reduceIte] at hk
        exact .inl hk
    · show g' < s.next + 1
      rw [hnew key'] at hk
      by_cases e : key' = key
      · subst e
        have hk' : s.next = g' := by simpa using hk
        exact hk' ▸ Nat.lt_succ_self _
      · have hk' : keyOf s key' = some g' := by simpa [e] using hk
        have := h₁ key' g' hk'
        exact Nat.lt_succ_of_lt this
    · rw [hnew k₁] at hk₁
      rw [hnew k₂] at hk₂
      by_cases e₁ : k₁ = key <;> by_cases e₂ : k₂ = key
      · rw [e₁, e₂]
      · subst e₁
        have h₁' : s.next = g' := by simpa using hk₁
        have h₂' : keyOf s k₂ = some g' := by simpa [e₂] using hk₂
        have := h₁ k₂ g' h₂'
        exact absurd (h₁' ▸ this) (Nat.lt_irrefl _)
      · subst e₂
        have h₂' : s.next = g' := by simpa using hk₂
        have h₁' : keyOf s k₁ = some g' := by simpa [e₁] using hk₁
        have := h₁ k₁ g' h₁'
        exact absurd (h₂' ▸ this) (Nat.lt_irrefl _)
      · have h₁' : keyOf s k₁ = some g' := by simpa [e₁] using hk₁
        have h₂' : keyOf s k₂ = some g' := by simpa [e₂] using hk₂
        exact h₂ k₁ k₂ g' h₁' h₂'
    · rcases List.mem_cons.1 hp with rfl | hp
      · refine .inr ?_
        rw [hnew key]
        simp
      · exact .inl hp
    · rw [hnew key]
      simp

/-- Reading the state: the continuation runs from the state it read. -/
theorem Sound.get_bind {α : Type} {f : St → M α} {Q : α → (Key.GKey → GlobalId → Prop) → Prop}
    (h : ∀ s a s', (f s).run s = .ok (a, s') → Grows s s' ∧ ∀ G, Covers G s' → Q a G) :
    Sound (MonadState.get >>= f) Q := by
  intro s a s' e
  rw [StateT.run_bind] at e
  simp only [StateT.run_get, pure_bind] at e
  exact h s a s' e

theorem sound_registerCtor (c : CId) (tag arity : Nat) :
    Sound (registerCtor c tag arity) fun _ _ => True := by
  unfold registerCtor
  refine Sound.get_bind fun s₀ a s' e => ?_
  cases h : s₀.ctors.get? c with
  | some info =>
    rw [h] at e
    exact Sound.ite (Q := fun _ _ => True) (fun _ => Sound.pure fun _ => trivial)
      (fun _ => Sound.decline) s₀ a s' e
  | none =>
    rw [h] at e
    simp only [StateT.run_set] at e
    cases e
    exact ⟨Grows.frame rfl rfl rfl rfl rfl, fun _ _ => trivial⟩

theorem Sound.forIn_unit {γ : Type} {f : γ → PUnit → M (ForInStep PUnit)} :
    ∀ {xs : List γ}, (∀ x ∈ xs, ∀ u, Sound (f x u) fun _ _ => True) →
      Sound (forIn xs PUnit.unit f) fun _ _ => True
  | [], _ => Sound.pure fun _ => trivial
  | x :: xs, h => by
    rw [List.forIn_cons]
    refine Sound.bind (h x List.mem_cons_self _) fun r => ?_
    cases r with
    | done b => exact Sound.pure fun _ _ => trivial
    | yield b =>
      cases b
      have ih := Sound.forIn_unit (f := f) fun y hy u => h y (List.mem_cons_of_mem _ hy) u
      exact ih.imp fun _ _ _ _ => trivial

theorem sound_registerBool (I : Input) : Sound (registerBool I) fun _ _ => True := by
  unfold registerBool
  refine Sound.bind (Q₁ := fun _ _ => True) (Sound.forIn_unit fun x _ u => ?_)
    fun _ => Sound.pure fun _ _ => trivial
  cases x with
  | none => exact Sound.pure fun _ => trivial
  | some c =>
    dsimp only
    split
    · exact Sound.bind (sound_registerCtor _ _ _) fun _ => Sound.pure fun _ _ => trivial
    · exact Sound.pure fun _ => trivial

/-! ## Registering the rows a root's result needs -/

/-- A step that changes only the constructor table. -/
def CtorsOnly (s s' : St) : Prop :=
  ∃ (cs : NatMap CtorInfo) (co : List CId), s' = { s with ctors := cs, ctorOrder := co }

theorem CtorsOnly.refl (s : St) : CtorsOnly s s := ⟨s.ctors, s.ctorOrder, rfl⟩

theorem CtorsOnly.trans {s₁ s₂ s₃ : St} (h₁ : CtorsOnly s₁ s₂) (h₂ : CtorsOnly s₂ s₃) :
    CtorsOnly s₁ s₃ := by
  obtain ⟨cs, co, rfl⟩ := h₁
  obtain ⟨cs', co', rfl⟩ := h₂
  exact ⟨cs', co', rfl⟩

theorem registerCtor_ctorsOnly {c : CId} {tag arity : Nat} {s s' : St} {u : Unit}
    (e : (registerCtor c tag arity).run s = .ok (u, s')) : CtorsOnly s s' := by
  unfold registerCtor at e
  rw [StateT.run_bind] at e
  simp only [StateT.run_get, pure_bind] at e
  cases h : s.ctors.get? c with
  | some info =>
    rw [h] at e
    dsimp only at e
    by_cases hc : (info.tag == tag && info.arity == arity) = true
    · simp only [hc, ↓reduceIte, StateT.run_pure] at e
      cases e
      exact CtorsOnly.refl s
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at e
      exact ((Sound.decline (Q := fun _ _ => False) s _ _ e).2 (fun _ _ => True)
        fun _ _ _ => trivial).elim
  | none =>
    rw [h] at e
    simp only [StateT.run_set] at e
    cases e
    exact ⟨_, _, rfl⟩

theorem registerResultRow_ctorsOnly (I : Input) {k : CId} {s s' : St} {u : Unit}
    (e : (registerResultRow I k).run s = .ok (u, s')) : CtorsOnly s s' := by
  unfold registerResultRow at e
  split at e
  · rw [StateT.run_bind] at e
    simp only [StateT.run_get, pure_bind] at e
    split at e
    · simp only [StateT.run_pure] at e
      cases e
      exact CtorsOnly.refl s
    · exact registerCtor_ctorsOnly e
  · simp only [StateT.run_pure] at e
    cases e
    exact CtorsOnly.refl s

/-- `registerRows` changes only the constructor table. -/
theorem registerRows_ctorsOnly (I : Input) : ∀ {ks : List CId} {s s' : St} {u : Unit},
    (registerRows I ks).run s = .ok (u, s') → CtorsOnly s s'
  | [], s, s', u, e => by
    simp only [registerRows, StateT.run_pure] at e
    cases e
    exact CtorsOnly.refl s
  | k :: ks, s, s', u, e => by
    simp only [registerRows] at e
    obtain ⟨_, s₁, e₁, e₂⟩ := Sound.bind_run e
    exact (registerResultRow_ctorsOnly I e₁).trans (registerRows_ctorsOnly I e₂)

end IxCC.Lam.Erase.Proof
