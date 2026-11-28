import IxCC.Sem.Simulation
import IxCC.Sem.Agrees

/-! # Clock-bounded simulation, compositionally

`SimUpTo R n c₁ c₂` is `Sim R id c₁ c₂` restricted to source clocks `k ≤ n`:
the forward clause (a source outcome other than `timeout` is matched at some
target clock) and the timeout clause with the identity clock map (a source
timeout at `k` is a target timeout or resource failure at `k`). A simulation
for every `n` is a `Sim` (`SimUpTo.sim`).

The rules below build such simulations one sequencing step at a time, the
way the evaluators are written (`bind`), with a charge on both sides
(`later`, one clock level down) or on the target only (`laterR`, tick
dominance: a target that spends more clock than its source). This lets a
translation that is clock-exact only in places (erasure's wrappers)
be proved by one induction on the clock for both clauses at once, instead
of separate "agrees at a larger clock" and "runs no further" lemmas. -/

namespace IxCC.Sem

theorem ClockMono.later {α : Type} {f : Nat → Result α} (h : ClockMono f) :
    ClockMono fun k => later k f := by
  intro k k' hle hk
  cases k with
  | zero => exact absurd rfl hk
  | succ j =>
    obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
    exact h (by omega) hk

theorem ClockMono.bind {α β : Type} {c : Nat → Result α} {d : α → Nat → Result β}
    (hc : ClockMono c) (hd : ∀ v, ClockMono (d v)) :
    ClockMono fun k => (c k).bind fun v => d v k := by
  intro k k' hle hk
  dsimp only at hk ⊢
  cases hck : c k with
  | ok v =>
    rw [hck] at hk
    rw [hc hle (by simp [hck]), hck]
    exact hd v hle hk
  | timeout => rw [hck] at hk; exact absurd rfl hk
  | _ => rw [hc hle (by simp [hck]), hck]; rfl

/-- A source outcome is matched at clock `k'`, or the target times out or
fails for a resource at the same clock. -/
structure SimUpTo {α β : Type} (R : α → β → Prop) (n : Nat) (c₁ : Nat → Result α)
    (c₂ : Nat → Result β) : Prop where
  fwd : ∀ k ≤ n, c₁ k ≠ .timeout → ∃ k', Result.Refines R (c₁ k) (c₂ k')
  tmo : ∀ k ≤ n, c₁ k = .timeout → c₂ k = .timeout ∨ ∃ failure, c₂ k = .resource failure

namespace SimUpTo

variable {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {n : Nat}
  {c₁ : Nat → Result α} {c₂ : Nat → Result β}

/-- A simulation at every bound is a clocked simulation with the identity
clock map. -/
theorem sim (h : ∀ n, SimUpTo R n c₁ c₂) : Sim R id c₁ c₂ where
  forward k hk := (h k).fwd k (Nat.le_refl k) hk
  timeout k hk := (h k).tmo k (Nat.le_refl k) hk

theorem mono_n {m : Nat} (h : SimUpTo R n c₁ c₂) (hm : m ≤ n) : SimUpTo R m c₁ c₂ where
  fwd k hk := h.fwd k (Nat.le_trans hk hm)
  tmo k hk := h.tmo k (Nat.le_trans hk hm)

theorem congr {c₁' : Nat → Result α} {c₂' : Nat → Result β} (h : SimUpTo R n c₁ c₂)
    (h₁ : ∀ k, c₁' k = c₁ k) (h₂ : ∀ k, c₂' k = c₂ k) : SimUpTo R n c₁' c₂' where
  fwd k hk hne := by
    rw [h₁] at hne ⊢
    obtain ⟨k', h'⟩ := h.fwd k hk hne
    exact ⟨k', by rw [h₂]; exact h'⟩
  tmo k hk ht := by rw [h₂]; exact h.tmo k hk (by rw [← h₁]; exact ht)

theorem weaken {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) (h : SimUpTo R n c₁ c₂) :
    SimUpTo R' n c₁ c₂ where
  fwd k hk hne := (h.fwd k hk hne).imp fun _ h' => h'.mono hR
  tmo := h.tmo

theorem ok {v : α} {w : β} (h : R v w) : SimUpTo R n (fun _ => .ok v) (fun _ => .ok w) where
  fwd _ _ _ := ⟨0, .ok h⟩
  tmo _ _ h' := nomatch h'

theorem trap : SimUpTo R n (fun _ => (.trap : Result α)) (fun _ => (.trap : Result β)) where
  fwd _ _ _ := ⟨0, .trap⟩
  tmo _ _ h' := nomatch h'

/-- A stuck source imposes nothing. -/
theorem stuck (c₂ : Nat → Result β) : SimUpTo R n (fun _ => (.stuck : Result α)) c₂ where
  fwd _ _ _ := ⟨0, .stuck⟩
  tmo _ _ h' := nomatch h'

/-- A source that is stuck wherever it does not time out, against a target
that times out at least where the source does. -/
theorem of_stuck_or_timeout (h₁ : ∀ k, c₁ k = .stuck ∨ c₁ k = .timeout)
    (h₂ : ∀ k ≤ n, c₁ k = .timeout → c₂ k = .timeout) : SimUpTo R n c₁ c₂ where
  fwd k _ hne := by
    rcases h₁ k with h | h
    · exact ⟨0, by rw [h]; exact .stuck⟩
    · exact absurd h hne
  tmo k hk ht := .inl (h₂ k hk ht)

theorem refines_ok_inv {v : α} {t : Result β} (h : Result.Refines R (.ok v) t) :
    (∃ w, t = .ok w ∧ R v w) ∨ ∃ failure, t = .resource failure := by
  cases h with
  | ok hvw => exact .inl ⟨_, rfl, hvw⟩
  | resource failure => exact .inr ⟨failure, rfl⟩

theorem refines_trap_inv {t : Result β} (h : Result.Refines R (.trap : Result α) t) :
    t = .trap ∨ ∃ failure, t = .resource failure := by
  cases h with
  | trap => exact .inl rfl
  | resource failure => exact .inr ⟨failure, rfl⟩

/-- Sequencing at the same clock on both sides; the continuation may use
that the source value arose. -/
theorem bind' {d : α → Nat → Result γ} {d' : β → Nat → Result δ}
    (hm : ClockMono c₂) (hm' : ∀ w, ClockMono (d' w)) (h : SimUpTo R n c₁ c₂)
    (hd : ∀ v w, R v w → (∃ k ≤ n, c₁ k = .ok v) → SimUpTo S n (d v) (d' w)) :
    SimUpTo S n (fun k => (c₁ k).bind fun v => d v k)
      (fun k => (c₂ k).bind fun w => d' w k) where
  fwd k hk hne := by
    try dsimp only at hne ⊢
    cases hc : c₁ k with
    | ok v =>
      rw [hc] at hne
      simp only [Result.bind] at hne ⊢
      obtain ⟨k₁, h₁⟩ := h.fwd k hk (by simp [hc])
      rw [hc] at h₁
      rcases refines_ok_inv h₁ with ⟨w, hc₂, hvw⟩ | ⟨failure, hc₂⟩
      · obtain ⟨k₂, h₂⟩ := (hd v w hvw ⟨k, hk, hc⟩).fwd k hk hne
        by_cases ht : d' w k₂ = .timeout
        · rw [ht] at h₂
          rcases h₂.of_timeout with h' | h'
          · exact absurd h' hne
          · exact ⟨0, by rw [h']; exact .stuck⟩
        · refine ⟨max k₁ k₂, ?_⟩
          have e₁ : c₂ (max k₁ k₂) = .ok w := hm.ok (Nat.le_max_left _ _) hc₂
          rw [e₁]; dsimp only
          rw [hm' w (Nat.le_max_right _ _) ht]
          exact h₂
      · exact ⟨k₁, by rw [hc₂]; exact .resource failure⟩
    | timeout => rw [hc] at hne; exact absurd rfl hne
    | resource failure =>
      obtain ⟨k₁, h₁⟩ := h.fwd k hk (by simp [hc])
      rw [hc] at h₁
      obtain ⟨failure', hf⟩ := h₁.of_resource
      exact ⟨k₁, by rw [hf]; exact .resource failure'⟩
    | trap =>
      obtain ⟨k₁, h₁⟩ := h.fwd k hk (by simp [hc])
      rw [hc] at h₁
      rcases refines_trap_inv h₁ with hc₂ | ⟨failure, hc₂⟩
      · exact ⟨k₁, by rw [hc₂]; exact .trap⟩
      · exact ⟨k₁, by rw [hc₂]; exact .resource failure⟩
    | stuck => exact ⟨0, .stuck⟩
  tmo k hk ht := by
    try dsimp only at ht ⊢
    cases hc : c₁ k with
    | timeout =>
      rcases h.tmo k hk hc with h' | ⟨failure, h'⟩
      · exact .inl (by rw [h']; rfl)
      · exact .inr ⟨failure, by rw [h']; rfl⟩
    | ok v =>
      rw [hc] at ht
      simp only [Result.bind] at ht
      obtain ⟨k₁, h₁⟩ := h.fwd k hk (by simp [hc])
      rw [hc] at h₁
      by_cases hk₂ : c₂ k = .timeout
      · exact .inl (by rw [hk₂]; rfl)
      · rcases refines_ok_inv h₁ with ⟨w, hc₂, hvw⟩ | ⟨failure, hc₂⟩
        · have : c₂ k = .ok w := by
            rw [hm.eq_of_ne_timeout hk₂ (by rw [hc₂]; simp)]; exact hc₂
          rw [this]
          simp only [Result.bind]
          exact (hd v w hvw ⟨k, hk, hc⟩).tmo k hk ht
        · have : c₂ k = .resource failure := by
            rw [hm.eq_of_ne_timeout hk₂ (by rw [hc₂]; simp)]; exact hc₂
          exact .inr ⟨failure, by rw [this]; rfl⟩
    | _ => rw [hc] at ht; exact nomatch ht


/-- Sequencing at the same clock on both sides. -/
theorem bind {d : α → Nat → Result γ} {d' : β → Nat → Result δ}
    (hm : ClockMono c₂) (hm' : ∀ w, ClockMono (d' w)) (h : SimUpTo R n c₁ c₂)
    (hd : ∀ v w, R v w → SimUpTo S n (d v) (d' w)) :
    SimUpTo S n (fun k => (c₁ k).bind fun v => d v k)
      (fun k => (c₂ k).bind fun w => d' w k) :=
  bind' hm hm' h fun v w hvw _ => hd v w hvw

/-- A charge on both sides: a simulation one clock level down. -/
theorem later {c₁ : Nat → Result α} {c₂ : Nat → Result β}
    (h : ∀ m, m + 1 ≤ n → SimUpTo R m c₁ c₂) :
    SimUpTo R n (fun k => Sem.later k c₁) (fun k => Sem.later k c₂) where
  fwd k hk hne := by
    cases k with
    | zero => exact absurd rfl hne
    | succ j =>
      obtain ⟨k', h'⟩ := (h j hk).fwd j (Nat.le_refl j) hne
      exact ⟨k' + 1, h'⟩
  tmo k hk ht := by
    cases k with
    | zero => exact .inl rfl
    | succ j => exact (h j hk).tmo j (Nat.le_refl j) ht

/-- A charge on the target only (tick dominance). -/
theorem laterR (hm : ClockMono c₂) (h : SimUpTo R n c₁ c₂) :
    SimUpTo R n c₁ (fun k => Sem.later k c₂) where
  fwd k hk hne := by
    obtain ⟨k', h'⟩ := h.fwd k hk hne
    exact ⟨k' + 1, h'⟩
  tmo k hk ht := by
    cases k with
    | zero => exact .inl rfl
    | succ j =>
      show c₂ j = .timeout ∨ ∃ failure, c₂ j = .resource failure
      by_cases hj : c₂ j = .timeout
      · exact .inl hj
      · rcases h.tmo (j + 1) hk ht with h' | ⟨failure, h'⟩
        · rw [hm (Nat.le_succ j) hj] at h'; exact absurd h' hj
        · rw [hm (Nat.le_succ j) hj] at h'; exact .inr ⟨failure, h'⟩

end SimUpTo

end IxCC.Sem
