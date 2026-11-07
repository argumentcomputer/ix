import IxCC.Sem.Clocked

/-!
# Clocked simulation and the divergence lemma

A pass is proved correct, per input, by a *clocked simulation*
`Sim R f c₁ c₂` between the source semantics `c₁` and the target semantics
`c₂` (design note `plans/x86-v2/00-conventions.md`, "Clock discipline"):

- **forward:** an outcome of the source at clock `k` other than `timeout` is
  matched by the target at *some* clock `k'`: a related value, the same
  trap, or a target resource failure; a stuck source imposes nothing;
- **timeout:** a source timeout at clock `f k` is a target timeout **or a
  target resource failure** at clock `k`. The target may run out of stack
  or heap on a diverging source; `f` need not be monotone.

The forward clause concludes target success, so no separate progress proof
is needed. `Sim.refines` (CakeML's `IMP_semantics_eq`,
`closPropsScript.sml`) turns a simulation into a refinement of behaviours,
including divergence; `Sim.backward` and `Sim.safe` are the per-clock shapes
of `compile_sound` and `compile_safe` (roadmap §1.1): a target outcome other
than a timeout or a resource failure is the source's own (related value or
trap), or the source is stuck.

Refinement lets the target add resource failures anywhere and asks nothing
of a stuck source.
-/

namespace IxCC.Sem

/-- Relational composition, for composing value relations. -/
def RelComp {α β γ : Type} (R : α → β → Prop) (S : β → γ → Prop) (a : α) (c : γ) : Prop :=
  ∃ b, R a b ∧ S b c

namespace Result

/-- An outcome that goes wrong: stuck or a trap (roadmap §1.1's
`GoesWrong`, per clock). -/
def GoesWrong {α : Type} : Result α → Prop
  | stuck => True
  | trap => True
  | _ => False

@[simp] theorem goesWrong_stuck {α : Type} : (stuck : Result α).GoesWrong := trivial
@[simp] theorem goesWrong_trap {α : Type} : (trap : Result α).GoesWrong := trivial
@[simp] theorem not_goesWrong_ok {α : Type} (value : α) : ¬ (ok value).GoesWrong := id
@[simp] theorem not_goesWrong_timeout {α : Type} : ¬ (timeout : Result α).GoesWrong := id
@[simp] theorem not_goesWrong_resource {α : Type} (failure : Resource) :
    ¬ (resource failure : Result α).GoesWrong := id

/-- Per-clock refinement: the target outcome `t` matches the source outcome
`s`. A target resource failure matches anything, and a stuck source is
matched by anything. -/
inductive Refines {α β : Type} (R : α → β → Prop) : Result α → Result β → Prop
  | ok {v : α} {w : β} : R v w → Refines R (.ok v) (.ok w)
  | timeout : Refines R .timeout .timeout
  | trap : Refines R .trap .trap
  | stuck {t : Result β} : Refines R .stuck t
  | resource {s : Result α} (failure : Resource) : Refines R s (.resource failure)

namespace Refines

variable {α β γ : Type} {R : α → β → Prop}

theorem refl {r : Result α} {R : α → α → Prop} (h : ∀ v, R v v) : Refines R r r := by
  cases r with
  | ok v => exact .ok (h v)
  | timeout => exact .timeout
  | resource failure => exact .resource failure
  | trap => exact .trap
  | stuck => exact .stuck

theorem trans {S : β → γ → Prop} {r₁ : Result α} {r₂ : Result β} {r₃ : Result γ}
    (h₁ : Refines R r₁ r₂) (h₂ : Refines S r₂ r₃) : Refines (RelComp R S) r₁ r₃ := by
  cases h₁ with
  | ok hvw => cases h₂ with
    | ok hwu => exact .ok ⟨_, hvw, hwu⟩
    | resource failure => exact .resource failure
  | timeout => cases h₂ with
    | timeout => exact .timeout
    | resource failure => exact .resource failure
  | trap => cases h₂ with
    | trap => exact .trap
    | resource failure => exact .resource failure
  | stuck => exact .stuck
  | resource failure => cases h₂ with
    | resource failure' => exact .resource failure'

theorem mono {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) {s : Result α} {t : Result β}
    (h : Refines R s t) : Refines R' s t := by
  cases h with
  | ok hvw => exact .ok (hR _ _ hvw)
  | timeout => exact .timeout
  | trap => exact .trap
  | stuck => exact .stuck
  | resource failure => exact .resource failure

theorem timeout_iff {t : Result β} :
    Refines R .timeout t ↔ t = .timeout ∨ ∃ failure, t = .resource failure := by
  constructor
  · intro h
    cases h with
    | timeout => exact .inl rfl
    | resource failure => exact .inr ⟨failure, rfl⟩
  · rintro (rfl | ⟨failure, rfl⟩)
    · exact .timeout
    · exact .resource failure

/-- A target timeout matches only a source timeout or a stuck source. -/
theorem of_timeout {s : Result α} (h : Refines R s .timeout) : s = .timeout ∨ s = .stuck := by
  cases h with
  | timeout => exact .inl rfl
  | stuck => exact .inr rfl

/-- A target value matches only a related source value or a stuck source. -/
theorem of_ok {s : Result α} {w : β} (h : Refines R s (.ok w)) :
    (∃ v, s = .ok v ∧ R v w) ∨ s = .stuck := by
  cases h with
  | ok hvw => exact .inl ⟨_, rfl, hvw⟩
  | stuck => exact .inr rfl

/-- A target trap matches only a source trap or a stuck source. -/
theorem of_trap {s : Result α} (h : Refines R s .trap) : s = .trap ∨ s = .stuck := by
  cases h with
  | trap => exact .inl rfl
  | stuck => exact .inr rfl

/-- A stuck target matches only a stuck source. -/
theorem of_stuck {s : Result α} (h : Refines R s .stuck) : s = .stuck := by
  cases h
  rfl

/-- A source resource failure is matched only by a target resource failure. -/
theorem of_resource {t : Result β} {failure : Resource}
    (h : Refines R (.resource failure) t) : ∃ failure', t = .resource failure' := by
  cases h with
  | resource failure' => exact ⟨failure', rfl⟩

/-- A target that goes wrong matches only a source that goes wrong. -/
theorem goesWrong {s : Result α} {t : Result β} (h : Refines R s t) (ht : t.GoesWrong) :
    s.GoesWrong := by
  cases h <;> simp_all [GoesWrong]

end Refines

end Result

namespace Behaviour

/-- Behaviour refinement: the target behaviour `b₂` matches the source
behaviour `b₁` up to `R` on values; the target may add resource failures,
and a stuck source imposes nothing. -/
inductive Refines {α β : Type} (R : α → β → Prop) : Behaviour α → Behaviour β → Prop
  | terminates {v : α} {w : β} : R v w → Refines R (.terminates v) (.terminates w)
  | diverges : Refines R .diverges .diverges
  | trap : Refines R .trap .trap
  | stuck {b : Behaviour β} : Refines R .stuck b
  | resource {b : Behaviour α} (failure : Resource) : Refines R b (.resource failure)

/-- A behaviour that goes wrong: stuck or a trap. -/
def GoesWrong {α : Type} : Behaviour α → Prop
  | stuck => True
  | trap => True
  | _ => False

namespace Refines

variable {α β γ : Type} {R : α → β → Prop}

theorem refl {b : Behaviour α} {R : α → α → Prop} (h : ∀ v, R v v) : Refines R b b := by
  cases b with
  | terminates v => exact .terminates (h v)
  | diverges => exact .diverges
  | resource failure => exact .resource failure
  | trap => exact .trap
  | stuck => exact .stuck

theorem trans {S : β → γ → Prop} {b₁ : Behaviour α} {b₂ : Behaviour β} {b₃ : Behaviour γ}
    (h₁ : Refines R b₁ b₂) (h₂ : Refines S b₂ b₃) : Refines (RelComp R S) b₁ b₃ := by
  cases h₁ with
  | terminates hvw => cases h₂ with
    | terminates hwu => exact .terminates ⟨_, hvw, hwu⟩
    | resource failure => exact .resource failure
  | diverges => cases h₂ with
    | diverges => exact .diverges
    | resource failure => exact .resource failure
  | trap => cases h₂ with
    | trap => exact .trap
    | resource failure => exact .resource failure
  | stuck => exact .stuck
  | resource failure => cases h₂ with
    | resource failure' => exact .resource failure'

theorem mono {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) {b₁ : Behaviour α}
    {b₂ : Behaviour β} (h : Refines R b₁ b₂) : Refines R' b₁ b₂ := by
  cases h with
  | terminates hvw => exact .terminates (hR _ _ hvw)
  | diverges => exact .diverges
  | trap => exact .trap
  | stuck => exact .stuck
  | resource failure => exact .resource failure

/-- A target that terminates matches a related source value or a stuck
source. -/
theorem of_terminates {b : Behaviour α} {w : β} (h : Refines R b (.terminates w)) :
    (∃ v, b = .terminates v ∧ R v w) ∨ b = .stuck := by
  cases h with
  | terminates hvw => exact .inl ⟨_, rfl, hvw⟩
  | stuck => exact .inr rfl

/-- A target that goes wrong matches only a source that goes wrong. -/
theorem goesWrong {b₁ : Behaviour α} {b₂ : Behaviour β} (h : Refines R b₁ b₂)
    (hb : b₂.GoesWrong) : b₁.GoesWrong := by
  cases h <;> simp_all [GoesWrong]

end Refines

end Behaviour

/-- Per-clock refinement gives behaviour refinement of the single outcomes. -/
theorem Result.Refines.toBehaviour {α β : Type} {R : α → β → Prop} {s : Result α}
    {t : Result β} (h : Result.Refines R s t) :
    Behaviour.Refines R s.toBehaviour t.toBehaviour := by
  cases h with
  | ok hvw => exact .terminates hvw
  | timeout => exact .diverges
  | trap => exact .trap
  | stuck => exact .stuck
  | resource failure => exact .resource failure

theorem Behaviour.goesWrong_toBehaviour {α : Type} {r : Result α} :
    r.toBehaviour.GoesWrong ↔ r.GoesWrong := by
  cases r <;> simp [Result.toBehaviour, Behaviour.GoesWrong, Result.GoesWrong]

/-- A clocked simulation from `c₁` to `c₂` with value relation `R` and clock
map `f` (see the module comment). -/
structure Sim {α β : Type} (R : α → β → Prop) (f : Nat → Nat)
    (c₁ : Nat → Result α) (c₂ : Nat → Result β) : Prop where
  /-- Every source outcome other than `timeout` is matched at some clock. -/
  forward : ∀ k, c₁ k ≠ .timeout → ∃ k', Result.Refines R (c₁ k) (c₂ k')
  /-- A source timeout at `f k` is a target timeout or resource failure at
  `k`. -/
  timeout : ∀ k, c₁ (f k) = .timeout → c₂ k = .timeout ∨ ∃ failure, c₂ k = .resource failure

namespace Sim

variable {α β γ : Type} {R : α → β → Prop} {f : Nat → Nat}
  {c₁ : Nat → Result α} {c₂ : Nat → Result β}

/-- The divergence lemma (CakeML's `IMP_semantics_eq`): a clocked simulation
between monotone semantics refines their behaviours, divergence included. -/
theorem refines (h₁ : ClockMono c₁) (h₂ : ClockMono c₂) (hs : Sim R f c₁ c₂) :
    Behaviour.Refines R (behaviour c₁) (behaviour c₂) := by
  by_cases hex : ∃ k, c₁ k ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨k', hr⟩ := hs.forward k hk
    rw [behaviour_of_ne_timeout h₁ hk]
    by_cases hk' : c₂ k' = .timeout
    · rw [hk'] at hr
      rcases hr.of_timeout with h | h
      · exact absurd h hk
      · rw [h]
        exact .stuck
    · rw [behaviour_of_ne_timeout h₂ hk']
      exact hr.toBehaviour
  · have hdiv : ∀ k, c₁ k = .timeout := fun k =>
      Classical.byContradiction fun hk => hex ⟨k, hk⟩
    rw [behaviour_of_forall_timeout hdiv]
    by_cases hfail : ∃ k failure, c₂ k = .resource failure
    · obtain ⟨k, failure, hk⟩ := hfail
      rw [behaviour_of_ne_timeout h₂ (k := k) (by simp [hk]), hk]
      exact .resource failure
    · have : ∀ k, c₂ k = .timeout := fun k => by
        rcases hs.timeout k (hdiv _) with h | ⟨failure, h⟩
        · exact h
        · exact absurd ⟨k, failure, h⟩ hfail
      rw [behaviour_of_forall_timeout this]
      exact .diverges

/-- Backward reading at one clock: a target outcome other than `timeout`
matches the source's outcome at clock `f k`. In particular a target value
comes from a related source value or a stuck source (`Result.Refines.of_ok`),
and a target trap from a source trap or a stuck source. -/
theorem backward (h₂ : ClockMono c₂) (hs : Sim R f c₁ c₂) {k : Nat}
    (hk : c₂ k ≠ .timeout) : Result.Refines R (c₁ (f k)) (c₂ k) := by
  cases hck : c₂ k with
  | timeout => exact absurd hck hk
  | resource failure => exact .resource failure
  | _ =>
    all_goals
      have hsrc : c₁ (f k) ≠ .timeout := fun ht => by
        rcases hs.timeout k ht with h | ⟨_, h⟩ <;> simp [hck] at h
      obtain ⟨k', hr⟩ := hs.forward _ hsrc
      by_cases hk' : c₂ k' = .timeout
      · rw [hk'] at hr
        rcases hr.of_timeout with h | h
        · exact absurd h hsrc
        · rw [h]
          exact .stuck
      · rwa [h₂.eq_of_ne_timeout hk' hk, hck] at hr

/-- Safety at one clock: if the source does not go wrong at clock `f k`,
the target does not go wrong at `k`; it returns a value, times out or runs
out of a resource (roadmap §1.1's `compile_safe`). -/
theorem safe (h₂ : ClockMono c₂) (hs : Sim R f c₁ c₂) {k : Nat}
    (hsrc : ¬ (c₁ (f k)).GoesWrong) : ¬ (c₂ k).GoesWrong := by
  intro ht
  have hk : c₂ k ≠ .timeout := fun h => by simp [h] at ht
  exact hsrc ((hs.backward h₂ hk).goesWrong ht)

/-- Simulations compose; the clock maps compose in reverse. -/
theorem comp {S : β → γ → Prop} {g : Nat → Nat} {c₃ : Nat → Result γ}
    (h₃ : ClockMono c₃) (hs : Sim R f c₁ c₂) (ht : Sim S g c₂ c₃) :
    Sim (RelComp R S) (fun k => f (g k)) c₁ c₃ where
  forward k hk := by
    obtain ⟨k', h₁₂⟩ := hs.forward k hk
    by_cases hk' : c₂ k' = .timeout
    · rw [hk'] at h₁₂
      rcases h₁₂.of_timeout with h | h
      · exact absurd h hk
      · rw [h]
        exact ⟨0, .stuck⟩
    · obtain ⟨k'', h₂₃⟩ := ht.forward k' hk'
      exact ⟨k'', h₁₂.trans h₂₃⟩
  timeout k hk := by
    rcases hs.timeout (g k) hk with h | ⟨failure, h⟩
    · exact ht.timeout k h
    · by_cases hk3 : c₃ k = .timeout
      · exact .inl hk3
      · obtain ⟨k', h₂₃⟩ := ht.forward (g k) (by simp [h])
        rw [h] at h₂₃
        obtain ⟨failure', h'⟩ := h₂₃.of_resource
        refine .inr ⟨failure', ?_⟩
        rw [h₃.eq_of_ne_timeout (k' := k') hk3 (by simp [h']), h']

/-- The identity simulation. -/
theorem refl {R : α → α → Prop} (hR : ∀ v, R v v) (c : Nat → Result α) : Sim R id c c where
  forward k _ := ⟨k, .refl hR⟩
  timeout _ h := .inl h

/-- A simulation for a stronger value relation is one for a weaker one. -/
theorem mono {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) (hs : Sim R f c₁ c₂) :
    Sim R' f c₁ c₂ where
  forward k hk := (hs.forward k hk).imp fun _ h => h.mono hR
  timeout := hs.timeout

/-- A source that does not go wrong at any clock has a target that never
goes wrong. -/
theorem safe_all (h₂ : ClockMono c₂) (hs : Sim R f c₁ c₂)
    (hsrc : ∀ k, ¬ (c₁ k).GoesWrong) (k : Nat) : ¬ (c₂ k).GoesWrong :=
  hs.safe h₂ (hsrc _)

end Sim

end IxCC.Sem
