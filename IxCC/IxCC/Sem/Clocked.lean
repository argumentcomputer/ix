import IxCC.Sem.Result

/-!
# Clocked semantics and their behaviours

Every executable semantics of the pipeline is a function of a clock,
`c : Nat → Result α` (design note `plans/x86-v2/00-conventions.md`). This
module fixes what such a function must satisfy and what it observes:

- `ClockMono c`: an outcome other than `timeout` stays the same at every
  larger clock. This is stronger than "`ok` stays `ok`": a run that traps,
  gets stuck or runs out of a resource does so at every larger clock too.
- `behaviour c`: the outcome at any clock that does not time out, or
  `diverges` if every clock times out. Monotonicity makes it well defined
  (`behaviour_of_ne_timeout`).

`behaviour` is a Prop-level definition (it decides an unbounded
quantifier), never evaluated; M2.8 evaluates only the passes.
-/

namespace IxCC.Sem

namespace Result

/-- The behaviour a single outcome shows: `timeout` is read as `diverges`,
which `behaviour` justifies once every clock times out. -/
def toBehaviour {α : Type} : Result α → Behaviour α
  | ok value => .terminates value
  | timeout => .diverges
  | resource failure => .resource failure
  | trap => .trap
  | stuck => .stuck

@[simp] theorem toBehaviour_ok {α : Type} (value : α) :
    (ok value).toBehaviour = .terminates value := rfl
@[simp] theorem toBehaviour_timeout {α : Type} : (timeout : Result α).toBehaviour = .diverges := rfl
@[simp] theorem toBehaviour_resource {α : Type} (failure : Resource) :
    (resource failure : Result α).toBehaviour = .resource failure := rfl
@[simp] theorem toBehaviour_trap {α : Type} : (trap : Result α).toBehaviour = .trap := rfl
@[simp] theorem toBehaviour_stuck {α : Type} : (stuck : Result α).toBehaviour = .stuck := rfl

theorem toBehaviour_eq_diverges {α : Type} {r : Result α} :
    r.toBehaviour = .diverges ↔ r = .timeout := by
  cases r <;> simp [toBehaviour]

theorem toBehaviour_injective {α : Type} {r r' : Result α}
    (h : r.toBehaviour = r'.toBehaviour) : r = r' := by
  cases r <;> cases r' <;> simp_all [toBehaviour]

end Result

/-- Clock monotonicity: an outcome other than `timeout` is the outcome at
every larger clock. -/
def ClockMono {α : Type} (c : Nat → Result α) : Prop :=
  ∀ ⦃k k' : Nat⦄, k ≤ k' → c k ≠ .timeout → c k' = c k

namespace ClockMono

variable {α : Type} {c : Nat → Result α}

/-- Two clocks that do not time out give the same outcome. -/
theorem eq_of_ne_timeout (h : ClockMono c) {k k' : Nat}
    (hk : c k ≠ .timeout) (hk' : c k' ≠ .timeout) : c k = c k' := by
  rcases Nat.le_total k k' with hle | hle
  · exact (h hle hk).symm
  · exact h hle hk'

/-- `ok` is kept at every larger clock. -/
theorem ok (h : ClockMono c) {k k' : Nat} {value : α} (hle : k ≤ k')
    (hk : c k = .ok value) : c k' = .ok value := by
  rw [h hle (by simp [hk]), hk]

/-- A timeout at some clock is a timeout at every smaller clock. -/
theorem timeout_of_le (h : ClockMono c) {k k' : Nat} (hle : k ≤ k')
    (hk' : c k' = .timeout) : c k = .timeout := by
  refine Classical.byContradiction fun hk => ?_
  rw [h hle hk] at hk'
  exact hk hk'

/-- A constant function of the clock is monotone. -/
theorem const (r : Result α) : ClockMono (fun _ => r) := fun _ _ _ _ => rfl

end ClockMono

/-- A clocked semantics packaged with its monotonicity. -/
structure Clocked (α : Type) where
  run : Nat → Result α
  mono : ClockMono run

open Classical in
/-- The observable behaviour of a clocked semantics: the outcome at any
clock that does not time out, or `diverges` if every clock times out. -/
noncomputable def behaviour {α : Type} (c : Nat → Result α) : Behaviour α :=
  if h : ∃ k, c k ≠ .timeout then (c (Classical.choose h)).toBehaviour else .diverges

section behaviour

variable {α : Type} {c : Nat → Result α}

/-- Under monotonicity, any clock that does not time out gives the
behaviour. -/
theorem behaviour_of_ne_timeout (h : ClockMono c) {k : Nat} (hk : c k ≠ .timeout) :
    behaviour c = (c k).toBehaviour := by
  unfold behaviour
  split
  · next hex => rw [h.eq_of_ne_timeout (Classical.choose_spec hex) hk]
  · next hex => exact absurd ⟨k, hk⟩ hex

theorem behaviour_of_forall_timeout (hc : ∀ k, c k = .timeout) : behaviour c = .diverges := by
  unfold behaviour
  split
  · next hex => exact absurd (hc _) (Classical.choose_spec hex)
  · rfl

/-- A semantics diverges exactly when every clock times out. -/
theorem behaviour_eq_diverges_iff (h : ClockMono c) :
    behaviour c = .diverges ↔ ∀ k, c k = .timeout := by
  constructor
  · intro hb k
    refine Classical.byContradiction fun hk => ?_
    rw [behaviour_of_ne_timeout h hk, Result.toBehaviour_eq_diverges] at hb
    exact hk hb
  · exact behaviour_of_forall_timeout

/-- Every behaviour other than divergence is the behaviour of some clock. -/
theorem behaviour_eq_iff_of_ne_diverges (h : ClockMono c) {b : Behaviour α}
    (hb : b ≠ .diverges) : behaviour c = b ↔ ∃ k, (c k).toBehaviour = b := by
  constructor
  · intro hc
    by_cases hex : ∃ k, c k ≠ .timeout
    · obtain ⟨k, hk⟩ := hex
      exact ⟨k, by rw [← hc, behaviour_of_ne_timeout h hk]⟩
    · refine absurd ?_ hb
      rw [← hc]
      exact behaviour_of_forall_timeout fun k =>
        Classical.byContradiction fun hk => hex ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    have hne : c k ≠ .timeout := by
      intro ht
      rw [ht] at hk
      exact hb hk.symm
    rw [behaviour_of_ne_timeout h hne, hk]

theorem behaviour_eq_terminates_iff (h : ClockMono c) {value : α} :
    behaviour c = .terminates value ↔ ∃ k, c k = .ok value := by
  rw [behaviour_eq_iff_of_ne_diverges h (by simp)]
  refine exists_congr fun k => ?_
  cases c k <;> simp [Result.toBehaviour]

theorem behaviour_eq_resource_iff (h : ClockMono c) {failure : Resource} :
    behaviour c = .resource failure ↔ ∃ k, c k = .resource failure := by
  rw [behaviour_eq_iff_of_ne_diverges h (by simp)]
  refine exists_congr fun k => ?_
  cases c k <;> simp [Result.toBehaviour]

theorem behaviour_eq_trap_iff (h : ClockMono c) :
    behaviour c = .trap ↔ ∃ k, c k = .trap := by
  rw [behaviour_eq_iff_of_ne_diverges h (by simp)]
  refine exists_congr fun k => ?_
  cases c k <;> simp [Result.toBehaviour]

theorem behaviour_eq_stuck_iff (h : ClockMono c) :
    behaviour c = .stuck ↔ ∃ k, c k = .stuck := by
  rw [behaviour_eq_iff_of_ne_diverges h (by simp)]
  refine exists_congr fun k => ?_
  cases c k <;> simp [Result.toBehaviour]

/-- Behaviour depends only on the clocked outcomes. -/
theorem behaviour_congr {c' : Nat → Result α} (hc : ∀ k, c k = c' k) :
    behaviour c = behaviour c' := by
  have : c = c' := funext hc
  rw [this]

end behaviour

namespace Clocked

/-- The behaviour of a packaged clocked semantics. -/
noncomputable def behaviour {α : Type} (c : Clocked α) : Behaviour α := Sem.behaviour c.run

theorem behaviour_of_ne_timeout {α : Type} (c : Clocked α) {k : Nat}
    (hk : c.run k ≠ .timeout) : c.behaviour = (c.run k).toBehaviour :=
  Sem.behaviour_of_ne_timeout c.mono hk

end Clocked

end IxCC.Sem
