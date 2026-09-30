import Compilatrix.Sem.Clock
import Compilatrix.Sem.Simulation

/-!
# The small-step core

Small-step levels (Cfg down to Xl) step a state with `step : σ → Step σ α`
(`Sem.Step`) and run it with the clocked runner `Sem.runClocked`, whose step
bound (`fuel`) keeps it structural. This module gives such a semantics its
relational reading and connects it to `Sim`:

- `Star step s c s'`: `s` reaches `s'` by `next` steps spending `c` charges;
  `Star.map` lifts a run into a larger state (a stack, a context).
- `Reaches step s k r`: from `s` with clock `k` the run ends in `r`, without
  fuel. It is deterministic (`Reaches.det`), monotone in the clock
  (`Reaches.mono`, `Reaches.down`), splits along `Star` (`Reaches.star`,
  `Reaches.of_star`), and times out exactly when some run spends more
  charges than the clock (`Reaches.timeout_iff`).
- `runClocked` is sound (`runClocked_sound`) and complete
  (`runClocked_complete`) for `Reaches`. A potential that free steps
  decrease and charges raise by at most `D` bounds the steps, so fuel above
  `φ s + k·(D + 1)` never runs out before the clock does
  (`Potential.runClocked`); `Runs step s c` then holds for the runner, and
  every `Runs` is clock monotone.
- A forward `Diagram` (each source step matched by target steps, each source
  charge by at least one target charge, with target resource failures
  allowed) gives `Sim` with the identity clock map (`Diagram.sim`). The clock
  plays the part of CompCert's stuttering measure (`Smallstep.v`,
  `forward_simulation_star_wf`): a stuttering source cannot run forever
  without charges once it `Runs`, and deterministic levels need no backward
  diagram.
- `Sim.ofStar` crosses from a big-step source (Src through Own, depth clocks)
  to a small-step target (Cfg downward, total clocks): the target reaches a
  matching final step at some clock, and a source timeout at `f k` gives a
  target run that spends more than `k` charges or fails for a resource.
-/

namespace Compilatrix.Sem

variable {σ α : Type}

/-- The outcome a final step shows; `next` shows none. -/
inductive Final : Step σ α → Result α → Prop
  | done {value : α} : Final (.done value) (.ok value)
  | fail {failure : Resource} : Final (.fail failure) (.resource failure)
  | trap : Final .trap .trap
  | stuck : Final .stuck .stuck

namespace Final

theorem ne_timeout {st : Step σ α} {r : Result α} (h : Final st r) : r ≠ .timeout := by
  cases h <;> simp

theorem det {st : Step σ α} {r r' : Result α} (h : Final st r) (h' : Final st r') : r = r' := by
  cases h <;> cases h' <;> rfl

theorem not_next {s : σ} {b : Bool} {r : Result α} : ¬ Final (.next s b) r := by
  intro h
  cases h

/-- The final outcome of a step, if it is final. -/
def outcome : Step σ α → Option (Result α)
  | .next _ _ => none
  | .done value => some (.ok value)
  | .fail failure => some (.resource failure)
  | .trap => some .trap
  | .stuck => some .stuck

theorem iff_outcome {st : Step σ α} {r : Result α} : Final st r ↔ outcome st = some r := by
  constructor
  · intro h
    cases h <;> rfl
  · intro h
    cases st <;> simp [outcome] at h <;> subst h <;> constructor

end Final

/-- `Star step s c s'`: `s` reaches `s'` by `next` steps spending `c`
charges. -/
inductive Star (step : σ → Step σ α) : σ → Nat → σ → Prop
  | refl (s : σ) : Star step s 0 s
  | free {s s' s'' : σ} {c : Nat} : step s = .next s' false → Star step s' c s'' →
      Star step s c s''
  | charge {s s' s'' : σ} {c : Nat} : step s = .next s' true → Star step s' c s'' →
      Star step s (c + 1) s''

namespace Star

variable {step : σ → Step σ α}

theorem trans {s s' s'' : σ} {c c' : Nat} (h : Star step s c s') (h' : Star step s' c' s'') :
    Star step s (c + c') s'' := by
  induction h with
  | refl => simpa using h'
  | free hs _ ih => exact .free hs (ih h')
  | charge hs _ ih =>
    have := Star.charge hs (ih h')
    rwa [Nat.add_right_comm] at this

theorem single {s s' : σ} {b : Bool} (hs : step s = .next s' b) : Star step s b.toNat s' := by
  cases b
  · exact .free hs (.refl _)
  · exact .charge hs (.refl _)

theorem head {s s' s'' : σ} {b : Bool} {c : Nat} (hs : step s = .next s' b)
    (h : Star step s' c s'') : Star step s (b.toNat + c) s'' :=
  (single hs).trans h

/-- Lift a run along a map that commutes with `next` steps, keeping the
charges; for example into a larger stack or context. -/
theorem map {τ β : Type} {step' : τ → Step τ β} (g : σ → τ)
    (hg : ∀ {s s' : σ} {b : Bool}, step s = .next s' b → step' (g s) = .next (g s') b)
    {s s' : σ} {c : Nat} (h : Star step s c s') : Star step' (g s) c (g s') := by
  induction h with
  | refl => exact .refl _
  | free hs _ ih => exact .free (hg hs) ih
  | charge hs _ ih => exact .charge (hg hs) ih

end Star

/-- `Reaches step s k r`: from `s` with clock `k` the run ends in `r`. A
charge with an empty clock is `timeout`. -/
inductive Reaches (step : σ → Step σ α) : σ → Nat → Result α → Prop
  | final {s : σ} {k : Nat} {r : Result α} : Final (step s) r → Reaches step s k r
  | free {s s' : σ} {k : Nat} {r : Result α} : step s = .next s' false →
      Reaches step s' k r → Reaches step s k r
  | charge {s s' : σ} {k : Nat} {r : Result α} : step s = .next s' true →
      Reaches step s' k r → Reaches step s (k + 1) r
  | timeout {s s' : σ} : step s = .next s' true → Reaches step s 0 .timeout

namespace Reaches

variable {step : σ → Step σ α}

/-! ## Inversion -/

theorem inv_final {s : σ} {k : Nat} {r r' : Result α} (hf : Final (step s) r)
    (h : Reaches step s k r') : r' = r := by
  cases h with
  | final hf' => exact hf'.det hf
  | free hs _ => rw [hs] at hf; exact absurd hf Final.not_next
  | charge hs _ => rw [hs] at hf; exact absurd hf Final.not_next
  | timeout hs => rw [hs] at hf; exact absurd hf Final.not_next

theorem inv_free {s s' : σ} {k : Nat} {r : Result α} (hs : step s = .next s' false)
    (h : Reaches step s k r) : Reaches step s' k r := by
  cases h with
  | final hf => rw [hs] at hf; exact absurd hf Final.not_next
  | free hs' h => rw [hs] at hs'; cases hs'; exact h
  | charge hs' _ => rw [hs] at hs'; cases hs'
  | timeout hs' => rw [hs] at hs'; cases hs'

theorem inv_charge {s s' : σ} {k : Nat} {r : Result α} (hs : step s = .next s' true)
    (h : Reaches step s (k + 1) r) : Reaches step s' k r := by
  cases h with
  | final hf => rw [hs] at hf; exact absurd hf Final.not_next
  | free hs' _ => rw [hs] at hs'; cases hs'
  | charge hs' h => rw [hs] at hs'; cases hs'; exact h

theorem inv_charge_zero {s s' : σ} {r : Result α} (hs : step s = .next s' true)
    (h : Reaches step s 0 r) : r = .timeout := by
  cases h with
  | final hf => rw [hs] at hf; exact absurd hf Final.not_next
  | free hs' _ => rw [hs] at hs'; cases hs'
  | timeout _ => rfl

/-! ## Determinism and the clock -/

/-- The outcome at a clock is unique. -/
theorem det {s : σ} {k : Nat} {r r' : Result α} (h : Reaches step s k r)
    (h' : Reaches step s k r') : r = r' := by
  induction h with
  | final hf => exact (inv_final hf h').symm
  | free hs _ ih => exact ih (inv_free hs h')
  | charge hs _ ih => exact ih (inv_charge hs h')
  | timeout hs => exact (inv_charge_zero hs h').symm

/-- An outcome other than `timeout` is kept at every larger clock. -/
theorem mono {s : σ} {k k' : Nat} {r : Result α} (h : Reaches step s k r)
    (hr : r ≠ .timeout) (hk : k ≤ k') : Reaches step s k' r := by
  induction h generalizing k' with
  | final hf => exact .final hf
  | free hs _ ih => exact .free hs (ih hr hk)
  | charge hs _ ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    exact .charge hs (ih hr (by omega))
  | timeout _ => exact absurd rfl hr

/-- With a smaller clock, the run ends the same way or times out. -/
theorem down {s : σ} {k k' : Nat} {r : Result α} (h : Reaches step s k r) (hk : k' ≤ k) :
    Reaches step s k' r ∨ Reaches step s k' .timeout := by
  induction h generalizing k' with
  | final hf => exact .inl (.final hf)
  | free hs _ ih => exact (ih hk).imp (.free hs) (.free hs)
  | @charge s s' k r hs _ ih =>
    cases k' with
    | zero => exact .inr (.timeout hs)
    | succ j => exact (ih (by omega)).imp (.charge hs) (.charge hs)
  | timeout hs =>
    obtain rfl : k' = 0 := by omega
    exact .inl (.timeout hs)

theorem timeout_le {s : σ} {k k' : Nat} (h : Reaches step s k .timeout) (hk : k' ≤ k) :
    Reaches step s k' .timeout :=
  (h.down hk).elim id id

/-! ## Splitting along `Star` -/

/-- Prefix a run: `c` charges on the way cost `c` units of clock. -/
theorem star {s s' : σ} {c k : Nat} {r : Result α} (hst : Star step s c s')
    (h : Reaches step s' k r) : Reaches step s (k + c) r := by
  induction hst with
  | refl => exact h
  | free hs _ ih => exact .free hs (ih h)
  | charge hs _ ih =>
    rw [← Nat.add_assoc]
    exact .charge hs (ih h)

/-- Drop a prefix: the run from `s` passes through `s'` with `c` fewer
units of clock. -/
theorem of_star {s s' : σ} {c k : Nat} {r : Result α} (hst : Star step s c s')
    (h : Reaches step s (k + c) r) : Reaches step s' k r := by
  induction hst with
  | refl => exact h
  | free hs _ ih => exact ih (inv_free hs h)
  | charge hs _ ih =>
    rw [← Nat.add_assoc] at h
    exact ih (inv_charge hs h)

/-- A run that spends more charges than the clock times out. -/
theorem timeout_of_star {s s' : σ} {c k : Nat} (hst : Star step s c s') (hk : k < c) :
    Reaches step s k .timeout := by
  induction hst generalizing k with
  | refl => omega
  | free hs _ ih => exact .free hs (ih hk)
  | charge hs _ ih =>
    cases k with
    | zero => exact .timeout hs
    | succ j => exact .charge hs (ih (by omega))

/-- A timeout at clock `k` is a run that spends more than `k` charges. -/
theorem timeout_iff {s : σ} {k : Nat} :
    Reaches step s k .timeout ↔ ∃ c s', Star step s c s' ∧ k < c := by
  constructor
  · intro h
    generalize hr : (Result.timeout : Result α) = r at h
    induction h with
    | final hf => subst hr; exact absurd rfl hf.ne_timeout
    | free hs _ ih =>
      obtain ⟨c, s'', hst, hk⟩ := ih hr
      exact ⟨c, s'', .free hs hst, hk⟩
    | charge hs _ ih =>
      obtain ⟨c, s'', hst, hk⟩ := ih hr
      exact ⟨c + 1, s'', .charge hs hst, by omega⟩
    | @timeout s s' hs => exact ⟨1, s', .charge hs (.refl _), by omega⟩
  · rintro ⟨c, s', hst, hk⟩
    exact timeout_of_star hst hk

/-- An outcome other than `timeout` is a final step reached within the
clock. -/
theorem iff_final {s : σ} {k : Nat} {r : Result α} (hr : r ≠ .timeout) :
    Reaches step s k r ↔ ∃ c s', Star step s c s' ∧ c ≤ k ∧ Final (step s') r := by
  constructor
  · intro h
    induction h with
    | @final s k r hf => exact ⟨0, s, .refl _, Nat.zero_le _, hf⟩
    | free hs _ ih =>
      obtain ⟨c, s'', hst, hk, hf⟩ := ih hr
      exact ⟨c, s'', .free hs hst, hk, hf⟩
    | charge hs _ ih =>
      obtain ⟨c, s'', hst, hk, hf⟩ := ih hr
      exact ⟨c + 1, s'', .charge hs hst, by omega, hf⟩
    | timeout _ => exact absurd rfl hr
  · rintro ⟨c, s', hst, hk, hf⟩
    have := star (k := k - c) hst (.final hf)
    rwa [Nat.sub_add_cancel hk] at this

/-- A final step reached with `c` charges is the outcome at every clock of
at least `c`. -/
theorem of_final {s s' : σ} {c k : Nat} {r : Result α} (hst : Star step s c s')
    (hf : Final (step s') r) (hk : c ≤ k) : Reaches step s k r :=
  (iff_final hf.ne_timeout).2 ⟨c, s', hst, hk, hf⟩

end Reaches

/-! ## Runs -/

/-- `c` is the clocked outcome of running `step` from `s`: at every clock,
the run reaches `c k`. -/
def Runs (step : σ → Step σ α) (s : σ) (c : Nat → Result α) : Prop :=
  ∀ k, Reaches step s k (c k)

namespace Runs

variable {step : σ → Step σ α} {s : σ} {c : Nat → Result α}

theorem eq (h : Runs step s c) {k : Nat} {r : Result α} (hr : Reaches step s k r) : c k = r :=
  (h k).det hr

/-- The outcome of a run is unique. -/
theorem unique {c' : Nat → Result α} (h : Runs step s c) (h' : Runs step s c') : c = c' :=
  funext fun k => h.eq (h' k)

/-- Every `Runs` is clock monotone. -/
theorem clockMono (h : Runs step s c) : ClockMono c := fun _ _ hk hne =>
  h.eq ((h _).mono hne hk)

end Runs

/-! ## The clocked runner -/

section runClocked

variable {step : σ → Step σ α}

/-- The runner is sound: an outcome other than `timeout` is reached. -/
theorem runClocked_sound {fuel k : Nat} {s : σ} {r : Result α}
    (h : runClocked step fuel k s = r) (hr : r ≠ .timeout) : Reaches step s k r := by
  induction fuel generalizing k s with
  | zero => simp [runClocked] at h; exact absurd h.symm hr
  | succ fuel ih =>
    unfold runClocked at h
    split at h
    · next s' hs => exact .free hs (ih h)
    · next s' hs =>
      cases k with
      | zero => exact absurd h.symm hr
      | succ k => exact .charge hs (ih h)
    · next value hs => subst h; exact .final (hs ▸ .done)
    · next failure hs => subst h; exact .final (hs ▸ .fail)
    · next hs => subst h; exact .final (hs ▸ .trap)
    · next hs => subst h; exact .final (hs ▸ .stuck)

/-- A timeout that is not the clock's comes from running out of fuel. -/
theorem runClocked_timeout {fuel k : Nat} {s : σ} (h : runClocked step fuel k s = .timeout) :
    Reaches step s k .timeout ∨ ∃ c s', Star step s c s' ∧ c ≤ k := by
  induction fuel generalizing k s with
  | zero => exact .inr ⟨0, s, .refl _, Nat.zero_le _⟩
  | succ fuel ih =>
    unfold runClocked at h
    split at h
    · next s' hs =>
      rcases ih h with h' | ⟨c, s'', hst, hk⟩
      · exact .inl (.free hs h')
      · exact .inr ⟨c, s'', .free hs hst, hk⟩
    · next s' hs =>
      cases k with
      | zero => exact .inl (.timeout hs)
      | succ k =>
        rcases ih h with h' | ⟨c, s'', hst, hk⟩
        · exact .inl (.charge hs h')
        · exact .inr ⟨c + 1, s'', .charge hs hst, by omega⟩
    all_goals simp at h

/-- The runner is complete: enough fuel reaches every outcome. -/
theorem runClocked_complete {s : σ} {k : Nat} {r : Result α} (h : Reaches step s k r) :
    ∃ n, ∀ fuel, n ≤ fuel → runClocked step fuel k s = r := by
  induction h with
  | @final s k r hf =>
    refine ⟨1, fun fuel hfuel => ?_⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    unfold runClocked
    generalize step s = st at hf ⊢
    cases hf <;> rfl
  | @free s s' k r hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun fuel hfuel => ?_⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [runClocked, hs]
    exact hn fuel (by omega)
  | @charge s s' k r hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun fuel hfuel => ?_⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [runClocked, hs]
    exact hn fuel (by omega)
  | timeout hs =>
    refine ⟨1, fun fuel hfuel => ?_⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [runClocked, hs]

/-- More fuel never changes an outcome other than `timeout`. -/
theorem runClocked_fuel_mono {fuel fuel' k : Nat} {s : σ}
    (h : runClocked step fuel k s ≠ .timeout) (hle : fuel ≤ fuel') :
    runClocked step fuel' k s = runClocked step fuel k s := by
  induction fuel generalizing fuel' k s with
  | zero => simp [runClocked] at h
  | succ fuel ih =>
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [runClocked] at h ⊢
    cases hs : step s with
    | next s' b =>
      cases b with
      | false =>
        simp only [hs] at h ⊢
        exact ih h (by omega)
      | true =>
        cases k with
        | zero => simp only [hs] at h ⊢
        | succ k =>
          simp only [hs] at h ⊢
          exact ih h (by omega)
    | _ => rfl

end runClocked

/-! ## Fuel sufficiency -/

/-- A potential for `step` under the invariant `inv`: a free step decreases
`φ`, and a charge raises it by at most `D`. -/
structure Potential (step : σ → Step σ α) (inv : σ → Prop) (φ : σ → Nat) (D : Nat) : Prop where
  free : ∀ {s s' : σ}, inv s → step s = .next s' false → inv s' ∧ φ s' < φ s
  charge : ∀ {s s' : σ}, inv s → step s = .next s' true → inv s' ∧ φ s' ≤ φ s + D

namespace Potential

variable {step : σ → Step σ α} {inv : σ → Prop} {φ : σ → Nat} {D : Nat}

/-- Fuel above `φ s + k·(D + 1)` never runs out before the clock does: the
runner reaches its outcome. -/
theorem runClocked (hp : Potential step inv φ D) {s : σ} {k fuel : Nat} (hs : inv s)
    (hfuel : φ s + k * (D + 1) < fuel) : Reaches step s k (runClocked step fuel k s) := by
  induction fuel generalizing k s with
  | zero => omega
  | succ fuel ih =>
    unfold Sem.runClocked
    split
    · next s' hst =>
      obtain ⟨hs', hφ⟩ := hp.free hs hst
      exact .free hst (ih hs' (by omega))
    · next s' hst =>
      obtain ⟨hs', hφ⟩ := hp.charge hs hst
      cases k with
      | zero => exact .timeout hst
      | succ k =>
        refine .charge hst (ih hs' ?_)
        rw [Nat.succ_mul] at hfuel
        omega
    · next value hst => exact .final (hst ▸ .done)
    · next failure hst => exact .final (hst ▸ .fail)
    · next hst => exact .final (hst ▸ .trap)
    · next hst => exact .final (hst ▸ .stuck)

/-- Every clock has an outcome. -/
theorem reaches (hp : Potential step inv φ D) {s : σ} (hs : inv s) (k : Nat) :
    ∃ r, Reaches step s k r :=
  ⟨_, hp.runClocked (fuel := φ s + k * (D + 1) + 1) hs (by omega)⟩

/-- The runner with sufficient fuel is the clocked outcome of the run. -/
theorem runs (hp : Potential step inv φ D) {s : σ} (hs : inv s) {fuel : Nat → Nat}
    (hfuel : ∀ k, φ s + k * (D + 1) < fuel k) :
    Runs step s (fun k => Sem.runClocked step (fuel k) k s) := fun k =>
  hp.runClocked hs (hfuel k)

/-- The runner with sufficient fuel is clock monotone. -/
theorem clockMono (hp : Potential step inv φ D) {s : σ} (hs : inv s) {fuel : Nat → Nat}
    (hfuel : ∀ k, φ s + k * (D + 1) < fuel k) :
    ClockMono (fun k => Sem.runClocked step (fuel k) k s) :=
  (hp.runs hs hfuel).clockMono

end Potential

/-! ## Simulation diagrams -/

section Diagram

variable {σ₁ σ₂ α β : Type} {step₁ : σ₁ → Step σ₁ α} {step₂ : σ₂ → Step σ₂ β}

/-- The target run from `s` fails for a resource. -/
def Fails (step : σ → Step σ α) (s : σ) : Prop :=
  ∃ c s' failure, Star step s c s' ∧ step s' = .fail failure

/-- A forward simulation diagram with state relation `M` and value
relation `R`: each source step is matched by target steps spending at least
as many charges, or the target fails for a resource; each final source step
is matched by a final target step. -/
structure Diagram (step₁ : σ₁ → Step σ₁ α) (step₂ : σ₂ → Step σ₂ β) (R : α → β → Prop)
    (M : σ₁ → σ₂ → Prop) : Prop where
  next : ∀ {s₁ s₁' : σ₁} {s₂ : σ₂} {b : Bool}, M s₁ s₂ → step₁ s₁ = .next s₁' b →
    (∃ c s₂', Star step₂ s₂ c s₂' ∧ b.toNat ≤ c ∧ M s₁' s₂') ∨ Fails step₂ s₂
  final : ∀ {s₁ : σ₁} {s₂ : σ₂} {r : Result α}, M s₁ s₂ → Final (step₁ s₁) r →
    ∃ c s₂' r₂, Star step₂ s₂ c s₂' ∧ Final (step₂ s₂') r₂ ∧ Result.Refines R r r₂

/-- A target timeout or resource failure at clock `k`. -/
private def TimeoutOrFail (step : σ → Step σ α) (s : σ) (k : Nat) : Prop :=
  Reaches step s k .timeout ∨ ∃ failure, Reaches step s k (.resource failure)

private theorem TimeoutOrFail.down {step : σ → Step σ α} {s : σ} {k j : Nat}
    (h : TimeoutOrFail step s k) (hj : j ≤ k) : TimeoutOrFail step s j := by
  rcases h with h | ⟨failure, h⟩
  · exact .inl (h.timeout_le hj)
  · exact (h.down hj).elim (fun h => .inr ⟨failure, h⟩) .inl

private theorem TimeoutOrFail.star {step : σ → Step σ α} {s s' : σ} {c k : Nat}
    (hst : Star step s c s') (h : c ≤ k → TimeoutOrFail step s' (k - c)) :
    TimeoutOrFail step s k := by
  by_cases hk : k < c
  · exact .inl (Reaches.timeout_of_star hst hk)
  · have := Nat.sub_add_cancel (Nat.le_of_not_lt hk)
    rcases h (by omega) with h | ⟨failure, h⟩
    · exact .inl (this ▸ h.star hst)
    · exact .inr ⟨failure, this ▸ h.star hst⟩

private theorem TimeoutOrFail.of_fails {step : σ → Step σ α} {s : σ} (hf : Fails step s)
    (k : Nat) : TimeoutOrFail step s k := by
  obtain ⟨c, s', failure, hst, hs'⟩ := hf
  exact TimeoutOrFail.star hst fun _ => .inr ⟨failure, .final (hs' ▸ .fail)⟩

namespace Diagram

variable {R : α → β → Prop} {M : σ₁ → σ₂ → Prop}

/-- The forward clause at the level of `Reaches`. -/
theorem forward (hd : Diagram step₁ step₂ R M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r ≠ .timeout) {s₂ : σ₂} (hm : M s₁ s₂) :
    ∃ k' r₂, Reaches step₂ s₂ k' r₂ ∧ Result.Refines R r r₂ := by
  induction h generalizing s₂ with
  | final hf =>
    obtain ⟨c, s₂', r₂, hst, hf₂, href⟩ := hd.final hm hf
    exact ⟨c, r₂, .of_final hst hf₂ (Nat.le_refl _), href⟩
  | free hs _ ih | charge hs _ ih =>
    rcases hd.next hm hs with ⟨c, s₂', hst, _, hm'⟩ | ⟨c, s₂', failure, hst, hf⟩
    · obtain ⟨k', r₂, h₂, href⟩ := ih hr hm'
      exact ⟨k' + c, r₂, h₂.star hst, href⟩
    · exact ⟨c, _, .of_final hst (hf ▸ .fail) (Nat.le_refl _), .resource failure⟩
  | timeout _ => exact absurd rfl hr

/-- The timeout clause at the level of `Reaches`, with the identity clock
map. -/
private theorem timeout' (hd : Diagram step₁ step₂ R M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r = .timeout) {s₂ : σ₂} (hm : M s₁ s₂) :
    TimeoutOrFail step₂ s₂ k := by
  induction h generalizing s₂ with
  | final hf => exact absurd hr hf.ne_timeout
  | @free _ _ k _ hs _ ih =>
    rcases hd.next hm hs with ⟨c, s₂', hst, _, hm'⟩ | hf
    · exact TimeoutOrFail.star hst fun _ => (ih hr hm').down (by omega)
    · exact TimeoutOrFail.of_fails hf _
  | @charge _ _ k _ hs _ ih =>
    rcases hd.next hm hs with ⟨c, s₂', hst, hc, hm'⟩ | hf
    · simp only [Bool.toNat_true] at hc
      exact TimeoutOrFail.star hst fun _ => (ih hr hm').down (by omega)
    · exact TimeoutOrFail.of_fails hf _
  | timeout hs =>
    rcases hd.next hm hs with ⟨c, s₂', hst, hc, _⟩ | hf
    · simp only [Bool.toNat_true] at hc
      exact .inl (Reaches.timeout_of_star hst (by omega))
    · exact TimeoutOrFail.of_fails hf _

theorem timeout (hd : Diagram step₁ step₂ R M) {s₁ : σ₁} {k : Nat}
    (h : Reaches step₁ s₁ k .timeout) {s₂ : σ₂} (hm : M s₁ s₂) :
    Reaches step₂ s₂ k .timeout ∨ ∃ failure, Reaches step₂ s₂ k (.resource failure) :=
  hd.timeout' h rfl hm

/-- A forward diagram gives a clocked simulation with the identity clock
map between related states that both run. -/
theorem sim (hd : Diagram step₁ step₂ R M) {s₁ : σ₁} {s₂ : σ₂} (hm : M s₁ s₂)
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} (h₁ : Runs step₁ s₁ c₁)
    (h₂ : Runs step₂ s₂ c₂) : Sim R id c₁ c₂ where
  forward k hk := by
    obtain ⟨k', r₂, hr₂, href⟩ := hd.forward (h₁ k) hk hm
    exact ⟨k', h₂.eq hr₂ ▸ href⟩
  timeout k hk := by
    have hk' : Reaches step₁ s₁ k .timeout := hk ▸ h₁ k
    rcases hd.timeout hk' hm with h | ⟨failure, h⟩
    · exact .inl (h₂.eq h)
    · exact .inr ⟨failure, h₂.eq h⟩

end Diagram

/-- From a big-step source to a small-step target: every source outcome
other than a timeout or a stuck state is matched by a final target step
reached with some number of charges, and a source timeout at `f k` gives a
target run that spends more than `k` charges or fails for a resource. -/
theorem Sim.ofStar {R : α → β → Prop} {f : Nat → Nat} {c₁ : Nat → Result α}
    {s₂ : σ₂} {c₂ : Nat → Result β} (h₂ : Runs step₂ s₂ c₂)
    (forward : ∀ k, c₁ k ≠ .timeout → c₁ k ≠ .stuck →
      ∃ c s₂' r₂, Star step₂ s₂ c s₂' ∧ Final (step₂ s₂') r₂ ∧ Result.Refines R (c₁ k) r₂)
    (timeout : ∀ k, c₁ (f k) = .timeout →
      ∃ c s₂', Star step₂ s₂ c s₂' ∧ (k < c ∨ ∃ failure, step₂ s₂' = .fail failure)) :
    Sim R f c₁ c₂ where
  forward k hk := by
    by_cases hst : c₁ k = .stuck
    · exact ⟨0, hst ▸ .stuck⟩
    · obtain ⟨c, s₂', r₂, hstar, hf, href⟩ := forward k hk hst
      exact ⟨c, (h₂.eq (.of_final hstar hf (Nat.le_refl _))) ▸ href⟩
  timeout k hk := by
    obtain ⟨c, s₂', hstar, hc | ⟨failure, hs'⟩⟩ := timeout k hk
    · exact .inl (h₂.eq (Reaches.timeout_of_star hstar hc))
    · rcases TimeoutOrFail.of_fails ⟨c, s₂', failure, hstar, hs'⟩ k with h | ⟨failure', h⟩
      · exact .inl (h₂.eq h)
      · exact .inr ⟨failure', h₂.eq h⟩

end Diagram

end Compilatrix.Sem
