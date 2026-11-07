import IxCC.Sem.Smallstep
import IxCC.Sem.Traced

/-!
# A traced clocked runner (IO toy support)

A small-step semantics whose states carry the events performed so far
(`tr : σ → List E`) runs with `runT`: `Sem.runClocked`, returning with the
outcome the trace of the state where the run stopped (at a final step, at a
charge with an empty clock, or out of fuel). Its relational reading
`ReachesT` mirrors `Sem.Reaches`: deterministic (`det`), keeping a final
outcome at larger clocks (`mono`), and, when every step extends the trace
(`Grows`), prefix monotone in the clock (`trace_mono`). A `Potential`
bounds the fuel as for `runClocked` (`reachesT_runT`), so the runner with
sufficient fuel `RunsT` and is trace monotone (`RunsT.traceMono`).

The Star lemmas connect runs to the simulation clauses: a final step
reached within the clock is the outcome (`of_final`), a path with more
charges than the clock times out before its end (`timeout_of_star`), and a
path within the clock is passed through (`passes`).

This lives with the toy: the IO design note decides whether small-step
levels carry their traces in their states.
-/

namespace IxCCTests.Sem.Toy.IO

open IxCC.Sem

variable {σ α E : Type}

/-- The clocked runner, returning the trace of the state where it
stopped. -/
def runT (step : σ → Step σ α) (tr : σ → List E) : (fuel k : Nat) → σ → Traced E α
  | 0, _, s => ⟨.timeout, tr s⟩
  | fuel + 1, k, s =>
      match step s with
      | .next s' false => runT step tr fuel k s'
      | .next s' true =>
          match k with
          | 0 => ⟨.timeout, tr s⟩
          | k + 1 => runT step tr fuel k s'
      | .done value => ⟨.ok value, tr s⟩
      | .fail r => ⟨.resource r, tr s⟩
      | .trap => ⟨.trap, tr s⟩
      | .stuck => ⟨.stuck, tr s⟩

/-- `ReachesT step tr s k t`: from `s` with clock `k` the run ends in `t`,
whose trace is the trace of the state where it stopped. -/
inductive ReachesT (step : σ → Step σ α) (tr : σ → List E) : σ → Nat → Traced E α → Prop
  | final {s : σ} {k : Nat} {r : Result α} : Final (step s) r → ReachesT step tr s k ⟨r, tr s⟩
  | free {s s' : σ} {k : Nat} {t : Traced E α} : step s = .next s' false →
      ReachesT step tr s' k t → ReachesT step tr s k t
  | charge {s s' : σ} {k : Nat} {t : Traced E α} : step s = .next s' true →
      ReachesT step tr s' k t → ReachesT step tr s (k + 1) t
  | timeout {s s' : σ} : step s = .next s' true → ReachesT step tr s 0 ⟨.timeout, tr s⟩

/-- Every step extends the trace. -/
def Grows (step : σ → Step σ α) (tr : σ → List E) : Prop :=
  ∀ {s s' : σ} {b : Bool}, step s = .next s' b → tr s <+: tr s'

theorem Star.trace_prefix {step : σ → Step σ α} {tr : σ → List E} (hg : Grows step tr)
    {s s' : σ} {c : Nat} (h : Star step s c s') : tr s <+: tr s' := by
  induction h with
  | refl => exact List.prefix_refl _
  | free hs _ ih => exact (hg hs).trans ih
  | charge hs _ ih => exact (hg hs).trans ih

namespace ReachesT

variable {step : σ → Step σ α} {tr : σ → List E}

theorem inv_final {s : σ} {k : Nat} {r : Result α} {t : Traced E α}
    (hf : Final (step s) r) (h : ReachesT step tr s k t) : t = ⟨r, tr s⟩ := by
  cases h with
  | final hf' => rw [hf'.det hf]
  | free hs _ => rw [hs] at hf; exact absurd hf Final.not_next
  | charge hs _ => rw [hs] at hf; exact absurd hf Final.not_next
  | timeout hs => rw [hs] at hf; exact absurd hf Final.not_next

theorem inv_free {s s' : σ} {k : Nat} {t : Traced E α} (hs : step s = .next s' false)
    (h : ReachesT step tr s k t) : ReachesT step tr s' k t := by
  cases h with
  | final hf => rw [hs] at hf; exact absurd hf Final.not_next
  | free hs' h => rw [hs] at hs'; cases hs'; exact h
  | charge hs' _ => rw [hs] at hs'; cases hs'
  | timeout hs' => rw [hs] at hs'; cases hs'

theorem inv_charge {s s' : σ} {k : Nat} {t : Traced E α} (hs : step s = .next s' true)
    (h : ReachesT step tr s (k + 1) t) : ReachesT step tr s' k t := by
  cases h with
  | final hf => rw [hs] at hf; exact absurd hf Final.not_next
  | free hs' _ => rw [hs] at hs'; cases hs'
  | charge hs' h => rw [hs] at hs'; cases hs'; exact h

theorem inv_charge_zero {s s' : σ} {t : Traced E α} (hs : step s = .next s' true)
    (h : ReachesT step tr s 0 t) : t = ⟨.timeout, tr s⟩ := by
  cases h with
  | final hf => rw [hs] at hf; exact absurd hf Final.not_next
  | free hs' _ => rw [hs] at hs'; cases hs'
  | timeout _ => rfl

/-- The outcome at a clock is unique. -/
theorem det {s : σ} {k : Nat} {t t' : Traced E α} (h : ReachesT step tr s k t)
    (h' : ReachesT step tr s k t') : t = t' := by
  induction h with
  | final hf => exact (inv_final hf h').symm
  | free hs _ ih => exact ih (inv_free hs h')
  | charge hs _ ih => exact ih (inv_charge hs h')
  | timeout hs => exact (inv_charge_zero hs h').symm

/-- An outcome other than `timeout` is kept, with its trace, at every
larger clock. -/
theorem mono {s : σ} {k k' : Nat} {t : Traced E α} (h : ReachesT step tr s k t)
    (ht : t.result ≠ .timeout) (hk : k ≤ k') : ReachesT step tr s k' t := by
  induction h generalizing k' with
  | final hf => exact .final hf
  | free hs _ ih => exact .free hs (ih ht hk)
  | charge hs _ ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    exact .charge hs (ih ht (by omega))
  | timeout _ => exact absurd rfl ht

/-- The trace where a run stops extends the trace where it started. -/
theorem start_prefix (hg : Grows step tr) {s : σ} {k : Nat} {t : Traced E α}
    (h : ReachesT step tr s k t) : tr s <+: t.trace := by
  induction h with
  | final _ => exact List.prefix_refl _
  | free hs _ ih => exact (hg hs).trans ih
  | charge hs _ ih => exact (hg hs).trans ih
  | timeout _ => exact List.prefix_refl _

/-- The trace is prefix monotone in the clock. -/
theorem trace_mono (hg : Grows step tr) {s : σ} {k k' : Nat} {t t' : Traced E α}
    (h : ReachesT step tr s k t) (h' : ReachesT step tr s k' t') (hk : k ≤ k') :
    t.trace <+: t'.trace := by
  induction h generalizing k' with
  | final hf => rw [inv_final hf h']; exact List.prefix_refl _
  | free hs _ ih => exact ih (inv_free hs h') hk
  | charge hs _ ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    exact ih (inv_charge hs h') (by omega)
  | timeout _ => exact start_prefix hg h'

/-- Prefix a run: `c` charges on the way cost `c` units of clock. -/
theorem star {s s' : σ} {c k : Nat} {t : Traced E α} (hst : Star step s c s')
    (h : ReachesT step tr s' k t) : ReachesT step tr s (k + c) t := by
  induction hst with
  | refl => exact h
  | free hs _ ih => exact .free hs (ih h)
  | charge hs _ ih =>
    rw [← Nat.add_assoc]
    exact .charge hs (ih h)

/-- Drop a prefix: the run from `s` passes through `s'` with `c` fewer
units of clock. -/
theorem of_star {s s' : σ} {c k : Nat} {t : Traced E α} (hst : Star step s c s')
    (h : ReachesT step tr s (k + c) t) : ReachesT step tr s' k t := by
  induction hst with
  | refl => exact h
  | free hs _ ih => exact ih (inv_free hs h)
  | charge hs _ ih =>
    rw [← Nat.add_assoc] at h
    exact ih (inv_charge hs h)

/-- A final step reached with `c` charges is the outcome at every clock of
at least `c`, with the trace of that state. -/
theorem of_final {s s' : σ} {c k : Nat} {r : Result α} (hst : Star step s c s')
    (hf : Final (step s') r) (hk : c ≤ k) : ReachesT step tr s k ⟨r, tr s'⟩ := by
  have := star (k := k - c) (tr := tr) hst (.final hf)
  rwa [Nat.sub_add_cancel hk] at this

/-- A path that spends more charges than the clock times out before its
end. -/
theorem timeout_of_star (hg : Grows step tr) {s s' : σ} {c k : Nat} (hst : Star step s c s')
    (hk : k < c) : ∃ tr', ReachesT step tr s k ⟨.timeout, tr'⟩ ∧ tr' <+: tr s' := by
  induction hst generalizing k with
  | refl => omega
  | free hs _ ih =>
    obtain ⟨tr', h, hp⟩ := ih hk
    exact ⟨tr', .free hs h, hp⟩
  | charge hs hst ih =>
    cases k with
    | zero => exact ⟨_, .timeout hs, (hg hs).trans (Star.trace_prefix hg hst)⟩
    | succ j =>
      obtain ⟨tr', h, hp⟩ := ih (k := j) (by omega)
      exact ⟨tr', .charge hs h, hp⟩

/-- A run with a clock of at least `c` passes through the end of a path
with `c` charges: its trace extends that state's. -/
theorem passes (hg : Grows step tr) {s s' : σ} {c k : Nat} {t : Traced E α}
    (hst : Star step s c s') (hk : c ≤ k) (h : ReachesT step tr s k t) : tr s' <+: t.trace := by
  have e : k = (k - c) + c := by omega
  rw [e] at h
  exact start_prefix hg (of_star hst h)

end ReachesT

/-- Fuel above `φ s + k·(D + 1)` never runs out before the clock does. -/
theorem reachesT_runT {step : σ → Step σ α} (tr : σ → List E) {inv : σ → Prop} {φ : σ → Nat}
    {D : Nat} (hp : Potential step inv φ D) {s : σ} {k fuel : Nat} (hs : inv s)
    (hfuel : φ s + k * (D + 1) < fuel) : ReachesT step tr s k (runT step tr fuel k s) := by
  induction fuel generalizing k s with
  | zero => omega
  | succ fuel ih =>
    unfold runT
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

/-- `c` is the traced clocked outcome of running `step` from `s`. -/
def RunsT (step : σ → Step σ α) (tr : σ → List E) (s : σ) (c : Nat → Traced E α) : Prop :=
  ∀ k, ReachesT step tr s k (c k)

namespace RunsT

variable {step : σ → Step σ α} {tr : σ → List E} {s : σ} {c : Nat → Traced E α}

theorem eq (h : RunsT step tr s c) {k : Nat} {t : Traced E α} (ht : ReachesT step tr s k t) :
    c k = t :=
  (h k).det ht

/-- A run whose steps extend the trace is trace monotone. -/
theorem traceMono (hg : Grows step tr) (h : RunsT step tr s c) : TraceMono c where
  final _ _ hle hk := h.eq ((h _).mono hk hle)
  grows _ _ hle := ReachesT.trace_mono hg (h _) (h _) hle

end RunsT

end IxCCTests.Sem.Toy.IO
