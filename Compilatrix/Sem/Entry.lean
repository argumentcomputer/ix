import Compilatrix.Sem.Simulation
import Compilatrix.Sem.SimUpTo
import Compilatrix.Sem.Clock

/-! # Running a root on its inputs, as the source applies it

The input of every Phase 1 level is a root index and `Nat` arguments
(`Nat × List Nat`, the `Lang` instances of SrcEval, Lam and Anf). Anf
applies a root to its arguments as a function: exactly as many arguments
enter it; fewer make a partial application (a closure, which has no
observation, charged when there are arguments); more apply its result to
the rest, which is stuck for a first-order value. Below Anf a root is a
function of fixed arity, so `entryRun` gives the levels Fir, Own and Cfg
the same convention: a call for the exact arity, a value with no
observation for fewer arguments, and the call followed by `stuck` for more.
Every run of the levels' own semantics on the exact arity is unchanged.

Also: the small-step runner is clock monotone for every step function, in
the clock and the step bound together (`runClocked_mono`), so a run whose
step bound grows with the clock is clock monotone with no further premise
(`ClockMono.runClocked`). -/

set_option autoImplicit false

namespace Compilatrix.Sem

/-- A run of a root of arity `n` on inputs `ns` (see the module comment):
`call` runs it on exactly `n` arguments, `none` is a value with no
observation. -/
def entryRun {α : Type} (n : Nat) (none : α) (call : List Nat → Nat → Result α) (ns : List Nat)
    (k : Nat) : Result α :=
  if ns.length = n then call ns k
  else if ns.length < n then (if ns = [] then .ok none else later k fun _ => .ok none)
  else (call (ns.take n) k).bind fun _ => .stuck

theorem entryRun_exact {α : Type} {n : Nat} {none : α} {call : List Nat → Nat → Result α}
    {ns : List Nat} (h : ns.length = n) (k : Nat) : entryRun n none call ns k = call ns k := by
  simp [entryRun, h]

theorem entryRun_mono {α : Type} {n : Nat} {none : α} {call : List Nat → Nat → Result α}
    (h : ∀ ns, ClockMono (call ns)) (ns : List Nat) : ClockMono (entryRun n none call ns) := by
  unfold entryRun
  by_cases he : ns.length = n
  · simp only [he, ↓reduceIte]; exact h ns
  · simp only [he, ↓reduceIte]
    by_cases hl : ns.length < n
    · simp only [hl, ↓reduceIte]
      by_cases hn : ns = []
      · simp only [hn, ↓reduceIte]; exact ClockMono.const _
      · simp only [hn, ↓reduceIte]; exact ClockMono.later (ClockMono.const _)
    · simp only [hl, ↓reduceIte]
      exact ClockMono.bind (h _) fun _ => ClockMono.const _

/-! ## Simulations of entries -/

section

variable {α β : Type} {R : α → β → Prop} {f : Nat → Nat}

/-- A simulation between equal runs. -/
theorem Sim.ofEq {c₁ c₁' : Nat → Result α} {c₂ c₂' : Nat → Result β} (h : Sim R f c₁ c₂)
    (h₁ : ∀ k, c₁' k = c₁ k) (h₂ : ∀ k, c₂' k = c₂ k) : Sim R f c₁' c₂' where
  forward k hk := by
    rw [h₁] at hk ⊢
    obtain ⟨k', h'⟩ := h.forward k hk
    exact ⟨k', by rw [h₂]; exact h'⟩
  timeout k ht := by rw [h₂]; exact h.timeout k (by rw [← h₁]; exact ht)

/-- A constant value against a constant value. -/
theorem Sim.okConst {a : α} {b : β} (h : R a b) : Sim R f (fun _ => .ok a) (fun _ => .ok b) where
  forward _ _ := ⟨0, .ok h⟩
  timeout _ h' := nomatch h'

/-- A charged constant value against a charged constant value, for a clock
map that is zero only at zero. -/
theorem Sim.laterConst {a : α} {b : β} (h : R a b) (hf : ∀ k, f k = 0 → k = 0) :
    Sim R f (fun k => later k fun _ => .ok a) (fun k => later k fun _ => .ok b) where
  forward k hk := by
    cases k with
    | zero => exact absurd rfl hk
    | succ k => exact ⟨k + 1, .ok h⟩
  timeout k hk := by
    cases hfk : f k with
    | zero => rw [hf k hfk]; exact .inl rfl
    | succ j => rw [hfk] at hk; cases hk

/-- A run followed by a step that is stuck on every value the source
returns, against the target run followed by `stuck`. -/
theorem Sim.bindStuck {α' β' : Type} {R' : α' → β' → Prop} {c₁ : Nat → Result α} {c₂ : Nat → Result β}
    {g : α → Nat → Result α'} (hs : Sim R f c₁ c₂) (hg : ∀ k v, c₁ k = .ok v → g v k = .stuck) :
    Sim R' f (fun k => (c₁ k).bind fun v => g v k) (fun k => (c₂ k).bind fun _ => (.stuck : Result β')) where
  forward k hk := by
    cases h₁ : c₁ k with
    | ok v => exact ⟨0, by rw [Result.bind_ok, hg k v h₁]; exact .stuck⟩
    | timeout => rw [h₁] at hk; exact absurd rfl hk
    | stuck => exact ⟨0, .stuck⟩
    | trap =>
      obtain ⟨k', hr⟩ := hs.forward k (by rw [h₁]; simp)
      rw [h₁] at hr
      refine ⟨k', ?_⟩
      rcases SimUpTo.refines_trap_inv hr with h₂ | ⟨fl, h₂⟩
      · rw [h₂]; exact .trap
      · rw [h₂]; exact .resource fl
    | resource fl =>
      obtain ⟨k', hr⟩ := hs.forward k (by rw [h₁]; simp)
      rw [h₁] at hr
      obtain ⟨fl', h₂⟩ := hr.of_resource
      exact ⟨k', by rw [h₂]; exact .resource fl'⟩
  timeout k hk := by
    have h₁ : c₁ (f k) = .timeout := by
      cases h : c₁ (f k) with
      | ok v => simp only [h, Result.bind_ok, hg (f k) v h] at hk; cases hk
      | timeout => rfl
      | _ => simp only [h] at hk; cases hk
    rcases hs.timeout k h₁ with h₂ | ⟨fl, h₂⟩
    · exact .inl (by simp only [h₂]; rfl)
    · exact .inr ⟨fl, by simp only [h₂]; rfl⟩

end

/-! ## The runner is clock monotone -/

theorem runClocked_mono {σ α : Type} (step : σ → Step σ α) :
    ∀ {fuel fuel' k k' : Nat} {s : σ}, fuel ≤ fuel' → k ≤ k' → runClocked step fuel k s ≠ .timeout →
      runClocked step fuel' k' s = runClocked step fuel k s
  | 0, _, _, _, _, _, _, h => by simp [runClocked] at h
  | fuel + 1, fuel', k, k', s, hf, hk, h => by
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    simp only [runClocked] at h ⊢
    cases hs : step s with
    | next s' b =>
      cases b with
      | false =>
        simp only [hs] at h ⊢
        exact runClocked_mono step (by omega) hk h
      | true =>
        cases k with
        | zero => simp [hs] at h
        | succ k =>
          obtain ⟨k₂, rfl⟩ : ∃ k₂, k' = k₂ + 1 := ⟨k' - 1, by omega⟩
          simp only [hs] at h ⊢
          exact runClocked_mono step (by omega) (by omega) h
    | _ => rfl

/-- A runner whose step bound grows with the clock is clock monotone. -/
theorem ClockMono.runClocked {σ α : Type} (step : σ → Step σ α) {fuel : Nat → Nat}
    (hf : ∀ {k k'}, k ≤ k' → fuel k ≤ fuel k') (s : σ) :
    ClockMono fun k => Sem.runClocked step (fuel k) k s :=
  fun _ _ hk hne => runClocked_mono step (hf hk) hk hne

end Compilatrix.Sem
