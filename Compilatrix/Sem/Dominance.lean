import Compilatrix.Sem.SimUpTo

/-! # Tick dominance under a charge

Two `SimUpTo` rules for a translation whose target runs the *rest* of a
computation under a charge that the source pays before it (M2.3):

* `SimUpTo.tick`: the source charges, computes `c` one clock down and then
  continues with `d` at the full clock; the target charges and runs all of
  `T` one clock down. This is Lam's `tick t` (and a CAF's or a thunk's
  charge) against a target `tick` whose body contains the continuation.
* `SimUpTo.tickConst`: the source's charged part is a constant (Lam's `glob`
  of a function global, a closure), and the continuation only has to agree,
  at clocks at least one, with a computation `D` simulated by `T`.

Both keep the identity clock map: the target times out wherever the source
does, because it runs the source's continuation at a smaller clock. -/

set_option autoImplicit false

namespace Compilatrix.Sem

namespace SimUpTo

variable {α γ δ : Type} {R : γ → δ → Prop} {n : Nat}

private theorem tmo_down {T : Nat → Result δ} (hT : ClockMono T) {j : Nat}
    (h : T (j + 1) = .timeout ∨ ∃ failure, T (j + 1) = .resource failure) :
    T j = .timeout ∨ ∃ failure, T j = .resource failure := by
  by_cases hj : T j = .timeout
  · exact .inl hj
  · rw [hT (Nat.le_succ j) hj] at h
    rcases h with h | h
    · exact absurd h hj
    · exact .inr h

/-- A charge on both sides, the target's continuation under it. -/
theorem tick {c : Nat → Result α} {d : α → Nat → Result γ} {T : Nat → Result δ}
    (hc : ClockMono c) (hT : ClockMono T) (h : SimUpTo R n (fun k => (c k).bind (d · k)) T) :
    SimUpTo R n (fun k => (Sem.later k c).bind (d · k)) (fun k => Sem.later k T) where
  fwd k hk hne := by
    cases k with
    | zero => exact absurd rfl hne
    | succ j =>
      simp only [later_succ] at hne ⊢
      cases hcj : c j with
      | ok v =>
        simp only [hcj, Result.bind_ok] at hne ⊢
        have e : (c (j + 1)).bind (d · (j + 1)) = d v (j + 1) := by
          rw [hc (Nat.le_succ j) (by simp [hcj]), hcj]; rfl
        obtain ⟨k', h'⟩ := h.fwd (j + 1) hk (by rw [e]; exact hne)
        exact ⟨k' + 1, by rw [e] at h'; exact h'⟩
      | timeout => simp [hcj, Result.bind] at hne
      | _ =>
        obtain ⟨k', h'⟩ := h.fwd j (by omega) (by simp [hcj, Result.bind])
        exact ⟨k' + 1, by simpa [hcj, Result.bind] using h'⟩
  tmo k hk ht := by
    cases k with
    | zero => exact .inl rfl
    | succ j =>
      simp only [later_succ] at ht ⊢
      cases hcj : c j with
      | ok v =>
        simp only [hcj, Result.bind_ok] at ht
        have e : (c (j + 1)).bind (d · (j + 1)) = d v (j + 1) := by
          rw [hc (Nat.le_succ j) (by simp [hcj]), hcj]; rfl
        exact tmo_down hT (h.tmo (j + 1) hk (by rw [e]; exact ht))
      | timeout => exact h.tmo j (by omega) (by simp [hcj, Result.bind])
      | _ => simp [hcj, Result.bind] at ht

/-- A charged constant on the source, against a charge over the target: the
continuation must agree with `D` at clocks at least one. -/
theorem tickConst {x : α} {d : α → Nat → Result γ} {D : Nat → Result γ} {T : Nat → Result δ}
    (hT : ClockMono T) (h : SimUpTo R n D T) (hd : ∀ k, 1 ≤ k → d x k = D k) :
    SimUpTo R n (fun k => (Sem.later k fun _ => .ok x).bind (d · k)) (fun k => Sem.later k T) where
  fwd k hk hne := by
    cases k with
    | zero => exact absurd rfl hne
    | succ j =>
      simp only [later_succ, Result.bind_ok] at hne ⊢
      rw [hd (j + 1) (by omega)] at hne ⊢
      obtain ⟨k', h'⟩ := h.fwd (j + 1) hk hne
      exact ⟨k' + 1, h'⟩
  tmo k hk ht := by
    cases k with
    | zero => exact .inl rfl
    | succ j =>
      simp only [later_succ, Result.bind_ok] at ht ⊢
      rw [hd (j + 1) (by omega)] at ht
      exact tmo_down hT (h.tmo (j + 1) hk ht)

/-- A target at a smaller clock: shifting the source up by one. -/
theorem shift {c₁ : Nat → Result γ} {c₂ : Nat → Result δ} (hm : ClockMono c₂)
    (h : SimUpTo R (n + 1) c₁ c₂) : SimUpTo R n (fun j => c₁ (j + 1)) c₂ where
  fwd j hj hne := h.fwd (j + 1) (by omega) hne
  tmo j hj ht := tmo_down hm (h.tmo (j + 1) (by omega) ht)

end SimUpTo

end Compilatrix.Sem
