import IxCC.Sem.Entry

/-!
# Simulations of a sequence whose first run is constant

Two calls in a row, as a caller makes them (`cx_init`, then a root): when
the source's first run returns the same value at every clock, a simulation
of it by the target's first run and, for every target value related to the
source's, a simulation of the second runs give a simulation of the
sequences (`Sim.bind_const`). Also: a simulation's source values satisfy
what every source value satisfies (`Sim.and_source`); a constant source
resource failure is simulated by a target that eventually fails for a
resource (`Sim.of_eventually_resource`).
-/

namespace IxCC.Sem

namespace Sim

variable {α β γ δ : Type} {R : α → β → Prop} {R' : γ → δ → Prop} {f : Nat → Nat}

/-- A simulation's related source values satisfy what every source value
returned at some clock satisfies. -/
theorem and_source {c₁ : Nat → Result α} {c₂ : Nat → Result β} (hs : Sim R f c₁ c₂) {P : α → Prop}
    (hP : ∀ k v, c₁ k = .ok v → P v) : Sim (fun v w => R v w ∧ P v) f c₁ c₂ where
  forward k hk := by
    obtain ⟨k', hr⟩ := hs.forward k hk
    refine ⟨k', ?_⟩
    generalize hc : c₁ k = s at hr ⊢
    generalize c₂ k' = t at hr ⊢
    cases hr with
    | ok h => exact .ok ⟨h, hP k _ hc⟩
    | timeout => exact .timeout
    | trap => exact .trap
    | stuck => exact .stuck
    | resource fl => exact .resource fl
  timeout := hs.timeout

/-- A constant source resource failure, against a target that fails for a
resource at some clock. -/
theorem of_eventually_resource {c₂ : Nat → Result β} {r : Resource} {k₀ : Nat} {fl : Resource}
    (h : c₂ k₀ = .resource fl) : Sim R f (fun _ => (.resource r : Result α)) c₂ where
  forward _ _ := ⟨k₀, by rw [h]; exact .resource fl⟩
  timeout _ h' := nomatch h'

/-- **Two runs in sequence, the source's first one constant.** -/
theorem bind_const {a : Nat → Result α} {v₀ : α} (ha : ∀ k, a k = .ok v₀) {b : Nat → Result β}
    (hb : ClockMono b) (hab : Sim R f a b) {c : α → Nat → Result γ} {d : β → Nat → Result δ}
    (hd : ∀ w, ClockMono (d w)) (hcd : ∀ w, R v₀ w → Sim R' f (c v₀) (d w)) :
    Sim R' f (fun k => (a k).bind fun v => c v k) (fun k => (b k).bind fun w => d w k) where
  forward k hk := by
    simp only [ha, Result.bind_ok] at hk ⊢
    obtain ⟨k₀, hr⟩ := hab.forward 0 (by rw [ha]; simp)
    rw [ha] at hr
    generalize hb₀ : b k₀ = t at hr
    cases hr with
    | resource fl =>
      exact ⟨k₀, by rw [hb₀]; exact .resource fl⟩
    | ok hR =>
      rename_i w
      obtain ⟨k₁, hr₁⟩ := (hcd w hR).forward k hk
      by_cases hd₁ : d w k₁ = .timeout
      · rw [hd₁] at hr₁
        rcases hr₁.of_timeout with h | h
        · exact absurd h hk
        · exact ⟨0, by rw [h]; exact .stuck⟩
      · refine ⟨max k₀ k₁, ?_⟩
        have hbK : b (max k₀ k₁) = .ok w := by
          rw [hb (Nat.le_max_left _ _) (by rw [hb₀]; simp), hb₀]
        rw [hbK, Result.bind_ok, hd w (Nat.le_max_right _ _) hd₁]
        exact hr₁
  timeout k hk := by
    simp only [ha, Result.bind_ok] at hk
    obtain ⟨k₀, hr⟩ := hab.forward 0 (by rw [ha]; simp)
    rw [ha] at hr
    by_cases hbk : b k = .timeout
    · exact .inl (by rw [hbk]; rfl)
    · generalize hb₀ : b k₀ = t at hr
      have hne : t ≠ .timeout := by cases hr <;> simp
      have heq : b k = t := hb₀ ▸ hb.eq_of_ne_timeout hbk (hb₀ ▸ hne)
      cases hr with
      | resource fl =>
        exact .inr ⟨fl, by rw [heq]; rfl⟩
      | ok hR =>
        rename_i w
        rw [heq, Result.bind_ok]
        exact (hcd w hR).timeout k hk

/-- Both runs' values mapped, to equal values where they were related. -/
theorem map_eq {c₁ : Nat → Result α} {c₂ : Nat → Result β} (hs : Sim R f c₁ c₂) {g₁ : α → γ} {g₂ : β → γ}
    (hg : ∀ v w, R v w → g₁ v = g₂ w) : Sim Eq f (fun k => (c₁ k).map g₁) (fun k => (c₂ k).map g₂) where
  forward k hk := by
    have hk' : c₁ k ≠ .timeout := fun h => hk (by simp [h, Result.map, Result.bind])
    obtain ⟨k', hr⟩ := hs.forward k hk'
    refine ⟨k', ?_⟩
    generalize c₁ k = s at hr ⊢
    generalize c₂ k' = t at hr ⊢
    cases hr with
    | ok h => exact .ok (hg _ _ h)
    | timeout => exact .timeout
    | trap => exact .trap
    | stuck => exact .stuck
    | resource fl => exact .resource fl
  timeout k hk := by
    have hk' : c₁ (f k) = .timeout := by
      cases h : c₁ (f k) <;> simp_all [Result.map, Result.bind]
    rcases hs.timeout k hk' with h | ⟨fl, h⟩
    · exact .inl (by simp [h, Result.map, Result.bind])
    · exact .inr ⟨fl, by simp [h, Result.map, Result.bind]⟩

end Sim

end IxCC.Sem
