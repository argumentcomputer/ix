import Compilatrix.Sem.Smallstep

/-!
# A lock-step diagram that asks nothing of a stuck source

`Sem.Diagram.final` asks a stuck source step to be matched by a final
target step. A register allocation cannot promise that: where Xv is stuck
(an unbound register, a call of the wrong arity) Xl runs on with whatever
its locations hold, and need not stop. `LockStep` drops that case, and asks
more of the others: each source step is matched by target steps spending
exactly its charge, and each final source step other than a stuck one by
the same final target step after free steps. Then the target reaches every
outcome of the source other than a stuck one at the same clock
(`LockStep.reaches`), timeouts included, which gives a clocked simulation
with the identity clock map (`LockStep.sim`).
-/

namespace Compilatrix.Xv.Validate

open Compilatrix.Sem

variable {σ₁ σ₂ α : Type} {step₁ : σ₁ → Step σ₁ α} {step₂ : σ₂ → Step σ₂ α}

/-- A step followed by free steps. -/
theorem star_zero_step {σ : Type} {step : σ → Step σ α} {s s' s'' : σ} {b : Bool}
    (h : Star step s 0 s') (hs : step s' = .next s'' b) : Star step s b.toNat s'' := by
  have := h.trans (Star.single hs)
  rwa [Nat.zero_add] at this

/-- A lock-step forward diagram with state relation `M`: each source step
is matched by target steps spending the same charge, and each final source
step other than a stuck one by free target steps and the same final step. -/
structure LockStep (step₁ : σ₁ → Step σ₁ α) (step₂ : σ₂ → Step σ₂ α) (M : σ₁ → σ₂ → Prop) : Prop where
  next : ∀ {s₁ s₁' : σ₁} {s₂ : σ₂} {b : Bool}, M s₁ s₂ → step₁ s₁ = .next s₁' b →
    ∃ s₂', Star step₂ s₂ b.toNat s₂' ∧ M s₁' s₂'
  final : ∀ {s₁ : σ₁} {s₂ : σ₂} {r : Result α}, M s₁ s₂ → Final (step₁ s₁) r → r ≠ .stuck →
    ∃ s₂', Star step₂ s₂ 0 s₂' ∧ Final (step₂ s₂') r

namespace LockStep

variable {M : σ₁ → σ₂ → Prop}

/-- The target reaches each outcome of the source other than a stuck one,
at the same clock. -/
theorem reaches (hd : LockStep step₁ step₂ M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r ≠ .stuck) {s₂ : σ₂} (hm : M s₁ s₂) : Reaches step₂ s₂ k r := by
  induction h generalizing s₂ with
  | final hf =>
    obtain ⟨s₂', hst, hf₂⟩ := hd.final hm hf hr
    exact .of_final hst hf₂ (Nat.zero_le _)
  | free hst _ ih =>
    obtain ⟨s₂', hst₂, hm'⟩ := hd.next hm hst
    exact (ih hr hm').star hst₂
  | charge hst _ ih =>
    obtain ⟨s₂', hst₂, hm'⟩ := hd.next hm hst
    exact (ih hr hm').star hst₂
  | timeout hst =>
    obtain ⟨s₂', hst₂, _⟩ := hd.next hm hst
    exact Reaches.timeout_of_star hst₂ (by simp)

/-- Between related states that both run, the target's outcome at each
clock is the source's, unless the source is stuck. -/
theorem eq (hd : LockStep step₁ step₂ M) {s₁ : σ₁} {s₂ : σ₂} (hm : M s₁ s₂)
    {c₁ c₂ : Nat → Result α} (h₁ : Runs step₁ s₁ c₁) (h₂ : Runs step₂ s₂ c₂) {k : Nat}
    (hk : c₁ k ≠ .stuck) : c₂ k = c₁ k :=
  h₂.eq (hd.reaches (h₁ k) hk hm)

/-- A lock-step diagram gives a clocked simulation with the identity clock
map, with equal values and no extra target resource failures. -/
theorem sim (hd : LockStep step₁ step₂ M) {s₁ : σ₁} {s₂ : σ₂} (hm : M s₁ s₂)
    {c₁ c₂ : Nat → Result α} (h₁ : Runs step₁ s₁ c₁) (h₂ : Runs step₂ s₂ c₂) : Sim Eq id c₁ c₂ where
  forward k _ := by
    by_cases hs : c₁ k = .stuck
    · exact ⟨0, hs ▸ .stuck⟩
    · exact ⟨k, hd.eq hm h₁ h₂ hs ▸ .refl fun _ => rfl⟩
  timeout k hk := by
    have hk' : c₁ k = .timeout := hk
    exact .inl ((hd.eq hm h₁ h₂ (by rw [hk']; simp)).trans hk')

end LockStep

end Compilatrix.Xv.Validate
