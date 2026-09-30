import Compilatrix.Sem.Smallstep

/-!
# A diagram that asks nothing of a stuck source

`Sem.Diagram.final` asks a stuck source step to be matched by a final
target step. A register allocation cannot promise that: where Xv is stuck
(an unbound register, a call of the wrong arity) Xl runs on with whatever
its locations hold, and need not stop. `StuckDiagram` drops that case, and
its forward clause needs no resource failure; `StuckDiagram.sim` still gives
a clocked simulation with the identity clock map, since `Sim` asks nothing
of a stuck source either.
-/

namespace Compilatrix.Xv.Validate

open Compilatrix.Sem

variable {σ₁ σ₂ α β : Type} {step₁ : σ₁ → Step σ₁ α} {step₂ : σ₂ → Step σ₂ β}

/-- A forward simulation diagram with state relation `M` and value relation
`R`: each source step is matched by target steps spending at least as many
charges, and each final source step other than a stuck one by a final
target step. -/
structure StuckDiagram (step₁ : σ₁ → Step σ₁ α) (step₂ : σ₂ → Step σ₂ β) (R : α → β → Prop)
    (M : σ₁ → σ₂ → Prop) : Prop where
  next : ∀ {s₁ s₁' : σ₁} {s₂ : σ₂} {b : Bool}, M s₁ s₂ → step₁ s₁ = .next s₁' b →
    ∃ c s₂', Star step₂ s₂ c s₂' ∧ b.toNat ≤ c ∧ M s₁' s₂'
  final : ∀ {s₁ : σ₁} {s₂ : σ₂} {r : Result α}, M s₁ s₂ → Final (step₁ s₁) r → r ≠ .stuck →
    ∃ c s₂' r₂, Star step₂ s₂ c s₂' ∧ Final (step₂ s₂') r₂ ∧ Result.Refines R r r₂

namespace StuckDiagram

variable {R : α → β → Prop} {M : σ₁ → σ₂ → Prop}

/-- The forward clause at the level of `Reaches`. -/
theorem forward (hd : StuckDiagram step₁ step₂ R M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r ≠ .timeout) (hs : r ≠ .stuck) {s₂ : σ₂} (hm : M s₁ s₂) :
    ∃ k' r₂, Reaches step₂ s₂ k' r₂ ∧ Result.Refines R r r₂ := by
  induction h generalizing s₂ with
  | final hf =>
    obtain ⟨c, s₂', r₂, hst, hf₂, href⟩ := hd.final hm hf hs
    exact ⟨c, r₂, .of_final hst hf₂ (Nat.le_refl _), href⟩
  | free hst _ ih | charge hst _ ih =>
    obtain ⟨c, s₂', hst₂, _, hm'⟩ := hd.next hm hst
    obtain ⟨k', r₂, h₂, href⟩ := ih hr hs hm'
    exact ⟨k' + c, r₂, h₂.star hst₂, href⟩
  | timeout _ => exact absurd rfl hr

/-- A source timeout is a target timeout at the same clock. -/
theorem timeout (hd : StuckDiagram step₁ step₂ R M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r = .timeout) {s₂ : σ₂} (hm : M s₁ s₂) :
    Reaches step₂ s₂ k .timeout := by
  induction h generalizing s₂ with
  | final hf => exact absurd hr hf.ne_timeout
  | @free _ _ k _ hst _ ih =>
    obtain ⟨c, s₂', hst₂, _, hm'⟩ := hd.next hm hst
    exact ((ih hr hm').star hst₂).timeout_le (by omega)
  | @charge _ _ k _ hst _ ih =>
    obtain ⟨c, s₂', hst₂, hc, hm'⟩ := hd.next hm hst
    simp only [Bool.toNat_true] at hc
    exact ((ih hr hm').star hst₂).timeout_le (by omega)
  | timeout hst =>
    obtain ⟨c, s₂', hst₂, hc, _⟩ := hd.next hm hst
    simp only [Bool.toNat_true] at hc
    exact Reaches.timeout_of_star hst₂ (by omega)

/-- A stuck-tolerant diagram gives a clocked simulation with the identity
clock map between related states that both run. -/
theorem sim (hd : StuckDiagram step₁ step₂ R M) {s₁ : σ₁} {s₂ : σ₂} (hm : M s₁ s₂)
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} (h₁ : Runs step₁ s₁ c₁)
    (h₂ : Runs step₂ s₂ c₂) : Sim R id c₁ c₂ where
  forward k hk := by
    by_cases hs : c₁ k = .stuck
    · exact ⟨0, hs ▸ .stuck⟩
    · obtain ⟨k', r₂, hr₂, href⟩ := hd.forward (h₁ k) hk hs hm
      exact ⟨k', h₂.eq hr₂ ▸ href⟩
  timeout k hk := .inl (h₂.eq (hd.timeout (h₁ k) hk hm))

end StuckDiagram

end Compilatrix.Xv.Validate
