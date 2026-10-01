import Compilatrix.Sem.Smallstep

/-!
# Forward diagrams that ask nothing of a stuck source

`Diagram.final` asks a stuck source step to be matched by a final target
step. A compiler whose target runs on where the source is stuck (an
operand outside the source's types, an alternative it never tests) cannot
promise that. `Forward` drops that case: each source step is matched by
target steps spending at least its charge, or the target fails for a
resource; each final source step other than a stuck one by a final target
step, or a resource failure. The source's outcomes other than a timeout or
a stuck state are then matched (`Forward.forward`), and its timeouts are
target timeouts or resource failures at the same clock (`Forward.timeout`),
which gives a clocked simulation with the identity clock map
(`Forward.sim`).
-/

namespace Compilatrix.Sem

variable {σ₁ σ₂ α β : Type} {step₁ : σ₁ → Step σ₁ α} {step₂ : σ₂ → Step σ₂ β}

/-- A forward diagram that asks nothing of a stuck source. -/
structure Forward (step₁ : σ₁ → Step σ₁ α) (step₂ : σ₂ → Step σ₂ β) (R : α → β → Prop)
    (M : σ₁ → σ₂ → Prop) : Prop where
  next : ∀ {s₁ s₁' : σ₁} {s₂ : σ₂} {b : Bool}, M s₁ s₂ → step₁ s₁ = .next s₁' b →
    (∃ c s₂', Star step₂ s₂ c s₂' ∧ b.toNat ≤ c ∧ M s₁' s₂') ∨ Fails step₂ s₂
  final : ∀ {s₁ : σ₁} {s₂ : σ₂} {r : Result α}, M s₁ s₂ → Final (step₁ s₁) r → r ≠ .stuck →
    (∃ c s₂' r₂, Star step₂ s₂ c s₂' ∧ Final (step₂ s₂') r₂ ∧ Result.Refines R r r₂) ∨ Fails step₂ s₂

namespace Forward

variable {R : α → β → Prop} {M : σ₁ → σ₂ → Prop}

/-- A target timeout or resource failure at clock `k`. -/
def TimeoutOrFail (step : σ → Step σ α) (s : σ) (k : Nat) : Prop :=
  Reaches step s k .timeout ∨ ∃ failure, Reaches step s k (.resource failure)

theorem TimeoutOrFail.down {σ : Type} {step : σ → Step σ α} {s : σ} {k j : Nat}
    (h : TimeoutOrFail step s k) (hj : j ≤ k) : TimeoutOrFail step s j := by
  rcases h with h | ⟨failure, h⟩
  · exact .inl (h.timeout_le hj)
  · exact (h.down hj).elim (fun h => .inr ⟨failure, h⟩) .inl

theorem TimeoutOrFail.star {σ : Type} {step : σ → Step σ α} {s s' : σ} {c k : Nat}
    (hst : Star step s c s') (h : c ≤ k → TimeoutOrFail step s' (k - c)) : TimeoutOrFail step s k := by
  by_cases hk : k < c
  · exact .inl (Reaches.timeout_of_star hst hk)
  · have := Nat.sub_add_cancel (Nat.le_of_not_lt hk)
    rcases h (by omega) with h | ⟨failure, h⟩
    · exact .inl (this ▸ h.star hst)
    · exact .inr ⟨failure, this ▸ h.star hst⟩

theorem TimeoutOrFail.of_fails {σ : Type} {step : σ → Step σ α} {s : σ} (hf : Fails step s) (k : Nat) :
    TimeoutOrFail step s k := by
  obtain ⟨c, s', failure, hst, hs'⟩ := hf
  exact TimeoutOrFail.star hst fun _ => .inr ⟨failure, .final (hs' ▸ .fail)⟩

/-- A target run that fails reaches its failure at some clock. -/
theorem reaches_of_fails {σ : Type} {step : σ → Step σ α} {s : σ} (hf : Fails step s) :
    ∃ k failure, Reaches step s k (.resource failure) := by
  obtain ⟨c, s', failure, hst, hs'⟩ := hf
  exact ⟨c, failure, .of_final hst (hs' ▸ .fail) (Nat.le_refl _)⟩

/-- **Every source outcome other than a timeout or a stuck state is
matched.** -/
theorem forward (hd : Forward step₁ step₂ R M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r ≠ .timeout) (hs : r ≠ .stuck) {s₂ : σ₂} (hm : M s₁ s₂) :
    ∃ k' r₂, Reaches step₂ s₂ k' r₂ ∧ Result.Refines R r r₂ := by
  induction h generalizing s₂ with
  | final hf =>
    rcases hd.final hm hf hs with ⟨c, s₂', r₂, hst, hf₂, href⟩ | hfail
    · exact ⟨c, r₂, .of_final hst hf₂ (Nat.le_refl _), href⟩
    · obtain ⟨k', failure, h⟩ := reaches_of_fails hfail
      exact ⟨k', _, h, .resource failure⟩
  | free hst _ ih | charge hst _ ih =>
    rcases hd.next hm hst with ⟨c, s₂', hst₂, _, hm'⟩ | hfail
    · obtain ⟨k', r₂, h₂, href⟩ := ih hr hs hm'
      exact ⟨k' + c, r₂, h₂.star hst₂, href⟩
    · obtain ⟨k', failure, h⟩ := reaches_of_fails hfail
      exact ⟨k', _, h, .resource failure⟩
  | timeout _ => exact absurd rfl hr

private theorem timeout' (hd : Forward step₁ step₂ R M) {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r = .timeout) {s₂ : σ₂} (hm : M s₁ s₂) : TimeoutOrFail step₂ s₂ k := by
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

/-- **A source timeout is a target timeout or resource failure at the same
clock.** -/
theorem timeout (hd : Forward step₁ step₂ R M) {s₁ : σ₁} {k : Nat} (h : Reaches step₁ s₁ k .timeout)
    {s₂ : σ₂} (hm : M s₁ s₂) :
    Reaches step₂ s₂ k .timeout ∨ ∃ failure, Reaches step₂ s₂ k (.resource failure) :=
  hd.timeout' h rfl hm

/-- A forward diagram gives a clocked simulation with the identity clock
map between related states that both run. -/
theorem sim (hd : Forward step₁ step₂ R M) {s₁ : σ₁} {s₂ : σ₂} (hm : M s₁ s₂)
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} (h₁ : Runs step₁ s₁ c₁) (h₂ : Runs step₂ s₂ c₂) :
    Sim R id c₁ c₂ where
  forward k hk := by
    by_cases hst : c₁ k = .stuck
    · exact ⟨0, hst ▸ .stuck⟩
    · obtain ⟨k', r₂, hr₂, href⟩ := hd.forward (h₁ k) hk hst hm
      exact ⟨k', h₂.eq hr₂ ▸ href⟩
  timeout k hk := by
    have hk' : Reaches step₁ s₁ k .timeout := hk ▸ h₁ k
    rcases hd.timeout hk' hm with h | ⟨failure, h⟩
    · exact .inl (h₂.eq h)
    · exact .inr ⟨failure, h₂.eq h⟩

end Forward

end Compilatrix.Sem
