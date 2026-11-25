import IxCC.Sem.Forward
import IxCC.Sem.Simulation

/-!
# Amortized potential forward simulation (`PotentialForward`)

Generalizes `IxCC.Sem.Forward` with a nonnegative potential `pot : σ₁ → σ₂ → Nat`
and clock multiplier `mult > 0` so transformations that convert a bounded number
of charged steps into free steps (function/self-recursive inlining and `U`× loop
unrolling) prove `Sem.Sim R (fun k => mult * k + initPot)` cleanly in one place.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Sem (Step Final Result Star Reaches Fails Runs Sim)
open IxCC.Sem.Forward (TimeoutOrFail reaches_of_fails)

/-- A forward simulation with nonnegative potential `pot` and positive multiplier `mult`. -/
structure PotentialForward {σ₁ σ₂ α β : Type}
    (step₁ : σ₁ → Step σ₁ α) (step₂ : σ₂ → Step σ₂ β)
    (R : α → β → Prop) (M : σ₁ → σ₂ → Prop)
    (pot : σ₁ → σ₂ → Nat) (mult : Nat) : Prop where
  mult_pos : 0 < mult
  next : ∀ {s₁ s₁' : σ₁} {s₂ : σ₂} {b : Bool}, M s₁ s₂ → step₁ s₁ = .next s₁' b →
    (∃ c s₂', Star step₂ s₂ c s₂' ∧ M s₁' s₂' ∧ b.toNat + pot s₁' s₂' ≤ mult * c + pot s₁ s₂) ∨
      Fails step₂ s₂
  final : ∀ {s₁ : σ₁} {s₂ : σ₂} {r : Result α}, M s₁ s₂ → Final (step₁ s₁) r → r ≠ .stuck →
    (∃ c s₂' r₂, Star step₂ s₂ c s₂' ∧ Final (step₂ s₂') r₂ ∧ Result.Refines R r r₂) ∨
      Fails step₂ s₂

namespace PotentialForward

variable {σ₁ σ₂ α β : Type} {step₁ : σ₁ → Step σ₁ α} {step₂ : σ₂ → Step σ₂ β}
  {R : α → β → Prop} {M : σ₁ → σ₂ → Prop} {pot : σ₁ → σ₂ → Nat} {mult : Nat}

/-- Every non-timeout, non-stuck source outcome is matched by the target. -/
theorem forward (hd : PotentialForward step₁ step₂ R M pot mult)
    {s₁ : σ₁} {k : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k r) (hr : r ≠ .timeout) (hs : r ≠ .stuck)
    {s₂ : σ₂} (hm : M s₁ s₂) :
    ∃ k' r₂, Reaches step₂ s₂ k' r₂ ∧ Result.Refines R r r₂ := by
  induction h generalizing s₂ with
  | final hf =>
      rcases hd.final hm hf hs with ⟨c, s₂', r₂, hst, hf₂, href⟩ | hfail
      · exact ⟨c, r₂, .of_final hst hf₂ (Nat.le_refl _), href⟩
      · obtain ⟨k', failure, h⟩ := reaches_of_fails hfail
        exact ⟨k', _, h, .resource failure⟩
  | free hst _ ih | charge hst _ ih =>
      rcases hd.next hm hst with ⟨c, s₂', hst₂, hm', _⟩ | hfail
      · obtain ⟨k', r₂, h₂, href⟩ := ih hr hs hm'
        exact ⟨k' + c, r₂, h₂.star hst₂, href⟩
      · obtain ⟨k', failure, h⟩ := reaches_of_fails hfail
        exact ⟨k', _, h, .resource failure⟩
  | timeout _ => exact absurd rfl hr

private theorem timeout_aux (hd : PotentialForward step₁ step₂ R M pot mult)
    {s₁ : σ₁} {k₁ : Nat} {r : Result α}
    (h : Reaches step₁ s₁ k₁ r) (hr : r = .timeout)
    {s₂ : σ₂} {k₂ : Nat} (hm : M s₁ s₂) (hbud : mult * k₂ + pot s₁ s₂ ≤ k₁) :
    TimeoutOrFail step₂ s₂ k₂ := by
  have hmpos := hd.mult_pos
  induction h generalizing s₂ k₂ with
  | final hf => exact absurd hr hf.ne_timeout
  | @free _ _ k _ hs _ ih =>
      rcases hd.next hm hs with ⟨c, s₂', hst, hm', hpot⟩ | hf
      · simp only [Bool.toNat_false, Nat.zero_add] at hpot
        refine TimeoutOrFail.star hst fun hc => ih hr hm' ?_
        have hmul : mult * (k₂ - c) + mult * c = mult * k₂ := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hc]
        omega
      · exact TimeoutOrFail.of_fails hf _
  | @charge _ _ k _ hs _ ih =>
      rcases hd.next hm hs with ⟨c, s₂', hst, hm', hpot⟩ | hf
      · simp only [Bool.toNat_true] at hpot
        refine TimeoutOrFail.star hst fun hc => ih hr hm' ?_
        have hmul : mult * (k₂ - c) + mult * c = mult * k₂ := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hc]
        omega
      · exact TimeoutOrFail.of_fails hf _
  | timeout hs =>
      rcases hd.next hm hs with ⟨c, s₂', hst, _, hpot⟩ | hf
      · simp only [Bool.toNat_true] at hpot
        have hk0 : k₂ = 0 := by
          cases k₂ with
          | zero => rfl
          | succ n =>
              have : mult * (n + 1) ≥ 1 := by
                rw [Nat.mul_succ]; omega
              omega
        have hcpos : 0 < c := by
          cases c with
          | zero => simp at hpot; omega
          | succ _ => exact Nat.succ_pos _
        exact .inl (Reaches.timeout_of_star hst (by omega))
      · exact TimeoutOrFail.of_fails hf _

/-- A potential forward diagram gives a clocked simulation with clock map
`k ↦ mult * k + initPot` whenever `pot s₁ s₂ ≤ initPot`. -/
theorem sim (hd : PotentialForward step₁ step₂ R M pot mult)
    {s₁ : σ₁} {s₂ : σ₂} {initPot : Nat} (hm : M s₁ s₂) (hpot0 : pot s₁ s₂ ≤ initPot)
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} (h₁ : Runs step₁ s₁ c₁) (h₂ : Runs step₂ s₂ c₂) :
    Sim R (fun k => mult * k + initPot) c₁ c₂ where
  forward k hk := by
    by_cases hst : c₁ k = .stuck
    · exact ⟨0, hst ▸ .stuck⟩
    · obtain ⟨k', r₂, hr₂, href⟩ := hd.forward (h₁ k) hk hst hm
      exact ⟨k', h₂.eq hr₂ ▸ href⟩
  timeout k hk := by
    have hk' : Reaches step₁ s₁ (mult * k + initPot) .timeout := hk ▸ h₁ (mult * k + initPot)
    rcases hd.timeout_aux (k₂ := k) hk' rfl hm (by omega) with h | ⟨failure, h⟩
    · exact .inl (h₂.eq h)
    · exact .inr ⟨failure, h₂.eq h⟩

end PotentialForward

/-- Compose two `Sem.Sim Eq` simulations cleanly. -/
theorem sim_eq_comp {α : Type} {f g : Nat → Nat}
    {c₁ c₂ c₃ : Nat → Result α} (h₃ : IxCC.Sem.ClockMono c₃)
    (h1 : Sim Eq f c₁ c₂) (h2 : Sim Eq g c₂ c₃) :
    Sim Eq (fun k => f (g k)) c₁ c₃ :=
  (h1.comp h₃ h2).mono fun _ _ ⟨_, heq, hr⟩ => heq ▸ hr

/-- Reflexive `Sem.Sim Eq id` for an unchanged program. -/
theorem sim_eq_refl {α : Type} (c : Nat → Result α) : Sim Eq id c c :=
  ⟨fun k _ => ⟨k, Result.Refines.refl (fun _ => rfl)⟩, fun _ hk => .inl hk⟩

end IxCC.Lir.Opt
