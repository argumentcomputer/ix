import Compilatrix.Sem.Clocked

/-! # Agreement of two outcomes

`Agrees r' r`: `r'` is `r` wherever `r` does not time out, so `r'` runs at
least as far as `r`. Clock monotonicity of an evaluator is `Agrees` between
a larger and a smaller clock, proved one sequencing step at a time with
`Agrees.bind` (the toy pipeline's pattern, `CompilatrixTests.Sem.Toy.Big`,
for the IRs' mutual evaluators; M2.2). -/

namespace Compilatrix.Sem

namespace Result

/-- `r'` is `r` wherever `r` does not time out. -/
def Agrees {α : Type} (r' r : Result α) : Prop := r ≠ .timeout → r' = r

namespace Agrees

variable {α β : Type}

theorem refl (r : Result α) : Agrees r r := fun _ => rfl

theorem of_timeout {r' : Result α} : Agrees r' .timeout := fun h => absurd rfl h

theorem trans {a b c : Result α} (h₁ : Agrees a b) (h₂ : Agrees b c) : Agrees a c := fun hc => by
  rw [h₁ (by rw [h₂ hc]; exact hc), h₂ hc]

theorem bind {r r' : Result α} {f f' : α → Result β} (hr : Agrees r' r)
    (hf : ∀ v, r = .ok v → Agrees (f' v) (f v)) : Agrees (r'.bind f') (r.bind f) := by
  intro hne
  cases r with
  | ok v => rw [hr (by simp)]; exact hf v rfl hne
  | timeout => exact absurd rfl hne
  | _ => rw [hr (by simp)]; rfl

/-- A clocked function whose outcomes agree upward is monotone. -/
theorem clockMono {c : Nat → Result α} (h : ∀ k k', k ≤ k' → Agrees (c k') (c k)) :
    ClockMono c := fun _ _ hle hk => h _ _ hle hk

end Agrees

end Result

end Compilatrix.Sem
