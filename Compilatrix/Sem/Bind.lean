import Compilatrix.Sem.Agrees

/-! # Bind-form reasoning about clocked results

A small kit for proofs that reason through an evaluator's bind-form
unfolding lemmas (`Src/Proof/Unfold`, `Lam/Proof/Unfold`) rather than its
`match`es: one inversion per outcome of `Result.bind`, and `Dom` ("runs no
further"), the dual of `Agrees`, with its sequencing rule. With
`Agrees.bind`, `ClockMono.bind` and `SimUpTo.bind`, a per-construct proof
is a chain of combinator applications, one per bind of the evaluator's
rule; when the evaluator later moves to a traced monad, these combinators
get traced counterparts and the chains keep their shape (the IO toy,
`CompilatrixTests.Sem.Toy.IO`, does this with `MAgrees.bind` and
`MDom.bind`). -/

namespace Compilatrix.Sem

namespace Result

variable {α β : Type} {r : Result α} {f : α → Result β}

theorem bind_eq_ok_iff {w : β} : r.bind f = .ok w ↔ ∃ v, r = .ok v ∧ f v = .ok w := by
  cases r <;> simp [bind]

theorem bind_eq_timeout_iff : r.bind f = .timeout ↔ r = .timeout ∨ ∃ v, r = .ok v ∧ f v = .timeout := by
  cases r <;> simp [bind]

theorem bind_eq_stuck_iff : r.bind f = .stuck ↔ r = .stuck ∨ ∃ v, r = .ok v ∧ f v = .stuck := by
  cases r <;> simp [bind]

theorem bind_eq_trap_iff : r.bind f = .trap ↔ r = .trap ∨ ∃ v, r = .ok v ∧ f v = .trap := by
  cases r <;> simp [bind]

theorem bind_eq_resource_iff {failure : Resource} :
    r.bind f = .resource failure ↔
      r = .resource failure ∨ ∃ v, r = .ok v ∧ f v = .resource failure := by
  cases r <;> simp [bind]

/-- `r'` is `r` or a timeout: `r'` runs no further than `r`. -/
def Dom (r' r : Result α) : Prop := r' = r ∨ r' = .timeout

namespace Dom

theorem refl (r : Result α) : Dom r r := .inl rfl

theorem timeout (r : Result α) : Dom .timeout r := .inr rfl

theorem trans {a b c : Result α} (h₁ : Dom a b) (h₂ : Dom b c) : Dom a c := by
  rcases h₁ with rfl | rfl
  · exact h₂
  · exact .inr rfl

theorem bind {r r' : Result α} {f f' : α → Result β} (hr : Dom r' r)
    (hf : ∀ v, r = .ok v → Dom (f' v) (f v)) : Dom (r'.bind f') (r.bind f) := by
  rcases hr with h | h
  · rw [h]
    cases r with
    | ok v => exact hf v rfl
    | _ => exact .inl rfl
  · rw [h]
    exact .inr rfl

/-- A run no further than a timeout is a timeout. -/
theorem eq_timeout {r' : Result α} (h : Dom r' .timeout) : r' = .timeout := by
  rcases h with h | h <;> exact h

end Dom

/-- A later clock agrees with an earlier one exactly when the earlier one
runs no further. -/
theorem Agrees.dom {r r' : Result α} (h : Agrees r' r) : Dom r r' := by
  by_cases hr : r = .timeout
  · exact .inr hr
  · exact .inl (h hr).symm

end Result

/-- Under clock monotonicity a smaller clock runs no further. -/
theorem ClockMono.dom {α : Type} {c : Nat → Result α} (h : ClockMono c) {k k' : Nat}
    (hle : k ≤ k') : Result.Dom (c k) (c k') := by
  by_cases hk : c k = .timeout
  · exact .inr hk
  · exact .inl (h hle hk).symm

end Compilatrix.Sem
