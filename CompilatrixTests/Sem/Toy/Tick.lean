import CompilatrixTests.Sem.Toy.Big

/-!
# Tick insertion: a pass whose certificate is a number

`Tick.pass p n` puts `n` ticks around every function body. The number is
the pass's certificate (`Cert := Nat`): untrusted, and the pass is correct
for every value of it. The target spends more clock than the source (tick
dominance), so

- the forward clause needs a larger clock, `k·(n + 1) + n`
  (`Tick.eval_agree`), and
- the timeout clause holds with the identity clock map: the target never
  runs further than the source at the same clock (`Tick.eval_dom`).
-/

namespace CompilatrixTests.Sem.Toy

open Compilatrix.Sem

theorem Dom.trans {α : Type} {a b c : Result α} (h₁ : Dom a b) (h₂ : Dom b c) : Dom a c := by
  rcases h₁ with rfl | rfl
  · exact h₂
  · exact .inr rfl

theorem Agrees.trans {α : Type} {a b c : Result α} (h₁ : Agrees a b) (h₂ : Agrees b c) :
    Agrees a c := fun hc => by
  rw [h₁ (by rw [h₂ hc]; exact hc), h₂ hc]

namespace Big

/-- `n` ticks cost `n` clock levels. -/
theorem eval_ticks (q : Prog) (j x : Nat) (e : Expr) :
    ∀ n, eval q (j + n) x (ticks n e) = eval q j x e
  | 0 => rfl
  | n + 1 => eval_ticks q j x e n

/-- Fewer than `n` clock levels time out on `n` ticks. -/
theorem eval_ticks_lt (q : Prog) (x : Nat) (e : Expr) :
    ∀ {j n : Nat}, j < n → eval q j x (ticks n e) = .timeout
  | 0, _ + 1, _ => rfl
  | j + 1, n + 1, h => eval_ticks_lt q x e (j := j) (n := n) (by omega)

end Big

namespace Tick

open Big

/-- Put `n` ticks around every function body. -/
def pass (p : Prog) (n : Nat) : Prog := p.map (ticks n)

theorem pass_get (p : Prog) (n f : Nat) : (pass p n)[f]? = (p[f]?).map (ticks n) := by
  simp [pass]

/-- The target runs no further than the source at the same clock. -/
theorem eval_dom (p : Prog) (n : Nat) :
    ∀ k x e, Dom (eval (pass p n) k x e) (eval p k x e)
  | 0, _, e => evalAt_dom
      (fun f v => by unfold callAt; rw [pass_get]; cases p[f]? <;> exact Dom.refl _)
      (fun _ _ => Dom.refl _) e
  | k + 1, _, e => evalAt_dom
      (fun f v => by
        unfold callAt
        rw [pass_get]
        cases p[f]? with
        | none => exact Dom.refl _
        | some body =>
          show Dom (eval (pass p n) k v (ticks n body)) (eval p k v body)
          by_cases hk : n ≤ k
          · have := eval_ticks (pass p n) (k - n) v body n
            rw [Nat.sub_add_cancel hk] at this
            rw [this]
            exact (eval_dom p n (k - n) v body).trans (eval_dom_of_le p (by omega) v body)
          · exact .inr (eval_ticks_lt _ v body (by omega)))
      (fun v e => eval_dom p n k v e) e
termination_by k => k

/-- The target at clock `k·(n + 1)` agrees with the source at `k` wherever
the source does not time out. -/
theorem eval_agree (p : Prog) (n : Nat) :
    ∀ k x e, Agrees (eval (pass p n) (k * (n + 1)) x e) (eval p k x e)
  | 0, _, e => by
    rw [Nat.zero_mul]
    exact evalAt_agree
      (fun f v => by unfold callAt; rw [pass_get]; cases p[f]? <;> exact Agrees.refl _)
      (fun _ _ => Agrees.refl _) e
  | k + 1, x, e => by
    rw [show (k + 1) * (n + 1) = (k * (n + 1) + n) + 1 by rw [Nat.succ_mul]; omega]
    exact evalAt_agree
      (fun f v => by
        unfold callAt
        rw [pass_get]
        cases p[f]? with
        | none => exact Agrees.refl _
        | some body =>
          show Agrees (eval (pass p n) (k * (n + 1) + n) v (ticks n body)) (eval p k v body)
          rw [eval_ticks]
          exact eval_agree p n k v body)
      (fun v e => (Big.eval_agree (pass p n) (Nat.le_add_right _ n) v e).trans
        (eval_agree p n k v e)) e

/-- The per-input simulation: identity clock map for the timeout clause. -/
theorem sim (p : Prog) (n x : Nat) : Sim Eq id (run p x) (run (pass p n) x) where
  forward k hk := by
    refine ⟨k * (n + 1) + n, ?_⟩
    have : run (pass p n) x (k * (n + 1) + n) = run p x k := by
      unfold run at hk ⊢
      rw [pass_get]
      cases h : p[0]? with
      | none => rfl
      | some main =>
        rw [h] at hk
        show eval (pass p n) (k * (n + 1) + n) x (ticks n main) = eval p k x main
        rw [eval_ticks]
        exact eval_agree p n k x main hk
    rw [this]
    exact .refl fun _ => rfl
  timeout k hk := by
    left
    simp only [id] at hk
    unfold run at hk ⊢
    rw [pass_get]
    cases h : p[0]? with
    | none => rw [h] at hk; exact hk
    | some main =>
      rw [h] at hk
      show eval (pass p n) k x (ticks n main) = .timeout
      by_cases hn : n ≤ k
      · have := eval_ticks (pass p n) (k - n) x main n
        rw [Nat.sub_add_cancel hn] at this
        rw [this]
        have hsrc : eval p (k - n) x main = .timeout :=
          (eval_mono p x main).timeout_of_le (by omega) hk
        rcases eval_dom p n (k - n) x main with h' | h'
        · rw [h', hsrc]
        · exact h'
      · exact eval_ticks_lt _ x main (by omega)

/-- Tick insertion as a pass: correct for every number of ticks. -/
def transform : Transform Prog Prog where
  name := "tick"
  Cert := Nat
  pre _ := True
  run p n := .ok (pass p n)
  post _ := True
  correct p n q _ h := by
    cases h
    exact ⟨trivial, Refines.of_sim (R := Eq) (fun _ _ h => h ▸ rfl) fun x => ⟨id, sim p n x⟩⟩

end Tick

end CompilatrixTests.Sem.Toy
