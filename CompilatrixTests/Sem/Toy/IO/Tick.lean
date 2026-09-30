import CompilatrixTests.Sem.Toy.IO.Big

/-!
# Tick insertion with IO: tick dominance and the trace clauses

`Tick.pass p n` puts `n` ticks around every function body; `n` is the
pass's untrusted certificate. As in the pure toy (`Toy.Tick`), the target
spends more clock than the source:

- **forward:** the target at clock `k·(n + 1) + n` is the source at `k`,
  trace included (`Tick.eval_agree`, whose trace half is also the
  **progress** clause: the source's trace at `k` is a prefix of the
  target's there);
- **timeout:** with the identity clock map, the target at `k` runs no
  further than the source at `k` (`Tick.eval_dom`): a timeout after a
  prefix of the source's trace.
-/

namespace CompilatrixTests.Sem.Toy.IO

open Compilatrix.Sem

namespace Big

/-- `n` ticks cost `n` clock levels. -/
theorem eval_ticks (o : Oracle) (q : Prog) (j x : Nat) (e : Expr) :
    ∀ n, eval o q (j + n) x (ticks n e) = eval o q j x e
  | 0 => rfl
  | n + 1 => eval_ticks o q j x e n

/-- Fewer than `n` clock levels time out on `n` ticks, with no event. -/
theorem eval_ticks_lt (o : Oracle) (q : Prog) (x : Nat) (e : Expr) :
    ∀ {j n : Nat}, j < n → eval o q j x (ticks n e) = M.halt .timeout
  | 0, _ + 1, _ => rfl
  | j + 1, n + 1, h => eval_ticks_lt o q x e (j := j) (n := n) (by omega)

end Big

namespace Tick

open Big

/-- Put `n` ticks around every function body. -/
def pass (p : Prog) (n : Nat) : Prog := p.map (ticks n)

theorem pass_get (p : Prog) (n f : Nat) : (pass p n)[f]? = (p[f]?).map (ticks n) := by
  simp [pass]

/-- The target runs no further than the source at the same clock. -/
theorem eval_dom (o : Oracle) (p : Prog) (n : Nat) :
    ∀ k x e, MDom (eval o (pass p n) k x e) (eval o p k x e)
  | 0, _, e => evalAt_dom
      (fun f v => by unfold callAt; rw [pass_get]; cases p[f]? <;> exact MDom.refl _)
      (fun _ _ => MDom.refl _) e
  | k + 1, _, e => evalAt_dom
      (fun f v => by
        unfold callAt
        rw [pass_get]
        cases p[f]? with
        | none => exact MDom.refl _
        | some body =>
          show MDom (eval o (pass p n) k v (ticks n body)) (eval o p k v body)
          by_cases hk : n ≤ k
          · have := eval_ticks o (pass p n) (k - n) v body n
            rw [Nat.sub_add_cancel hk] at this
            rw [this]
            exact (eval_dom o p n (k - n) v body).trans (eval_dom_of_le o p (by omega) v body)
          · rw [eval_ticks_lt _ _ v body (by omega)]
            exact MDom.halt_timeout _)
      (fun v e => eval_dom o p n k v e) e
termination_by k => k

/-- The target at clock `k·(n + 1)` agrees with the source at `k` wherever
the source does not time out, and extends its trace. -/
theorem eval_agree (o : Oracle) (p : Prog) (n : Nat) :
    ∀ k x e, MAgrees (eval o (pass p n) (k * (n + 1)) x e) (eval o p k x e)
  | 0, _, e => by
    rw [Nat.zero_mul]
    exact evalAt_agree
      (fun f v => by unfold callAt; rw [pass_get]; cases p[f]? <;> exact MAgrees.refl _)
      (fun _ _ => MAgrees.refl _) e
  | k + 1, x, e => by
    rw [show (k + 1) * (n + 1) = (k * (n + 1) + n) + 1 by rw [Nat.succ_mul]; omega]
    exact evalAt_agree
      (fun f v => by
        unfold callAt
        rw [pass_get]
        cases p[f]? with
        | none => exact MAgrees.refl _
        | some body =>
          show MAgrees (eval o (pass p n) (k * (n + 1) + n) v (ticks n body)) (eval o p k v body)
          rw [eval_ticks]
          exact eval_agree o p n k v body)
      (fun v e => (Big.eval_agree o (pass p n) (Nat.le_add_right _ n) v e).trans
        (eval_agree o p n k v e)) e

/-- The target run at clock `k·(n + 1) + n` agrees with the source run at
`k`. -/
theorem run_agree (p : Prog) (n x : Nat) (o : Oracle) (k : Nat) :
    TAgrees (Big.run (pass p n) x o (k * (n + 1) + n)) (Big.run p x o k) := by
  unfold Big.run
  rw [pass_get]
  cases p[0]? with
  | none => exact ⟨fun _ => rfl, List.prefix_refl _⟩
  | some main =>
    show TAgrees (eval o (pass p n) (k * (n + 1) + n) x (ticks n main) []) _
    rw [eval_ticks]
    exact eval_agree o p n k x main []

/-- The target run at clock `k` runs no further than the source run at
`k`. -/
theorem run_dom (p : Prog) (n x : Nat) (o : Oracle) (k : Nat) :
    TDom (Big.run (pass p n) x o k) (Big.run p x o k) := by
  unfold Big.run
  rw [pass_get]
  cases p[0]? with
  | none => exact .inl rfl
  | some main =>
    show TDom (eval o (pass p n) k x (ticks n main) []) _
    by_cases hn : n ≤ k
    · have := eval_ticks o (pass p n) (k - n) x main n
      rw [Nat.sub_add_cancel hn] at this
      rw [this]
      exact ((eval_dom o p n (k - n) x main).trans (eval_dom_of_le o p (by omega) x main)) []
    · rw [eval_ticks_lt _ _ x main (by omega)]
      exact MDom.halt_timeout _ []

/-- The per-input traced simulation: identity clock map for the timeout
clause, clock `k·(n + 1) + n` for forward and progress. -/
theorem sim (p : Prog) (n x : Nat) : TSim Eq id (Big.run p x) (Big.run (pass p n) x) where
  forward o k hk := ⟨k * (n + 1) + n, by
    rw [(run_agree p n x o k).1 hk]
    exact .refl (fun _ => rfl) _⟩
  timeout o k hk := by
    obtain ⟨ht, hp⟩ := (run_dom p n x o k).timeout hk
    exact ⟨.inl ht, hp⟩
  progress o k := ⟨k * (n + 1) + n, .inl (run_agree p n x o k).2⟩

/-- Tick insertion as a traced pass: correct for every number of ticks. -/
def transform : TTransform Prog Prog where
  name := "tick"
  Cert := Nat
  pre _ := True
  run p n := .ok (pass p n)
  post _ := True
  correct p n q _ h := by
    cases h
    exact ⟨trivial, TRefines.of_sim (R := Eq) (fun _ _ h => h ▸ rfl) fun x => ⟨id, sim p n x⟩⟩

end Tick

end CompilatrixTests.Sem.Toy.IO
