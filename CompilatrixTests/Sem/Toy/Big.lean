import Compilatrix.Sem.Transform

/-!
# A toy big-step language for the semantic framework

The first of three levels that exercise `Compilatrix.Sem` end to end
(M2.1): a first-order language of one-argument functions over exact `Nat`,
with a *depth* clock as Src through Own use. A call or a `tick` evaluates
its body one clock level down; `timeout` means the depth ran out.

`eval p (k + 1)` is `evalAt p (eval p k)`: one clock level, whose `below`
evaluates callee bodies and ticked expressions at the next level down. Both
recursions are structural. `evalAt_agree` and `evalAt_dom` compare two
clock levels (or two programs) whose `below`s agree, and give clock
monotonicity (`eval_mono`) here and tick dominance in `Toy.Tick`.
-/

namespace CompilatrixTests.Sem.Toy

open Compilatrix.Sem

inductive Expr where
  | lit (n : Nat)
  | arg
  | add (a b : Expr)
  | sub (a b : Expr)
  /-- `ifz c t e`: `t` if `c` is zero, else `e`. -/
  | ifz (c t e : Expr)
  /-- Call function `f` on `a`; charges the clock. -/
  | call (f : Nat) (a : Expr)
  /-- Charge the clock, then evaluate `e`. -/
  | tick (e : Expr)
  deriving Repr, Inhabited

/-- `n` ticks around `e`. -/
def ticks : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => .tick (ticks n e)

/-- Function bodies; function 0 is `main`. -/
abbrev Prog := List Expr

/-- `r'` is `r` or a timeout: `r'` runs no further than `r`. -/
def Dom {α : Type} (r' r : Result α) : Prop := r' = r ∨ r' = .timeout

/-- `r'` is `r` wherever `r` does not time out: `r'` runs at least as far
as `r`. -/
def Agrees {α : Type} (r' r : Result α) : Prop := r ≠ .timeout → r' = r

theorem Dom.refl {α : Type} (r : Result α) : Dom r r := .inl rfl

theorem Agrees.refl {α : Type} (r : Result α) : Agrees r r := fun _ => rfl

theorem Dom.bind {α β : Type} {r r' : Result α} {f f' : α → Result β} (hr : Dom r' r)
    (hf : ∀ v, r = .ok v → Dom (f' v) (f v)) : Dom (r'.bind f') (r.bind f) := by
  rcases hr with h | h
  · rw [h]
    cases r with
    | ok v => exact hf v rfl
    | _ => exact .inl rfl
  · rw [h]
    exact .inr rfl

theorem Agrees.bind {α β : Type} {r r' : Result α} {f f' : α → Result β} (hr : Agrees r' r)
    (hf : ∀ v, r = .ok v → Agrees (f' v) (f v)) : Agrees (r'.bind f') (r.bind f) := by
  intro hne
  cases r with
  | ok v => rw [hr (by simp)]; exact hf v rfl hne
  | timeout => exact absurd rfl hne
  | _ => rw [hr (by simp)]; rfl

namespace Big

/-- A call at one clock level: the body at the level below, or `stuck` for
an unknown function. -/
def callAt (p : Prog) (below : Nat → Expr → Result Nat) (f v : Nat) : Result Nat :=
  match p[f]? with
  | some body => below v body
  | none => .stuck

/-- One clock level with argument `x`. -/
def evalAt (p : Prog) (below : Nat → Expr → Result Nat) (x : Nat) : Expr → Result Nat
  | .lit n => .ok n
  | .arg => .ok x
  | .add a b =>
      (evalAt p below x a).bind fun va => (evalAt p below x b).bind fun vb => .ok (va + vb)
  | .sub a b =>
      (evalAt p below x a).bind fun va => (evalAt p below x b).bind fun vb => .ok (va - vb)
  | .ifz c t e =>
      (evalAt p below x c).bind fun vc =>
        if vc = 0 then evalAt p below x t else evalAt p below x e
  | .call f a => (evalAt p below x a).bind (callAt p below f)
  | .tick e => below x e

/-- Evaluation with depth clock `k` and argument `x`. -/
def eval (p : Prog) : Nat → Nat → Expr → Result Nat
  | 0 => evalAt p fun _ _ => .timeout
  | k + 1 => evalAt p (eval p k)

/-- Run `main` on `x` with clock `k`. -/
def run (p : Prog) (x k : Nat) : Result Nat :=
  match p[0]? with
  | some main => eval p k x main
  | none => .stuck

theorem eval_zero (p : Prog) : eval p 0 = evalAt p fun _ _ => .timeout := rfl
theorem eval_succ (p : Prog) (k : Nat) : eval p (k + 1) = evalAt p (eval p k) := rfl

/-- Two clock levels, possibly of two programs, agree where the first does
not time out if their calls and ticks do. -/
theorem evalAt_agree {p p' : Prog} {below below' : Nat → Expr → Result Nat} {x : Nat}
    (hcall : ∀ f v, Agrees (callAt p' below' f v) (callAt p below f v))
    (htick : ∀ v e, Agrees (below' v e) (below v e)) :
    ∀ e, Agrees (evalAt p' below' x e) (evalAt p below x e)
  | .lit _ => Agrees.refl _
  | .arg => Agrees.refl _
  | .add a b => Agrees.bind (evalAt_agree hcall htick a) fun _ _ =>
      Agrees.bind (evalAt_agree hcall htick b) fun _ _ => Agrees.refl _
  | .sub a b => Agrees.bind (evalAt_agree hcall htick a) fun _ _ =>
      Agrees.bind (evalAt_agree hcall htick b) fun _ _ => Agrees.refl _
  | .ifz c t e => Agrees.bind (evalAt_agree hcall htick c) fun vc _ => by
      by_cases h : vc = 0
      · simp only [h, ↓reduceIte]; exact evalAt_agree hcall htick t
      · simp only [h, ↓reduceIte]; exact evalAt_agree hcall htick e
  | .call f a => Agrees.bind (evalAt_agree hcall htick a) fun v _ => hcall f v
  | .tick e => htick x e

/-- Two clock levels, possibly of two programs: the second runs no further
than the first if their calls and ticks do not. -/
theorem evalAt_dom {p p' : Prog} {below below' : Nat → Expr → Result Nat} {x : Nat}
    (hcall : ∀ f v, Dom (callAt p' below' f v) (callAt p below f v))
    (htick : ∀ v e, Dom (below' v e) (below v e)) :
    ∀ e, Dom (evalAt p' below' x e) (evalAt p below x e)
  | .lit _ => Dom.refl _
  | .arg => Dom.refl _
  | .add a b => Dom.bind (evalAt_dom hcall htick a) fun _ _ =>
      Dom.bind (evalAt_dom hcall htick b) fun _ _ => Dom.refl _
  | .sub a b => Dom.bind (evalAt_dom hcall htick a) fun _ _ =>
      Dom.bind (evalAt_dom hcall htick b) fun _ _ => Dom.refl _
  | .ifz c t e => Dom.bind (evalAt_dom hcall htick c) fun vc _ => by
      by_cases h : vc = 0
      · simp only [h, ↓reduceIte]; exact evalAt_dom hcall htick t
      · simp only [h, ↓reduceIte]; exact evalAt_dom hcall htick e
  | .call f a => Dom.bind (evalAt_dom hcall htick a) fun v _ => hcall f v
  | .tick e => htick x e

theorem callAt_agree {p : Prog} {below below' : Nat → Expr → Result Nat}
    (h : ∀ v e, Agrees (below' v e) (below v e)) (f v : Nat) :
    Agrees (callAt p below' f v) (callAt p below f v) := by
  unfold callAt
  split
  · exact h _ _
  · exact Agrees.refl _

/-- Clock monotonicity: a larger clock agrees wherever a smaller one does
not time out. -/
theorem eval_agree (p : Prog) :
    ∀ {k k' : Nat}, k ≤ k' → ∀ x e, Agrees (eval p k' x e) (eval p k x e)
  | 0, 0, _, _, _ => Agrees.refl _
  | 0, k' + 1, _, x, e => evalAt_agree (callAt_agree fun _ _ h => absurd rfl h)
      (fun _ _ h => absurd rfl h) e
  | k + 1, k' + 1, hle, x, e =>
      evalAt_agree (callAt_agree fun v e => eval_agree p (by omega) v e)
        (fun v e => eval_agree p (by omega) v e) e

theorem eval_mono (p : Prog) (x : Nat) (e : Expr) : ClockMono fun k => eval p k x e :=
  fun _ _ hle hne => eval_agree p hle x e hne

theorem run_mono (p : Prog) (x : Nat) : ClockMono (run p x) := by
  unfold run
  split
  · exact eval_mono p x _
  · exact ClockMono.const _

/-- A smaller clock runs no further. -/
theorem eval_dom_of_le (p : Prog) {k k' : Nat} (hle : k ≤ k') (x : Nat) (e : Expr) :
    Dom (eval p k x e) (eval p k' x e) := by
  by_cases h : eval p k x e = .timeout
  · exact .inr h
  · exact .inl (eval_agree p hle x e h).symm

end Big

/-- The big-step language. -/
instance : Lang Nat Prog where
  Val := Nat
  run := Big.run
  mono := Big.run_mono
  obs v := some (.nat v)

end CompilatrixTests.Sem.Toy
