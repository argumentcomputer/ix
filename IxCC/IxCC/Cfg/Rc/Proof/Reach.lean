import IxCC.Cfg.Rc.Proof.Step

/-! The existing Cfg CPS trace interface instantiated for explicit RC steps.
The proof cases and source stuck/resource convention are preserved from
Cfg.Proof.Step; no source simulation is assumed by these trace combinators. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Sem (Result Star)
open IxCC.Own (RVal Heap)
open IxCC.Fir (Var FunId)

variable {P : Program}

theorem step_ret_cons {v : RVal} {fr : Frame} {x : Var} {stk : List (Frame × Var)} {H : Heap} :
    step P (.ret v ((fr, x) :: stk) H) = .next (.run { fr with env := fr.env.insert x v } stk H) false := rfl

def Reach (P : Program) (k : Nat) (s : State) (stk : List (Frame × Var)) :
    Result (RVal × Heap) → Prop
  | .ok (v, H') => ∃ n, Star (step P) s n (.ret v stk H')
  | .trap => ∃ n s', Star (step P) s n s' ∧ step P s' = .trap
  | .timeout => ∃ n s', Star (step P) s n s' ∧ k < n
  | .stuck => True
  | .resource _ => False

namespace Reach

variable {k : Nat} {s s' : State} {stk : List (Frame × Var)}

theorem stuck : Reach P k s stk .stuck := trivial

/-- A free step first. -/
theorem free {r : Result (RVal × Heap)} (hs : step P s = .next s' false) (h : Reach P k s' stk r) :
    Reach P k s stk r := by
  match r, h with
  | .ok (v, H'), ⟨n, hn⟩ => exact ⟨n, .free hs hn⟩
  | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨n, s'', .free hs hn, ht⟩
  | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨n, s'', .free hs hn, hk⟩
  | .stuck, _ => trivial
  | .resource _, h => exact h.elim

/-- Free steps first. -/
theorem star {r : Result (RVal × Heap)} (hs : Star (step P) s 0 s') (h : Reach P k s' stk r) :
    Reach P k s stk r := by
  match r, h with
  | .ok (v, H'), ⟨n, hn⟩ => exact ⟨0 + n, hs.trans hn⟩
  | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨0 + n, s'', hs.trans hn, ht⟩
  | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨0 + n, s'', hs.trans hn, by omega⟩
  | .stuck, _ => trivial
  | .resource _, h => exact h.elim

/-- A charge: Own's `Sem.later k` against a charged step. -/
theorem charge {r : Nat → Result (RVal × Heap)} (hs : step P s = .next s' true)
    (h : ∀ k', k = k' + 1 → Reach P k' s' stk (r k')) : Reach P k s stk (Sem.later k r) := by
  cases k with
  | zero => exact ⟨1, s', .charge hs (.refl _), by omega⟩
  | succ k' =>
    simp only [Sem.later_succ]
    have h' := h k' rfl
    generalize r k' = r' at h'
    match r', h' with
    | .ok (v, H'), ⟨n, hn⟩ => exact ⟨n + 1, .charge hs hn⟩
    | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨n + 1, s'', .charge hs hn, ht⟩
    | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨n + 1, s'', .charge hs hn, by omega⟩
    | .stuck, _ => trivial
    | .resource _, h => exact h.elim

/-- A non-tail call, then the rest of the caller. -/
theorem call {fr : Frame} {x : Var} {f : FunId} {vs : List RVal} {continuation : Frame} {H : Heap}
    {r : Result (RVal × Heap)} {g : RVal × Heap → Result (RVal × Heap)}
    (hs : step P (.run fr stk H) = .next (.call f vs ((continuation, x) :: stk) H) false)
    (h₁ : Reach P k (.call f vs ((continuation, x) :: stk) H) ((continuation, x) :: stk) r)
    (h₂ : ∀ v H', r = .ok (v, H') →
      Reach P k (.run { continuation with env := continuation.env.insert x v } stk H') stk (g (v, H'))) :
    Reach P k (.run fr stk H) stk (r.bind g) := by
  match r, h₁ with
  | .ok (v, H'), ⟨n, hn⟩ =>
    simp only [Result.bind_ok]
    have hc := h₂ v H' rfl
    generalize g (v, H') = r' at hc
    have hpre : Star (step P) (.run fr stk H) n
        (.run { continuation with env := continuation.env.insert x v } stk H') := by
      have := (Star.free hs hn).trans (Star.free (s' := .run { continuation with env := continuation.env.insert x v } stk H')
        step_ret_cons (.refl _))
      simpa using this
    match r', hc with
    | .ok (v', H''), ⟨n', hn'⟩ => exact ⟨n + n', hpre.trans hn'⟩
    | .trap, ⟨n', s'', hn', ht⟩ => exact ⟨n + n', s'', hpre.trans hn', ht⟩
    | .timeout, ⟨n', s'', hn', hk⟩ => exact ⟨n + n', s'', hpre.trans hn', by omega⟩
    | .stuck, _ => trivial
    | .resource _, h => exact h.elim
  | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨n, s'', .free hs hn, ht⟩
  | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨n, s'', .free hs hn, hk⟩
  | .stuck, _ => trivial
  | .resource _, h => exact h.elim

end Reach



end IxCC.Cfg.Rc
