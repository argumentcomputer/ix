import CompilatrixTests.Sem.Toy.Tick
import CompilatrixTests.Sem.Toy.Stack

/-!
# The toy pipeline: two passes composed with `Transform.comp`

Tick insertion (certificate: the number of ticks) followed by compilation to
the stack machine (no certificate), composed by `Transform.comp`. The
corollaries below are the toy's `compile_sound`, `compile_safe` and
divergence preservation, obtained from `Transform.comp_correct` and
`Refines` alone: no clock map, `Sim` or `Star` reaches this level.
-/

namespace CompilatrixTests.Sem.Toy

open Compilatrix.Sem

/-- Tick insertion, then compilation to the stack machine. -/
def pipeline : Transform Prog Stack.Program :=
  Tick.transform.comp Stack.transform fun _ _ => trivial

/-- Run the pipeline with `n` ticks, or `none` if it rejects the program. -/
def compile (p : Prog) (n : Nat) : Option Stack.Program :=
  match pipeline.run p (n, ()) with
  | .ok q => some q
  | .error _ => none

theorem pipeline_correct {p : Prog} {n : Nat} {q : Stack.Program}
    (h : pipeline.run p (n, ()) = .ok q) : q ≠ [] ∧ Refines p q :=
  Transform.comp_correct Tick.transform Stack.transform _ trivial h

theorem compile_correct {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q) :
    Refines p q := by
  unfold compile at h
  split at h
  · next h' => cases h; exact (pipeline_correct h').2
  · cases h

/-- The toy `compile_sound`: a value the machine returns is the source's
value at some clock, or the source is stuck. -/
theorem compile_sound {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    {x k w : Nat} (hw : Stack.run q x k = .ok w) :
    (∃ k', Big.run p x k' = .ok w) ∨ ∃ k', Big.run p x k' = .stuck := by
  rcases (compile_correct h).backward (i := x) (k := k) (w := w) hw with
    ⟨k', v, hv, hobs⟩ | hs
  · have : v = w := by
      simpa [Lang.ObsEq, Lang.obs] using hobs
    exact .inl ⟨k', this ▸ hv⟩
  · exact .inr hs

/-- The toy `compile_safe`: if the source goes wrong at no clock, the
machine returns, times out or overflows at every clock. -/
theorem compile_safe {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    {x : Nat} (hs : ∀ k, ¬ (Big.run p x k).GoesWrong) (k : Nat) :
    ¬ (Stack.run q x k).GoesWrong :=
  (compile_correct h).safe (i := x) hs k

/-- Divergence is preserved through both passes. -/
theorem compile_diverges {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    {x : Nat} (hs : ∀ k, Big.run p x k = .timeout) :
    (∀ k, Stack.run q x k = .timeout) ∨ ∃ k failure, Stack.run q x k = .resource failure :=
  (compile_correct h).diverges (i := x) hs

end CompilatrixTests.Sem.Toy
