import CompilatrixTests.Sem.Toy.IO.Tick
import CompilatrixTests.Sem.Toy.IO.Stack

/-!
# The IO toy pipeline: two traced passes composed with `TTransform.comp`

Tick insertion (certificate: the number of ticks) followed by compilation
to the IO stack machine, composed by `TTransform.comp`. The corollaries are
the toy's `compile_sound_io` (a returned value with its events), trace
safety, `compile_live_io` (the machine keeps up with the source's events),
`compile_safe` and divergence preservation, obtained from
`TTransform.comp_correct` and `TRefines` alone: no clock map, `TSim` or
`Star` reaches this level, and every statement holds for every oracle.
-/

namespace CompilatrixTests.Sem.Toy.IO

open Compilatrix.Sem

/-- Tick insertion, then compilation to the IO stack machine. -/
def pipeline : TTransform Prog Stack.Program :=
  Tick.transform.comp Stack.transform fun _ _ => trivial

/-- Run the pipeline with `n` ticks, or `none` if it rejects the program. -/
def compile (p : Prog) (n : Nat) : Option Stack.Program :=
  match pipeline.run p (n, ()) with
  | .ok q => some q
  | .error _ => none

theorem pipeline_correct {p : Prog} {n : Nat} {q : Stack.Program}
    (h : pipeline.run p (n, ()) = .ok q) : q ≠ [] ∧ TRefines p q :=
  TTransform.comp_correct Tick.transform Stack.transform _ trivial h

theorem compile_correct {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q) :
    TRefines p q := by
  unfold compile at h
  split at h
  · next h' => cases h; exact (pipeline_correct h').2
  · cases h

/-- The toy `compile_sound_io`: a value the machine returns, with its
events, is the source's at some clock, or the source is stuck. -/
theorem compile_sound {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    {x : Nat} {o : Oracle} {k w : Nat} {tr : List Ev} (hw : Stack.run q x o k = ⟨.ok w, tr⟩) :
    (∃ k', Big.run p x o k' = ⟨.ok w, tr⟩) ∨ ∃ k', (Big.run p x o k').result = .stuck := by
  rcases (compile_correct h).backward (i := x) (o := o) (k := k) (w := w) hw with
    ⟨k', v, hv, hobs⟩ | hs
  · have : v = w := by simpa [TLang.ObsEq, TLang.obs] using hobs
    exact .inl ⟨k', this ▸ hv⟩
  · exact .inr hs

/-- Trace safety: every event sequence the machine performs is one the
source performs, or the source is stuck. -/
theorem compile_trace_prefix {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    (x : Nat) (o : Oracle) (k : Nat) :
    (∃ k', (Stack.run q x o k).trace <+: (Big.run p x o k').trace) ∨
      ∃ k', (Big.run p x o k').result = .stuck :=
  (compile_correct h).trace_prefix x o k

/-- The toy `compile_live_io`: every event sequence the source performs,
the machine performs, unless it fails for a resource or the source is
stuck. -/
theorem compile_live {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    (x : Nat) (o : Oracle) (k : Nat) :
    (∃ k', (Big.run p x o k).trace <+: (Stack.run q x o k').trace) ∨
      (∃ k' failure, (Stack.run q x o k').result = .resource failure) ∨
      ∃ k', (Big.run p x o k').result = .stuck :=
  (compile_correct h).live x o k

/-- The toy `compile_safe`: if the source goes wrong at no clock, the
machine returns, times out or overflows at every clock. -/
theorem compile_safe {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    {x : Nat} {o : Oracle} (hs : ∀ k, ¬ (Big.run p x o k).result.GoesWrong) (k : Nat) :
    ¬ (Stack.run q x o k).result.GoesWrong :=
  (compile_correct h).safe (i := x) (o := o) hs k

/-- Divergence is preserved through both passes. -/
theorem compile_diverges {p : Prog} {n : Nat} {q : Stack.Program} (h : compile p n = some q)
    {x : Nat} {o : Oracle} (hs : ∀ k, (Big.run p x o k).result = .timeout) :
    (∀ k, (Stack.run q x o k).result = .timeout) ∨
      ∃ k failure, (Stack.run q x o k).result = .resource failure :=
  (compile_correct h).diverges (i := x) (o := o) hs

end CompilatrixTests.Sem.Toy.IO
