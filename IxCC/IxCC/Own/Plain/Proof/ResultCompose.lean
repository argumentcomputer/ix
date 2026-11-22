import IxCC.Own.Plain.Proof.Results
import IxCC.Sem.Agrees

/-! Logical composition for the code induction. Continuation premises are
induction hypotheses; no such premise is exposed by the final program theorem. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result later)

theorem ResultRel.ofOption {α : Type} {H : Heap} {external : Nat → Nat}
    {o : Option α} {f : α → Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ∀ a, o = some a → ResultRel H external (f a) target) :
    ResultRel H external ((Result.ofOption o).bind f) target := by
  cases ho : o with
  | none => exact .stuck
  | some a => exact h a ho

theorem ResultRel.later {H : Heap} {external : Nat → Nat} {k : Nat}
    {f : Nat → Result Fir.Val} {g : Nat → Result (RVal × Heap)}
    (h : ∀ k', k' < k → ResultRel H external (f k') (g k')) :
    ResultRel H external (later k f) (later k g) := by
  cases k with
  | zero => exact .timeout
  | succ k => exact h k (by omega)

theorem ResultRel.bind_frame {H H₀ : Heap} {external external₀ : Nat → Nat}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRel H external source target)
    {f : Fir.Val → Result Fir.Val} {g : RVal × Heap → Result (RVal × Heap)}
    (step : ∀ w v H', Proof.Den H' v w → Balance H' external [v] → ExternalPreserved H H' external →
      ResultRel H₀ external₀ (f w) (g (v, H'))) :
    ResultRel H₀ external₀ (source.bind f) (target.bind g) := by
  cases h with
  | ok hd hb hp => exact step _ _ _ hd hb hp
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

theorem ExternalPreserved.of_values {H H' : Heap} {external : Nat → Nat}
    (h : ∀ root, ExternalRoot external root → H.value? root = H'.value? root) :
    ExternalPreserved H H' external := by
  intro root w hr hd
  change H'.value? root = some w
  rw [← h root hr]
  exact hd


end IxCC.Own.Plain
