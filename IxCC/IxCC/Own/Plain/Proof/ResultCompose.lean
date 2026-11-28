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
  | ok hd hb hp _ => exact step _ _ _ hd hb hp
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

theorem ResultRel.bind_frame_reach {H H₀ : Heap} {external external₀ : Nat → Nat}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRel H external source target)
    {f : Fir.Val → Result Fir.Val} {g : RVal × Heap → Result (RVal × Heap)}
    (step : ∀ w v H', Proof.Den H' v w → Balance H' external [v] → ExternalPreserved H H' external →
      ReachablePreserved H H' external → ResultRel H₀ external₀ (f w) (g (v, H'))) :
    ResultRel H₀ external₀ (source.bind f) (target.bind g) := by
  cases h with
  | ok hd hb hp hreach => exact step _ _ _ hd hb hp hreach
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

theorem ResultRelFull.ofOption {α : Type} {H : Heap} {external : Nat → Nat} {priv : Nat → Prop}
    {ctors : List Lam.CtorInfo} {retUniq : Bool}
    {o : Option α} {f : α → Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ∀ a, o = some a → ResultRelFull H external priv ctors retUniq (f a) target) :
    ResultRelFull H external priv ctors retUniq ((Result.ofOption o).bind f) target := by
  cases ho : o with
  | none => exact .stuck
  | some a => exact h a ho

theorem ResultRelFull.later {H : Heap} {external : Nat → Nat} {priv : Nat → Prop}
    {ctors : List Lam.CtorInfo} {retUniq : Bool} {k : Nat}
    {f : Nat → Result Fir.Val} {g : Nat → Result (RVal × Heap)}
    (h : ∀ k', k' < k → ResultRelFull H external priv ctors retUniq (f k') (g k')) :
    ResultRelFull H external priv ctors retUniq (later k f) (later k g) := by
  cases k with
  | zero => exact .timeout
  | succ k => exact h k (by omega)

theorem ResultRelFull.bind_frame_full {H H₀ : Heap} {external external₀ : Nat → Nat}
    {priv priv₀ : Nat → Prop} {ctors : List Lam.CtorInfo} {retUniq retUniq₀ : Bool}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRelFull H external priv ctors retUniq source target)
    {f : Fir.Val → Result Fir.Val} {g : RVal × Heap → Result (RVal × Heap)}
    (step : ∀ w v H', Proof.Den H' v w → Balance H' external [v] →
      ExternalPreserved H H' external → ReachablePreserved H H' external →
      PrivPreserved H H' priv → (∀ l, priv l → v ≠ .loc l) →
      (retUniq = true → UniqVal ctors H' external [v] v) →
      ResultRelFull H₀ external₀ priv₀ ctors retUniq₀ (f w) (g (v, H'))) :
    ResultRelFull H₀ external₀ priv₀ ctors retUniq₀ (source.bind f) (target.bind g) := by
  cases h with
  | ok hd hb hp hreach hpriv hret hru => exact step _ _ _ hd hb hp hreach hpriv hret hru
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

end IxCC.Own.Plain
