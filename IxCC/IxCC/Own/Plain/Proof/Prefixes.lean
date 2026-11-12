import IxCC.Own.Plain.Proof.Actions
import IxCC.Own.Plain.Proof.Environment
import IxCC.Own.Plain.Proof.Unfold

/-! Running a list of actions (`evalActions`) and the unfolding of an action prefix
(`eval_actionPrefix`: the continuation keeps the source clock and environment). The Cfg layer's
marker steps use them. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

def evalActions (ρ : Own.Env) (H : Heap) : List Action → Result Heap
  | [] => .ok H
  | a :: acts => (evalAction ρ H a).bind fun H' => evalActions ρ H' acts

theorem eval_actionPrefix (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry)
    (H : Heap) (acts : List Action) (c : Code) :
    eval P k ρ J H (actionPrefix acts c) =
      (evalActions ρ H acts).bind fun H' => eval P k ρ J H' c := by
  induction acts generalizing H with
  | nil => rfl
  | cons a acts ih =>
    rw [actionPrefix, eval_act]
    simp only [evalActions]
    cases ha : evalAction ρ H a <;> simp [Result.bind, ih]

def ArgsOwned (ρ : Own.Env) (args : List Fir.Arg) (roots : List RVal) : Prop :=
  ∀ x, Fir.Arg.var x ∈ args → ∃ v, ρ.get? x = some v ∧ v ∈ roots

theorem balance_rotate {H : Heap} {external : Nat → Nat}
    {values roots : List RVal} {v : RVal}
    (h : Balance H external (values ++ v :: roots)) :
    Balance H external (v :: values ++ roots) := by
  intro l
  have he := h l
  simp only [refsIn_append, refsIn] at *
  omega


end IxCC.Own.Plain
