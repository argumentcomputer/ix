import Compilatrix.Own.Plain.Proof.Actions
import Compilatrix.Own.Plain.Proof.Unfold

/-! Execution of the producer's action prefixes. Arguments are duplicated
per occurrence, including aliases; immediate arguments need no heap action.
The continuation retains precisely the source clock and environment. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

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

theorem copies_sound (ρ : Own.Env) (H : Heap) (args : List Fir.Arg)
    {external : Nat → Nat} {roots values : List RVal}
    (hb : Balance H external roots) (ho : ArgsOwned ρ args roots)
    (ha : Own.evalArgs ρ args = some values) :
    ∃ H', evalActions ρ H (copies args) = .ok H' ∧
      Balance H' external (values ++ roots) ∧
      ∀ root, H.value? root = H'.value? root := by
  induction args generalizing H roots values with
  | nil =>
    have he : values = [] := by simpa [Own.evalArgs] using ha.symm
    subst values
    exact ⟨H, rfl, hb, fun _ => rfl⟩
  | cons arg args ih =>
    cases arg with
    | var x =>
      obtain ⟨v, hx, hm⟩ := ho x (by simp)
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, Own.evalArg, hx, hs] at ha
      | some vs =>
        have he : v :: vs = values := by simpa [Own.evalArgs, Own.evalArg, hx, hs] using ha
        subst values
        obtain ⟨H₁, hi, hb₁, hv₁⟩ := evalAction_inc_owned hx hb hm
        have ho₁ : ArgsOwned ρ args (v :: roots) := by
          intro y hy
          obtain ⟨w, hw, hm⟩ := ho y (List.mem_cons_of_mem _ hy)
          exact ⟨w, hw, List.mem_cons_of_mem _ hm⟩
        obtain ⟨H₂, hs₂, hb₂, hv₂⟩ := ih H₁ hb₁ ho₁ hs
        refine ⟨H₂, ?_, balance_rotate hb₂, fun root => (hv₁ root).trans (hv₂ root)⟩
        simp [copies, evalActions, hi, Result.bind, hs₂]
    | lit lit =>
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, Own.evalArg, hs] at ha
      | some vs =>
        have he : RVal.lit lit :: vs = values := by simpa [Own.evalArgs, Own.evalArg, hs] using ha
        subst values
        have ho₁ : ArgsOwned ρ args roots := by
          intro y hy
          exact ho y (List.mem_cons_of_mem _ hy)
        obtain ⟨H', hh, hb', hv⟩ := ih H hb ho₁ hs
        exact ⟨H', hh, by simpa [Balance, refsIn] using hb', hv⟩
    | erased =>
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, Own.evalArg, hs] at ha
      | some vs =>
        have he : RVal.erased :: vs = values := by simpa [Own.evalArgs, Own.evalArg, hs] using ha
        subst values
        have ho₁ : ArgsOwned ρ args roots := by
          intro y hy
          exact ho y (List.mem_cons_of_mem _ hy)
        obtain ⟨H', hh, hb', hv⟩ := ih H hb ho₁ hs
        exact ⟨H', hh, by simpa [Balance, refsIn] using hb', hv⟩


end Compilatrix.Own.Plain
