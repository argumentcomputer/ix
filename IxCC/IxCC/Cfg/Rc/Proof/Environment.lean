import IxCC.Cfg.Rc.Proof.Prefix

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Sem (Result Star)

/-- Cfg may retain dead lexical bindings; each present source binding must
still resolve to its original value. No equality of entire maps is assumed. -/
def EnvSub (ρ target : Own.Env) : Prop :=
  ∀ x v, ρ.get? x = some v → target.get? x = some v

theorem evalAction_sub {ρ target : Own.Env} (h : EnvSub ρ target)
    {H H' : Own.Heap} {a : Action} (he : Own.Plain.evalAction ρ H a = .ok H') :
    Own.Plain.evalAction target H a = .ok H' := by
  cases a with
  | inc x n =>
    cases hx : ρ.get? x with
    | none => simp [Own.Plain.evalAction, hx] at he
    | some v => simpa only [Own.Plain.evalAction, hx, h x v hx] using he
  | dec x =>
    cases hx : ρ.get? x with
    | none => simp [Own.Plain.evalAction, hx] at he
    | some v => simpa only [Own.Plain.evalAction, hx, h x v hx] using he

theorem evalActions_sub {ρ target : Own.Env} (h : EnvSub ρ target)
    {H H' : Own.Heap} {as : List Action} (he : Own.Plain.evalActions ρ H as = .ok H') :
    Own.Plain.evalActions target H as = .ok H' := by
  induction as generalizing H with
  | nil => exact he
  | cons a as ih =>
    cases ha : Own.Plain.evalAction ρ H a with
    | ok H₁ =>
      have hs := evalAction_sub h ha
      simp only [Own.Plain.evalActions, ha, Result.bind_ok] at he
      simp only [Own.Plain.evalActions, hs, Result.bind_ok]
      exact ih he
    | timeout | resource _ | trap | stuck =>
      simp [Own.Plain.evalActions, ha, Result.bind] at he

theorem evalResetMask_sub {ρ target : Own.Env} (h : EnvSub ρ target)
    {H : Own.Heap} {x : Fir.Var} {ctor : Fir.CtorInfo} {mask : Nat} {uniq : Bool}
    {res : Own.RVal × Own.Heap}
    (he : Own.Plain.evalResetMask ρ H x ctor mask uniq = .ok res) :
    Own.Plain.evalResetMask target H x ctor mask uniq = .ok res := by
  unfold Own.Plain.evalResetMask at he ⊢
  split at he
  · cases he
  · next hfl =>
    simp only [hfl]
    cases hx : ρ.get? x with
    | none => simp [hx] at he
    | some v =>
      rw [hx] at he
      rw [h x v hx]
      exact he

theorem evalReuseVal_sub {ρ target : Own.Env} (h : EnvSub ρ target)
    {H : Own.Heap} {sv : Own.RVal} {ctor : Fir.CtorInfo} {args : List Fir.Arg} {uniq : Bool}
    {res : Own.RVal × Own.Heap}
    (he : Own.Plain.evalReuseVal ρ H sv ctor args uniq = .ok res) :
    Own.Plain.evalReuseVal target H sv ctor args uniq = .ok res := by
  unfold Own.Plain.evalReuseVal at he ⊢
  cases ha : Own.evalArgs ρ args with
  | none => simp [ha] at he
  | some vs =>
    have ha' : Own.evalArgs target args = some vs := by
      clear he
      induction args generalizing vs with
      | nil => simpa [Own.evalArgs] using ha
      | cons a rest ih =>
        simp only [Own.evalArgs] at ha ⊢
        cases hv : Own.evalArg ρ a with
        | none => simp [hv] at ha
        | some v =>
          have hv' : Own.evalArg target a = some v := by
            cases a with
            | var x => exact h x v hv
            | lit _ | erased => exact hv
          simp only [hv, hv'] at ha ⊢
          cases hr : Own.evalArgs ρ rest with
          | none => simp [hr] at ha
          | some vs' =>
            rw [ih vs' hr]
            simpa [hr] using ha
    simpa only [ha, ha'] using he

theorem prefix_reach_sub {P : Program} (first : Nat) (as : List Action)
    {ρ : Own.Env} {fr : Frame} {stk : List (Frame × Fir.Var)} {H H' : Own.Heap}
    {rest : List Instr} {table : ActionTable} (env : EnvSub ρ fr.env)
    (hr : fr.rest = encodePrefix P.base.size first as ++ rest)
    (ht : P.actions.get? fr.fn = some table) (slots : Slots table first as)
    (run : Own.Plain.evalActions ρ H as = .ok H') :
    Star (step P) (.run fr stk H) 0 (.run { fr with rest } stk H') :=
  prefix_reach first as hr ht slots (evalActions_sub env run)


end IxCC.Cfg.Rc
