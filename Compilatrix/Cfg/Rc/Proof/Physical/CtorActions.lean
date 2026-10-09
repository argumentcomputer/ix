import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.CtorInvariant
import Compilatrix.Own.Plain.Proof.Prefixes

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc

/-- Constructor compatibility survives the actual source count/release
operation. This does not require source values in omitted registers to have
physical constructor representations. -/
theorem HeapCtorOk.evalAction {tables : Rt.Lower.Tables} {H H' : Heap}
    {ρ : Own.Env} {action : Own.Plain.Action}
    (before : HeapCtorOk tables H) (result : Own.Plain.evalAction ρ H action = .ok H') :
    HeapCtorOk tables H' := by
  cases action with
  | inc x n =>
    cases lookup : ρ.get? x with
    | none => simp [Own.Plain.evalAction, lookup] at result
    | some value =>
      cases operation : inc H value n with
      | none => simp [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption] at result
      | some after =>
        simp only [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption, Sem.Result.ok.injEq] at result
        subst H'
        exact before.changeCount operation
  | dec x =>
    cases lookup : ρ.get? x with
    | none => simp [Own.Plain.evalAction, lookup] at result
    | some value =>
      cases operation : Own.Rc.dropAll H [value] with
      | none => simp [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption] at result
      | some after =>
        simp only [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption, Sem.Result.ok.injEq] at result
        subst H'
        exact HeapCtorOk.dropAll H [value] before operation

theorem HeapCtorOk.evalActions {tables : Rt.Lower.Tables} {H H' : Heap}
    {ρ : Own.Env} {actions : List Own.Plain.Action}
    (before : HeapCtorOk tables H) (result : Own.Plain.evalActions ρ H actions = .ok H') :
    HeapCtorOk tables H' := by
  induction actions generalizing H with
  | nil => cases result; exact before
  | cons action actions ih =>
    cases step : Own.Plain.evalAction ρ H action with
    | ok next =>
      have tail : Own.Plain.evalActions ρ next actions = .ok H' := by
        simpa only [Own.Plain.evalActions, step, Sem.Result.bind_ok] using result
      exact ih (before.evalAction step) tail
    | timeout | resource _ | trap | stuck =>
      simp [Own.Plain.evalActions, step, Sem.Result.bind] at result



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
