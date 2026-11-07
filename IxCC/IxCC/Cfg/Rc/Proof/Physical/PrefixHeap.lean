import IxCC.Cfg.Rc.Proof.Physical.CtorActions
import IxCC.Cfg.Rc.Proof.Physical.FrameTransport

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc

theorem actions_heapOk {H H' : Heap} {ρ : Own.Env} {actions : List Action}
    (before : HeapOk H) (result : Own.Plain.evalActions ρ H actions = .ok H') : HeapOk H' := by
  induction actions generalizing H with
  | nil => cases result; exact before
  | cons action actions ih =>
    cases step : Own.Plain.evalAction ρ H action with
    | ok next =>
      have tail : Own.Plain.evalActions ρ next actions = .ok H' := by
        simpa only [Own.Plain.evalActions, step, Sem.Result.bind_ok] using result
      exact ih (Own.Plain.action_shape before step).1 tail
    | timeout | resource _ | trap | stuck =>
      simp [Own.Plain.evalActions, step, Sem.Result.bind] at result


end IxCC.Cfg.Rc.Native
