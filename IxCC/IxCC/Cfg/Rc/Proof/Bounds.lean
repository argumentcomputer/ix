import IxCC.Cfg.Rc.Bounds
import IxCC.Cfg.Rc.Proof.Lower

set_option autoImplicit false
namespace IxCC.Cfg.Rc


theorem checked_action_operand {limit first : Nat} {i : Instr} {slot : Nat} {a : Action}
    (hr : reserved limit i = true) (hd : decode limit i = some (slot, a))
    (hb : instrBound limit first i = true) : first ≤ slot ∧
      (match a with | .inc x _ | .dec x => x < first) := by
  cases a <;> simpa [instrBound, hr, hd, actionBound] using hb

end IxCC.Cfg.Rc
