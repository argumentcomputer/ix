import IxCC.Own.Plain.Proof.Bindings
import IxCC.Own.Plain.Proof.StackScope
import IxCC.Own.Plain.Proof.Scope
import IxCC.Own.Plain.Proof.Results

/-! Call suspension and resumption use actual root counts: caller tokens are held externally
while the callee runs, then restored beside the returned token (`balance_resume`). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc

theorem balance_resume {H : Heap} {external : Nat → Nat} {held active : List RVal}
    (h : Balance H (holdRoots external held) active) : Balance H external (held ++ active) :=
  balance_append_comm (balance_hold.mpr h)


end IxCC.Own.Plain
