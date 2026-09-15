import Compilatrix.Aiur.Wire.ComponentCheck
import Compilatrix.Aiur.Wire.CodecProofs

namespace Compilatrix.Aiur.Wire

open Compilatrix.Ixon

theorem ComponentChecked.evidence {limits : CheckLimits} {value : _root_.Aiur.Bytecode.Toplevel}
    (checked : ComponentChecked limits value) :
    value.callComponents.isEmpty = true ∨ value.validCallComponents = true := by
  simpa only [componentsValid, Bool.or_eq_true] using checked.accepted

theorem Ingress.validated {limits : Limits} {checkLimits : CheckLimits}
    {bytes : ByteArray} {root : Address} (ingress : Ingress limits checkLimits bytes root) :
    preimage ingress.value = bytes ∧ Address.blake3 bytes = root ∧ Fits limits ingress.value ∧
      componentCheckFits checkLimits ingress.value = true ∧
      (ingress.value.callComponents.isEmpty = true ∨ ingress.value.validCallComponents = true) :=
  ⟨ingress.toAddressed.canonical, ingress.toAddressed.root_eq, ingress.toAddressed.fits,
    ingress.checked.bounded, ingress.checked.evidence⟩

end Compilatrix.Aiur.Wire
