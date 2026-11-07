import IxCC.Aiur.Wire.ComponentCheck
import IxCC.Aiur.Wire.CodecProofs

namespace IxCC.Aiur.Wire

open IxCC.Ixon

theorem ComponentChecked.evidence {limits : CheckLimits} {value : _root_.IxCC.Vendor.Aiur.Bytecode.Toplevel}
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

end IxCC.Aiur.Wire
