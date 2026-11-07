import IxCC.Aiur.Wire.Codec
import IxCC.Aiur.Wire.RecordProofs

namespace IxCC.Aiur.Wire

open _root_.Aiur.Bytecode
open IxCC.Ixon
open IxCC.IxIR

theorem getPreimage_spec (limits : Limits) (value : Toplevel)
    (admitted : toplevelFits limits value = true) :
    GetSpec (getPreimage limits) (preimage value) value :=
  GetSpec.bind (Decode.expectBytes_spec header) (getToplevel_spec limits value admitted)

theorem decode_roundtrip (limits : Limits) (value : Toplevel) (fits : Fits limits value) :
    decode limits (preimage value) = .ok value :=
  Bounded.run_roundtrip limits.toLimits _ _ _ value fits.1 fits.2
    (getPreimage_spec limits value fits.2)

theorem decode_canonical (limits : Limits) {bytes : ByteArray} {value : Toplevel}
    (accepted : decode limits bytes = .ok value) : preimage value = bytes :=
  (Bounded.run_spec limits.toLimits _ _ _ accepted).1

theorem decode_fits (limits : Limits) {bytes : ByteArray} {value : Toplevel}
    (accepted : decode limits bytes = .ok value) : Fits limits value := by
  have spec := Bounded.run_spec limits.toLimits _ _ _ accepted
  exact ⟨spec.1 ▸ spec.2.1, spec.2.2⟩

theorem preimage_injective (limits : Limits) {left right : Toplevel}
    (leftFits : Fits limits left) (rightFits : Fits limits right)
    (equal : preimage left = preimage right) : left = right := by
  have lhs := decode_roundtrip limits left leftFits
  rw [equal, decode_roundtrip limits right rightFits] at lhs
  exact (Except.ok.inj lhs).symm

theorem Encoded.roundtrip {limits : Limits} {value : Toplevel} (encoded : Encoded limits value) :
    decode limits encoded.bytes = .ok value := by
  rw [encoded.exact]
  exact decode_roundtrip limits value encoded.fits

theorem Addressed.canonical {limits : Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) : preimage decoded.value = bytes :=
  decode_canonical limits decoded.decoded

theorem Addressed.fits {limits : Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) : Fits limits decoded.value :=
  decode_fits limits decoded.decoded

theorem Addressed.root_eq {limits : Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) : Address.blake3 bytes = root := by
  rw [← decoded.canonical]
  exact decoded.identity

/-- Content-root reuse retains an explicit pairwise collision premise. -/
theorem Addressed.matches {limits : Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) (expected : Toplevel)
    (fits : Fits limits expected) (identity : address expected = root)
    (collision : Address.Blake3NoCollision (preimage decoded.value) (preimage expected)) :
    decoded.value = expected :=
  preimage_injective limits decoded.fits fits (collision (decoded.identity.trans identity.symm))

end IxCC.Aiur.Wire
