import IxCCTests.Aiur.WireFixtures
import IxCC.Aiur.Wire.IngressProofs

namespace IxCCTests.Aiur.WireProofs

open IxCC.Aiur.Wire
open IxCCTests.Aiur.WireFixtures

theorem counter_fits : Fits {} counter := by
  unfold Fits
  cbv

theorem counter_roundtrip : decode {} (preimage counter) = .ok counter :=
  decode_roundtrip {} counter counter_fits

theorem counter_components : componentsValid counter = true := by cbv

theorem ranked_mutual_components : componentsValid rankedMutual = true := by cbv

theorem unranked_mutual_rejected :
    componentsValid { rankedMutual with callComponents := #[⟨0, false⟩, ⟨0, false⟩] } = false := by
  cbv

end IxCCTests.Aiur.WireProofs
