import Aiur.Library.Field.BN254.Prime
import Aiur.Library.U32
import Aiur.Library.U64

/-! Explicit BN254 scalar-field selection for Aiur programs. The shared byte
and word libraries use the ambient field only within their proved integer
bounds; both bounds hold for this modulus. -/
namespace Aiur.Library.Field.BN254

abbrev F := ZMod modulus

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

theorem u32_compatible : U32.Compatible F :=
  U32.compatible_of_charP F modulus (by decide)

theorem u64_compatible : U64.Compatible F :=
  U64.compatible_of_charP F modulus (by decide)

end Aiur.Library.Field.BN254
