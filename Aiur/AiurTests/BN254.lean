import Aiur.Library.Field.BN254

/-! The BN254 field instance and integer-library compatibility proofs use
only the standard Lean foundational axioms. -/

/-- info: 'Aiur.Library.Field.BN254.modulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Field.BN254.modulus_prime

/-- info: 'Aiur.Library.Field.BN254.u32_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Field.BN254.u32_compatible

/-- info: 'Aiur.Library.Field.BN254.u64_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Field.BN254.u64_compatible
