module

@[expose] public section

/-!
# Literal facts for the toolchain fixtures

Each fixture toolchain compiles this file with its own `lean`, and its
`lean4export` exports these theorems with the roles and the certificate
theorems (`Regenerate.lean`). Each fact holds by `rfl` on literals, so checking
it reduces that toolchain's bound operations, among them the bitwise ones that
4.33.1 and 4.34.1 define differently, and the literal support. The file
imports only `Init` and elaborates unchanged from 4.29.0 to 4.35.0.
-/

namespace ToolchainFixture

theorem natLand : Nat.land 12 10 = 8 := rfl
theorem natLor : Nat.lor 12 10 = 14 := rfl
theorem natXor : Nat.xor 12 10 = 6 := rfl
theorem natDiv : 100 / 7 = 14 := rfl
theorem natMod : 100 % 7 = 2 := rfl
theorem natGcd : Nat.gcd 12 18 = 6 := rfl
theorem natMul : 12 * 18 = 216 := rfl
theorem charLiteral : 'a'.toNat = 97 := rfl
theorem stringLiteral : "ab" = String.ofList ['a', 'b'] := rfl

end ToolchainFixture
