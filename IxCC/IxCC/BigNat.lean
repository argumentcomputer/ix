import IxCC.BigNat.LimbOps
import IxCC.BigNat.Basic
import IxCC.BigNat.Linear
import IxCC.BigNat.Mul
import IxCC.BigNat.Div
import IxCC.BigNat.GcdConv

/-! # Pure-Lean Formally Verified Multi-Precision Arithmetic (`IxCC.BigNat`)

Umbrella module for IxCC's clean-room, formally verified GMP (`mpn`) equivalent
over canonical little-endian `Array UInt64` (`docs/bignum-design.md`):

- `IxCC.BigNat.LimbOps`: 5 hardware 64-bit limb primitives (`addCarry64`,
  `subBorrow64`, `mulWide64`, `divWide64`, `clz64`) + `mulAddCarry64`.
- `IxCC.BigNat.Basic`: Canonical normal form `WF`, `toNat`, `normalize`,
  `ofUInt64`, `ofSmall`, `ofNat`, `toSmall?`.
- `IxCC.BigNat.Linear`: `cmp`, `beq`, `ble`, `blt`, `add`, `subRaw`, `sub`,
  `pred`, `land`, `lor`, `xor`, `shiftLimbs`, `shiftLeft`, `shiftRight`, `log2`.
- `IxCC.BigNat.Mul`: `mulSchoolbook`, `sqrSchoolbook`, Karatsuba (`mulKaratsuba`,
  `sqrKaratsuba`, `K = 32`), `mul`, `sqr`, `pow` (left-to-right binary squaring).
- `IxCC.BigNat.Div`: `divMod1`, Knuth Algorithm D `divMod`, `div`, `mod`.
- `IxCC.BigNat.GcdConv`: `gcd`, `mulAdd1`, `10^19`-chunked `toDecimalChunks`,
  `ofDecimalChunks`, `toDecimalDigits`, `ofDecimalDigits`, `toDecimal`, `ofDecimal`.

For Layer-1 formal correctness proofs, import `IxCC.BigNat.Proof`.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2: *Seminumerical Algorithms*,
  §4.3.1, §4.3.3, §4.4, §4.5.2, §4.6.3.
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied Cryptography*,
  Ch. 14 (14.7, 14.9, 14.12, 14.16, 14.20, 14.54, 14.79).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, Ch. 1.
-/
