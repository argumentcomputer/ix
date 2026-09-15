import Compilatrix.Ixon.Address

namespace CompilatrixTests

open Compilatrix.Ixon

/-- The universal BLAKE3 empty-input test vector:
`af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262`. -/
def expectedEmptyBlake3 : List Nat :=
  [0xaf, 0x13, 0x49, 0xb9, 0xf5, 0xf9, 0xa1, 0xa6,
   0xa0, 0x40, 0x4d, 0xea, 0x36, 0xdc, 0xc9, 0x49,
   0x9b, 0xcb, 0x25, 0xc9, 0xad, 0xc1, 0x12, 0xb7,
   0xcc, 0x9a, 0x93, 0xca, 0xe4, 0x1f, 0x32, 0x62]

def hashNats (a : Address) : List Nat :=
  a.hash.data.toList.map (fun (b : UInt8) => b.toNat)

/-- Deterministic distinct addresses for the compiled environment-index smoke
test. The first three bytes are a little-endian natural; the remaining bytes
are zero. -/
def indexedAddress (n : Nat) : Address :=
  Address.ofFn fun index =>
    if index.val == 0 then n.toUInt8
    else if index.val == 1 then (n / 256).toUInt8
    else if index.val == 2 then (n / (256 * 256)).toUInt8
    else 0

end CompilatrixTests
