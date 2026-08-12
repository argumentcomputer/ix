import Navigatrix

/-!
Runtime test executable: everything that must *execute* FFI (blake3)
lives here, compiled and linked against the static lib — elaboration-
time `#guard`s can't run FFI (no dynlib in the interpreter). Run by the
flake's `tests` check; prints `tests-ok` on success.
-/

open Navigatrix.Ixon

/-- The universal BLAKE3 empty-input test vector:
`af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262`. -/
def expectedEmptyBlake3 : List Nat :=
  [0xaf, 0x13, 0x49, 0xb9, 0xf5, 0xf9, 0xa1, 0xa6,
   0xa0, 0x40, 0x4d, 0xea, 0x36, 0xdc, 0xc9, 0x49,
   0x9b, 0xcb, 0x25, 0xc9, 0xad, 0xc1, 0x12, 0xb7,
   0xcc, 0x9a, 0x93, 0xca, 0xe4, 0x1f, 0x32, 0x62]

/-- Golden address of the sample axiom below. Deliberately
format-freezing: any change to the Ixon v2 canonical encoding breaks
this — bump it only with an intentional format roll. -/
def expectedSampleAxiomAddr : List Nat :=
  [175, 190, 20, 2, 194, 88, 190, 182, 79, 114, 28, 108, 112, 136,
   43, 71, 254, 192, 235, 145, 134, 231, 227, 179, 11, 181, 74, 208,
   29, 62, 109, 135]

def hashNats (a : Address) : List Nat :=
  a.hash.data.toList.map (fun (b : UInt8) => b.toNat)

def main : IO UInt32 := do
  let mut ok := true

  let empty := Address.blake3 (ByteArray.mk #[])
  if empty.hash.size != 32 then
    IO.eprintln s!"FAIL: hash size = {empty.hash.size}"
    ok := false
  if hashNats empty != expectedEmptyBlake3 then
    IO.eprintln s!"FAIL: blake3(empty) = {hashNats empty}"
    IO.eprintln s!"      expected       {expectedEmptyBlake3}"
    ok := false

  if !(Address.blake3 (ByteArray.mk #[1, 2, 3])
      == Address.blake3 (ByteArray.mk #[1, 2, 3])) then
    IO.eprintln "FAIL: blake3 nondeterministic"
    ok := false
  if Address.blake3 (ByteArray.mk #[1, 2, 3])
      == Address.blake3 (ByteArray.mk #[1, 2, 4]) then
    IO.eprintln "FAIL: blake3 input-insensitive"
    ok := false

  let c : Constant :=
    { info := .axio { isUnsafe := false, lvls := 1, typ := .sort 3 }
      sharing := #[], refs := #[], univs := #[.zero] }
  if hashNats c.address != expectedSampleAxiomAddr then
    IO.eprintln s!"FAIL: addr(sampleAxiom) = {hashNats c.address}"
    IO.eprintln s!"      expected           {expectedSampleAxiomAddr}"
    ok := false

  if ok then
    IO.println "tests-ok"
    return 0
  else
    return 1
