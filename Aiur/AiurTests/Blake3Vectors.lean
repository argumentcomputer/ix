import Aiur.Library.Blake3.Correctness

/-! # Known-answer vectors for the Lean BLAKE3 model

`Aiur.Library.Blake3.digest` is the specification that the Lean models of the
`Blake3` library are proved against (`Aiur/Aiur/Library/Blake3/Correctness.lean`;
no theorem yet relates the Aiur source to those models). These
are the official BLAKE3 test vectors (`test_vectors/test_vectors.json` in
BLAKE3-team/BLAKE3 at 1.5.4): the input of length `n` is the bytes `i % 251`
for `i < n`, and the expected value is the first 32 bytes of the `hash`
output. They cover the empty input, one byte, one block, both sides of the
1024-byte chunk boundary, and trees of two, three, four and nine chunks. -/

namespace AiurBlake3Vectors
open Aiur.Library.Blake3

private def pattern (n : Nat) : List UInt8 :=
  (List.range n).map fun i => (i % 251).toUInt8

private def hexByte (b : UInt8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  String.ofList (if digits.length < 2 then '0' :: digits else digits)

private def hex (d : Digest) : String :=
  String.join (d.toList.map hexByte)

#guard hex (digest (pattern 0)) ==
  "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
#guard hex (digest (pattern 1)) ==
  "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"
#guard hex (digest (pattern 64)) ==
  "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98"
#guard hex (digest (pattern 1023)) ==
  "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11"
#guard hex (digest (pattern 1024)) ==
  "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"
#guard hex (digest (pattern 1025)) ==
  "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"
#guard hex (digest (pattern 2048)) ==
  "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a"
#guard hex (digest (pattern 2049)) ==
  "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"
#guard hex (digest (pattern 3072)) ==
  "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2"
#guard hex (digest (pattern 3073)) ==
  "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3"
#guard hex (digest (pattern 8193)) ==
  "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b"

end AiurBlake3Vectors
