import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby Compilatrix.Tools.Check

def wordCases (check : Check) : IO Unit := do
  need (System.Platform.numBits == 64) "USize source oracle requires the pinned 64-bit platform"
  for a in [:256] do
    for b in #[0, 1, 7, 8, 9, 15, 16, 31, 32, 63, 64, 127, 128, 254, 255] do
      let left := a.toUInt8
      let right := b.toUInt8
      check 27 #[word left.toUInt32, word right.toUInt32] (word (left + right).toUInt32)
      check 28 #[word left.toUInt32, word right.toUInt32] (word (left <<< right).toUInt32)
      check 29 #[word left.toUInt32, word right.toUInt32] (word (left >>> right).toUInt32)
      check 26 #[word left.toUInt32, word right.toUInt32] (boolean (left == right))
    check 24 #[word a.toUInt32] (natural a)
    check 25 #[word a.toUInt32] (word a.toUInt32)
  let numbers := #[0, 1, 7, 31, 32, 63, 255, 256, 65535, 2 ^ 32 - 1, 2 ^ 32,
    goldilocksModulus - 1, goldilocksModulus, 2 ^ 64 - 1, 2 ^ 64,
    2 ^ 80 + 17, 2 ^ 256 + 37]
  for n in numbers do
    check 23 #[natural n] (word n.toUInt8.toUInt32)
    check 32 #[word n.toUInt32] (word n.toUInt32.toUInt8.toUInt32)
    check 30 #[natural n] (word n.toUInt32)
    check 31 #[natural n, .erased] (word n.toUInt32)
    check 33 #[word n.toUInt32] (natural n.toUInt32.toNat)
    check 44 #[natural n] (natural n.toUSize.toNat)
    check 45 #[natural n.toUSize.toNat] (natural n.toUSize.toNat)
  for a in numbers do
    for b in numbers do
      let left := a.toUInt32
      let right := b.toUInt32
      for (id, expected) in #[(34, left + right), (35, left - right), (36, left * right),
          (37, left &&& right), (38, left ||| right), (39, left ^^^ right),
          (40, left <<< right), (41, left >>> right)] do
        check id #[word left, word right] (word expected)
      check 42 #[word left, word right] (boolean (left == right))
      check 43 #[word left, word right] (boolean (left < right))
      let left := a.toUSize
      let right := b.toUSize
      check 46 #[natural left.toNat, natural right.toNat] (natural (left + right).toNat)
      check 47 #[natural left.toNat, natural right.toNat] (natural (left - right).toNat)
      check 48 #[natural left.toNat, natural right.toNat] (boolean (left == right))
      check 49 #[natural left.toNat, natural right.toNat] (boolean (left < right))

end CompilatrixTests.Ixby.Native
