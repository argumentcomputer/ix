import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby

def scalarCases (check : Check) : IO Unit := do
  let numbers := #[0, 1, 15, 16, 17, 2 ^ 28 - 1, 2 ^ 28, 2 ^ 32 - 1, 2 ^ 32,
    2 ^ 32 + 1, goldilocksModulus - 1, goldilocksModulus, goldilocksModulus + 1,
    2 ^ 64, 2 ^ 65 + 37, 2 ^ 80 + 17, 2 ^ 256 + 255, 2 ^ 512 - 1]
  for n in numbers do
    for (weight, acc) in #[(0, 0), (1, 0), (16, 7), (0xffffffff, 0x98765432)] do
      check 0 #[natural n, word weight, word acc] (word (acc + n.toUInt32 * weight))
    for (weight, acc) in #[(0, 17), (1, 0), (256, 19), (2 ^ 80, 2 ^ 96 + 7)] do
      check 1 #[word n.toUInt32, natural weight, natural acc]
        (natural (acc + n.toUInt32.toNat * weight))
    check 2 #[word n.toUInt32] (natural n.toUInt32.toNat)
    check 3 #[natural n] (natural n)
    check 4 #[natural n] (word n.toUInt32)
    check 5 #[natural n] (natural n)
    let field := Goldilocks.reduce n
    check 6 #[.scalar (.field field)] (natural field.val)
    check 7 #[natural n] (.scalar (.field field))
    check 8 #[natural n] (.scalar (.field field))
    check 83 #[natural n] (natural field.val)
    check 87 #[natural field.val] (natural field.neg.val)
    check 88 #[natural field.val] (natural field.inverse.val)
    for shift in #[0, 1, 31, 32, 63, 64, 511, 512, 2 ^ 80] do
      let expected := if shift > 512 then 0 else n >>> shift
      check 9 #[natural n, natural shift] (natural expected)
      check 21 #[natural n, natural shift] (natural expected)
    check 10 #[natural n, natural 23] (natural (23 + n.log2))
    check 22 #[natural n] (natural n.log2)
  for a in numbers do
    for b in numbers do
      for (id, output) in #[(12, natural (a + b)), (13, natural (a - b)),
          (14, natural (a * b)), (15, natural (a / b)), (16, natural (a % b)),
          (17, boolean (a == b)), (18, boolean (a < b)), (19, boolean (a ≤ b))] do
        check id #[natural a, natural b] output
      let a := Goldilocks.reduce a
      let b := Goldilocks.reduce b
      for (id, value) in #[(84, a.add b), (85, a.sub b), (86, a.mul b)] do
        check id #[natural a.val, natural b.val] (natural value.val)
      check 89 #[natural a.val, natural b.val] (.scalar (.extField ⟨a, b⟩))
      let left : ExtGoldilocks := ⟨a, b⟩
      let right : ExtGoldilocks := ⟨b, a⟩
      for (id, value) in #[(90, left.add right), (91, left.sub right), (92, left.mul right)] do
        check id #[.scalar (.extField left), .scalar (.extField right)] (.scalar (.extField value))
      check 93 #[.scalar (.extField left)] (.scalar (.extField left.inverse))
      check 94 #[.scalar (.extField left), .scalar (.extField right)] (boolean (left == right))
      check 95 #[.scalar (.extField left)] (natural a.val)
      check 96 #[.scalar (.extField left)] (natural b.val)
  for base in #[0, 1, 2, 3, 7, 2 ^ 32, 2 ^ 64 + 17] do
    for exponent in #[0, 1, 2, 3, 7, 31] do
      let power := base ^ exponent
      check 20 #[natural base, natural exponent] (natural power)
      for accumulator in #[0, 1, 19] do
        check 11 #[natural base, natural exponent, natural accumulator] (natural (accumulator * power))
  for exponent in #[2 ^ 64, 2 ^ 80 + 1, 2 ^ 256] do
    for base in #[0, 1] do
      check 20 #[natural base, natural exponent] (natural base)
      for accumulator in #[0, 1, 19] do
        check 11 #[natural base, natural exponent, natural accumulator] (natural (accumulator * base))

end CompilatrixTests.Ixby.Native
