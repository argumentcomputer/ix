import Compilatrix.Ixby.Runtime.Builder

/-! Revision-two scalar ABI. Nat and erased Fin/USize values use exact Nat
scalars; UInt8/UInt32 use Word32 scalars. Every change of type is explicit.
No numeric constructor or cached low word is allocated by this runtime. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

private def direct (operation : Primitive) (arity : Nat) : CodeM Unit := do
  ret (← primitive operation ((List.range arity).map Operand.local))

private def wordBinary (operation : Primitive) (bits : Nat) (shift := false) : CodeM Unit := do
  let rhs ← if shift then primitive .word32And [.local 1, word (bits - 1)] else pure (.local 1)
  let result ← primitive operation [.local 0, rhs]
  ret (← if bits < 32 then primitive .word32And [result, word (2 ^ bits - 1)] else pure result)

private def usizeBinary (operation : Primitive) (subtract := false) : CodeM Unit := do
  let left ← if subtract then primitive .natAdd [.local 0, rawNat (2 ^ 64)] else pure (.local 0)
  let result ← primitive operation [left, .local 1]
  ret (← primitive .natMod [result, rawNat (2 ^ 64)])

def numberFunctions : Array (Name × Nat) := #[
  (`Ixby.Runtime.toWord, 3), (`Ixby.Runtime.fromWordLoop, 3),
  (`Ixby.Runtime.fromWord, 1), (`Ixby.Runtime.fromRaw, 1),
  (`Ixby.Runtime.lowWord, 1), (`Ixby.Runtime.natural, 1),
  (`Ixby.Runtime.fieldNatural, 1), (`Ixby.Runtime.asField, 1),
  (`Ixby.Runtime.fieldFromNatural, 1),
  (`Ixby.Runtime.shiftRightLoop, 2), (`Ixby.Runtime.log2Loop, 2),
  (`Ixby.Runtime.powLoop, 3),
  (`Nat.add, 2), (`Nat.sub, 2), (`Nat.mul, 2), (`Nat.div, 2), (`Nat.mod, 2),
  (`Nat.decEq, 2), (`Nat.decLt, 2), (`Nat.decLe, 2),
  (`Nat.pow, 2), (`Nat.shiftRight, 2), (`Nat.log2, 1),
  (`UInt8.ofNat, 1), (`UInt8.toNat, 1), (`UInt8.toUInt32, 1),
  (`UInt8.decEq, 2), (`UInt8.add, 2), (`UInt8.shiftLeft, 2), (`UInt8.shiftRight, 2),
  (`UInt32.ofNat, 1), (`UInt32.ofNatLT, 2), (`UInt32.toUInt8, 1), (`UInt32.toNat, 1),
  (`UInt32.add, 2), (`UInt32.sub, 2), (`UInt32.mul, 2),
  (`UInt32.land, 2), (`UInt32.lor, 2), (`UInt32.xor, 2),
  (`UInt32.shiftLeft, 2), (`UInt32.shiftRight, 2), (`UInt32.decEq, 2), (`UInt32.decLt, 2),
  (`USize.ofNat, 1), (`USize.toNat, 1), (`USize.add, 2), (`USize.sub, 2),
  (`USize.decEq, 2), (`USize.decLt, 2)]

def buildNumbers : BuildM Unit := do
  for (name, arity) in numberFunctions do discard <| reserveFunction name arity
  let define (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Unit :=
    discard <| defineFunction name arity body
  -- The historical three-argument API retains its weighted accumulator law.
  define `Ixby.Runtime.toWord 3 do
    let low ← primitive .natToWord32 [.local 0]
    let weighted ← primitive .word32Mul [low, .local 1]
    ret (← primitive .word32Add [.local 2, weighted])
  define `Ixby.Runtime.fromWordLoop 3 do
    let n ← primitive .word32ToNat [.local 0]
    let weighted ← primitive .natMul [n, .local 1]
    ret (← primitive .natAdd [.local 2, weighted])
  for name in #[`Ixby.Runtime.fromWord, `UInt8.toNat, `UInt32.toNat] do
    define name 1 (direct .word32ToNat 1)
  for name in #[`Ixby.Runtime.fromRaw, `Ixby.Runtime.natural, `USize.toNat, `UInt8.toUInt32] do
    define name 1 (ret (.local 0))
  for name in #[`Ixby.Runtime.lowWord, `UInt32.ofNat] do
    define name 1 (direct .natToWord32 1)
  define `UInt32.ofNatLT 2 do ret (← primitive .natToWord32 [.local 0])
  define `UInt8.ofNat 1 do
    ret (← primitive .word32And [← primitive .natToWord32 [.local 0], word 255])
  define `UInt32.toUInt8 1 do ret (← primitive .word32And [.local 0, word 255])
  define `USize.ofNat 1 do ret (← primitive .natMod [.local 0, rawNat (2 ^ 64)])
  define `Ixby.Runtime.fieldNatural 1 (direct .fieldToNat 1)
  for name in #[`Ixby.Runtime.asField, `Ixby.Runtime.fieldFromNatural] do
    define name 1 (direct .natToField 1)
  for (name, operation) in #[(`Nat.add, Primitive.natAdd), (`Nat.sub, .natSub),
      (`Nat.mul, .natMul), (`Nat.div, .natDiv), (`Nat.mod, .natMod),
      (`Nat.decEq, .natEq), (`Nat.decLt, .natLt),
      (`USize.decEq, .natEq), (`USize.decLt, .natLt),
      (`UInt8.decEq, .word32Eq), (`UInt32.decEq, .word32Eq), (`UInt32.decLt, .word32Lt)] do
    define name 2 (direct operation 2)
  define `Nat.decLe 2 do
    branch (← primitive .natLt [.local 1, .local 0]) (ret (boolean false)) (ret (boolean true))
  define `Ixby.Runtime.shiftRightLoop 2 do
    branch (← primitive .natEq [.local 1, rawNat 0]) (ret (.local 0)) do
      branch (← primitive .natEq [.local 0, rawNat 0]) (ret (rawNat 0)) do
        let n ← primitive .natDiv [.local 0, rawNat 2]
        let shift ← primitive .natSub [.local 1, rawNat 1]
        tailCall `Ixby.Runtime.shiftRightLoop [n, shift]
  define `Nat.shiftRight 2 (tailCall `Ixby.Runtime.shiftRightLoop [.local 0, .local 1])
  define `Ixby.Runtime.log2Loop 2 do
    branch (← primitive .natLt [.local 0, rawNat 2]) (ret (.local 1)) do
      let n ← primitive .natDiv [.local 0, rawNat 2]
      let log ← primitive .natAdd [.local 1, rawNat 1]
      tailCall `Ixby.Runtime.log2Loop [n, log]
  define `Nat.log2 1 (tailCall `Ixby.Runtime.log2Loop [.local 0, rawNat 0])
  define `Ixby.Runtime.powLoop 3 do
    branch (← primitive .natEq [.local 1, rawNat 0]) (ret (.local 2)) do
      let next ← primitive .natDiv [.local 1, rawNat 2]
      let bit ← primitive .natMod [.local 1, rawNat 2]
      let rest (acc : Operand) : CodeM Unit := do
        branch (← primitive .natEq [next, rawNat 0]) (ret acc) do
          let base ← primitive .natMul [.local 0, .local 0]
          tailCall `Ixby.Runtime.powLoop [base, next, acc]
      branch (← primitive .natEq [bit, rawNat 1])
        (do rest (← primitive .natMul [.local 2, .local 0]))
        (rest (.local 2))
  define `Nat.pow 2 (tailCall `Ixby.Runtime.powLoop [.local 0, .local 1, rawNat 1])
  define `UInt8.add 2 (wordBinary .word32Add 8)
  for (name, operation) in #[(`UInt32.add, Primitive.word32Add),
      (`UInt32.sub, .word32Sub), (`UInt32.mul, .word32Mul),
      (`UInt32.land, .word32And), (`UInt32.lor, .word32Or), (`UInt32.xor, .word32Xor)] do
    define name 2 (direct operation 2)
  for (name, operation, bits) in #[(`UInt8.shiftLeft, Primitive.word32Shl, 8),
      (`UInt8.shiftRight, .word32Shr, 8), (`UInt32.shiftLeft, .word32Shl, 32),
      (`UInt32.shiftRight, .word32Shr, 32)] do
    define name 2 (wordBinary operation bits true)
  define `USize.add 2 (usizeBinary .natAdd)
  define `USize.sub 2 (usizeBinary .natSub true)

end Compilatrix.Ixby.Runtime
