import Compilatrix.Ixby.Runtime.Builder

/-! Exact natural arithmetic, with an optional cached low Word32 for byte indices.
Mathematical Nat values and native fields retain their distinct semantics.
Field-backed numbers expose an exact Nat view when the source requires it. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

private def pair (n low : Operand) : CodeM Operand :=
  make `Ixby.Runtime.Number [n, low]

private def rawNumber (n : Operand) : CodeM Operand := make `Ixby.Runtime.RawNumber [n]

private def binary (natOp wordOp : Primitive) : CodeM Unit := do
  let a ← natural (.local 0)
  let b ← natural (.local 1)
  let n ← primitive natOp [a, b]
  caseCtor (.local 0) #[
    (`Ixby.Runtime.Number, 2, fun a => caseCtor (.local 1) #[
      (`Ixby.Runtime.Number, 2, fun b => do
        ret (← pair n (← primitive wordOp [a[1]!, b[1]!]))),
      (`Ixby.Runtime.RawNumber, 1, fun _ => do ret (← rawNumber n)),
      (`Ixby.Runtime.FieldNumber, 1, fun _ => do ret (← rawNumber n))]),
    (`Ixby.Runtime.RawNumber, 1, fun _ => do ret (← rawNumber n)),
    (`Ixby.Runtime.FieldNumber, 1, fun _ => do ret (← rawNumber n))]

private def compare (operation : Primitive) (reverse := false) : CodeM Unit := do
  let a ← natural (.local 0)
  let b ← natural (.local 1)
  ret (← primitive operation (if reverse then [b, a] else [a, b]))

private def truncate (bits : Nat) (input : Operand) : CodeM Operand := do
  let (n, low) ← numberParts input
  let n ← primitive .natMod [n, rawNat (2 ^ bits)]
  let low ← if bits < 32 then primitive .word32And [low, word (2 ^ bits - 1)] else pure low
  pair n low

private def modularBinary (bits : Nat) (natOp wordOp : Primitive) (subtract := false) : CodeM Unit := do
  let (a, lowA) ← numberParts (.local 0)
  let (b, lowB) ← numberParts (.local 1)
  let a ← if subtract then primitive .natAdd [a, rawNat (2 ^ bits)] else pure a
  let n ← primitive natOp [a, b]
  let low ← primitive wordOp [lowA, lowB]
  ret (← truncate bits (← pair n low))

private def wordBinary (operation : Primitive) (bits : Nat) (shift := false) : CodeM Unit := do
  let a ← lowWord (.local 0)
  let b ← lowWord (.local 1)
  let b ← if shift then primitive .word32And [b, word (bits - 1)] else pure b
  let result ← primitive operation [a, b]
  let result ← if bits < 32 then primitive .word32And [result, word (2 ^ bits - 1)] else pure result
  tailCall `Ixby.Runtime.fromWord [result]

-- A four-bit digit crosses representations through a balanced tree of exact
-- comparisons with literals. Callers first reduce/mask the input below 16.
-- This uses only the existing instruction set, without a host conversion.
private def nibbleTree (lo width : Nat) (toWord : Bool) : Nat → CodeM Unit
  | 0 => trap
  | fuel + 1 => do
    if width == 1 then ret (if toWord then word lo else rawNat lo)
    else
      let half := width / 2
      let mid := lo + half
      let less ← primitive (if toWord then .natLt else .word32Lt)
        [.local 0, if toWord then rawNat mid else word mid]
      branch less (nibbleTree lo half toWord fuel) (nibbleTree mid half toWord fuel)

def numberFunctions : Array (Name × Nat) := #[
  (`Ixby.Runtime.toWord, 3), (`Ixby.Runtime.fromWordLoop, 3),
  (`Ixby.Runtime.fromWord, 1), (`Ixby.Runtime.fromRaw, 1),
  (`Ixby.Runtime.lowWord, 1), (`Ixby.Runtime.natural, 1),
  (`Ixby.Runtime.fieldNatural, 1), (`Ixby.Runtime.asField, 1),
  (`Ixby.Runtime.fieldFromNatural, 1),
  (`Ixby.Runtime.nibbleWord, 1), (`Ixby.Runtime.nibbleNat, 1),
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
  define `Ixby.Runtime.nibbleWord 1 (nibbleTree 0 16 true 5)
  define `Ixby.Runtime.nibbleNat 1 (nibbleTree 0 16 false 5)
  -- toWord n weight accumulator, consuming four low bits per iteration.
  define `Ixby.Runtime.toWord 3 do
    let zero ← primitive .natEq [.local 0, rawNat 0]
    branch zero (ret (.local 2)) do
      let done ← primitive .word32Eq [.local 1, word 0]
      branch done (ret (.local 2)) do
        let digit ← call `Ixby.Runtime.nibbleWord [← primitive .natMod [.local 0, rawNat 16]]
        let acc ← primitive .word32Add [.local 2, ← primitive .word32Mul [digit, .local 1]]
        let next ← primitive .natDiv [.local 0, rawNat 16]
        let weight ← primitive .word32Shl [.local 1, word 4]
        tailCall `Ixby.Runtime.toWord [next, weight, acc]
  -- fromWordLoop word weight accumulator returns a raw mathematical Nat.
  define `Ixby.Runtime.fromWordLoop 3 do
    let zero ← primitive .word32Eq [.local 0, word 0]
    branch zero (ret (.local 2)) do
      let digit ← call `Ixby.Runtime.nibbleNat [← primitive .word32And [.local 0, word 15]]
      let acc ← primitive .natAdd [.local 2, ← primitive .natMul [digit, .local 1]]
      let next ← primitive .word32Shr [.local 0, word 4]
      let weight ← primitive .natMul [.local 1, rawNat 16]
      tailCall `Ixby.Runtime.fromWordLoop [next, weight, acc]
  define `Ixby.Runtime.fromWord 1 do
    let n ← call `Ixby.Runtime.fromWordLoop [.local 0, rawNat 1, rawNat 0]
    ret (← pair n (.local 0))
  define `Ixby.Runtime.fromRaw 1 do
    ret (← rawNumber (.local 0))
  define `Ixby.Runtime.lowWord 1 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Number, 2, fun fields => ret fields[1]!),
      (`Ixby.Runtime.RawNumber, 1, fun fields =>
        tailCall `Ixby.Runtime.toWord [fields[0]!, word 1, word 0]),
      (`Ixby.Runtime.FieldNumber, 1, fun fields => do
        let bytes ← primitive .fieldToBytes [fields[0]!]
        ret (← primitive .bytesToWord32 [← primitive .bytesSlice [bytes, word 0, word 4]]))]
  define `Ixby.Runtime.fieldNatural 1 do
    let bytes ← primitive .fieldToBytes [.local 0]
    let read (offset : Nat) : CodeM Operand := do
      let chunk ← primitive .bytesSlice [bytes, word offset, word 4]
      call `Ixby.Runtime.fromWordLoop [← primitive .bytesToWord32 [chunk], rawNat 1, rawNat 0]
    let low ← read 0
    let high ← read 4
    ret (← primitive .natAdd [low, ← primitive .natMul [high, rawNat (2 ^ 32)]])
  define `Ixby.Runtime.natural 1 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Number, 2, fun fields => ret fields[0]!),
      (`Ixby.Runtime.RawNumber, 1, fun fields => ret fields[0]!),
      (`Ixby.Runtime.FieldNumber, 1, fun fields => tailCall `Ixby.Runtime.fieldNatural [fields[0]!])]
  define `Ixby.Runtime.fieldFromNatural 1 do
    let n ← primitive .natMod [.local 0, rawNat goldilocksModulus]
    let low ← call `Ixby.Runtime.toWord [n, word 1, word 0]
    let high ← call `Ixby.Runtime.toWord [← primitive .natDiv [n, rawNat (2 ^ 32)], word 1, word 0]
    let low ← primitive .word32ToField [low]
    let high ← primitive .word32ToField [high]
    let weight := Operand.literal (.field (Goldilocks.reduce (2 ^ 32)))
    ret (← primitive .fieldAdd [low, ← primitive .fieldMul [high, weight]])
  define `Ixby.Runtime.asField 1 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Number, 2, fun fields => tailCall `Ixby.Runtime.fieldFromNatural [fields[0]!]),
      (`Ixby.Runtime.RawNumber, 1, fun fields => tailCall `Ixby.Runtime.fieldFromNatural [fields[0]!]),
      (`Ixby.Runtime.FieldNumber, 1, fun fields => ret fields[0]!)]
  define `Nat.add 2 (binary .natAdd .word32Add)
  define `Nat.mul 2 (binary .natMul .word32Mul)
  define `Nat.sub 2 do
    let a ← natural (.local 0)
    let b ← natural (.local 1)
    let underflow ← primitive .natLt [a, b]
    branch underflow
      (do ret (← number 0))
      (binary .natSub .word32Sub)
  for (name, operation) in #[(`Nat.div, Primitive.natDiv), (`Nat.mod, .natMod)] do
    define name 2 do
      let a ← natural (.local 0)
      let b ← natural (.local 1)
      tailCall `Ixby.Runtime.fromRaw [← primitive operation [a, b]]
  define `Nat.decEq 2 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Number, 2, fun _ => compare .natEq),
      (`Ixby.Runtime.RawNumber, 1, fun _ => compare .natEq),
      (`Ixby.Runtime.FieldNumber, 1, fun a => caseCtor (.local 1) #[
        (`Ixby.Runtime.Number, 2, fun _ => compare .natEq),
        (`Ixby.Runtime.RawNumber, 1, fun _ => compare .natEq),
        (`Ixby.Runtime.FieldNumber, 1, fun b => do ret (← primitive .fieldEq [a[0]!, b[0]!]))])]
  define `Nat.decLt 2 (compare .natLt)
  define `Nat.decLe 2 do
    let a ← natural (.local 0)
    let b ← natural (.local 1)
    branch (← primitive .natLt [b, a]) (ret (boolean false)) (ret (boolean true))
  define `Ixby.Runtime.shiftRightLoop 2 do
    branch (← primitive .natEq [.local 1, rawNat 0])
      (tailCall `Ixby.Runtime.fromRaw [.local 0]) do
        branch (← primitive .natEq [.local 0, rawNat 0])
          (do ret (← number 0)) do
            let n ← primitive .natDiv [.local 0, rawNat 2]
            let shift ← primitive .natSub [.local 1, rawNat 1]
            tailCall `Ixby.Runtime.shiftRightLoop [n, shift]
  define `Nat.shiftRight 2 do
    tailCall `Ixby.Runtime.shiftRightLoop [← natural (.local 0), ← natural (.local 1)]
  define `Ixby.Runtime.log2Loop 2 do
    branch (← primitive .natLt [.local 0, rawNat 2])
      (tailCall `Ixby.Runtime.fromRaw [.local 1]) do
        let n ← primitive .natDiv [.local 0, rawNat 2]
        let log ← primitive .natAdd [.local 1, rawNat 1]
        tailCall `Ixby.Runtime.log2Loop [n, log]
  define `Nat.log2 1 do
    tailCall `Ixby.Runtime.log2Loop [← natural (.local 0), rawNat 0]
  define `Ixby.Runtime.powLoop 3 do
    branch (← primitive .natEq [.local 1, rawNat 0]) (ret (.local 2)) do
      let next ← primitive .natDiv [.local 1, rawNat 2]
      let bit ← primitive .natMod [.local 1, rawNat 2]
      let rest (acc : Operand) : CodeM Unit := do
        branch (← primitive .natEq [next, rawNat 0]) (ret acc) do
          let base ← call `Nat.mul [.local 0, .local 0]
          tailCall `Ixby.Runtime.powLoop [base, next, acc]
      branch (← primitive .natEq [bit, rawNat 1])
        (do rest (← call `Nat.mul [.local 2, .local 0]))
        (rest (.local 2))
  define `Nat.pow 2 do
    tailCall `Ixby.Runtime.powLoop [.local 0, ← natural (.local 1), ← number 1]
  for name in #[`UInt8.toNat, `UInt8.toUInt32, `UInt32.toNat, `USize.toNat] do
    define name 1 (ret (.local 0))
  for (name, arity, bits) in #[(`UInt8.ofNat, 1, 8), (`UInt32.ofNat, 1, 32),
      (`UInt32.ofNatLT, 2, 32), (`UInt32.toUInt8, 1, 8), (`USize.ofNat, 1, 64)] do
    define name arity do ret (← truncate bits (.local 0))
  for name in #[`UInt8.decEq, `UInt32.decEq, `USize.decEq] do define name 2 (compare .natEq)
  for name in #[`UInt32.decLt, `USize.decLt] do define name 2 (compare .natLt)
  define `UInt8.add 2 (modularBinary 8 .natAdd .word32Add)
  define `UInt32.add 2 (modularBinary 32 .natAdd .word32Add)
  define `UInt32.sub 2 (modularBinary 32 .natSub .word32Sub true)
  define `UInt32.mul 2 (modularBinary 32 .natMul .word32Mul)
  define `USize.add 2 (modularBinary 64 .natAdd .word32Add)
  define `USize.sub 2 (modularBinary 64 .natSub .word32Sub true)
  for (name, operation, bits, shift) in #[
      (`UInt8.shiftLeft, Primitive.word32Shl, 8, true),
      (`UInt8.shiftRight, .word32Shr, 8, true),
      (`UInt32.shiftLeft, .word32Shl, 32, true),
      (`UInt32.shiftRight, .word32Shr, 32, true),
      (`UInt32.land, .word32And, 32, false),
      (`UInt32.lor, .word32Or, 32, false),
      (`UInt32.xor, .word32Xor, 32, false)] do
    define name 2 (wordBinary operation bits shift)

end Compilatrix.Ixby.Runtime
