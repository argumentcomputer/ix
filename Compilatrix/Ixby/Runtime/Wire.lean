import Compilatrix.Ixby.Runtime.Array
import Ix.MultiStark.Verify.Codec.Wire

/-! Optional lowering of the pinned Stage2 wire helpers. These produce ordinary
Ixby instructions and retain the source writer's admission checks. Like the
typed frontend, this lowering currently has differential tests, not a refinement
certificate. The byte comparison is specific to the source's `Array UInt8`
instantiation; polymorphic array comparisons still compile from source. -/

namespace Compilatrix.Ixby.Runtime

open Lean Lean.Compiler Ix.Ixby

theorem wire_littleEndian_definition (width n : Nat) :
    MultiStark.Verify.Codec.Wire.littleEndian width n = bytesLE width n := rfl

theorem wire_fromLittleEndian_definition (bytes : Array UInt8) :
    MultiStark.Verify.Codec.Wire.fromLittleEndian bytes = natOfBytesLE bytes := rfl

/-- Canonical field admission can use the two native words without constructing
an intermediate Nat. The maximum high word admits only a zero low word. -/
theorem wire_field_canonical_words (low high : UInt32) :
    low.toNat + 2 ^ 32 * high.toNat < goldilocksModulus ↔
      high.toNat < 2 ^ 32 - 1 ∨ low.toNat = 0 := by
  have := low.toNat_lt
  have := high.toNat_lt
  change low.toNat + 4294967296 * high.toNat < 18446744069414584321 ↔
    high.toNat < 4294967295 ∨ low.toNat = 0
  omega

private def sourceFunction (name : Name) : BuildM Unit := do
  if (← get).functionNames.contains name then return
  let some decl ← LCNF.getMonoDecl? name | throwThe String s!"missing wire dependency {name}"
  discard <| reserveFunction name decl.params.size
  modify fun state => { state with pending := state.pending.push name }

private def pack (data size : Operand) : CodeM Operand :=
  make `Ixby.Runtime.Bytes [data, size]

def buildWire : BuildM Unit := do
  sourceFunction `MultiStark.Verify.Codec.Wire.writeBytes
  sourceFunction `MultiStark.Verify.Codec.Wire.readBytes
  for (name, arity) in #[
      (`Ixby.Runtime.wireLittleLoop, 3), (`Ixby.Runtime.wireFromLoop, 3),
      (`MultiStark.Verify.Codec.Wire.littleEndian, 2),
      (`MultiStark.Verify.Codec.Wire.fromLittleEndian, 1),
      (`MultiStark.Verify.Codec.Wire.writeByte, 2),
      (`MultiStark.Verify.Codec.Wire.readField, 1),
      (`MultiStark.Verify.Codec.Wire.writeField, 2),
      (`Array.instDecidableEqImpl._at_.MultiStark.Verify.Codec.Wire.canonicalize.spec_0, 2)] do
    discard <| reserveFunction name arity
  let define (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Unit :=
    discard <| defineFunction name arity body
  -- Raw width, raw natural, accumulated scalar bytes. The uncommon arbitrary
  -- width case consumes a word at a time, including a final partial word.
  define `Ixby.Runtime.wireLittleLoop 3 do
    let low ← call `Ixby.Runtime.toWord [.local 1, word 1, word 0]
    let encoded ← primitive .word32ToBytes [low]
    branch (← primitive .natLt [.local 0, rawNat 5])
      (do
        let width ← call `Ixby.Runtime.toWord [.local 0, word 1, word 0]
        let encoded ← primitive .bytesSlice [encoded, word 0, width]
        ret (← primitive .bytesAppend [.local 2, encoded]))
      (do
        let rest ← primitive .natSub [.local 0, rawNat 4]
        let high ← primitive .natDiv [.local 1, rawNat (2 ^ 32)]
        let encoded ← primitive .bytesAppend [.local 2, encoded]
        tailCall `Ixby.Runtime.wireLittleLoop [rest, high, encoded])
  define `MultiStark.Verify.Codec.Wire.littleEndian 2 do
    let (width, widthLow) ← numberParts (.local 0)
    let (n, low) ← numberParts (.local 1)
    let encoded ← primitive .word32ToBytes [low]
    branch (← primitive .natLt [width, rawNat 5])
      (do ret (← pack (← primitive .bytesSlice [encoded, word 0, widthLow]) (.local 0)))
      (do
        let rest ← primitive .natSub [width, rawNat 4]
        let high ← primitive .natDiv [n, rawNat (2 ^ 32)]
        let encoded ← call `Ixby.Runtime.wireLittleLoop [rest, high, encoded]
        ret (← pack encoded (.local 0)))
  define `Ixby.Runtime.wireFromLoop 3 do
    branch (← primitive .word32Eq [.local 1, word 0]) (ret (.local 2)) do
      let next ← primitive .word32Sub [.local 1, word 1]
      let byte ← call `Ixby.Runtime.fromWord [← primitive .bytesGet [.local 0, next]]
      let acc ← call `Nat.add [byte, ← call `Nat.mul [.local 2, ← number 256]]
      tailCall `Ixby.Runtime.wireFromLoop [.local 0, next, acc]
  define `MultiStark.Verify.Codec.Wire.fromLittleEndian 1 do
    let data ← call `Ixby.Runtime.toBytes [.local 0]
    let size ← primitive .bytesLength [data]
    let wordAt (offset : Nat) : CodeM Operand := do
      call `Ixby.Runtime.fromWord [← primitive .bytesToWord32
        [← primitive .bytesSlice [data, word offset, word 4]]]
    branch (← primitive .word32Eq [size, word 4])
      (do ret (← wordAt 0)) do
        branch (← primitive .word32Eq [size, word 8])
          (do
            let high ← call `Nat.mul [← wordAt 4, ← number (2 ^ 32)]
            tailCall `Nat.add [← wordAt 0, high])
          (do tailCall `Ixby.Runtime.wireFromLoop [data, size, ← number 0])
  define `MultiStark.Verify.Codec.Wire.writeByte 2 do
    let encoded ← primitive .word32ToBytes [← lowWord (.local 0)]
    let byte ← pack (← primitive .bytesSlice [encoded, word 0, word 1]) (← number 1)
    tailCall `MultiStark.Verify.Codec.Wire.writeBytes [byte, .local 1]
  define `MultiStark.Verify.Codec.Wire.readField 1 do
    let result ← call `MultiStark.Verify.Codec.Wire.readBytes [← number 8, .local 0]
    caseCtor result #[
      (`Except.error, 1, fun _ => ret result),
      (`Except.ok, 1, fun fields => do
        let pair ← pure fields[0]!
        let data ← call `Ixby.Runtime.toBytes [← project pair 0]
        let high ← primitive .bytesToWord32 [← primitive .bytesSlice [data, word 4, word 4]]
        let accept : CodeM Unit := do
          let field ← make `Ixby.Runtime.FieldNumber [← primitive .bytesToField [data]]
          let pair ← make `Prod.mk [field, ← project pair 1]
          ret (← make `Except.ok [pair])
        branch (← primitive .word32Lt [high, word (2 ^ 32 - 1)]) accept do
          let low ← primitive .bytesToWord32 [← primitive .bytesSlice [data, word 0, word 4]]
          branch (← primitive .word32Eq [low, word 0]) accept do
            ret (← make `Except.error [← make `MultiStark.Verify.DecodeError.field []]))]
  define `MultiStark.Verify.Codec.Wire.writeField 2 do
    let data ← primitive .fieldToBytes [← call `Ixby.Runtime.asField [.local 0]]
    tailCall `MultiStark.Verify.Codec.Wire.writeBytes [← pack data (← number 8), .local 1]
  define `Array.instDecidableEqImpl._at_.MultiStark.Verify.Codec.Wire.canonicalize.spec_0 2 do
    let left ← call `Ixby.Runtime.toBytes [.local 0]
    let right ← call `Ixby.Runtime.toBytes [.local 1]
    ret (← primitive .bytesEq [left, right])

end Compilatrix.Ixby.Runtime
