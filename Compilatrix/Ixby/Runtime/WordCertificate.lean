import Compilatrix.Ixby.Runtime.WordCode
import Compilatrix.Ixby.Runtime.NumberConversion

namespace Compilatrix.Ixby.Runtime.Words

open Ix.Ixby ScalarFunction

structure Links where
  conversions : Conversion.Links
  u8OfNat : FunctionId
  u8ToNat : FunctionId
  u8ToU32 : FunctionId
  u8Equal : FunctionId
  u8Add : FunctionId
  u8ShiftLeft : FunctionId
  u8ShiftRight : FunctionId
  u32OfNat : FunctionId
  u32OfNatLT : FunctionId
  u32ToU8 : FunctionId
  u32ToNat : FunctionId
  u32Add : FunctionId
  u32Sub : FunctionId
  u32Mul : FunctionId
  u32And : FunctionId
  u32Or : FunctionId
  u32Xor : FunctionId
  u32ShiftLeft : FunctionId
  u32ShiftRight : FunctionId
  u32Equal : FunctionId
  u32Less : FunctionId
  usizeOfNat : FunctionId
  usizeToNat : FunctionId
  usizeAdd : FunctionId
  usizeSub : FunctionId
  usizeEqual : FunctionId
  usizeLess : FunctionId

/-- Complete code and dependency evidence for all twenty-seven emitted word
helpers. USize code uses the compiler's fixed 64-bit representation. -/
structure Certificate (program : Program) (links : Links) : Type where
  conversions : Conversion.Certificate program links.conversions
  u8OfNat : Checked program links.u8OfNat (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 8)
  u8ToNat : Checked program links.u8ToNat (Words.identity)
  u8ToU32 : Checked program links.u8ToU32 (Words.identity)
  u8Equal : Checked program links.u8Equal (Words.compare links.conversions.natural .natEq)
  u8Add : Checked program links.u8Add (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 8 .natAdd .word32Add)
  u8ShiftLeft : Checked program links.u8ShiftLeft (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shl 8)
  u8ShiftRight : Checked program links.u8ShiftRight (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shr 8)
  u32OfNat : Checked program links.u32OfNat (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 32)
  u32OfNatLT : Checked program links.u32OfNatLT (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 2 32)
  u32ToU8 : Checked program links.u32ToU8 (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 8)
  u32ToNat : Checked program links.u32ToNat (Words.identity)
  u32Add : Checked program links.u32Add (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 32 .natAdd .word32Add)
  u32Sub : Checked program links.u32Sub (Words.subtract links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 32)
  u32Mul : Checked program links.u32Mul (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 32 .natMul .word32Mul)
  u32And : Checked program links.u32And (Words.logical links.conversions.lowWord links.conversions.fromWord .word32And)
  u32Or : Checked program links.u32Or (Words.logical links.conversions.lowWord links.conversions.fromWord .word32Or)
  u32Xor : Checked program links.u32Xor (Words.logical links.conversions.lowWord links.conversions.fromWord .word32Xor)
  u32ShiftLeft : Checked program links.u32ShiftLeft (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shl 32)
  u32ShiftRight : Checked program links.u32ShiftRight (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shr 32)
  u32Equal : Checked program links.u32Equal (Words.compare links.conversions.natural .natEq)
  u32Less : Checked program links.u32Less (Words.compare links.conversions.natural .natLt)
  usizeOfNat : Checked program links.usizeOfNat (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 64)
  usizeToNat : Checked program links.usizeToNat (Words.identity)
  usizeAdd : Checked program links.usizeAdd (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 64 .natAdd .word32Add)
  usizeSub : Checked program links.usizeSub (Words.subtract links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 64)
  usizeEqual : Checked program links.usizeEqual (Words.compare links.conversions.natural .natEq)
  usizeLess : Checked program links.usizeLess (Words.compare links.conversions.natural .natLt)

def certify (program : Program) (links : Links) : Except String (Certificate program links) := do
  let conversions ← Conversion.certify program links.conversions
  let u8OfNat ← check program links.u8OfNat (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 8)
  let u8ToNat ← check program links.u8ToNat (Words.identity)
  let u8ToU32 ← check program links.u8ToU32 (Words.identity)
  let u8Equal ← check program links.u8Equal (Words.compare links.conversions.natural .natEq)
  let u8Add ← check program links.u8Add (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 8 .natAdd .word32Add)
  let u8ShiftLeft ← check program links.u8ShiftLeft (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shl 8)
  let u8ShiftRight ← check program links.u8ShiftRight (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shr 8)
  let u32OfNat ← check program links.u32OfNat (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 32)
  let u32OfNatLT ← check program links.u32OfNatLT (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 2 32)
  let u32ToU8 ← check program links.u32ToU8 (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 8)
  let u32ToNat ← check program links.u32ToNat (Words.identity)
  let u32Add ← check program links.u32Add (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 32 .natAdd .word32Add)
  let u32Sub ← check program links.u32Sub (Words.subtract links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 32)
  let u32Mul ← check program links.u32Mul (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 32 .natMul .word32Mul)
  let u32And ← check program links.u32And (Words.logical links.conversions.lowWord links.conversions.fromWord .word32And)
  let u32Or ← check program links.u32Or (Words.logical links.conversions.lowWord links.conversions.fromWord .word32Or)
  let u32Xor ← check program links.u32Xor (Words.logical links.conversions.lowWord links.conversions.fromWord .word32Xor)
  let u32ShiftLeft ← check program links.u32ShiftLeft (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shl 32)
  let u32ShiftRight ← check program links.u32ShiftRight (Words.shift links.conversions.lowWord links.conversions.fromWord .word32Shr 32)
  let u32Equal ← check program links.u32Equal (Words.compare links.conversions.natural .natEq)
  let u32Less ← check program links.u32Less (Words.compare links.conversions.natural .natLt)
  let usizeOfNat ← check program links.usizeOfNat (Words.truncate links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 1 64)
  let usizeToNat ← check program links.usizeToNat (Words.identity)
  let usizeAdd ← check program links.usizeAdd (Words.modular links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 64 .natAdd .word32Add)
  let usizeSub ← check program links.usizeSub (Words.subtract links.conversions.natural links.conversions.lowWord links.conversions.cachedCtor 64)
  let usizeEqual ← check program links.usizeEqual (Words.compare links.conversions.natural .natEq)
  let usizeLess ← check program links.usizeLess (Words.compare links.conversions.natural .natLt)
  return { conversions, u8OfNat, u8ToNat, u8ToU32, u8Equal, u8Add, u8ShiftLeft, u8ShiftRight, u32OfNat, u32OfNatLT, u32ToU8, u32ToNat, u32Add, u32Sub, u32Mul, u32And, u32Or, u32Xor, u32ShiftLeft, u32ShiftRight, u32Equal, u32Less, usizeOfNat, usizeToNat, usizeAdd, usizeSub, usizeEqual, usizeLess }

end Compilatrix.Ixby.Runtime.Words
