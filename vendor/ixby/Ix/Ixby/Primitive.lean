module
public import Ix.Ixby.Basic
public import Ix.Ixby.Blake3

/-! Closed scalar semantics. These definitions are reference computations;
their arithmetizations and source-correctness theorems remain separate work. -/

public section
@[expose] section

namespace Ix.Ixby

def Scalar.validate (limits : Limits) : Scalar → Except Error Unit
  | .nat n =>
    if n != 0 && n.log2 ≥ limits.natBits then .error (.limit .natBits)
    else .ok ()
  | .str s =>
    if s.utf8ByteSize > limits.stringBytes then .error (.limit .stringBytes)
    else .ok ()
  | .bytes b =>
    if b.size > limits.byteArrayBytes then .error (.limit .byteArrayBytes)
    else .ok ()
  | .bool _ | .word32 _ | .field _ | .extField _ => .ok ()

/-- Fixed-width little-endian encoding; callers establish that the value fits.
This helper is not an admission check and deliberately exposes truncation. -/
def bytesLE (width n : Nat) : Array UInt8 :=
  (Array.range width).map fun i => (n >>> (8 * i)).toUInt8

def natOfBytesLE (bytes : Array UInt8) : Nat :=
  bytes.toList.foldr (fun b n => b.toNat + 256 * n) 0

def word32Rotr (a n : UInt32) : UInt32 :=
  let shift := n % 32
  if shift == 0 then a else (a >>> shift) ||| (a <<< (32 - shift))

def Primitive.eval (limits : Limits) (primitive : Primitive) (args : List Value) :
    Except Error Value := do
  if args.length != primitive.arity then
    throw (.arityMismatch primitive.arity args.length)
  -- Check byte/large-scalar bounds before computing any variable-size result,
  -- including when this public helper is called outside whole-image execution.
  for arg in args do
    if let .scalar value := arg then value.validate limits
  let result : Scalar ← match primitive, args with
    | .natAdd, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a + b))
    | .natSub, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a - b))
    | .natMul, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a * b))
    | .natDiv, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a / b))
    | .natMod, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a % b))
    | .natEq, [.scalar (.nat a), .scalar (.nat b)] => pure (.bool (a == b))
    | .natLt, [.scalar (.nat a), .scalar (.nat b)] => pure (.bool (a < b))
    | .strAppend, [.scalar (.str a), .scalar (.str b)] => pure (.str (a ++ b))
    | .strLength, [.scalar (.str s)] => pure (.nat s.length)
    | .strEq, [.scalar (.str a), .scalar (.str b)] => pure (.bool (a == b))
    | .word32Add, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.word32 (a + b))
    | .word32Sub, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.word32 (a - b))
    | .word32Mul, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.word32 (a * b))
    | .word32And, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.word32 (a &&& b))
    | .word32Or, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.word32 (a ||| b))
    | .word32Xor, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.word32 (a ^^^ b))
    | .word32Shl, [.scalar (.word32 a), .scalar (.word32 b)] =>
      pure (.word32 (if b < 32 then a <<< b else 0))
    | .word32Shr, [.scalar (.word32 a), .scalar (.word32 b)] =>
      pure (.word32 (if b < 32 then a >>> b else 0))
    | .word32Rotr, [.scalar (.word32 a), .scalar (.word32 b)] =>
      pure (.word32 (Ix.Ixby.word32Rotr a b))
    | .word32Eq, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.bool (a == b))
    | .word32Lt, [.scalar (.word32 a), .scalar (.word32 b)] => pure (.bool (a < b))
    | .word32ToBytes, [.scalar (.word32 a)] => pure (.bytes (bytesLE 4 a.toNat))
    | .bytesToWord32, [.scalar (.bytes a)] =>
      if a.size == 4 then pure (.word32 (natOfBytesLE a).toUInt32)
      else throw (.primitiveValue primitive)
    | .word32ToField, [.scalar (.word32 a)] => pure (.field (Goldilocks.reduce a.toNat))
    | .fieldAdd, [.scalar (.field a), .scalar (.field b)] => pure (.field (a.add b))
    | .fieldSub, [.scalar (.field a), .scalar (.field b)] => pure (.field (a.sub b))
    | .fieldMul, [.scalar (.field a), .scalar (.field b)] => pure (.field (a.mul b))
    | .fieldInverse, [.scalar (.field a)] => pure (.field a.inverse)
    | .fieldEq, [.scalar (.field a), .scalar (.field b)] => pure (.bool (a == b))
    | .fieldToBytes, [.scalar (.field a)] => pure (.bytes (bytesLE 8 a.val))
    | .bytesToField, [.scalar (.bytes a)] =>
      if a.size != 8 then throw (.primitiveValue primitive)
      else if h : natOfBytesLE a < goldilocksModulus then pure (.field ⟨natOfBytesLE a, h⟩)
      else throw (.primitiveValue primitive)
    | .extAdd, [.scalar (.extField a), .scalar (.extField b)] => pure (.extField (a.add b))
    | .extSub, [.scalar (.extField a), .scalar (.extField b)] => pure (.extField (a.sub b))
    | .extMul, [.scalar (.extField a), .scalar (.extField b)] => pure (.extField (a.mul b))
    | .extInverse, [.scalar (.extField a)] => pure (.extField a.inverse)
    | .extEq, [.scalar (.extField a), .scalar (.extField b)] => pure (.bool (a == b))
    | .extPack, [.scalar (.field a), .scalar (.field b)] => pure (.extField ⟨a, b⟩)
    | .extFst, [.scalar (.extField a)] => pure (.field a.c0)
    | .extSnd, [.scalar (.extField a)] => pure (.field a.c1)
    | .bytesLength, [.scalar (.bytes a)] =>
      if a.size < 2 ^ 32 then pure (.word32 a.size.toUInt32)
      else throw (.primitiveValue primitive)
    | .bytesGet, [.scalar (.bytes a), .scalar (.word32 i)] =>
      match a[i.toNat]? with
      | some b => pure (.word32 b.toUInt32)
      | none => throw (.primitiveValue primitive)
    | .bytesAppend, [.scalar (.bytes a), .scalar (.bytes b)] =>
      if a.size + b.size > limits.byteArrayBytes then throw (.limit .byteArrayBytes)
      else pure (.bytes (a ++ b))
    | .bytesSlice, [.scalar (.bytes a), .scalar (.word32 start), .scalar (.word32 length)] =>
      if start.toNat + length.toNat ≤ a.size then
        pure (.bytes (a.extract start.toNat (start.toNat + length.toNat)))
      else throw (.primitiveValue primitive)
    | .bytesEq, [.scalar (.bytes a), .scalar (.bytes b)] => pure (.bool (a == b))
    | .blake3, [.scalar (.bytes a)] => pure (.bytes (Blake3.hash a))
    | _, _ => throw (.primitiveType primitive)
  result.validate limits
  return .scalar result

end Ix.Ixby
