import Ix.Ixby.Primitive
import Compilatrix.Ixby.Runtime.Chunked.Value

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Scalar Primitive Limits Error Goldilocks ExtGoldilocks
  goldilocksModulus bytesLE natOfBytesLE)

def evalScalarUnchecked (primitive : Primitive) (args : List Value) :
    Except Error Value := do
  let result : Scalar ← match primitive, args with
    | .natAdd, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a + b))
    | .natSub, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a - b))
    | .natMul, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a * b))
    | .natDiv, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a / b))
    | .natMod, [.scalar (.nat a), .scalar (.nat b)] => pure (.nat (a % b))
    | .natEq, [.scalar (.nat a), .scalar (.nat b)] => pure (.bool (a == b))
    | .natLt, [.scalar (.nat a), .scalar (.nat b)] => pure (.bool (a < b))
    | .natToWord32, [.scalar (.nat n)] => pure (.word32 n.toUInt32)
    | .word32ToNat, [.scalar (.word32 w)] => pure (.nat w.toNat)
    | .fieldToNat, [.scalar (.field f)] => pure (.nat f.val)
    | .natToField, [.scalar (.nat n)] => pure (.field (Goldilocks.reduce n))
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
    | .bytesSlice, [.scalar (.bytes a), .scalar (.word32 start), .scalar (.word32 length)] =>
      if start.toNat + length.toNat ≤ a.size then
        pure (.bytes (a.extract start.toNat (start.toNat + length.toNat)))
      else throw (.primitiveValue primitive)
    | .bytesEq, [.scalar (.bytes a), .scalar (.bytes b)] => pure (.bool (a == b))
    | .blake3, [.scalar (.bytes a)] => pure (.bytes (Ix.Ixby.Blake3.hash a))
    | _, _ => throw (.primitiveType primitive)
  return .scalar result

def validateArg (limits : Limits) (primitive : Primitive) : Value → Except Error Unit
    | .scalar value => value.validate limits
    | .array values =>
      if values.size ≥ 2 ^ 32 then .error (.primitiveValue primitive) else .ok ()
    | .byteBuilder builder =>
      if builder.size > limits.byteArrayBytes then .error (.limit .byteArrayBytes) else .ok ()
    | _ => pure ()

/-- Collection operations preserve aliases and perform checks before allocation.
Only builder append uses a different host representation. -/
def evalUnchecked (limits : Limits) (primitive : Primitive) (args : List Value) :
    Except Error Value := match primitive, args with
    | .arrayEmpty, [] => pure (.array #[])
    | .arrayLength, [.array values] => pure (.scalar (.nat values.size))
    | .arrayGet, [.array values, .scalar (.nat i)] =>
      match values[i]? with
      | some value => pure value
      | none => throw (.primitiveValue primitive)
    | .arraySet, [.array values, .scalar (.nat i), value] =>
      if i < values.size then pure (.array (values.set! i value))
      else throw (.primitiveValue primitive)
    | .arrayPush, [.array values, value] =>
      if values.size + 1 < 2 ^ 32 then pure (.array (values.push value))
      else throw (.primitiveValue primitive)
    | .byteBuilderEmpty, [] => pure (.byteBuilder Builder.empty)
    | .byteBuilderAppend, [.byteBuilder bytes, .scalar (.bytes chunk)] =>
      if bytes.size + chunk.size > limits.byteArrayBytes then
        throw (.limit .byteArrayBytes)
      else pure (.byteBuilder (bytes.append chunk))
    | .byteBuilderFreeze, [.byteBuilder bytes] => pure (.scalar (.bytes bytes.freeze))
    | .byteBuilderLength, [.byteBuilder bytes] => pure (.scalar (.nat bytes.size))
    | .bytesAppend, [.scalar (.bytes a), .scalar (.bytes b)] =>
      if a.size + b.size > limits.byteArrayBytes then throw (.limit .byteArrayBytes)
      else pure (.scalar (.bytes (a ++ b)))
    | _, _ => evalScalarUnchecked primitive args

def validateResult (limits : Limits) (result : Value) : Except Error Value := do
  if let .scalar value := result then value.validate limits
  return result

def eval (limits : Limits) (primitive : Primitive) (args : List Value) :
    Except Error Value := do
  if args.length != primitive.arity then
    throw (.arityMismatch primitive.arity args.length)
  for arg in args do validateArg limits primitive arg
  validateResult limits (← evalUnchecked limits primitive args)

end Compilatrix.Ixby.Runtime.Chunked
