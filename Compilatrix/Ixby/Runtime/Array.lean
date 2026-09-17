import Compilatrix.Ixby.Runtime.Bytes

/-! Source arrays store a native persistent array. A one-field view tag lets
polymorphic array operations distinguish element storage from packed byte
views. There is no interpreted tree or capacity arithmetic. Byte views use
checked slices; byte accumulation freezes before returning a source value. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

private def array (values : Operand) : CodeM Operand := make `Ixby.Runtime.Array [values]
private def bytes (data size : Operand) : CodeM Operand := make `Ixby.Runtime.Bytes [data, size]

private def onArray (value : Operand) (packed native : Array Operand → CodeM Unit) : CodeM Unit :=
  caseCtor value #[(`Ixby.Runtime.Bytes, 2, packed), (`Ixby.Runtime.Array, 1, native),
    (`Ixby.Runtime.WriterBuffer, 1, fun fields => do
      let data ← primitive .byteBuilderFreeze [fields[0]!]
      let size ← primitive .byteBuilderLength [fields[0]!]
      packed #[data, size])]

private def singletonByte (value : Operand) : CodeM Operand := do
  let encoded ← primitive .word32ToBytes [value]
  primitive .bytesSlice [encoded, word 0, word 1]

def arrayFunctions : Array (Name × Nat) := #[
  (`Ixby.Runtime.arrayBytes, 4), (`Ixby.Runtime.toBytes, 1),
  (`Ixby.Runtime.fromList, 2), (`Ixby.Runtime.toList, 3),
  (`Ixby.Runtime.fromBytes, 4), (`Ixby.Runtime.copyArray, 1),
  (`Ixby.Runtime.extract, 4), (`Ixby.Runtime.replicate, 3),
  (`Array.size, 2), (`Array.usize, 2),
  (`Array.emptyWithCapacity, 2), (`Array.mkEmpty, 2),
  (`Array.getInternal, 4), (`Array.getInternalBorrowed, 4),
  (`Array.uget, 4), (`Array.ugetBorrowed, 4),
  (`Array.get!Internal, 4), (`Array.get!InternalBorrowed, 4),
  (`Array.push, 3), (`Array.set!, 4), (`Array.uset, 5),
  (`Array.extract, 4), (`Array.extract._redArg, 3),
  (`Array.append, 3), (`Array.append._redArg, 2),
  (`Array.pop, 2), (`Array.mk, 2), (`Array.toList, 2), (`Array.replicate, 3),
  (`String.toUTF8, 1), (`ByteArray.data, 1), (`Ix.Ixby.Blake3.hash, 1)]

def buildArrays : BuildM Unit := do
  for (name, arity) in arrayFunctions do discard <| reserveFunction name arity
  buildByteBuffers
  let define (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Unit :=
    discard <| defineFunction name arity body
  define `Array.size 2 do
    caseCtor (.local 1) #[
      (`Ixby.Runtime.Bytes, 2, fun fields => ret fields[1]!),
      (`Ixby.Runtime.Array, 1, fun fields => do ret (← primitive .arrayLength [fields[0]!])),
      (`Ixby.Runtime.WriterBuffer, 1, fun fields => do
        ret (← primitive .byteBuilderLength [fields[0]!]))]
  define `Array.usize 2 (tailCall `Array.size [.erased, .local 1])
  for name in #[`Array.emptyWithCapacity, `Array.mkEmpty] do
    define name 2 do ret (← array (← primitive .arrayEmpty []))
  define `Array.getInternal 4 do
    -- Dispatch once, retaining the full Nat guard before byte addressing.
    -- Writer buffers are frozen only after the length and bounds checks.
    caseCtor (.local 1) #[
      (`Ixby.Runtime.Bytes, 2, fun fields => do
        branch (← primitive .natLt [.local 2, fields[1]!])
          (do ret (← primitive .bytesGet [fields[0]!, ← lowWord (.local 2)])) trap),
      (`Ixby.Runtime.Array, 1, fun fields => do
        let size ← primitive .arrayLength [fields[0]!]
        branch (← primitive .natLt [.local 2, size])
          (do ret (← primitive .arrayGet [fields[0]!, .local 2])) trap),
      (`Ixby.Runtime.WriterBuffer, 1, fun fields => do
        let size ← primitive .byteBuilderLength [fields[0]!]
        branch (← primitive .natLt [.local 2, size])
          (do
            let data ← primitive .byteBuilderFreeze [fields[0]!]
            ret (← primitive .bytesGet [data, ← lowWord (.local 2)])) trap)]
  for name in #[`Array.getInternalBorrowed, `Array.uget, `Array.ugetBorrowed] do
    define name 4 (tailCall `Array.getInternal [.erased, .local 1, .local 2, .erased])
  for name in #[`Array.get!Internal, `Array.get!InternalBorrowed] do
    define name 4 do
      let size ← call `Array.size [.erased, .local 2]
      branch (← primitive .natLt [.local 3, size])
        (tailCall `Array.getInternal [.erased, .local 2, .local 3, .erased])
        (ret (.local 1))
  define `Array.push 3 do
    onArray (.local 1)
      (fun _ => do
        let copied ← call `Ixby.Runtime.copyArray [.local 1]
        tailCall `Array.push [.erased, copied, .local 2])
      (fun fields => do ret (← array (← primitive .arrayPush [fields[0]!, .local 2])))
  define `Array.set! 4 do
    let size ← call `Array.size [.erased, .local 1]
    -- Source `set!` returns the identical input on an invalid index.
    branch (← primitive .natLt [.local 2, size])
      (onArray (.local 1)
        (fun _ => do
          let copied ← call `Ixby.Runtime.copyArray [.local 1]
          tailCall `Array.set! [.erased, copied, .local 2, .local 3])
        (fun fields => do ret (← array (← primitive .arraySet [fields[0]!, .local 2, .local 3]))))
      (ret (.local 1))
  define `Array.uset 5 do
    let size ← call `Array.size [.erased, .local 1]
    branch (← primitive .natLt [.local 2, size])
      (tailCall `Array.set! [.erased, .local 1, .local 2, .local 3]) trap
  -- A polymorphic update may change UInt8 elements to arbitrary source values.
  define `Ixby.Runtime.fromBytes 4 do
    branch (← primitive .natLt [.local 1, .local 2])
      (do
        let value ← primitive .bytesGet [.local 0, ← lowWord (.local 1)]
        let next ← primitive .natAdd [.local 1, rawNat 1]
        let acc ← call `Array.push [.erased, .local 3, value]
        tailCall `Ixby.Runtime.fromBytes [.local 0, next, .local 2, acc])
      (ret (.local 3))
  define `Ixby.Runtime.copyArray 1 do
    onArray (.local 0)
      (fun fields => do
        let acc ← call `Array.mkEmpty [.erased, fields[1]!]
        tailCall `Ixby.Runtime.fromBytes [fields[0]!, rawNat 0, fields[1]!, acc])
      (fun _ => ret (.local 0))
  define `Ixby.Runtime.extract 4 do
    branch (← primitive .natLt [.local 1, .local 2])
      (do
        let value ← call `Array.getInternal [.erased, .local 0, .local 1, .erased]
        let acc ← call `Array.push [.erased, .local 3, value]
        let next ← primitive .natAdd [.local 1, rawNat 1]
        tailCall `Ixby.Runtime.extract [.local 0, next, .local 2, acc])
      (ret (.local 3))
  define `Array.extract._redArg 3 do
    let size ← call `Array.size [.erased, .local 0]
    let extractTo (stop : Operand) : CodeM Unit := do
      branch (← primitive .natLt [.local 1, stop])
        (onArray (.local 0)
          (fun fields => do
            let length ← primitive .natSub [stop, .local 1]
            let data ← primitive .bytesSlice [fields[0]!, ← lowWord (.local 1), ← lowWord length]
            ret (← bytes data length))
          (fun _ => do
            let acc ← call `Array.mkEmpty [.erased, rawNat 0]
            tailCall `Ixby.Runtime.extract [.local 0, .local 1, stop, acc]))
        (do ret (← array (← primitive .arrayEmpty [])))
    branch (← primitive .natLt [size, .local 2]) (extractTo size) (extractTo (.local 2))
  define `Array.extract 4 (tailCall `Array.extract._redArg [.local 1, .local 2, .local 3])
  define `Array.append._redArg 2 do
    let leftSize ← call `Array.size [.erased, .local 0]
    let rightSize ← call `Array.size [.erased, .local 1]
    let generic : CodeM Unit := do
      let left ← call `Ixby.Runtime.copyArray [.local 0]
      tailCall `Ixby.Runtime.extract [.local 1, rawNat 0, rightSize, left]
    branch (← primitive .natEq [leftSize, rawNat 0]) (ret (.local 1)) do
      branch (← primitive .natEq [rightSize, rawNat 0]) (ret (.local 0)) do
        onArray (.local 0)
          (fun left => onArray (.local 1)
            (fun right => do
              let data ← call `Ixby.Runtime.appendBytes [left[0]!, right[0]!]
              ret (← bytes data (← primitive .natAdd [leftSize, rightSize])))
            (fun _ => generic))
          (fun _ => generic)
  define `Array.append 3 (tailCall `Array.append._redArg [.local 1, .local 2])
  define `Array.pop 2 do
    let size ← call `Array.size [.erased, .local 1]
    branch (← primitive .natEq [size, rawNat 0]) (ret (.local 1)) do
      let next ← primitive .natSub [size, rawNat 1]
      tailCall `Array.extract._redArg [.local 1, rawNat 0, next]
  define `Ixby.Runtime.fromList 2 do
    caseCtor (.local 0) #[
      (`List.nil, 0, fun _ => ret (.local 1)),
      (`List.cons, 2, fun fields => do
        let next ← call `Array.push [.erased, .local 1, fields[0]!]
        tailCall `Ixby.Runtime.fromList [fields[1]!, next])]
  define `Array.mk 2 do
    let empty ← call `Array.mkEmpty [.erased, rawNat 0]
    tailCall `Ixby.Runtime.fromList [.local 1, empty]
  define `Ixby.Runtime.toList 3 do
    branch (← primitive .natEq [.local 1, rawNat 0]) (ret (.local 2)) do
      let next ← primitive .natSub [.local 1, rawNat 1]
      let value ← call `Array.getInternal [.erased, .local 0, next, .erased]
      let result ← make `List.cons [value, .local 2]
      tailCall `Ixby.Runtime.toList [.local 0, next, result]
  define `Array.toList 2 do
    tailCall `Ixby.Runtime.toList [.local 1, ← call `Array.size [.erased, .local 1],
      ← make `List.nil []]
  define `Ixby.Runtime.replicate 3 do
    branch (← primitive .natEq [.local 0, rawNat 0]) (ret (.local 2)) do
      let next ← primitive .natSub [.local 0, rawNat 1]
      let acc ← call `Array.push [.erased, .local 2, .local 1]
      tailCall `Ixby.Runtime.replicate [next, .local 1, acc]
  define `Array.replicate 3 do
    let empty ← call `Array.mkEmpty [.erased, .local 1]
    tailCall `Ixby.Runtime.replicate [.local 1, .local 2, empty]
  define `Ixby.Runtime.arrayBytes 4 do
    branch (← primitive .natLt [.local 1, .local 2])
      (do
        let value ← primitive .arrayGet [.local 0, .local 1]
        let builder ← primitive .byteBuilderAppend [.local 3, ← singletonByte value]
        let next ← primitive .natAdd [.local 1, rawNat 1]
        tailCall `Ixby.Runtime.arrayBytes [.local 0, next, .local 2, builder])
      (do ret (← primitive .byteBuilderFreeze [.local 3]))
  define `Ixby.Runtime.toBytes 1 do
    onArray (.local 0) (fun fields => ret fields[0]!)
      (fun fields => do
        let size ← primitive .arrayLength [fields[0]!]
        let builder ← primitive .byteBuilderEmpty []
        tailCall `Ixby.Runtime.arrayBytes [fields[0]!, rawNat 0, size, builder])
  for name in #[`String.toUTF8, `ByteArray.data] do define name 1 (ret (.local 0))
  define `Ix.Ixby.Blake3.hash 1 do
    let data ← call `Ixby.Runtime.toBytes [.local 0]
    ret (← bytes (← primitive .blake3 [data]) (rawNat 32))

end Compilatrix.Ixby.Runtime
