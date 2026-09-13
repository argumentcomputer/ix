import Compilatrix.Ixby.Runtime.Bytes

/-! Immutable arrays use a binary tree with a logical length and a power-of-two
capacity. Byte inputs and fixed keys have a packed representation. Both forms
are ordinary constructor values and use only the existing Ixby instruction set. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

private def emptyTree : CodeM Operand := make `Ixby.Runtime.Empty []
private def node (left right : Operand) : CodeM Operand := make `Ixby.Runtime.Node [left, right]
private def leaf (value : Operand) : CodeM Operand := make `Ixby.Runtime.Leaf [value]
private def array (size capacity tree : Operand) : CodeM Operand :=
  make `Ixby.Runtime.Array [size, capacity, tree]
private def bytes (data size : Operand) : CodeM Operand := make `Ixby.Runtime.Bytes [data, size]

private def onArray (value : Operand) (packed tree rope : Array Operand → CodeM Unit) : CodeM Unit :=
  caseCtor value #[(`Ixby.Runtime.Bytes, 2, packed), (`Ixby.Runtime.Array, 3, tree),
    (`Ixby.Runtime.Rope, 4, rope)]

private def singletonByte (value : Operand) : CodeM Operand := do
  let low ← lowWord value
  let encoded ← primitive .word32ToBytes [low]
  primitive .bytesSlice [encoded, word 0, word 1]

def arrayFunctions : Array (Name × Nat) := #[
  (`Ixby.Runtime.treeGet, 3), (`Ixby.Runtime.treeSet, 4),
  (`Ixby.Runtime.treeBytes, 3), (`Ixby.Runtime.toBytes, 1),
  (`Ixby.Runtime.fromList, 2), (`Ixby.Runtime.toList, 3),
  (`Ixby.Runtime.fromBytes, 4), (`Ixby.Runtime.copyArray, 1),
  (`Ixby.Runtime.extract, 4),
  (`Ixby.Runtime.replicate, 3),
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
  buildByteTrees
  let define (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Unit :=
    discard <| defineFunction name arity body
  define `Ixby.Runtime.treeGet 3 do
    branch (← primitive .natEq [.local 1, rawNat 1])
      (do ret (← project (.local 0) 0)) do
        let half ← primitive .natDiv [.local 1, rawNat 2]
        branch (← primitive .natLt [.local 2, half])
          (do tailCall `Ixby.Runtime.treeGet [← project (.local 0) 0, half, .local 2])
          (do tailCall `Ixby.Runtime.treeGet [← project (.local 0) 1, half,
                ← primitive .natSub [.local 2, half]])
  define `Ixby.Runtime.treeSet 4 do
    branch (← primitive .natEq [.local 1, rawNat 1])
      (do ret (← leaf (.local 3))) do
        let half ← primitive .natDiv [.local 1, rawNat 2]
        let rest (left right : Operand) : CodeM Unit := do
          branch (← primitive .natLt [.local 2, half])
            (do let updated ← call `Ixby.Runtime.treeSet [left, half, .local 2, .local 3]
                ret (← node updated right))
            (do let index ← primitive .natSub [.local 2, half]
                let updated ← call `Ixby.Runtime.treeSet [right, half, index, .local 3]
                ret (← node left updated))
        caseCtor (.local 0) #[
          (`Ixby.Runtime.Empty, 0, fun _ => do let empty ← emptyTree; rest empty empty),
          (`Ixby.Runtime.Node, 2, fun fields => rest fields[0]! fields[1]!)]
  define `Array.size 2 do
    onArray (.local 1) (fun fields => ret fields[1]!) (fun fields => ret fields[0]!)
      (fun fields => ret fields[0]!)
  define `Array.usize 2 do
    tailCall `USize.ofNat [← call `Array.size [.erased, .local 1]]
  for name in #[`Array.emptyWithCapacity, `Array.mkEmpty] do
    define name 2 do ret (← array (← number 0) (rawNat 1) (← emptyTree))
  define `Array.getInternal 4 do
    let size ← call `Array.size [.erased, .local 1]
    let valid ← call `Nat.decLt [.local 2, size]
    branch valid
      (onArray (.local 1)
        (fun fields => do
          let index ← lowWord (.local 2)
          tailCall `Ixby.Runtime.fromWord [← primitive .bytesGet [fields[0]!, index]])
        (fun fields => do
          tailCall `Ixby.Runtime.treeGet [fields[2]!, fields[1]!, ← project (.local 2) 0])
        (fun _ => tailCall `Ixby.Runtime.byteGet [.local 1, .local 2]))
      trap
  for name in #[`Array.getInternalBorrowed, `Array.uget, `Array.ugetBorrowed] do
    define name 4 (tailCall `Array.getInternal [.erased, .local 1, .local 2, .erased])
  for name in #[`Array.get!Internal, `Array.get!InternalBorrowed] do
    define name 4 do
      let size ← call `Array.size [.erased, .local 2]
      branch (← call `Nat.decLt [.local 3, size])
        (tailCall `Array.getInternal [.erased, .local 2, .local 3, .erased])
        (ret (.local 1))
  define `Array.push 3 do
    let size ← call `Array.size [.erased, .local 1]
    let next ← call `Nat.add [size, ← number 1]
    onArray (.local 1)
      (fun _ => do
        let copied ← call `Ixby.Runtime.copyArray [.local 1]
        tailCall `Array.push [.erased, copied, .local 2])
      (fun fields => do
        let index ← project size 0
        let write (root capacity : Operand) : CodeM Unit := do
          let updated ← call `Ixby.Runtime.treeSet [root, capacity, index, .local 2]
          ret (← array next capacity updated)
        branch (← primitive .natLt [index, fields[1]!])
          (write fields[2]! fields[1]!)
          (do let capacity ← primitive .natAdd [fields[1]!, fields[1]!]
              let root ← node fields[2]! (← emptyTree)
              write root capacity))
      (fun _ => do
        let copied ← call `Ixby.Runtime.copyArray [.local 1]
        tailCall `Array.push [.erased, copied, .local 2])
  define `Array.set! 4 do
    let size ← call `Array.size [.erased, .local 1]
    branch (← call `Nat.decLt [.local 2, size])
      (onArray (.local 1)
        (fun _ => do
          let copied ← call `Ixby.Runtime.copyArray [.local 1]
          tailCall `Array.set! [.erased, copied, .local 2, .local 3])
        (fun fields => do
          let root ← call `Ixby.Runtime.treeSet [fields[2]!, fields[1]!,
            ← project (.local 2) 0, .local 3]
          ret (← array size fields[1]! root))
        (fun _ => do
          let copied ← call `Ixby.Runtime.copyArray [.local 1]
          tailCall `Array.set! [.erased, copied, .local 2, .local 3]))
      (ret (.local 1))
  define `Array.uset 5 do
    let size ← call `Array.size [.erased, .local 1]
    branch (← call `Nat.decLt [.local 2, size])
      (tailCall `Array.set! [.erased, .local 1, .local 2, .local 3]) trap
  -- Packed storage must be widened before a polymorphic update. A source
  -- `Array.map` can change the element type, including to constructors/PAPs.
  define `Ixby.Runtime.fromBytes 4 do
    branch (← call `Nat.decLt [.local 1, .local 2])
      (do
        let low ← lowWord (.local 1)
        let value ← call `Ixby.Runtime.fromWord [← primitive .bytesGet [.local 0, low]]
        let next ← call `Nat.add [.local 1, ← number 1]
        let acc ← call `Array.push [.erased, .local 3, value]
        tailCall `Ixby.Runtime.fromBytes [.local 0, next, .local 2, acc])
      (ret (.local 3))
  define `Ixby.Runtime.copyArray 1 do
    onArray (.local 0)
      (fun fields => do
        let acc ← call `Array.mkEmpty [.erased, fields[1]!]
        tailCall `Ixby.Runtime.fromBytes [fields[0]!, ← number 0, fields[1]!, acc])
      (fun _ => ret (.local 0))
      (fun fields => do
        let acc ← call `Array.mkEmpty [.erased, fields[0]!]
        tailCall `Ixby.Runtime.extract [.local 0, ← number 0, fields[0]!, acc])
  define `Ixby.Runtime.extract 4 do
    branch (← call `Nat.decLt [.local 1, .local 2])
      (do
        let value ← call `Array.getInternal [.erased, .local 0, .local 1, .erased]
        let acc ← call `Array.push [.erased, .local 3, value]
        let next ← call `Nat.add [.local 1, ← number 1]
        tailCall `Ixby.Runtime.extract [.local 0, next, .local 2, acc])
      (ret (.local 3))
  define `Array.extract._redArg 3 do
    let size ← call `Array.size [.erased, .local 0]
    let extractTo (stop : Operand) : CodeM Unit := do
      branch (← call `Nat.decLt [.local 1, stop])
        (onArray (.local 0)
          (fun fields => do
            let length ← call `Nat.sub [stop, .local 1]
            let data ← primitive .bytesSlice [fields[0]!, ← lowWord (.local 1), ← lowWord length]
            ret (← bytes data length))
          (fun _ => do
            let acc ← call `Array.mkEmpty [.erased, ← number 0]
            tailCall `Ixby.Runtime.extract [.local 0, .local 1, stop, acc])
          (fun _ => do
            let acc ← call `Array.mkEmpty [.erased, ← number 0]
            tailCall `Ixby.Runtime.extract [.local 0, .local 1, stop, acc]))
        (do ret (← packedBytes #[]))
    branch (← call `Nat.decLt [size, .local 2]) (extractTo size) (extractTo (.local 2))
  define `Array.extract 4 (tailCall `Array.extract._redArg [.local 1, .local 2, .local 3])
  define `Array.append._redArg 2 do
    let leftSize ← call `Array.size [.erased, .local 0]
    let rightSize ← call `Array.size [.erased, .local 1]
    let generic : CodeM Unit := do
      let left ← call `Ixby.Runtime.copyArray [.local 0]
      tailCall `Ixby.Runtime.extract [.local 1, ← number 0, rightSize, left]
    let byteLeft : CodeM Unit :=
      onArray (.local 1)
        (fun _ => tailCall `Ixby.Runtime.byteAppend [.local 0, .local 1])
        (fun _ => generic)
        (fun _ => tailCall `Ixby.Runtime.byteAppend [.local 0, .local 1])
    branch (← call `Nat.decEq [leftSize, ← number 0]) (ret (.local 1)) do
      branch (← call `Nat.decEq [rightSize, ← number 0]) (ret (.local 0)) do
        onArray (.local 0) (fun _ => byteLeft) (fun _ => generic) (fun _ => byteLeft)
  define `Array.append 3 (tailCall `Array.append._redArg [.local 1, .local 2])
  define `Array.pop 2 do
    let size ← call `Array.size [.erased, .local 1]
    branch (← call `Nat.decEq [size, ← number 0]) (ret (.local 1)) do
      let next ← call `Nat.sub [size, ← number 1]
      onArray (.local 1)
        (fun fields => do
          let data ← primitive .bytesSlice [fields[0]!, word 0, ← lowWord next]
          ret (← bytes data next))
        (fun fields => do ret (← array next fields[1]! fields[2]!))
        (fun _ => do tailCall `Array.extract._redArg [.local 1, ← number 0, next])
  define `Ixby.Runtime.fromList 2 do
    caseCtor (.local 0) #[
      (`List.nil, 0, fun _ => ret (.local 1)),
      (`List.cons, 2, fun fields => do
        let next ← call `Array.push [.erased, .local 1, fields[0]!]
        tailCall `Ixby.Runtime.fromList [fields[1]!, next])]
  define `Array.mk 2 do
    let empty ← call `Array.mkEmpty [.erased, ← number 0]
    tailCall `Ixby.Runtime.fromList [.local 1, empty]
  define `Ixby.Runtime.toList 3 do
    branch (← call `Nat.decEq [.local 1, ← number 0]) (ret (.local 2)) do
      let next ← call `Nat.sub [.local 1, ← number 1]
      let value ← call `Array.getInternal [.erased, .local 0, next, .erased]
      let result ← make `List.cons [value, .local 2]
      tailCall `Ixby.Runtime.toList [.local 0, next, result]
  define `Array.toList 2 do
    tailCall `Ixby.Runtime.toList [.local 1, ← call `Array.size [.erased, .local 1],
      ← make `List.nil []]
  define `Ixby.Runtime.replicate 3 do
    let n ← project (.local 0) 0
    branch (← primitive .natLt [.local 1, n])
      (do let capacity ← primitive .natAdd [.local 1, .local 1]
          let tree ← node (.local 2) (.local 2)
          tailCall `Ixby.Runtime.replicate [.local 0, capacity, tree])
      (do ret (← array (.local 0) (.local 1) (.local 2)))
  define `Array.replicate 3 do
    branch (← call `Nat.decEq [.local 1, ← number 0])
      (tailCall `Array.mkEmpty [.erased, .local 1])
      (do tailCall `Ixby.Runtime.replicate [.local 1, rawNat 1, ← leaf (.local 2)])
  define `Ixby.Runtime.treeBytes 3 do
    branch (← primitive .natEq [.local 2, rawNat 0])
      (ret (.literal (.bytes #[]))) do
        branch (← primitive .natEq [.local 1, rawNat 1])
          (do ret (← singletonByte (← project (.local 0) 0))) do
            let half ← primitive .natDiv [.local 1, rawNat 2]
            let left ← project (.local 0) 0
            branch (← primitive .natLt [half, .local 2])
              (do let left ← call `Ixby.Runtime.treeBytes [left, half, half]
                  let right ← project (.local 0) 1
                  let count ← primitive .natSub [.local 2, half]
                  let right ← call `Ixby.Runtime.treeBytes [right, half, count]
                  ret (← primitive .bytesAppend [left, right]))
              (tailCall `Ixby.Runtime.treeBytes [left, half, .local 2])
  define `Ixby.Runtime.toBytes 1 do
    onArray (.local 0) (fun fields => ret fields[0]!)
      (fun fields => do tailCall `Ixby.Runtime.treeBytes [fields[2]!, fields[1]!, ← project fields[0]! 0])
      (fun _ => tailCall `Ixby.Runtime.byteFlatten [.local 0])
  for name in #[`String.toUTF8, `ByteArray.data] do define name 1 (ret (.local 0))
  define `Ix.Ixby.Blake3.hash 1 do
    let data ← call `Ixby.Runtime.toBytes [.local 0]
    ret (← bytes (← primitive .blake3 [data]) (← number 32))

end Compilatrix.Ixby.Runtime
