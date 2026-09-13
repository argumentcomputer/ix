import Compilatrix.Ixby.Runtime.Number

/-! Balanced concatenation of byte blocks. A rope retains ordinary immutable
Ixby values; no host buffer or new evaluator operation is introduced. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

def byteFunctions : Array (Name × Nat) := #[
  (`Ixby.Runtime.byteHeight, 1), (`Ixby.Runtime.byteNode, 2),
  (`Ixby.Runtime.byteBalance, 2), (`Ixby.Runtime.byteAppend, 2),
  (`Ixby.Runtime.byteGet, 2), (`Ixby.Runtime.byteFlatten, 1)]

def buildByteTrees : BuildM Unit := do
  for (name, arity) in byteFunctions do discard <| reserveFunction name arity
  let define (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Unit :=
    discard <| defineFunction name arity body
  define `Ixby.Runtime.byteHeight 1 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Bytes, 2, fun _ => ret (word 0)),
      (`Ixby.Runtime.Rope, 4, fun fields => ret fields[1]!)]
  define `Ixby.Runtime.byteNode 2 do
    let leftSize ← call `Array.size [.erased, .local 0]
    let rightSize ← call `Array.size [.erased, .local 1]
    let size ← call `Nat.add [leftSize, rightSize]
    let left ← call `Ixby.Runtime.byteHeight [.local 0]
    let right ← call `Ixby.Runtime.byteHeight [.local 1]
    let finish (height : Operand) : CodeM Unit := do
      let height ← primitive .word32Add [height, word 1]
      ret (← make `Ixby.Runtime.Rope [size, height, .local 0, .local 1])
    branch (← primitive .word32Lt [left, right]) (finish right) (finish left)
  define `Ixby.Runtime.byteBalance 2 do
    let left ← call `Ixby.Runtime.byteHeight [.local 0]
    let right ← call `Ixby.Runtime.byteHeight [.local 1]
    let leftHeavy ← primitive .word32Lt [← primitive .word32Add [right, word 1], left]
    branch leftHeavy
      (do
        let a ← project (.local 0) 2
        let b ← project (.local 0) 3
        let ha ← call `Ixby.Runtime.byteHeight [a]
        let hb ← call `Ixby.Runtime.byteHeight [b]
        branch (← primitive .word32Lt [ha, hb])
          (do
            let a ← call `Ixby.Runtime.byteNode [a, ← project b 2]
            let b ← call `Ixby.Runtime.byteNode [← project b 3, .local 1]
            tailCall `Ixby.Runtime.byteNode [a, b])
          (do
            let b ← call `Ixby.Runtime.byteNode [b, .local 1]
            tailCall `Ixby.Runtime.byteNode [a, b]))
      (do
        let rightHeavy ← primitive .word32Lt [← primitive .word32Add [left, word 1], right]
        branch rightHeavy
          (do
            let a ← project (.local 1) 2
            let b ← project (.local 1) 3
            let ha ← call `Ixby.Runtime.byteHeight [a]
            let hb ← call `Ixby.Runtime.byteHeight [b]
            branch (← primitive .word32Lt [hb, ha])
              (do
                let b ← call `Ixby.Runtime.byteNode [← project a 3, b]
                let a ← call `Ixby.Runtime.byteNode [.local 0, ← project a 2]
                tailCall `Ixby.Runtime.byteNode [a, b])
              (do
                let a ← call `Ixby.Runtime.byteNode [.local 0, a]
                tailCall `Ixby.Runtime.byteNode [a, b]))
          (tailCall `Ixby.Runtime.byteNode [.local 0, .local 1]))
  -- Array.append has already removed empty inputs. Heights count tree levels,
  -- independently of the number of bytes in a leaf.
  define `Ixby.Runtime.byteAppend 2 do
    let left ← call `Ixby.Runtime.byteHeight [.local 0]
    let right ← call `Ixby.Runtime.byteHeight [.local 1]
    let join : CodeM Unit := do
      let leftHeavy ← primitive .word32Lt [← primitive .word32Add [right, word 1], left]
      branch leftHeavy
        (do
          let a ← project (.local 0) 2
          let b ← call `Ixby.Runtime.byteAppend [← project (.local 0) 3, .local 1]
          tailCall `Ixby.Runtime.byteBalance [a, b])
        (do
          let rightHeavy ← primitive .word32Lt [← primitive .word32Add [left, word 1], right]
          branch rightHeavy
            (do
              let a ← call `Ixby.Runtime.byteAppend [.local 0, ← project (.local 1) 2]
              let b ← project (.local 1) 3
              tailCall `Ixby.Runtime.byteBalance [a, b])
            (tailCall `Ixby.Runtime.byteNode [.local 0, .local 1]))
    branch (← primitive .word32Eq [left, word 0])
      (branch (← primitive .word32Eq [right, word 0])
        (do
          let size ← call `Nat.add [← project (.local 0) 1, ← project (.local 1) 1]
          -- Coalescing small wire writes avoids one tree level per tiny field.
          branch (← call `Nat.decLt [size, ← number 1025])
            (do
              let data ← primitive .bytesAppend [← project (.local 0) 0, ← project (.local 1) 0]
              ret (← make `Ixby.Runtime.Bytes [data, size]))
            join)
        join)
      join
  define `Ixby.Runtime.byteGet 2 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Bytes, 2, fun fields => do
        let byte ← primitive .bytesGet [fields[0]!, ← lowWord (.local 1)]
        tailCall `Ixby.Runtime.fromWord [byte]),
      (`Ixby.Runtime.Rope, 4, fun fields => do
        let leftSize ← call `Array.size [.erased, fields[2]!]
        branch (← call `Nat.decLt [.local 1, leftSize])
          (tailCall `Ixby.Runtime.byteGet [fields[2]!, .local 1])
          (do tailCall `Ixby.Runtime.byteGet [fields[3]!, ← call `Nat.sub [.local 1, leftSize]]))]
  define `Ixby.Runtime.byteFlatten 1 do
    caseCtor (.local 0) #[
      (`Ixby.Runtime.Bytes, 2, fun fields => ret fields[0]!),
      (`Ixby.Runtime.Rope, 4, fun fields => do
        let left ← call `Ixby.Runtime.byteFlatten [fields[2]!]
        let right ← call `Ixby.Runtime.byteFlatten [fields[3]!]
        ret (← primitive .bytesAppend [left, right]))]

end Compilatrix.Ixby.Runtime
