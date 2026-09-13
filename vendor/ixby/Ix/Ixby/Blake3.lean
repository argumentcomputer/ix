module
public import Std

/-! Pure reference BLAKE3, unkeyed, 32-byte output only. No FFI, witness hints,
keyed hashing, or XOF interface is part of this definition. The compression
schedule and tree flags follow the pinned `blake3` 1.8.4 portable implementation;
the existing Aiur gadget lives in `Ix/IxVM/Blake3.lean`. Conformance tests are
not a proof of collision resistance or of the gadget's constraint soundness. -/

public section
@[expose] section

namespace Ix.Ixby.Blake3

namespace Internal

def iv : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def permutation : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

def mix (s : Array UInt32) (a b c d : Nat) (x y : UInt32) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]! + x)
  s := s.set! d (rotr (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!)
  s := s.set! b (rotr (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]! + y)
  s := s.set! d (rotr (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!)
  return s.set! b (rotr (s[b]! ^^^ s[c]!) 7)

def round (s m : Array UInt32) : Array UInt32 :=
  let s := mix s 0 4 8 12 m[0]! m[1]!
  let s := mix s 1 5 9 13 m[2]! m[3]!
  let s := mix s 2 6 10 14 m[4]! m[5]!
  let s := mix s 3 7 11 15 m[6]! m[7]!
  let s := mix s 0 5 10 15 m[8]! m[9]!
  let s := mix s 1 6 11 12 m[10]! m[11]!
  let s := mix s 2 7 8 13 m[12]! m[13]!
  mix s 3 4 9 14 m[14]! m[15]!

def compress (cv block : Array UInt32) (counter : Nat)
    (length flags : UInt32) : Array UInt32 := Id.run do
  let mut s := cv ++ #[iv[0]!, iv[1]!, iv[2]!, iv[3]!,
    counter.toUInt32, (counter >>> 32).toUInt32, length, flags]
  let mut m := block
  for _ in [0:7] do
    s := round s m
    m := permutation.map (fun i => m[i]!)
  return (Array.range 8).map (fun i => s[i]! ^^^ s[i + 8]!)

structure Output where
  cv : Array UInt32
  block : Array UInt32
  counter : Nat
  length : UInt32
  flags : UInt32

def Output.chainingValue (o : Output) : Array UInt32 :=
  compress o.cv o.block o.counter o.length o.flags

def chunk (bytes : Array UInt8) (index : Nat) : Output := Id.run do
  let blocks := max 1 ((bytes.size + 63) / 64)
  let mut cv := iv
  for b in [0:blocks - 1] do
    let words := (Array.range 16).map fun i =>
      (List.range 4).foldl (fun acc j =>
        acc ||| ((bytes[b * 64 + i * 4 + j]?.getD 0).toUInt32 <<< (8 * j).toUInt32)) 0
    cv := compress cv words index 64 (if b == 0 then 1 else 0)
  let last := blocks - 1
  let words := (Array.range 16).map fun i =>
    (List.range 4).foldl (fun acc j =>
      acc ||| ((bytes[last * 64 + i * 4 + j]?.getD 0).toUInt32 <<< (8 * j).toUInt32)) 0
  return ⟨cv, words, index, (bytes.size - last * 64).toUInt32,
    2 ||| (if last == 0 then 1 else 0)⟩

def parent (left right : Array UInt32) : Output :=
  ⟨iv, left ++ right, 0, 64, 4⟩

/-- Pair adjacent nodes at each tree level, retaining an unpaired final node.
This gives BLAKE3's left-full tree and preserves the final compression input
so ROOT is applied to the root output, not to an already-compressed CV. -/
def layer : List Output → List Output
  | a :: b :: rest => parent a.chainingValue b.chainingValue :: layer rest
  | rest => rest

def root : Nat → List Output → Output
  | 0, nodes => nodes.headD (chunk #[] 0)
  | _, [] => chunk #[] 0
  | _, [node] => node
  | fuel + 1, nodes => root fuel (layer nodes)

end Internal

open Internal

/-- Hashing work is proportional to the byte input, not one constant-cost
machine row. Callers enforce their byte/work admission limits. -/
def hash (bytes : Array UInt8) : Array UInt8 := Id.run do
  let count := max 1 ((bytes.size + 1023) / 1024)
  let nodes := (List.range count).map fun i =>
    chunk (bytes.extract (i * 1024) (min bytes.size ((i + 1) * 1024))) i
  let o := root (count.log2 + 1) nodes
  let words := compress o.cv o.block 0 o.length (o.flags ||| 8)
  return (Array.range 32).map fun i => (words[i / 4]! >>> (8 * (i % 4)).toUInt32).toUInt8

@[simp] theorem hash_size (bytes : Array UInt8) : (hash bytes).size = 32 := by
  simp [hash]

end Ix.Ixby.Blake3
