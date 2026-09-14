/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Transcript

/-! Total, unkeyed, 32-byte BLAKE3 for the native transcript and PCS.
Words and compression blocks have checked dimensions. The canonical tree
splits at the largest power of two strictly below the input byte length.
The native input bound is separate from the total mathematical function.
-/

namespace Aiur.NativeAIR.Blake3

abbrev CV := Vector UInt32 8
abbrev Block := Vector UInt32 16
abbrev Digest := Vector UInt8 32

def iv : CV := #v[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def schedules : Vector (Vector (Fin 16) 16) 7 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
  #v[3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
  #v[10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
  #v[12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
  #v[9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
  #v[11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13]]

def rotateRight (word count : UInt32) : UInt32 :=
  (word >>> count) ||| (word <<< (32 - count))

def mix (a b c d x y : UInt32) : Vector UInt32 4 :=
  let a := a + b + x
  let d := rotateRight (d ^^^ a) 16
  let c := c + d
  let b := rotateRight (b ^^^ c) 12
  let a := a + b + y
  let d := rotateRight (d ^^^ a) 8
  let c := c + d
  let b := rotateRight (b ^^^ c) 7
  #v[a, b, c, d]

def g (state : Block) (a b c d : Fin 16) (x y : UInt32) : Block :=
  let words := mix state[a] state[b] state[c] state[d] x y
  (((state.set a words[0]).set b words[1]).set c words[2]).set d words[3]

def round (state message : Block) (schedule : Vector (Fin 16) 16) : Block :=
  let state := g state 0 4 8 12 message[schedule[0]] message[schedule[1]]
  let state := g state 1 5 9 13 message[schedule[2]] message[schedule[3]]
  let state := g state 2 6 10 14 message[schedule[4]] message[schedule[5]]
  let state := g state 3 7 11 15 message[schedule[6]] message[schedule[7]]
  let state := g state 0 5 10 15 message[schedule[8]] message[schedule[9]]
  let state := g state 1 6 11 12 message[schedule[10]] message[schedule[11]]
  let state := g state 2 7 8 13 message[schedule[12]] message[schedule[13]]
  g state 3 4 9 14 message[schedule[14]] message[schedule[15]]

def initialWords (cv : CV) (counter : UInt64) (blockLen flags : UInt32) : Block :=
  #v[cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
    iv[0], iv[1], iv[2], iv[3], counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]

def compress (cv : CV) (message : Block) (counter : UInt64) (blockLen flags : UInt32) : CV :=
  let state := schedules.foldl (fun state schedule => round state message schedule)
    (initialWords cv counter blockLen flags)
  Vector.ofFn fun index => state[index.val] ^^^ state[index.val + 8]

def wordBytes (word : UInt32) : Vector UInt8 4 :=
  Vector.ofFn fun index => (word.toNat / 256^index.val).toUInt8

def bytesWord (bytes : Vector UInt8 4) : UInt32 :=
  UInt32.ofNat (Challenger.littleEndian bytes.toList)

/-- Zero padding is part of block framing, including the empty input block. -/
def blockWords (bytes : List UInt8) : Block :=
  let input := bytes.toArray
  Vector.ofFn fun word => bytesWord (Vector.ofFn fun byte => input[word.val * 4 + byte.val]?.getD 0)

def cvBytes (cv : CV) : Digest :=
  Vector.ofFn fun index => (wordBytes cv[index.val / 4])[index.val % 4]

structure Output where
  cv : CV
  block : Block
  blockLen : UInt32
  counter : UInt64
  flags : UInt32
  deriving DecidableEq, Repr

def Output.chainingValue (output : Output) : CV :=
  compress output.cv output.block output.counter output.blockLen output.flags

def Output.rootHash (output : Output) : Digest :=
  cvBytes (compress output.cv output.block 0 output.blockLen (output.flags ||| 8))

/-- A full last block receives CHUNK_END; it is never followed by an empty block. -/
def chunkLoop (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8) : Output :=
  if h : input.length ≤ 64 then
    ⟨cv, blockWords input, input.length.toUInt32, counter, (if start then 1 else 0) ||| 2⟩
  else
    let next := compress cv (blockWords (input.take 64)) counter 64 (if start then 1 else 0)
    chunkLoop counter next false (input.drop 64)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

def chunkOutput (counter : UInt64) (input : List UInt8) : Output :=
  chunkLoop counter iv true input

/-- This internal BLAKE3 parent is distinct from hashing a PCS Merkle pair. -/
def parentOutput (left right : CV) : Output :=
  ⟨iv, left ++ right, 64, 0, 4⟩

def leftLen (size : Nat) : Nat := 2 ^ (size - 1).log2

theorem leftLen_positive (size : Nat) : 0 < leftLen size := Nat.two_pow_pos _

theorem leftLen_lt {size : Nat} (large : 1024 < size) : leftLen size < size := by
  have := Nat.log2_self_le (n := size - 1) (by omega)
  unfold leftLen
  omega

def subtree (counter : Nat) (input : List UInt8) : Output :=
  if _h : input.length ≤ 1024 then chunkOutput counter.toUInt64 input
  else
    let split := leftLen input.length
    let left := subtree counter (input.take split)
    let right := subtree (counter + split / 1024) (input.drop split)
    parentOutput left.chainingValue right.chainingValue
termination_by input.length
decreasing_by
  · have := leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := leftLen_positive input.length
    simp only [List.length_drop]; omega

def digest (input : List UInt8) : Digest := (subtree 0 input).rootHash

def hash : Challenger.Hash32 :=
  fun input =>
    let bytes := digest input
    fun index => bytes[index]

/-- Native BLAKE3 supports at most 2^64 - 1 input bytes. -/
def NativeInput (input : List UInt8) : Prop := input.length < 2^64

def replay (fuel : Nat) (key : KeyCodec.Key) (proof : ProofCodec.Data)
    (claims : List (List G)) : Option Transcript.Replay := Transcript.replay hash fuel key proof claims

def verifyArithmetic (fuel : Nat) (key : KeyCodec.Key) (proof : ProofCodec.Data)
    (claims : List (List G)) (rows : List ProofShape.Row) : Option Transcript.Replay :=
  Transcript.verifyArithmetic hash fuel key proof claims rows

end Aiur.NativeAIR.Blake3
