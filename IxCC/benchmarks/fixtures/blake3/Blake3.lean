/-! K4 `blake3`: standalone total unkeyed 32-byte BLAKE3 over `ByteArray` and
`Array UInt32`, hashing the canonical official test-vector byte pattern
`buf[i] = i % 251` of length `n`. -/

namespace Blake3Bench

def iv : Array UInt32 := #[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
]

def sched0 : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def sched1 : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def sched2 : Array Nat := #[3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1]
def sched3 : Array Nat := #[10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6]
def sched4 : Array Nat := #[12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4]
def sched5 : Array Nat := #[9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7]
def sched6 : Array Nat := #[11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13]

@[inline] def rotr32 (w c : UInt32) : UInt32 :=
  (w >>> c) ||| (w <<< (32 - c))

@[inline] def g (st : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := st[a]!
  let vb := st[b]!
  let vc := st[c]!
  let vd := st[d]!
  let va := va + vb + mx
  let vd := rotr32 (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr32 (vb ^^^ vc) 12
  let va := va + vb + my
  let vd := rotr32 (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr32 (vb ^^^ vc) 7
  (((st.set! a va).set! b vb).set! c vc).set! d vd

def round (st msg : Array UInt32) (s : Array Nat) : Array UInt32 :=
  let st := g st 0 4 8 12 msg[s[0]!]! msg[s[1]!]!
  let st := g st 1 5 9 13 msg[s[2]!]! msg[s[3]!]!
  let st := g st 2 6 10 14 msg[s[4]!]! msg[s[5]!]!
  let st := g st 3 7 11 15 msg[s[6]!]! msg[s[7]!]!
  let st := g st 0 5 10 15 msg[s[8]!]! msg[s[9]!]!
  let st := g st 1 6 11 12 msg[s[10]!]! msg[s[11]!]!
  let st := g st 2 7 8 13 msg[s[12]!]! msg[s[13]!]!
  g st 3 4 9 14 msg[s[14]!]! msg[s[15]!]!

def compress (cv msg : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) : Array UInt32 :=
  let st : Array UInt32 := #[
    cv[0]!, cv[1]!, cv[2]!, cv[3]!, cv[4]!, cv[5]!, cv[6]!, cv[7]!,
    iv[0]!, iv[1]!, iv[2]!, iv[3]!,
    counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags
  ]
  let st := round st msg sched0
  let st := round st msg sched1
  let st := round st msg sched2
  let st := round st msg sched3
  let st := round st msg sched4
  let st := round st msg sched5
  let st := round st msg sched6
  #[
    st[0]! ^^^ st[8]!,  st[1]! ^^^ st[9]!,  st[2]! ^^^ st[10]!, st[3]! ^^^ st[11]!,
    st[4]! ^^^ st[12]!, st[5]! ^^^ st[13]!, st[6]! ^^^ st[14]!, st[7]! ^^^ st[15]!
  ]

@[inline] def getByteOrZero (buf : ByteArray) (offset len idx : Nat) : UInt32 :=
  if idx < len then (buf.get! (offset + idx)).toUInt32 else 0

def blockWords (buf : ByteArray) (offset len : Nat) : Array UInt32 := Id.run do
  let mut out := Array.emptyWithCapacity 16
  for w in [0:16] do
    let base := w * 4
    let b0 := getByteOrZero buf offset len base
    let b1 := getByteOrZero buf offset len (base + 1)
    let b2 := getByteOrZero buf offset len (base + 2)
    let b3 := getByteOrZero buf offset len (base + 3)
    out := out.push (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  return out

def cvBytes (cv : Array UInt32) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:8] do
    let w := cv[i]!
    out := out.push w.toUInt8
    out := out.push (w >>> 8).toUInt8
    out := out.push (w >>> 16).toUInt8
    out := out.push (w >>> 24).toUInt8
  return out

structure Output where
  cv : Array UInt32
  block : Array UInt32
  blockLen : UInt32
  counter : UInt64
  flags : UInt32

def Output.chainingValue (o : Output) : Array UInt32 :=
  compress o.cv o.block o.counter o.blockLen o.flags

def Output.rootHash (o : Output) : ByteArray :=
  cvBytes (compress o.cv o.block 0 o.blockLen (o.flags ||| 8))

def chunkLoop (buf : ByteArray) (counter : UInt64) :
    Nat → Nat → Nat → Array UInt32 → Bool → Output
  | 0, offset, rem, cv, isStart =>
    { cv, block := blockWords buf offset rem, blockLen := rem.toUInt32,
      counter, flags := (if isStart then 1 else 0) ||| 2 }
  | fuel + 1, offset, rem, cv, isStart =>
    if rem ≤ 64 then
      { cv, block := blockWords buf offset rem, blockLen := rem.toUInt32,
        counter, flags := (if isStart then 1 else 0) ||| 2 }
    else
      let next := compress cv (blockWords buf offset 64) counter 64 (if isStart then 1 else 0)
      chunkLoop buf counter fuel (offset + 64) (rem - 64) next false

def chunkOutput (buf : ByteArray) (offset len : Nat) (counter : UInt64) : Output :=
  chunkLoop buf counter 16 offset len iv true

def parentOutput (left right : Array UInt32) : Output :=
  let block : Array UInt32 := #[
    left[0]!, left[1]!, left[2]!, left[3]!, left[4]!, left[5]!, left[6]!, left[7]!,
    right[0]!, right[1]!, right[2]!, right[3]!, right[4]!, right[5]!, right[6]!, right[7]!
  ]
  { cv := iv, block, blockLen := 64, counter := 0, flags := 4 }

def largestPow2Lt (n : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, p => p
    | fuel + 1, p => if p * 2 < n then go fuel (p * 2) else p
  go 64 1

def subtree (buf : ByteArray) : Nat → Nat → Nat → Nat → Output
  | 0, offset, len, counter => chunkOutput buf offset len counter.toUInt64
  | fuel + 1, offset, len, counter =>
    if len ≤ 1024 then chunkOutput buf offset len counter.toUInt64
    else
      let split := largestPow2Lt len
      let left := subtree buf fuel offset split counter
      let right := subtree buf fuel (offset + split) (len - split) (counter + split / 1024)
      parentOutput left.chainingValue right.chainingValue

def mkInput (n : Nat) : ByteArray := Id.run do
  let mut buf := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    buf := buf.push (i % 251).toUInt8
  return buf

def hashInput (n : Nat) : ByteArray :=
  let buf := mkInput n
  (subtree buf 64 0 n 0).rootHash

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

def toHex (bs : ByteArray) : String := Id.run do
  let mut chars : Array Char := Array.emptyWithCapacity (bs.size * 2)
  for i in [0:bs.size] do
    let b := (bs.get! i).toNat
    chars := chars.push (hexDigit (b / 16))
    chars := chars.push (hexDigit (b % 16))
  return String.ofList chars.toList

end Blake3Bench

/-- The pure benchmark entry: 32-byte BLAKE3 digest of the canonical `n`-byte test pattern. -/
def entry (n : Nat) : ByteArray := Blake3Bench.hashInput n

def main : List String → IO UInt32
  | [n] => do
    IO.println (Blake3Bench.toHex (entry n.toNat!))
    pure 0
  | _ => do
    IO.eprintln "usage: blake3 N"
    pure 1
