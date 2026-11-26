/-! # Idiomatic Pure-Lean 7-Round BLAKE3 Block Compression (`Blake3Block`)

Zero-annotation, idiomatic pure Lean 4 implementation of the 7-round BLAKE3
compression function written using standard infix operators (`+`, `^^^`, `>>>`,
`<<<`, `|||`) and modular helper functions (`rotr16`, `rotr12`, `rotr8`,
`rotr7`, `g`, `round`, `permute`, `compressLoop`).

* **Zero forbidden constructs**: pure total Lean 4 only — structural recursion
  (`termination_by structural`), zero `sorry`, zero `partial`, zero `unsafe`,
  zero `native_decide`, zero `Ix.Circuit` annotations required.
* **Official test vector**: `#guard` verifies that compressing the all-zero
  block with `blockLen = 0` and `flags = 11` (`CHUNK_START | CHUNK_END | ROOT`)
  produces the official `BLAKE3("")` digest
  `af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262`.
* Designed for the M1/M3a head-to-head benchmark comparing `--typed` vs
  `--typed --inline-fuse` against hand-written `Aiur.Library.Blake3`. -/

set_option autoImplicit false

namespace Blake3Block

/-- 8-word (32-byte) BLAKE3 chaining value / digest. -/
structure Digest where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  deriving BEq, DecidableEq, Repr

/-- Output of one BLAKE3 quarter-round `g`. -/
structure Quarter where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving BEq, DecidableEq, Repr

/-- 16-word internal compression state. -/
structure State16 where
  v0 : UInt32
  v1 : UInt32
  v2 : UInt32
  v3 : UInt32
  v4 : UInt32
  v5 : UInt32
  v6 : UInt32
  v7 : UInt32
  v8 : UInt32
  v9 : UInt32
  v10 : UInt32
  v11 : UInt32
  v12 : UInt32
  v13 : UInt32
  v14 : UInt32
  v15 : UInt32
  deriving BEq, DecidableEq, Repr

/-- 16-word (64-byte) BLAKE3 message block. -/
structure Block16 where
  m0 : UInt32
  m1 : UInt32
  m2 : UInt32
  m3 : UInt32
  m4 : UInt32
  m5 : UInt32
  m6 : UInt32
  m7 : UInt32
  m8 : UInt32
  m9 : UInt32
  m10 : UInt32
  m11 : UInt32
  m12 : UInt32
  m13 : UInt32
  m14 : UInt32
  m15 : UInt32
  deriving BEq, DecidableEq, Repr

/-- Idiomatic bit-rotation helpers using standard infix `>>>`, `<<<`, `|||`. -/
def rotr16 (x : UInt32) : UInt32 := (x >>> 16) ||| (x <<< 16)
def rotr12 (x : UInt32) : UInt32 := (x >>> 12) ||| (x <<< 20)
def rotr8  (x : UInt32) : UInt32 := (x >>> 8)  ||| (x <<< 24)
def rotr7  (x : UInt32) : UInt32 := (x >>> 7)  ||| (x <<< 25)

/-- Idiomatic BLAKE3 quarter-round `G` using standard infix `+`, `^^^`, and `rotr*`. -/
def g (a b c d mx my : UInt32) : Quarter :=
  let a1 := a + b + mx
  let d1 := rotr16 (d ^^^ a1)
  let c1 := c + d1
  let b1 := rotr12 (b ^^^ c1)
  let a2 := a1 + b1 + my
  let d2 := rotr8 (d1 ^^^ a2)
  let c2 := c1 + d2
  let b2 := rotr7 (b1 ^^^ c2)
  { a := a2, b := b2, c := c2, d := d2 }

/-- One full BLAKE3 round (4 column quarter-rounds + 4 diagonal quarter-rounds). -/
def round (s : State16) (m : Block16) : State16 :=
  let c0 := g s.v0 s.v4 s.v8  s.v12 m.m0  m.m1
  let c1 := g s.v1 s.v5 s.v9  s.v13 m.m2  m.m3
  let c2 := g s.v2 s.v6 s.v10 s.v14 m.m4  m.m5
  let c3 := g s.v3 s.v7 s.v11 s.v15 m.m6  m.m7
  let d0 := g c0.a c1.b c2.c  c3.d  m.m8  m.m9
  let d1 := g c1.a c2.b c3.c  c0.d  m.m10 m.m11
  let d2 := g c2.a c3.b c0.c  c1.d  m.m12 m.m13
  let d3 := g c3.a c0.b c1.c  c2.d  m.m14 m.m15
  { v0 := d0.a, v1 := d1.a, v2 := d2.a, v3 := d3.a
    v4 := d3.b, v5 := d0.b, v6 := d1.b, v7 := d2.b
    v8 := d2.c, v9 := d3.c, v10 := d0.c, v11 := d1.c
    v12 := d1.d, v13 := d2.d, v14 := d3.d, v15 := d0.d }

/-- BLAKE3 message-schedule permutation between rounds. -/
def permute (m : Block16) : Block16 :=
  { m0 := m.m2,  m1 := m.m6,  m2 := m.m3,  m3 := m.m10
    m4 := m.m7,  m5 := m.m0,  m6 := m.m4,  m7 := m.m13
    m8 := m.m1,  m9 := m.m11, m10 := m.m12, m11 := m.m5
    m12 := m.m9, m13 := m.m14, m14 := m.m15, m15 := m.m8 }

/-- Countdown-recursive 7-round BLAKE3 compression loop (`rem = 6` runs rounds `0..6`
and XORs the two halves of the final state to produce the 8-word digest). -/
def compressLoop (rem : Nat) (s : State16) (m : Block16) : Digest :=
  let s1 := round s m
  match rem with
  | 0 =>
    { w0 := s1.v0 ^^^ s1.v8,  w1 := s1.v1 ^^^ s1.v9
      w2 := s1.v2 ^^^ s1.v10, w3 := s1.v3 ^^^ s1.v11
      w4 := s1.v4 ^^^ s1.v12, w5 := s1.v5 ^^^ s1.v13
      w6 := s1.v6 ^^^ s1.v14, w7 := s1.v7 ^^^ s1.v15 }
  | k + 1 =>
    compressLoop k s1 (permute m)
termination_by structural rem

/-- Standard BLAKE3 IV. -/
def iv : Digest :=
  { w0 := 0x6A09E667, w1 := 0xBB67AE85, w2 := 0x3C6EF372, w3 := 0xA54FF53A
    w4 := 0x510E527F, w5 := 0x9B05688C, w6 := 0x1F83D9AB, w7 := 0x5BE0CD19 }

/-- Single-block BLAKE3 compression with `counter = 0`. -/
def compress (cv : Digest) (m : Block16) (blockLen flags : UInt32) : Digest :=
  let k := iv
  let st : State16 :=
    { v0 := cv.w0, v1 := cv.w1, v2 := cv.w2, v3 := cv.w3
      v4 := cv.w4, v5 := cv.w5, v6 := cv.w6, v7 := cv.w7
      v8 := k.w0,  v9 := k.w1,  v10 := k.w2, v11 := k.w3
      v12 := 0,    v13 := 0,    v14 := blockLen, v15 := flags }
  compressLoop 6 st m

/-- Benchmark entrypoint: compresses a single 64-byte block whose first word is
`m0` (remaining 15 words zero) with `blockLen = len` and `flags = 11`
(`CHUNK_START | CHUNK_END | ROOT`), returning the full 8-word `Digest`.
On `(0, 0)` this produces the exact official `BLAKE3("")` hash! -/
def entry (m0 len : Nat) : Digest :=
  let block : Block16 :=
    { m0 := UInt32.ofNat m0, m1 := 0, m2 := 0, m3 := 0
      m4 := 0, m5 := 0, m6 := 0, m7 := 0
      m8 := 0, m9 := 0, m10 := 0, m11 := 0
      m12 := 0, m13 := 0, m14 := 0, m15 := 0 }
  compress iv block (UInt32.ofNat len) 11

/-! ## Official BLAKE3 Test Vectors (`#guard`) -/

private def officialEmptyBlake3 : Digest :=
  { w0 := 0xb94913af, w1 := 0xa6a1f9f5, w2 := 0xea4d40a0, w3 := 0x49c9dc36
    w4 := 0xc925cb9b, w5 := 0xb712c1ad, w6 := 0xca939acc, w7 := 0x62321fe4 }

-- Official BLAKE3("") test vector:
-- af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
#guard entry 0 0 == officialEmptyBlake3

-- Non-trivial 3-byte input "abc" (0x00636261 little-endian, len = 3):
-- Official BLAKE3("abc") = 6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85
private def officialAbcBlake3 : Digest :=
  { w0 := 0xacb33764, w1 := 0x33514638, w2 := 0x753bb6ff, w3 := 0xb58d3a27
    w4 := 0x4658c548, w5 := 0x03db795d, w6 := 0x6c9c35fd, w7 := 0x859dbdd5 }

#guard entry 0x00636261 3 == officialAbcBlake3

end Blake3Block
