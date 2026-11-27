import Ix.Compile.CircuitContract

/-! # Production Binary Wire Deserializers & BLAKE3/Goldilocks Primitives (`StarkWire`)

Pure total Lean 4 foundation for the single-source `CompressWrap` / `CompressGL`
Protocol `v6` Multi-STARK verifier over real Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$.

## Architecture
1. **Monomorphic unboxed ADTs (`ShapeInfer`-unboxed, 0 `Obj` fallback)**:
   `ByteList`, `BitList`, `NatList`, `U64Bytes`, `U64List`, `U64ListList`, `U64List3`,
   `Digest32`, `DigestBytes`, `DigestBytesList`, `MerkleCapList`, `ExtGl`, `ExtGlList`,
   `ExtGlListList`, `OpenedRound`, `ExtGlList3`, `Digest32Words`, plus monomorphic
   binary parse-result structs (`ParseU8`, `ParseNat`, `ParseU64`, `ParseExt`, ...).
2. **Exact Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$ & Cubic Extension
   $\mathbb{F}_{p_{\mathrm{GL}}^3} = \mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$**:
   * Base-field ops annotated with `@[circuit_intrinsic "field.{add,sub,mul,neg,inv,div,is_zero,eq}"]`
     so `FieldLower` lowers them directly to zero-lookup native `Field` arithmetic
     on Goldilocks (breaking the 56-bit ceiling!) AND `--emulate-goldilocks` lowers
     the exact same source to `Goldilocks.Emulated` on BN254 / BLS12-381.
   * All 64-bit Goldilocks constants (`glPrime`, `glInv2`, `glGen32`, `glW2Inv`,
     `glW3Inv`) are assembled from `< 2^32` words so `TypedLower` never sees an
     oversized `Nat` literal `≥ 2^56`.
   * 6-mul Karatsuba `extMul`, adjugate-norm `extInvDirect`, and Tier-2 `checked def extInv`
     with a zero-`sorry`, zero-Mathlib kernel-checked uniqueness proof directly over
     $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$.
3. **Full Pure-Lean Multi-Block / Multi-Chunk Standard & Keyed BLAKE3 (`StarkHash`)**:
   * Peephole-fusible 7-round `UInt32` compression (`blake3Compress`) with full 64-bit
     chunk counters, exact Merkle tree folding (`blake3HashBytesWithCv`), `@[circuit_intrinsic "blake3.hash"]`
     entry `blake3HashBytes`, and exact Protocol `v6` `derive_key_context` CVs
     (`v6MerkleLeafCv`, `v6MerkleCompressCv`, `v6TranscriptBatchCv`).
   * Exact `"ix/compress-wrap/v1\0"` (20 B) + `key_digest` (32 B) + `claims_digest` (32 B)
     84-byte statement preimage & little-endian `packDigest`, matching
     `MultiStark/Modules/CompressWrap.lean` and `crates/stark-verifier/src/compress_wrap.rs`
     byte-for-byte.
4. **Exact Production Binary Wire Deserializers & Canonical Encoders**:
   * Faithful byte-for-byte ports of `SystemDeserialize.lean` (`readSystem`),
     `StarkVerifier.lean` (`readClaims`), and `ProofDeserialize.lean` (`readBatchProof`),
     enforcing every magic/version tag, canonical `< p_GL` check, DAG acyclicity check,
     `OptIdx` monotonicity check, and trailing-byte rejection.

## Proof & Compilation Hygiene
* ONLY `import Ix.Compile.CircuitContract` (zero `MultiStark` / `Aiur` / `IxCC` / `Mathlib`).
* Zero `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `partial`, `unsafe`,
  `@[extern]`, or `@[implemented_by]`; strictly structural recursion throughout.
* 100% Ixon content-address invariant under `open scoped Ix.Circuit`.
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace StarkWire

/-! ## Section 1: Monomorphic Unboxed Core ADTs -/

/-- Canonical byte stream (`Bytes::Stream = Lists::List<UInt8::U8>`). Each byte is `< 256`. -/
inductive ByteList where
  | nil
  | cons (byte : Nat) (rest : ByteList)
  deriving BEq, DecidableEq, Repr

/-- LSB-first bit list (`Lists::List<Field>`). -/
inductive BitList where
  | nil
  | cons (bit : Nat) (rest : BitList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of lists of LSB-first bits (query indices). -/
inductive BitListList where
  | nil
  | cons (head : BitList) (tail : BitListList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of natural numbers (node IDs, heights, active flags, log degrees). -/
inductive NatList where
  | nil
  | cons (head : Nat) (tail : NatList)
  deriving BEq, DecidableEq, Repr

/-- Flat 8-byte little-endian 64-bit word (`UInt64::U64 = [UInt8::U8; 8]`). -/
structure U64Bytes where
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  b5 : Nat
  b6 : Nat
  b7 : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of 8-byte words (`Lists::List<UInt64::U64>`). -/
inductive U64List where
  | nil
  | cons (head : U64Bytes) (tail : U64List)
  deriving BEq, DecidableEq, Repr

/-- List of rows / claims (`Lists::List<Lists::List<UInt64::U64>>`). -/
inductive U64ListList where
  | nil
  | cons (head : U64List) (tail : U64ListList)
  deriving BEq, DecidableEq, Repr

/-- Per-query opened matrix rows (`Lists::List<Lists::List<Lists::List<UInt64::U64>>>`). -/
inductive U64List3 where
  | nil
  | cons (head : U64ListList) (tail : U64List3)
  deriving BEq, DecidableEq, Repr

/-- 8-word (32-byte) flat unboxed `UInt32` BLAKE3 chaining value / digest. -/
structure Digest32 where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  deriving BEq, DecidableEq, Repr

/-- Packed 8-word little-endian statement digest (`Blake3::pack_digest : [Field; 8]`). -/
structure Digest32Words where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  w4 : Nat
  w5 : Nat
  w6 : Nat
  w7 : Nat
  deriving BEq, DecidableEq, Repr

/-- 32-byte digest as four 8-byte words (`ProofDeserialize::Digest = [UInt64::U64; 4]`). -/
structure DigestBytes where
  d0 : U64Bytes
  d1 : U64Bytes
  d2 : U64Bytes
  d3 : U64Bytes
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of 32-byte digests (`MerkleCap` and MMCS sibling paths). -/
inductive DigestBytesList where
  | nil
  | cons (head : DigestBytes) (tail : DigestBytesList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of Merkle caps (`Lists::List<ProofDeserialize::MerkleCap>`). -/
inductive MerkleCapList where
  | nil
  | cons (head : DigestBytesList) (tail : MerkleCapList)
  deriving BEq, DecidableEq, Repr

/-- Cubic extension element `c0 + c1·X + c2·X² ∈ F_{p_GL}[X]/(X³ - X - 1)`. -/
structure ExtGl where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of cubic extension elements (`Lists::List<Ext>`). -/
inductive ExtGlList where
  | nil
  | cons (head : ExtGl) (tail : ExtGlList)
  deriving BEq, DecidableEq, Repr

/-- 2D list of cubic extension elements (`Lists::List<Lists::List<Ext>>`). -/
inductive ExtGlListList where
  | nil
  | cons (head : ExtGlList) (tail : ExtGlListList)
  deriving BEq, DecidableEq, Repr

/-- 3D list of cubic extension elements (`OpenedRound` & commit-phase siblings). -/
inductive OpenedRound where
  | nil
  | cons (head : ExtGlListList) (tail : OpenedRound)
  deriving BEq, DecidableEq, Repr

/-! ### Basic Monomorphic List Utilities -/

@[circuit_noinline]
def byteListLen : ByteList → Nat
  | .nil => 0
  | .cons _ rest => 1 + byteListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def byteListAppend (xs ys : ByteList) : ByteList :=
  match xs with
  | .nil => ys
  | .cons b rest => .cons b (byteListAppend rest ys)
termination_by structural xs

@[circuit_noinline]
def byteListRevOnto (xs acc : ByteList) : ByteList :=
  match xs with
  | .nil => acc
  | .cons b rest => byteListRevOnto rest (.cons b acc)
termination_by structural xs

@[circuit_noinline]
def natListLen : NatList → Nat
  | .nil => 0
  | .cons _ rest => 1 + natListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def bitListLen : BitList → Nat
  | .nil => 0
  | .cons _ rest => 1 + bitListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def bitListRevOnto (xs acc : BitList) : BitList :=
  match xs with
  | .nil => acc
  | .cons b rest => bitListRevOnto rest (.cons b acc)
termination_by structural xs

@[circuit_noinline]
def bitListDrop (n : Nat) (xs : BitList) : BitList :=
  match n with
  | 0 => xs
  | n' + 1 =>
    match xs with
    | .nil => .nil
    | .cons _ rest => bitListDrop n' rest
termination_by structural n

@[circuit_noinline]
def bitsToNum : BitList → Nat
  | .nil => 0
  | .cons b rest =>
    let r := bitsToNum rest
    b + r + r
termination_by structural xs => xs

@[circuit_noinline]
def u64ListLen : U64List → Nat
  | .nil => 0
  | .cons _ rest => 1 + u64ListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def u64ListAppend (xs ys : U64List) : U64List :=
  match xs with
  | .nil => ys
  | .cons x rest => .cons x (u64ListAppend rest ys)
termination_by structural xs

@[circuit_noinline]
def u64ListListLen : U64ListList → Nat
  | .nil => 0
  | .cons _ rest => 1 + u64ListListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def u64ListListAppend (xs ys : U64ListList) : U64ListList :=
  match xs with
  | .nil => ys
  | .cons x rest => .cons x (u64ListListAppend rest ys)
termination_by structural xs

@[circuit_noinline]
def u64List3Len : U64List3 → Nat
  | .nil => 0
  | .cons _ rest => 1 + u64List3Len rest
termination_by structural xs => xs

@[circuit_noinline]
def digestBytesListLen : DigestBytesList → Nat
  | .nil => 0
  | .cons _ rest => 1 + digestBytesListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def merkleCapListLen : MerkleCapList → Nat
  | .nil => 0
  | .cons _ rest => 1 + merkleCapListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def extGlListLen : ExtGlList → Nat
  | .nil => 0
  | .cons _ rest => 1 + extGlListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def extGlListAppend (xs ys : ExtGlList) : ExtGlList :=
  match xs with
  | .nil => ys
  | .cons x rest => .cons x (extGlListAppend rest ys)
termination_by structural xs

@[circuit_noinline]
def extGlListListLen : ExtGlListList → Nat
  | .nil => 0
  | .cons _ rest => 1 + extGlListListLen rest
termination_by structural xs => xs

@[circuit_noinline]
def openedRoundLen : OpenedRound → Nat
  | .nil => 0
  | .cons _ rest => 1 + openedRoundLen rest
termination_by structural xs => xs

@[circuit_noinline]
def bitListListLen : BitListList → Nat
  | .nil => 0
  | .cons _ rest => 1 + bitListListLen rest
termination_by structural xs => xs

/-! ## Section 2: Exact Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$ & Cubic Extension `ExtGl` -/

/-- `2^k` as a `Nat` (structural recursion; prevents Lean/ANF from constant-folding
`glPrime` into a `≥ 2^56` literal before `FieldLower` lowers `@[circuit_intrinsic "field.*"]`). -/
def pow2Nat : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2Nat k
termination_by structural k => k

/-- Exact Goldilocks prime $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1 = 18446744069414584321$,
assembled via structural `pow2Nat 32` so `TypedLower` never sees a literal `≥ 2^56`. -/
def glPrime : Nat :=
  (pow2Nat 32 - 1) * pow2Nat 32 + 1

/-- Pure-`Nat` structural-fuel extended Euclidean worker modulo `p`. -/
def glEgcdStep (p : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, t0, _ => t0
  | fuel + 1, r0, r1, t0, t1 =>
    match r1 with
    | 0 => if r0 == 1 then t0 else 0
    | r1' + 1 =>
      let d := r1' + 1
      let q := r0 / d
      let r2 := r0 % d
      let qt1 := (q * t1) % p
      let t2 := (t0 + p - qt1) % p
      glEgcdStep p fuel d r2 t1 t2
termination_by structural fuel => fuel

/-- Native Goldilocks base-field addition (`(a + b) mod p_GL`). -/
@[circuit_noinline, circuit_intrinsic "field.add"]
def glAdd (a b : Nat) : Nat :=
  (a + b) % glPrime

/-- Native Goldilocks base-field subtraction (`(a - b) mod p_GL`). -/
@[circuit_noinline, circuit_intrinsic "field.sub"]
def glSub (a b : Nat) : Nat :=
  (a + glPrime - (b % glPrime)) % glPrime

/-- Native Goldilocks base-field multiplication (`(a * b) mod p_GL`). -/
@[circuit_noinline, circuit_intrinsic "field.mul"]
def glMul (a b : Nat) : Nat :=
  (a * b) % glPrime

/-- Native Goldilocks base-field negation (`(-a) mod p_GL`). -/
@[circuit_noinline, circuit_intrinsic "field.neg"]
def glNeg (a : Nat) : Nat :=
  if a % glPrime == 0 then 0 else glPrime - (a % glPrime)

/-- Native Goldilocks total base-field inverse (`a⁻¹ mod p_GL`, with `0⁻¹ = 0`). -/
@[circuit_noinline, circuit_intrinsic "field.inv"]
def glInv (a : Nat) : Nat :=
  if a % glPrime == 0 then 0 else glEgcdStep glPrime 131 glPrime (a % glPrime) 0 1

/-- Native Goldilocks total base-field division (`a / b mod p_GL`, with `a / 0 = 0`). -/
@[circuit_noinline, circuit_intrinsic "field.div"]
def glDiv (a b : Nat) : Nat :=
  glMul a (glInv b)

/-- Native Goldilocks zero indicator (`1` iff `a ≡ 0 (mod p_GL)`, else `0`). -/
@[circuit_noinline, circuit_intrinsic "field.is_zero"]
def glIsZero (a : Nat) : Nat :=
  if a % glPrime == 0 then 1 else 0

/-- Native Goldilocks equality indicator (`1` iff `a ≡ b (mod p_GL)`, else `0`). -/
@[circuit_noinline, circuit_intrinsic "field.eq"]
def glEq (a b : Nat) : Nat :=
  if a % glPrime == b % glPrime then 1 else 0

/-- Assemble a 64-bit Goldilocks element from two `< 2^32` halves `lo + hi * 2^32`
using purely `@[circuit_intrinsic "field.*"]` ops (zero literals `≥ 2^56`). -/
@[circuit_inline]
def glOfU32Pair (lo hi : Nat) : Nat :=
  glAdd lo (glMul hi 4294967296)

/-- Exact Goldilocks `2⁻¹ = (p_GL + 1) / 2 = 9223372034707292161`. -/
@[circuit_inline]
def glInv2 : Nat :=
  glOfU32Pair 2147483649 2147483647

/-- Exact Goldilocks primitive `2^32`-th root of unity (`1753635133440165772`). -/
@[circuit_inline]
def glGen32 : Nat :=
  glOfU32Pair 3663234956 408299996

/-- Exact Goldilocks inverse of primitive 4th root `two_adic_gen(2)⁻¹ = 18446462594437873665`. -/
@[circuit_inline]
def glW2Inv : Nat :=
  glOfU32Pair 1 4294901759

/-- Exact Goldilocks inverse of primitive 8th root `two_adic_gen(3)⁻¹ = 1099511627520`. -/
@[circuit_inline]
def glW3Inv : Nat :=
  glOfU32Pair 4294967040 255

/-- Plonky3 / MultiStark Goldilocks multiplicative coset shift (`7`). -/
@[circuit_inline]
def glCosetShift : Nat := 7

/-- Repeated squaring `base^(2^k) mod p_GL` (structural countdown). -/
@[circuit_noinline]
def glExpPow2 (base : Nat) : Nat → Nat
  | 0 => base
  | k + 1 => glExpPow2 (glMul base base) k
termination_by structural k => k

/-- Primitive `2^bits`-th root of unity in Goldilocks (`StarkVerifier::two_adic_gen`). -/
@[circuit_inline]
def glTwoAdicGen (bits : Nat) : Nat :=
  if bits == 0 then 1 else glExpPow2 glGen32 (32 - bits)

/-- Conditional Goldilocks multiplication avoiding join-point splitting. -/
@[circuit_noinline]
def glCondMul (bit base half : Nat) : Nat :=
  if bit == 0 then half else glMul base half

/-- Binary exponentiation `base^(bitsToNum bits) mod p_GL` (`Pcs::exp_by_bits`). -/
@[circuit_noinline]
def glExpByBits (base : Nat) : BitList → Nat
  | .nil => 1
  | .cons b rest =>
    let half := glExpByBits (glMul base base) rest
    glCondMul b base half
termination_by structural bits => bits

/-- `2^k` in Goldilocks (`StarkVerifier::pow2`). -/
@[circuit_noinline]
def glPow2 : Nat → Nat
  | 0 => 1
  | k + 1 =>
    let half := glPow2 k
    glAdd half half
termination_by structural k => k

/-- Zero 8-byte word. -/
@[circuit_inline]
def u64Zero : U64Bytes :=
  { b0 := 0, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }

/-- Canonical check `x < p_GL = 2^64 - 2^32 + 1` on an 8-byte little-endian word
(`Goldilocks::gl_lt_p`). Every intermediate sum is `≤ 1020 << 2^56`. -/
@[circuit_inline]
def glLtPBytes (x : U64Bytes) : Nat :=
  let hiSum := x.b4 + x.b5 + x.b6 + x.b7
  let loSum := x.b0 + x.b1 + x.b2 + x.b3
  if hiSum == 1020 then
    if loSum == 0 then 1 else 0
  else 1

/-- Decode an 8-byte little-endian word to a Goldilocks field element (`Goldilocks::gl_val`)
using `< 2^32` byte recombination followed by native `glOfU32Pair`. -/
@[circuit_inline]
def glValBytes (x : U64Bytes) : Nat :=
  let lo := x.b0 + 256 * x.b1 + 65536 * x.b2 + 16777216 * x.b3
  let hi := x.b4 + 256 * x.b5 + 65536 * x.b6 + 16777216 * x.b7
  glOfU32Pair lo hi

/-- Encode a `< 2^32` natural number into an 8-byte little-endian `U64Bytes`
(high 4 bytes zero; stays strictly `< 2^32 << 2^56` for `TypedLower`). -/
@[circuit_noinline]
def u64BytesOfU32 (v : Nat) : U64Bytes :=
  let b0 := v % 256; let q1 := v / 256
  let b1 := q1 % 256; let q2 := q1 / 256
  let b2 := q2 % 256; let b3 := q2 / 256
  { b0 := b0, b1 := b1, b2 := b2, b3 := b3 % 256, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }

/-- Encode any `< 2^64` natural number (including full Goldilocks elements) into 8 LE bytes. -/
def u64BytesOfNat (v : Nat) : U64Bytes :=
  let b0 := v % 256; let q1 := v / 256
  let b1 := q1 % 256; let q2 := q1 / 256
  let b2 := q2 % 256; let q3 := q2 / 256
  let b3 := q3 % 256; let q4 := q3 / 256
  let b4 := q4 % 256; let q5 := q4 / 256
  let b5 := q5 % 256; let q6 := q5 / 256
  let b6 := q6 % 256; let b7 := (q6 / 256) % 256
  { b0 := b0, b1 := b1, b2 := b2, b3 := b3, b4 := b4, b5 := b5, b6 := b6, b7 := b7 }

/-- Exact equality on `U64Bytes` (`1` iff all 8 bytes match). -/
@[circuit_inline]
def u64BytesEq (a b : U64Bytes) : Nat :=
  if a.b0 == b.b0 && a.b1 == b.b1 && a.b2 == b.b2 && a.b3 == b.b3 &&
     a.b4 == b.b4 && a.b5 == b.b5 && a.b6 == b.b6 && a.b7 == b.b7 then 1 else 0

/-- Unsigned 64-bit `≤` comparison on little-endian `U64Bytes` (`StarkVerifier::bytes8_le`). -/
@[circuit_noinline]
def u64BytesLe (x y : U64Bytes) : Nat :=
  if x.b7 != y.b7 then if x.b7 < y.b7 then 1 else 0
  else if x.b6 != y.b6 then if x.b6 < y.b6 then 1 else 0
  else if x.b5 != y.b5 then if x.b5 < y.b5 then 1 else 0
  else if x.b4 != y.b4 then if x.b4 < y.b4 then 1 else 0
  else if x.b3 != y.b3 then if x.b3 < y.b3 then 1 else 0
  else if x.b2 != y.b2 then if x.b2 < y.b2 then 1 else 0
  else if x.b1 != y.b1 then if x.b1 < y.b1 then 1 else 0
  else if x.b0 ≤ y.b0 then 1 else 0

/-- Prepend 8 bytes of `x` onto `tail` (`StarkVerifier::b8_onto`). -/
@[circuit_inline]
def u64BytesOnto (x : U64Bytes) (tail : ByteList) : ByteList :=
  .cons x.b0 (.cons x.b1 (.cons x.b2 (.cons x.b3
    (.cons x.b4 (.cons x.b5 (.cons x.b6 (.cons x.b7 tail)))))))

/-- Prepend all words in `xs` onto `tail` (`StarkVerifier::limbs_onto`). -/
@[circuit_noinline]
def u64ListOnto (xs : U64List) (tail : ByteList) : ByteList :=
  match xs with
  | .nil => tail
  | .cons x rest => u64BytesOnto x (u64ListOnto rest tail)
termination_by structural xs

/-! ### Exact Cubic Extension `ExtGl` ($\mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$) -/

@[circuit_inline]
def extZero : ExtGl := { c0 := 0, c1 := 0, c2 := 0 }

@[circuit_inline]
def extOne : ExtGl := { c0 := 1, c1 := 0, c2 := 0 }

@[circuit_inline]
def extOfBase (x : Nat) : ExtGl := { c0 := x, c1 := 0, c2 := 0 }

@[circuit_inline]
def extCanonical (a : ExtGl) : Bool :=
  decide (a.c0 < glPrime) && decide (a.c1 < glPrime) && decide (a.c2 < glPrime)

@[circuit_inline]
def extIsZero (a : ExtGl) : Nat :=
  if glIsZero a.c0 == 1 then
    if glIsZero a.c1 == 1 then glIsZero a.c2 else 0
  else 0

@[circuit_inline]
def extEq (a b : ExtGl) : Nat :=
  if glEq a.c0 b.c0 == 1 then
    if glEq a.c1 b.c1 == 1 then glEq a.c2 b.c2 else 0
  else 0

@[circuit_noinline]
def extAdd (a b : ExtGl) : ExtGl :=
  { c0 := glAdd a.c0 b.c0
    c1 := glAdd a.c1 b.c1
    c2 := glAdd a.c2 b.c2 }

@[circuit_noinline]
def extSub (a b : ExtGl) : ExtGl :=
  { c0 := glSub a.c0 b.c0
    c1 := glSub a.c1 b.c1
    c2 := glSub a.c2 b.c2 }

@[circuit_inline]
def extNeg (a : ExtGl) : ExtGl :=
  { c0 := glNeg a.c0
    c1 := glNeg a.c1
    c2 := glNeg a.c2 }

@[circuit_noinline]
def extScale (a : ExtGl) (k : Nat) : ExtGl :=
  { c0 := glMul a.c0 k
    c1 := glMul a.c1 k
    c2 := glMul a.c2 k }

/-- Exact 6-mul Karatsuba multiplication in $\mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$
matching `Goldilocks::eg_mul` line-for-line. -/
@[circuit_noinline]
def extMul (a b : ExtGl) : ExtGl :=
  let v0 := glMul a.c0 b.c0
  let v1 := glMul a.c1 b.c1
  let v2 := glMul a.c2 b.c2
  let m01 := glSub (glSub (glMul (glAdd a.c0 a.c1) (glAdd b.c0 b.c1)) v0) v1
  let m02 := glSub (glSub (glMul (glAdd a.c0 a.c2) (glAdd b.c0 b.c2)) v0) v2
  let m12 := glSub (glSub (glMul (glAdd a.c1 a.c2) (glAdd b.c1 b.c2)) v1) v2
  { c0 := glAdd v0 m12
    c1 := glAdd (glAdd m01 m12) v2
    c2 := glAdd (glAdd m02 v1) v2 }

/-- Squaring in `ExtGl`. -/
@[circuit_noinline]
def extSquare (a : ExtGl) : ExtGl :=
  extMul a a

/-- Repeated squaring `a^(2^k)` in `ExtGl` (`StarkVerifier::ext_exp_pow2`). -/
@[circuit_noinline]
def extExpPow2 (a : ExtGl) : Nat → ExtGl
  | 0 => a
  | k + 1 => extExpPow2 (extSquare a) k
termination_by structural k => k

/-- Adjugate in $\mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$ (`Goldilocks::eg_inverse`). -/
@[circuit_noinline]
def extAdj (a : ExtGl) : ExtGl :=
  let s := glAdd a.c0 a.c2
  let d0 := glSub (glMul s s) (glMul a.c1 (glAdd a.c1 a.c2))
  let d1 := glSub (glMul a.c2 a.c2) (glMul a.c0 a.c1)
  let d2 := glSub (glMul a.c1 a.c1) (glMul a.c2 s)
  { c0 := d0, c1 := d1, c2 := d2 }

/-- Cubic norm `N(a) = a0·d0 + a2·d1 + a1·d2 mod p_GL`. -/
@[circuit_noinline]
def extNorm (a : ExtGl) : Nat :=
  let d := extAdj a
  glAdd (glAdd (glMul a.c0 d.c0) (glMul a.c2 d.c1)) (glMul a.c1 d.c2)

/-- Direct cubic extension inverse via adjugate and native `glInv` (`Goldilocks::eg_inverse`).
Lowers directly to native zero-lookup `Field` ops under `--field-lower` with zero guesses! -/
@[circuit_noinline]
def extInvDirect (a : ExtGl) : ExtGl :=
  if extIsZero a == 1 then extZero
  else
    let d := extAdj a
    let norm := glAdd (glAdd (glMul a.c0 d.c0) (glMul a.c2 d.c1)) (glMul a.c1 d.c2)
    let ninv := glInv norm
    extScale d ninv

/-! ### Kernel-Checked Uniqueness Proof for `checked def extInv` over Real Goldilocks $p_{\mathrm{GL}}$ -/

private theorem glPrime_eq : glPrime = 18446744069414584321 := rfl

private theorem glPrime_pos : 0 < glPrime := by decide

private theorem glPrime_ge2 : 2 ≤ glPrime := by decide

private theorem glPrime_lt_pow2_65 : glPrime < pow2Nat 65 := by decide

private theorem mul_mod_right_p (p a b : Nat) : (a * (b % p)) % p = (a * b) % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem two_mul_mod_lt_nat (r0 r1 : Nat) (hr1 : 0 < r1) (hle : r1 ≤ r0) :
    2 * (r0 % r1) < r0 := by
  have hdm : r1 * (r0 / r1) + r0 % r1 = r0 := Nat.div_add_mod r0 r1
  have hmod : r0 % r1 < r1 := Nat.mod_lt r0 hr1
  have hq : 1 ≤ r0 / r1 := Nat.div_pos hle hr1
  by_cases hq1 : r0 / r1 = 1
  · rw [hq1, Nat.mul_one] at hdm; omega
  · have hq2 : 2 ≤ r0 / r1 := by omega
    have hmul : r1 * 2 ≤ r1 * (r0 / r1) := Nat.mul_le_mul_left r1 hq2
    omega

private theorem add_mod_right_cancel_p (p x y z : Nat) (hp : 0 < p)
    (hx : x < p) (hy : y < p)
    (h : (x + z) % p = (y + z) % p) : x = y := by
  have hz : z % p < p := Nat.mod_lt z hp
  have hx' : (x + z) % p = (x + z % p) % p := by
    rw [Nat.add_mod x z p, Nat.mod_eq_of_lt hx]
  have hy' : (y + z) % p = (y + z % p) % p := by
    rw [Nat.add_mod y z p, Nat.mod_eq_of_lt hy]
  rw [hx', hy'] at h
  generalize z % p = z' at hz h
  by_cases h1 : x + z' < p
  · rw [Nat.mod_eq_of_lt h1] at h
    by_cases h2 : y + z' < p
    · rw [Nat.mod_eq_of_lt h2] at h; omega
    · have hsub : (y + z') % p = y + z' - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at h; omega
  · have hsub1 : (x + z') % p = x + z' - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub1] at h
    by_cases h2 : y + z' < p
    · rw [Nat.mod_eq_of_lt h2] at h; omega
    · have hsub2 : (y + z') % p = y + z' - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub2] at h; omega

private theorem gl_bezout_step (p a r0 r1 t0 t1 : Nat) (hp : 0 < p)
    (ht0 : (a * t0) % p = r0 % p)
    (ht1 : (a * t1) % p = r1 % p) :
    let q := r0 / r1
    let r2 := r0 % r1
    let qt1 := (q * t1) % p
    let t2 := (t0 + p - qt1) % p
    t2 < p ∧ (a * t2) % p = r2 % p := by
  intro q r2 qt1 t2
  have hqt1Lt : qt1 < p := Nat.mod_lt (q * t1) hp
  have ht2Lt : t2 < p := Nat.mod_lt (t0 + p - qt1) hp
  refine ⟨ht2Lt, ?_⟩
  have hsumMod : (t2 + qt1) % p = t0 % p := by
    have h1 : (t2 + qt1) % p = ((t0 + p - qt1) + qt1) % p := by
      rw [Nat.add_mod, show t2 % p = (t0 + p - qt1) % p from Nat.mod_mod _ _,
        ← Nat.add_mod]
    have h2 : (t0 + p - qt1) + qt1 = t0 + p := by omega
    rw [h1, h2, Nat.add_mod_right]
  have hmulSum : (a * t2 + a * qt1) % p = r0 % p := by
    rw [← Nat.mul_add, Nat.mul_mod, hsumMod, ← Nat.mul_mod, ht0]
  have haqt1 : (a * qt1) % p = (q * r1) % p := by
    calc
      (a * qt1) % p = (a * ((q * t1) % p)) % p := rfl
      _ = (a * (q * t1)) % p := mul_mod_right_p p a (q * t1)
      _ = (q * (a * t1)) % p := by rw [Nat.mul_left_comm]
      _ = (q * ((a * t1) % p)) % p := (mul_mod_right_p p q (a * t1)).symm
      _ = (q * (r1 % p)) % p := by rw [ht1]
      _ = (q * r1) % p := mul_mod_right_p p q r1
  have hr0Eq : r2 + q * r1 = r0 := by
    have hdm : r1 * q + r2 = r0 := Nat.div_add_mod r0 r1
    rw [Nat.mul_comm r1 q, Nat.add_comm] at hdm; exact hdm
  have hEq : ((a * t2) % p + (q * r1) % p) % p =
      (r2 % p + (q * r1) % p) % p := by
    calc
      ((a * t2) % p + (q * r1) % p) % p
        = ((a * t2) % p + (a * qt1) % p) % p := by rw [haqt1]
      _ = (a * t2 + a * qt1) % p := by rw [← Nat.add_mod]
      _ = r0 % p := hmulSum
      _ = (r2 + q * r1) % p := by rw [hr0Eq]
      _ = (r2 % p + (q * r1) % p) % p := Nat.add_mod r2 (q * r1) p
  exact add_mod_right_cancel_p p ((a * t2) % p) (r2 % p) ((q * r1) % p) hp
    (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hEq

private theorem gcd_step_nat (r0 r1 : Nat) : Nat.gcd r1 (r0 % r1) = Nat.gcd r0 r1 := by
  rw [Nat.gcd_comm r1 (r0 % r1), ← Nat.gcd_rec r1 r0, Nat.gcd_comm]

private theorem glEgcdStep_spec (p a : Nat) (hp : 2 ≤ p) :
    ∀ (k fuel r0 r1 t0 t1 : Nat),
      2 * k + 1 ≤ fuel →
      r0 < pow2Nat k →
      r1 ≤ r0 →
      t0 < p →
      t1 < p →
      (a * t0) % p = r0 % p →
      (a * t1) % p = r1 % p →
      Nat.gcd r0 r1 = 1 →
      let out := glEgcdStep p fuel r0 r1 t0 t1
      out < p ∧ (a * out) % p = 1 := by
  intro k
  induction k with
  | zero =>
    intro fuel r0 r1 t0 t1 _ hr0 hle _ _ _ _ hgcd
    have hr0z : r0 = 0 := by have : pow2Nat 0 = 1 := rfl; omega
    have hr1z : r1 = 0 := by omega
    subst hr0z; subst hr1z; simp at hgcd
  | succ k ih =>
    intro fuel r0 r1 t0 t1 hfuel hr0 hle ht0Lt ht1Lt ht0 ht1 hgcd
    have hpPos : 0 < p := by omega
    obtain ⟨fuel1, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    cases r1 with
    | zero =>
      have hr0One : r0 = 1 := by simpa using hgcd
      subst hr0One
      change t0 < p ∧ (a * t0) % p = 1
      exact ⟨ht0Lt, by simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using ht0⟩
    | succ r1' =>
      let d := r1' + 1
      have hdPos : 0 < d := Nat.succ_pos r1'
      have hbz1 := gl_bezout_step p a r0 d t0 t1 hpPos ht0 ht1
      let q1 := r0 / d
      let r2 := r0 % d
      let t2 := (t0 + p - (q1 * t1) % p) % p
      have ht2Lt : t2 < p := hbz1.1
      have ht2Eq : (a * t2) % p = r2 % p := hbz1.2
      have hgcd1 : Nat.gcd d r2 = 1 := by rw [gcd_step_nat r0 d]; exact hgcd
      have h2r2 : 2 * r2 < r0 := two_mul_mod_lt_nat r0 d hdPos hle
      have hr2Pow : r2 < pow2Nat k := by have : pow2Nat (k + 1) = 2 * pow2Nat k := rfl; omega
      obtain ⟨fuel2, rfl⟩ : ∃ m, fuel1 = m + 1 := ⟨fuel1 - 1, by omega⟩
      have hstep1 : glEgcdStep p (fuel2 + 1 + 1) r0 d t0 t1 = glEgcdStep p (fuel2 + 1) d r2 t1 t2 := rfl
      show let out := glEgcdStep p (fuel2 + 1 + 1) r0 d t0 t1; out < p ∧ (a * out) % p = 1
      rw [hstep1]
      cases hr2Case : r2 with
      | zero =>
        rw [hr2Case] at hgcd1
        have hdOne : d = 1 := by simpa using hgcd1
        have ht1d : (a * t1) % p = d % p := ht1
        rw [hdOne] at ht1d ⊢
        change t1 < p ∧ (a * t1) % p = 1
        exact ⟨ht1Lt, by simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using ht1d⟩
      | succ r2' =>
        have hr2Pos : 0 < r2 := by omega
        have hbz2 := gl_bezout_step p a d r2 t1 t2 hpPos ht1 ht2Eq
        let q2 := d / r2
        let r3 := d % r2
        let t3 := (t1 + p - (q2 * t2) % p) % p
        have hstep2 : glEgcdStep p (fuel2 + 1) d (r2' + 1) t1 t2 = glEgcdStep p fuel2 r2 r3 t2 t3 := by
          change glEgcdStep p fuel2 (r2' + 1) (d % (r2' + 1)) t2
            ((t1 + p - (d / (r2' + 1) * t2) % p) % p) =
            glEgcdStep p fuel2 r2 (d % r2) t2 ((t1 + p - (d / r2 * t2) % p) % p)
          rw [hr2Case]
        rw [hstep2]
        have hgcd2 : Nat.gcd r2 r3 = 1 := by rw [gcd_step_nat d r2]; exact hgcd1
        have hr3Le : r3 ≤ r2 := Nat.le_of_lt (Nat.mod_lt d hr2Pos)
        exact ih fuel2 r2 r3 t2 t3 (by omega) hr2Pow hr3Le ht2Lt hbz2.1 ht2Eq hbz2.2 hgcd2

private theorem gcd_eq_one_of_mul_mod_one_gl (a r : Nat) (h : (a * r) % glPrime = 1) :
    Nat.gcd glPrime a = 1 := by
  have hdvdP : Nat.gcd glPrime a ∣ glPrime := Nat.gcd_dvd_left glPrime a
  have hdvdA : Nat.gcd glPrime a ∣ a := Nat.gcd_dvd_right glPrime a
  have hdvdAR : Nat.gcd glPrime a ∣ a * r := Nat.dvd_mul_right_of_dvd hdvdA r
  have hdvdPQ : Nat.gcd glPrime a ∣ glPrime * (a * r / glPrime) :=
    Nat.dvd_mul_right_of_dvd hdvdP (a * r / glPrime)
  have hdm : glPrime * (a * r / glPrime) + 1 = a * r := by
    have := Nat.div_add_mod (a * r) glPrime
    rw [h] at this; exact this
  rw [← hdm] at hdvdAR
  exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hdvdPQ).mp hdvdAR)

private theorem glInv_spec_of_coprime (a : Nat) (hcop : Nat.gcd glPrime a = 1) :
    glInv a < glPrime ∧ (a * glInv a) % glPrime = 1 := by
  have ha0 : a % glPrime ≠ 0 := by
    intro h0
    have hdvd : glPrime ∣ a := Nat.dvd_of_mod_eq_zero h0
    have hgcd : Nat.gcd glPrime a = glPrime := Nat.gcd_eq_left hdvd
    rw [hcop] at hgcd
    exact absurd hgcd (by decide)
  unfold glInv
  have ha0B : (a % glPrime == 0) = false := beq_false_of_ne ha0
  simp only [ha0B, Bool.false_eq_true, ↓reduceIte]
  have hgcdMod : Nat.gcd glPrime (a % glPrime) = 1 := by
    rw [Nat.gcd_comm glPrime (a % glPrime), ← Nat.gcd_rec glPrime a]
    exact hcop
  exact glEgcdStep_spec glPrime a glPrime_ge2 65 131 glPrime (a % glPrime) 0 1
    (by decide) glPrime_lt_pow2_65 (Nat.le_of_lt (Nat.mod_lt a glPrime_pos))
    glPrime_pos (by decide) (by simp) (by simp [Nat.mul_one]) hgcdMod

private theorem imod_add {P a a' b b' : Int} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a + b) % P = (a' + b') % P := by
  rw [Int.add_emod, ha, hb, ← Int.add_emod]

private theorem imod_sub {P a a' b b' : Int} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a - b) % P = (a' - b') % P := by
  rw [Int.sub_emod, ha, hb, ← Int.sub_emod]

private theorem imod_mul {P a a' b b' : Int} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a * b) % P = (a' * b') % P := by
  rw [Int.mul_emod, ha, hb, ← Int.mul_emod]

private theorem glAdd_imod (a b : Nat) :
    ((glAdd a b : Nat) : Int) % (glPrime : Int) = ((a : Int) + (b : Int)) % (glPrime : Int) := by
  unfold glAdd
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_add]

private theorem glMul_imod (a b : Nat) :
    ((glMul a b : Nat) : Int) % (glPrime : Int) = ((a : Int) * (b : Int)) % (glPrime : Int) := by
  unfold glMul
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_mul]

private theorem glSub_imod (a b : Nat) :
    ((glSub a b : Nat) : Int) % (glPrime : Int) = ((a : Int) - (b : Int)) % (glPrime : Int) := by
  unfold glSub
  have hbLt : b % glPrime < glPrime := Nat.mod_lt b glPrime_pos
  rw [Int.natCast_emod, Int.emod_emod]
  have hcast : ((a + glPrime - b % glPrime : Nat) : Int) =
      (a : Int) - ((b % glPrime : Nat) : Int) + (glPrime : Int) := by omega
  rw [hcast, Int.add_emod_right, Int.natCast_emod]
  exact imod_sub rfl (Int.emod_emod (b : Int) (glPrime : Int))

private theorem nat_eq_of_imod_gl (u v : Nat) (hu : u < glPrime) (hv : v < glPrime)
    (h : (u : Int) % (glPrime : Int) = (v : Int) % (glPrime : Int)) : u = v := by
  have hu' : (u : Int) % (glPrime : Int) = (u : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg u) (Int.ofNat_lt.mpr hu)
  have hv' : (v : Int) % (glPrime : Int) = (v : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg v) (Int.ofNat_lt.mpr hv)
  rw [hu', hv'] at h
  exact Int.ofNat.inj h

private theorem extMul_imod (a b : ExtGl) :
    let m := extMul a b
    let a0 : Int := a.c0; let a1 : Int := a.c1; let a2 : Int := a.c2
    let b0 : Int := b.c0; let b1 : Int := b.c1; let b2 : Int := b.c2
    let P : Int := glPrime
    (m.c0 : Int) % P = (a0 * b0 + a1 * b2 + a2 * b1) % P ∧
    (m.c1 : Int) % P = (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2) % P ∧
    (m.c2 : Int) % P = (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) % P := by
  dsimp only [extMul]
  have hv0 := glMul_imod a.c0 b.c0
  have hv1 := glMul_imod a.c1 b.c1
  have hv2 := glMul_imod a.c2 b.c2
  have hm01 : ((glSub (glSub (glMul (glAdd a.c0 a.c1) (glAdd b.c0 b.c1))
      (glMul a.c0 b.c0)) (glMul a.c1 b.c1) : Nat) : Int) % (glPrime : Int) =
      ((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int)) % (glPrime : Int) := by
    refine (glSub_imod _ _).trans ?_
    refine (imod_sub ((glSub_imod _ _).trans
      (imod_sub ((glMul_imod _ _).trans
        (imod_mul (glAdd_imod _ _) (glAdd_imod _ _))) hv0)) hv1).trans ?_
    congr 1; simp only [Int.add_mul, Int.mul_add]; omega
  have hm02 : ((glSub (glSub (glMul (glAdd a.c0 a.c2) (glAdd b.c0 b.c2))
      (glMul a.c0 b.c0)) (glMul a.c2 b.c2) : Nat) : Int) % (glPrime : Int) =
      ((a.c0 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c0 : Int)) % (glPrime : Int) := by
    refine (glSub_imod _ _).trans ?_
    refine (imod_sub ((glSub_imod _ _).trans
      (imod_sub ((glMul_imod _ _).trans
        (imod_mul (glAdd_imod _ _) (glAdd_imod _ _))) hv0)) hv2).trans ?_
    congr 1; simp only [Int.add_mul, Int.mul_add]; omega
  have hm12 : ((glSub (glSub (glMul (glAdd a.c1 a.c2) (glAdd b.c1 b.c2))
      (glMul a.c1 b.c1)) (glMul a.c2 b.c2) : Nat) : Int) % (glPrime : Int) =
      ((a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) % (glPrime : Int) := by
    refine (glSub_imod _ _).trans ?_
    refine (imod_sub ((glSub_imod _ _).trans
      (imod_sub ((glMul_imod _ _).trans
        (imod_mul (glAdd_imod _ _) (glAdd_imod _ _))) hv1)) hv2).trans ?_
    congr 1; simp only [Int.add_mul, Int.mul_add]; omega
  refine ⟨?_, ?_, ?_⟩
  · refine (glAdd_imod _ _).trans ((imod_add hv0 hm12).trans ?_)
    congr 1; omega
  · refine (glAdd_imod _ _).trans ((imod_add ((glAdd_imod _ _).trans (imod_add hm01 hm12)) hv2).trans ?_)
    congr 1; omega
  · refine (glAdd_imod _ _).trans ((imod_add ((glAdd_imod _ _).trans (imod_add hm02 hv1)) hv2).trans ?_)
    congr 1; omega

private theorem extMul_canonical (a b : ExtGl) :
    (extMul a b).c0 < glPrime ∧ (extMul a b).c1 < glPrime ∧ (extMul a b).c2 < glPrime :=
  ⟨Nat.mod_lt _ glPrime_pos, Nat.mod_lt _ glPrime_pos, Nat.mod_lt _ glPrime_pos⟩

private theorem extAdj_imod (a : ExtGl) :
    let d := extAdj a
    let a0 : Int := a.c0; let a1 : Int := a.c1; let a2 : Int := a.c2
    let P : Int := glPrime
    (d.c0 : Int) % P = ((a0 + a2) * (a0 + a2) - a1 * (a1 + a2)) % P ∧
    (d.c1 : Int) % P = (a2 * a2 - a0 * a1) % P ∧
    (d.c2 : Int) % P = (a1 * a1 - a2 * (a0 + a2)) % P := by
  dsimp only [extAdj]
  refine ⟨?_, ?_, ?_⟩
  · exact (glSub_imod _ _).trans <| imod_sub
      ((glMul_imod _ _).trans (imod_mul (glAdd_imod _ _) (glAdd_imod _ _)))
      ((glMul_imod _ _).trans (imod_mul rfl (glAdd_imod _ _)))
  · exact (glSub_imod _ _).trans <| imod_sub (glMul_imod _ _) (glMul_imod _ _)
  · exact (glSub_imod _ _).trans <| imod_sub
      (glMul_imod _ _)
      ((glMul_imod _ _).trans (imod_mul rfl (glAdd_imod _ _)))

private theorem extNorm_imod (a : ExtGl) :
    let a0 : Int := a.c0; let a1 : Int := a.c1; let a2 : Int := a.c2
    let d0 := (a0 + a2) * (a0 + a2) - a1 * (a1 + a2)
    let d1 := a2 * a2 - a0 * a1
    let d2 := a1 * a1 - a2 * (a0 + a2)
    ((extNorm a : Nat) : Int) % (glPrime : Int) = (a0 * d0 + a2 * d1 + a1 * d2) % (glPrime : Int) := by
  have hadj := extAdj_imod a
  dsimp only [extNorm]
  exact (glAdd_imod _ _).trans <|
    imod_add ((glAdd_imod _ _).trans
      (imod_add ((glMul_imod _ _).trans (imod_mul rfl hadj.1))
        ((glMul_imod _ _).trans (imod_mul rfl hadj.2.1))))
      ((glMul_imod _ _).trans (imod_mul rfl hadj.2.2))

private theorem extNorm_mul_poly (a0 a1 a2 b0 b1 b2 : Int) :
    let norm (x0 x1 x2 : Int) : Int :=
      x0 * ((x0 + x2) * (x0 + x2) - x1 * (x1 + x2)) +
      x2 * (x2 * x2 - x0 * x1) +
      x1 * (x1 * x1 - x2 * (x0 + x2))
    let c0 := a0 * b0 + a1 * b2 + a2 * b1
    let c1 := a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2
    let c2 := a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2
    norm c0 c1 c2 = norm a0 a1 a2 * norm b0 b1 b2 := by
  dsimp only
  grind

private theorem extNorm_mul_imod (a b : ExtGl) :
    ((extNorm (extMul a b) : Nat) : Int) % (glPrime : Int) =
      (((extNorm a : Nat) : Int) * ((extNorm b : Nat) : Int)) % (glPrime : Int) := by
  have hm := extMul_imod a b
  have hnab := extNorm_imod (extMul a b)
  have hna := extNorm_imod a
  have hnb := extNorm_imod b
  have hpoly := extNorm_mul_poly (a.c0 : Int) (a.c1 : Int) (a.c2 : Int) (b.c0 : Int) (b.c1 : Int) (b.c2 : Int)
  refine hnab.trans ?_
  have hsub :
      (((extMul a b).c0 : Int) * ((((extMul a b).c0 : Int) + ((extMul a b).c2 : Int)) *
          (((extMul a b).c0 : Int) + ((extMul a b).c2 : Int)) -
          ((extMul a b).c1 : Int) * (((extMul a b).c1 : Int) + ((extMul a b).c2 : Int))) +
        ((extMul a b).c2 : Int) * (((extMul a b).c2 : Int) * ((extMul a b).c2 : Int) -
          ((extMul a b).c0 : Int) * ((extMul a b).c1 : Int)) +
        ((extMul a b).c1 : Int) * (((extMul a b).c1 : Int) * ((extMul a b).c1 : Int) -
          ((extMul a b).c2 : Int) * (((extMul a b).c0 : Int) + ((extMul a b).c2 : Int)))) % (glPrime : Int) =
      (((a.c0 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) *
          ((((a.c0 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) +
            ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int))) *
           (((a.c0 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) +
            ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int))) -
           ((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c2 : Int)) *
           (((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c2 : Int)) +
            ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int)))) +
        ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int)) *
          (((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int)) *
           ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int)) -
           ((a.c0 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) *
           ((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c2 : Int))) +
        ((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c2 : Int)) *
          (((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c2 : Int)) *
           ((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c2 : Int)) -
           ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int)) *
           (((a.c0 : Int) * (b.c0 : Int) + (a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) +
            ((a.c0 : Int) * (b.c2 : Int) + (a.c1 : Int) * (b.c1 : Int) + (a.c2 : Int) * (b.c0 : Int) + (a.c2 : Int) * (b.c2 : Int))))) % (glPrime : Int) :=
    imod_add
      (imod_add
        (imod_mul hm.1 (imod_sub
          (imod_mul (imod_add hm.1 hm.2.2) (imod_add hm.1 hm.2.2))
          (imod_mul hm.2.1 (imod_add hm.2.1 hm.2.2))))
        (imod_mul hm.2.2 (imod_sub (imod_mul hm.2.2 hm.2.2) (imod_mul hm.1 hm.2.1))))
      (imod_mul hm.2.1 (imod_sub (imod_mul hm.2.1 hm.2.1) (imod_mul hm.2.2 (imod_add hm.1 hm.2.2))))
  refine hsub.trans ?_
  dsimp only at hpoly
  rw [hpoly]
  exact (imod_mul hna hnb).symm

private theorem extMul_comm (a b : ExtGl) : extMul a b = extMul b a := by
  have hab := extMul_imod a b
  have hba := extMul_imod b a
  have hc1 := extMul_canonical a b
  have hc2 := extMul_canonical b a
  cases hm1 : extMul a b with
  | mk x0 x1 x2 =>
    cases hm2 : extMul b a with
    | mk y0 y1 y2 =>
      rw [hm1] at hab hc1; rw [hm2] at hba hc2
      have h0 : x0 = y0 := nat_eq_of_imod_gl x0 y0 hc1.1 hc2.1 (by rw [hab.1, hba.1]; congr 1; grind)
      have h1 : x1 = y1 := nat_eq_of_imod_gl x1 y1 hc1.2.1 hc2.2.1 (by rw [hab.2.1, hba.2.1]; congr 1; grind)
      have h2 : x2 = y2 := nat_eq_of_imod_gl x2 y2 hc1.2.2 hc2.2.2 (by rw [hab.2.2, hba.2.2]; congr 1; grind)
      rw [h0, h1, h2]

private theorem extMul_assoc (a b c : ExtGl) :
    extMul (extMul a b) c = extMul a (extMul b c) := by
  have hab := extMul_imod a b
  have hbc := extMul_imod b c
  have hlhs := extMul_imod (extMul a b) c
  have hrhs := extMul_imod a (extMul b c)
  have hcL := extMul_canonical (extMul a b) c
  have hcR := extMul_canonical a (extMul b c)
  cases hL : extMul (extMul a b) c with
  | mk x0 x1 x2 =>
    cases hR : extMul a (extMul b c) with
    | mk y0 y1 y2 =>
      rw [hL] at hlhs hcL; rw [hR] at hrhs hcR
      have h0 : x0 = y0 := nat_eq_of_imod_gl x0 y0 hcL.1 hcR.1 (by
        refine hlhs.1.trans ?_
        refine (imod_add (imod_add (imod_mul hab.1 rfl) (imod_mul hab.2.1 rfl)) (imod_mul hab.2.2 rfl)).trans ?_
        refine Eq.trans ?_ (imod_add (imod_add (imod_mul rfl hbc.1) (imod_mul rfl hbc.2.2)) (imod_mul rfl hbc.2.1)).symm |>.trans hrhs.1.symm
        congr 1; grind)
      have h1 : x1 = y1 := nat_eq_of_imod_gl x1 y1 hcL.2.1 hcR.2.1 (by
        refine hlhs.2.1.trans ?_
        refine (imod_add (imod_add (imod_add (imod_add (imod_mul hab.1 rfl) (imod_mul hab.2.1 rfl))
          (imod_mul hab.2.1 rfl)) (imod_mul hab.2.2 rfl)) (imod_mul hab.2.2 rfl)).trans ?_
        refine Eq.trans ?_ (imod_add (imod_add (imod_add (imod_add (imod_mul rfl hbc.2.1) (imod_mul rfl hbc.1))
          (imod_mul rfl hbc.2.2)) (imod_mul rfl hbc.2.1)) (imod_mul rfl hbc.2.2)).symm |>.trans hrhs.2.1.symm
        congr 1; grind)
      have h2 : x2 = y2 := nat_eq_of_imod_gl x2 y2 hcL.2.2 hcR.2.2 (by
        refine hlhs.2.2.trans ?_
        refine (imod_add (imod_add (imod_add (imod_mul hab.1 rfl) (imod_mul hab.2.1 rfl))
          (imod_mul hab.2.2 rfl)) (imod_mul hab.2.2 rfl)).trans ?_
        refine Eq.trans ?_ (imod_add (imod_add (imod_add (imod_mul rfl hbc.2.2) (imod_mul rfl hbc.2.1))
          (imod_mul rfl hbc.1)) (imod_mul rfl hbc.2.2)).symm |>.trans hrhs.2.2.symm
        congr 1; grind)
      rw [h0, h1, h2]

private theorem extMul_one_right (a : ExtGl)
    (hc0 : a.c0 < glPrime) (hc1 : a.c1 < glPrime) (hc2 : a.c2 < glPrime) :
    extMul a extOne = a := by
  have hm := extMul_imod a extOne
  have hcan := extMul_canonical a extOne
  cases heq : extMul a extOne with
  | mk x0 x1 x2 =>
    rw [heq] at hm hcan
    cases a with
    | mk a0 a1 a2 =>
      dsimp only [extOne] at hm
      have h0 : x0 = a0 := nat_eq_of_imod_gl x0 a0 hcan.1 hc0 (by rw [hm.1]; simp)
      have h1 : x1 = a1 := nat_eq_of_imod_gl x1 a1 hcan.2.1 hc1 (by rw [hm.2.1]; simp)
      have h2 : x2 = a2 := nat_eq_of_imod_gl x2 a2 hcan.2.2 hc2 (by rw [hm.2.2]; simp)
      rw [h0, h1, h2]

private theorem extMul_scale_right (a b : ExtGl) (k : Nat) :
    extMul a (extScale b k) = extScale (extMul a b) k := by
  have hm1 := extMul_imod a (extScale b k)
  have hm2 := extMul_imod a b
  have hc1 := extMul_canonical a (extScale b k)
  have hs0 := glMul_imod b.c0 k
  have hs1 := glMul_imod b.c1 k
  have hs2 := glMul_imod b.c2 k
  cases hL : extMul a (extScale b k) with
  | mk x0 x1 x2 =>
    rw [hL] at hm1 hc1
    dsimp only [extScale] at hm1 ⊢
    have h0 : x0 = glMul (extMul a b).c0 k :=
      nat_eq_of_imod_gl x0 _ hc1.1 (Nat.mod_lt _ glPrime_pos) (by
        refine hm1.1.trans ?_
        refine (imod_add (imod_add (imod_mul rfl hs0) (imod_mul rfl hs2)) (imod_mul rfl hs1)).trans ?_
        refine Eq.trans ?_ ((glMul_imod _ _).trans (imod_mul hm2.1 rfl)).symm
        congr 1; grind)
    have h1 : x1 = glMul (extMul a b).c1 k :=
      nat_eq_of_imod_gl x1 _ hc1.2.1 (Nat.mod_lt _ glPrime_pos) (by
        refine hm1.2.1.trans ?_
        refine (imod_add (imod_add (imod_add (imod_add (imod_mul rfl hs1) (imod_mul rfl hs0))
          (imod_mul rfl hs2)) (imod_mul rfl hs1)) (imod_mul rfl hs2)).trans ?_
        refine Eq.trans ?_ ((glMul_imod _ _).trans (imod_mul hm2.2.1 rfl)).symm
        congr 1; grind)
    have h2 : x2 = glMul (extMul a b).c2 k :=
      nat_eq_of_imod_gl x2 _ hc1.2.2 (Nat.mod_lt _ glPrime_pos) (by
        refine hm1.2.2.trans ?_
        refine (imod_add (imod_add (imod_add (imod_mul rfl hs2) (imod_mul rfl hs1))
          (imod_mul rfl hs0)) (imod_mul rfl hs2)).trans ?_
        refine Eq.trans ?_ ((glMul_imod _ _).trans (imod_mul hm2.2.2 rfl)).symm
        congr 1; grind)
    rw [h0, h1, h2]

private theorem extMul_adj_eq_norm (a : ExtGl) :
    extMul a (extAdj a) = extOfBase (extNorm a) := by
  have hm := extMul_imod a (extAdj a)
  have hadj := extAdj_imod a
  have hcan := extMul_canonical a (extAdj a)
  have hnormE := extNorm_imod a
  cases heq : extMul a (extAdj a) with
  | mk x0 x1 x2 =>
    rw [heq] at hm hcan
    dsimp only [extOfBase]
    have h0 : x0 = extNorm a :=
      nat_eq_of_imod_gl x0 (extNorm a) hcan.1 (Nat.mod_lt _ glPrime_pos) (by
        refine hm.1.trans ?_
        refine (imod_add (imod_add (imod_mul rfl hadj.1) (imod_mul rfl hadj.2.2)) (imod_mul rfl hadj.2.1)).trans ?_
        refine Eq.trans ?_ hnormE.symm
        congr 1; grind)
    have h1 : x1 = 0 :=
      nat_eq_of_imod_gl x1 0 hcan.2.1 glPrime_pos (by
        refine hm.2.1.trans ?_
        refine (imod_add (imod_add (imod_add (imod_add (imod_mul rfl hadj.2.1) (imod_mul rfl hadj.1))
          (imod_mul rfl hadj.2.2)) (imod_mul rfl hadj.2.1)) (imod_mul rfl hadj.2.2)).trans ?_
        have hzero :
            (a.c0 : Int) * ((a.c2 : Int) * (a.c2 : Int) - (a.c0 : Int) * (a.c1 : Int)) +
            (a.c1 : Int) * (((a.c0 : Int) + (a.c2 : Int)) * ((a.c0 : Int) + (a.c2 : Int)) -
              (a.c1 : Int) * ((a.c1 : Int) + (a.c2 : Int))) +
            (a.c1 : Int) * ((a.c1 : Int) * (a.c1 : Int) - (a.c2 : Int) * ((a.c0 : Int) + (a.c2 : Int))) +
            (a.c2 : Int) * ((a.c2 : Int) * (a.c2 : Int) - (a.c0 : Int) * (a.c1 : Int)) +
            (a.c2 : Int) * ((a.c1 : Int) * (a.c1 : Int) - (a.c2 : Int) * ((a.c0 : Int) + (a.c2 : Int))) = 0 := by
          grind
        rw [hzero]; rfl)
    have h2 : x2 = 0 :=
      nat_eq_of_imod_gl x2 0 hcan.2.2 glPrime_pos (by
        refine hm.2.2.trans ?_
        refine (imod_add (imod_add (imod_add (imod_mul rfl hadj.2.2) (imod_mul rfl hadj.2.1))
          (imod_mul rfl hadj.1)) (imod_mul rfl hadj.2.2)).trans ?_
        have hzero :
            (a.c0 : Int) * ((a.c1 : Int) * (a.c1 : Int) - (a.c2 : Int) * ((a.c0 : Int) + (a.c2 : Int))) +
            (a.c1 : Int) * ((a.c2 : Int) * (a.c2 : Int) - (a.c0 : Int) * (a.c1 : Int)) +
            (a.c2 : Int) * (((a.c0 : Int) + (a.c2 : Int)) * ((a.c0 : Int) + (a.c2 : Int)) -
              (a.c1 : Int) * ((a.c1 : Int) + (a.c2 : Int))) +
            (a.c2 : Int) * ((a.c1 : Int) * (a.c1 : Int) - (a.c2 : Int) * ((a.c0 : Int) + (a.c2 : Int))) = 0 := by
          grind
        rw [hzero]; rfl)
    rw [h0, h1, h2]

private theorem glEq_eq_one_iff_mod (x y : Nat) : glEq x y = 1 ↔ x % glPrime = y % glPrime := by
  unfold glEq
  by_cases h : x % glPrime = y % glPrime
  · simp [h]
  · have hb : (x % glPrime == y % glPrime) = false := beq_false_of_ne h
    simp [hb, h]

private theorem extEq_canonical_eq_one_iff (a b : ExtGl)
    (ha : extCanonical a = true) (hb : extCanonical b = true) :
    extEq a b = 1 ↔ a = b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  unfold extCanonical at ha hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha hb
  unfold extEq
  by_cases h0 : a0 = b0
  · subst h0
    have g0 : glEq a0 a0 = 1 := (glEq_eq_one_iff_mod a0 a0).mpr rfl
    simp only [g0, beq_self_eq_true, ↓reduceIte]
    by_cases h1 : a1 = b1
    · subst h1
      have g1 : glEq a1 a1 = 1 := (glEq_eq_one_iff_mod a1 a1).mpr rfl
      simp only [g1, beq_self_eq_true, ↓reduceIte]
      rw [glEq_eq_one_iff_mod, Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2]
      simp
    · have g1 : glEq a1 b1 = 0 := by
        unfold glEq
        have hne : a1 % glPrime ≠ b1 % glPrime := by
          rw [Nat.mod_eq_of_lt ha.1.2, Nat.mod_eq_of_lt hb.1.2]; exact h1
        have hbf : (a1 % glPrime == b1 % glPrime) = false := beq_false_of_ne hne
        simp [hbf]
      simp [g1, h1]
  · have g0 : glEq a0 b0 = 0 := by
      unfold glEq
      have hne : a0 % glPrime ≠ b0 % glPrime := by
        rw [Nat.mod_eq_of_lt ha.1.1, Nat.mod_eq_of_lt hb.1.1]; exact h0
      have hbf : (a0 % glPrime == b0 % glPrime) = false := beq_false_of_ne hne
      simp [hbf]
    simp [g0, h0]

private theorem extZero_canonical : extCanonical extZero = true := by decide

private theorem extOne_canonical : extCanonical extOne = true := by decide

private theorem extMul_canonical_bool (a b : ExtGl) : extCanonical (extMul a b) = true := by
  have hc := extMul_canonical a b
  unfold extCanonical
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩

/-- **Tier-2 `guess` (`checked def`)**: Cubic extension field inverse over real Goldilocks
$p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$, with a kernel-checked uniqueness proof (`extInv.check_unique`)
established purely from ring identities and norm multiplicativity (zero `sorry`, zero Mathlib). -/
@[circuit_noinline]
checked def extInv (a : ExtGl) : ExtGl :=
  hint extInvDirect a
  where check fun r =>
    if extIsZero a == 1 then extCanonical r && (extEq r extZero == 1)
    else extCanonical r && (extEq (extMul a r) extOne == 1)
  by
    intro res hr
    unfold extInv.check at hr
    unfold extInv extInvDirect
    by_cases haz : extIsZero a = 1
    · simp only [haz, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hr ⊢
      exact (extEq_canonical_eq_one_iff res extZero hr.1 extZero_canonical).mp hr.2
    · have hazB : (extIsZero a == 1) = false := beq_false_of_ne haz
      rw [hazB] at hr ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hr ⊢
      obtain ⟨hcanRes, hmulEq⟩ := hr
      have hmul : extMul a res = extOne :=
        (extEq_canonical_eq_one_iff (extMul a res) extOne (extMul_canonical_bool a res) extOne_canonical).mp hmulEq
      have hnormProdI : (((extNorm a : Nat) : Int) * ((extNorm res : Nat) : Int)) % (glPrime : Int) = 1 := by
        have h1 := (extNorm_mul_imod a res).symm
        rw [hmul] at h1
        have hnorm1 : extNorm extOne = 1 := by decide
        rw [hnorm1] at h1
        exact h1.trans (Int.emod_eq_of_lt (by decide) (by decide))
      have hnormProd : (extNorm a * extNorm res) % glPrime = 1 := by
        have hcast : (((extNorm a * extNorm res) % glPrime : Nat) : Int) =
            (((extNorm a : Nat) : Int) * ((extNorm res : Nat) : Int)) % (glPrime : Int) := by
          rw [Int.natCast_emod, Int.natCast_mul]
        rw [hnormProdI] at hcast
        exact Int.ofNat.inj hcast
      have hcop : Nat.gcd glPrime (extNorm a) = 1 :=
        gcd_eq_one_of_mul_mod_one_gl (extNorm a) (extNorm res) hnormProd
      have hinvSpec := glInv_spec_of_coprime (extNorm a) hcop
      have hnormDef : glAdd (glAdd (glMul a.c0 (extAdj a).c0) (glMul a.c2 (extAdj a).c1))
          (glMul a.c1 (extAdj a).c2) = extNorm a := rfl
      rw [hnormDef]
      have hcanInv : extCanonical (extScale (extAdj a) (glInv (extNorm a))) = true := by
        unfold extCanonical extScale
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨Nat.mod_lt _ glPrime_pos, Nat.mod_lt _ glPrime_pos⟩, Nat.mod_lt _ glPrime_pos⟩
      have hmulInv : extMul a (extScale (extAdj a) (glInv (extNorm a))) = extOne := by
        rw [extMul_scale_right a (extAdj a), extMul_adj_eq_norm a]
        dsimp only [extScale, extOfBase, extOne, glMul]
        rw [hinvSpec.2, Nat.zero_mul, Nat.zero_mod]
      unfold extCanonical at hcanRes hcanInv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcanRes hcanInv
      calc
        res = extMul res extOne :=
          (extMul_one_right res hcanRes.1.1 hcanRes.1.2 hcanRes.2).symm
        _ = extMul res (extMul a (extScale (extAdj a) (glInv (extNorm a)))) := by rw [hmulInv]
        _ = extMul (extMul res a) (extScale (extAdj a) (glInv (extNorm a))) :=
          (extMul_assoc res a _).symm
        _ = extMul (extMul a res) (extScale (extAdj a) (glInv (extNorm a))) := by
          rw [extMul_comm res a]
        _ = extMul extOne (extScale (extAdj a) (glInv (extNorm a))) := by rw [hmul]
        _ = extMul (extScale (extAdj a) (glInv (extNorm a))) extOne :=
          extMul_comm extOne _
        _ = extScale (extAdj a) (glInv (extNorm a)) :=
          extMul_one_right _ hcanInv.1.1 hcanInv.1.2 hcanInv.2

/-! ## Section 3: Full Multi-Block / Multi-Chunk BLAKE3 & `CompressWrap` Statement Digest -/

/-- Output of one BLAKE3 quarter-round `G`. -/
structure QuarterOut where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving BEq, DecidableEq, Repr

/-- 16-word internal BLAKE3 compression state. -/
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

/-- Monomorphic BLAKE3 chunk Merkle tree stack (`Blake3::LayerNode`). -/
inductive LayerStack where
  | nil
  | push (rest : LayerStack) (cv : Digest32)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic optional 8-word digest for `blake3NextLayer` (`Blake3::MaybeDigest`). -/
inductive MaybeDigest32 where
  | none
  | some (cv : Digest32)
  deriving BEq, DecidableEq, Repr

/-- Result of one `blake3NextLayer` tree-folding pass. -/
structure NextLayerOut where
  last : MaybeDigest32
  layer : LayerStack
  deriving BEq, DecidableEq, Repr

/-- Result of consuming up to 64 bytes into one `Block16` (`Blake3::BlockRead`). -/
structure BlockTakeResult where
  block : Block16
  len : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

/-- Standard BLAKE3 IV (`Aiur.Library.Blake3.iv`). -/
@[circuit_inline]
def blake3IV : Digest32 :=
  { w0 := 0x6A09E667, w1 := 0xBB67AE85, w2 := 0x3C6EF372, w3 := 0xA54FF53A
    w4 := 0x510E527F, w5 := 0x9B05688C, w6 := 0x1F83D9AB, w7 := 0x5BE0CD19 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key_context("multi-stark/v6/merkle/leaf")`
(`StarkHash::v6_merkle_leaf_cv`). -/
@[circuit_inline]
def v6MerkleLeafCv : Digest32 :=
  { w0 := 0x77042819, w1 := 0x5A1DD04F, w2 := 0x2F8D0BB8, w3 := 0x39D27832
    w4 := 0x552A30F6, w5 := 0x546C9899, w6 := 0x8510A8EF, w7 := 0x83ECCD66 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key_context("multi-stark/v6/merkle/compress")`
(`StarkHash::v6_merkle_compress_cv`). -/
@[circuit_inline]
def v6MerkleCompressCv : Digest32 :=
  { w0 := 0xCC4D7633, w1 := 0xF8492FEC, w2 := 0x5704B1FD, w3 := 0x2D69A6B5
    w4 := 0xA871EBB5, w5 := 0x6439610D, w6 := 0x89E86BE6, w7 := 0x02E22A34 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key_context("multi-stark/v6/transcript/batch")`
(`StarkHash::v6_transcript_batch_cv`). -/
@[circuit_inline]
def v6TranscriptBatchCv : Digest32 :=
  { w0 := 0x56945548, w1 := 0x0BAEB2C2, w2 := 0xB0BC28DD, w3 := 0x9EBE2699
    w4 := 0xD7B24F82, w5 := 0x35470F4D, w6 := 0x065F18D3, w7 := 0xF3B2994F }

/-- BLAKE3 quarter-round `G` in Peephole-fusible direct `UInt32.*` form. -/
@[circuit_inline]
def blake3G (a b c d mx my : UInt32) : QuarterOut :=
  let a1 := UInt32.add (UInt32.add a b) mx
  let t1 := UInt32.xor d a1
  let d1 := UInt32.lor (UInt32.shiftRight t1 (UInt32.ofNat 16)) (UInt32.shiftLeft t1 (UInt32.ofNat 16))
  let c1 := UInt32.add c d1
  let t2 := UInt32.xor b c1
  let b1 := UInt32.lor (UInt32.shiftRight t2 (UInt32.ofNat 12)) (UInt32.shiftLeft t2 (UInt32.ofNat 20))
  let a2 := UInt32.add (UInt32.add a1 b1) my
  let t3 := UInt32.xor d1 a2
  let d2 := UInt32.lor (UInt32.shiftRight t3 (UInt32.ofNat 8)) (UInt32.shiftLeft t3 (UInt32.ofNat 24))
  let c2 := UInt32.add c1 d2
  let t4 := UInt32.xor b1 c2
  let b2 := UInt32.lor (UInt32.shiftRight t4 (UInt32.ofNat 7)) (UInt32.shiftLeft t4 (UInt32.ofNat 25))
  { a := a2, b := b2, c := c2, d := d2 }

/-- One full BLAKE3 round (4 column + 4 diagonal quarter-rounds), shared as one
memoized Peephole-fused chip across all compressions. -/
@[circuit_noinline]
def blake3Round (s : State16) (m : Block16) : State16 :=
  let c0 := blake3G s.v0 s.v4 s.v8 s.v12 m.m0 m.m1
  let c1 := blake3G s.v1 s.v5 s.v9 s.v13 m.m2 m.m3
  let c2 := blake3G s.v2 s.v6 s.v10 s.v14 m.m4 m.m5
  let c3 := blake3G s.v3 s.v7 s.v11 s.v15 m.m6 m.m7
  let d0 := blake3G c0.a c1.b c2.c c3.d m.m8 m.m9
  let d1 := blake3G c1.a c2.b c3.c c0.d m.m10 m.m11
  let d2 := blake3G c2.a c3.b c0.c c1.d m.m12 m.m13
  let d3 := blake3G c3.a c0.b c1.c c2.d m.m14 m.m15
  { v0 := d0.a, v1 := d1.a, v2 := d2.a, v3 := d3.a
    v4 := d3.b, v5 := d0.b, v6 := d1.b, v7 := d2.b
    v8 := d2.c, v9 := d3.c, v10 := d0.c, v11 := d1.c
    v12 := d1.d, v13 := d2.d, v14 := d3.d, v15 := d0.d }

/-- BLAKE3 message-schedule permutation between rounds. -/
@[circuit_inline]
def blake3Permute (m : Block16) : Block16 :=
  { m0 := m.m2,  m1 := m.m6,  m2 := m.m3,  m3 := m.m10
    m4 := m.m7,  m5 := m.m0,  m6 := m.m4,  m7 := m.m13
    m8 := m.m1,  m9 := m.m11, m10 := m.m12, m11 := m.m5
    m12 := m.m9, m13 := m.m14, m14 := m.m15, m15 := m.m8 }

/-- Structural 7-round BLAKE3 compression loop (`rem = 6` executes rounds `0..6`). -/
@[circuit_noinline]
def blake3CompressLoop (rem : Nat) (s : State16) (m : Block16) : Digest32 :=
  let s1 := blake3Round s m
  match rem with
  | 0 =>
    { w0 := UInt32.xor s1.v0 s1.v8,  w1 := UInt32.xor s1.v1 s1.v9
      w2 := UInt32.xor s1.v2 s1.v10, w3 := UInt32.xor s1.v3 s1.v11
      w4 := UInt32.xor s1.v4 s1.v12, w5 := UInt32.xor s1.v5 s1.v13
      w6 := UInt32.xor s1.v6 s1.v14, w7 := UInt32.xor s1.v7 s1.v15 }
  | k + 1 =>
    blake3CompressLoop k s1 (blake3Permute m)
termination_by structural rem

/-- Full BLAKE3 block compression with 64-bit chunk counter `(ctrLo, ctrHi)`. -/
@[circuit_noinline]
def blake3Compress (cv : Digest32) (m : Block16) (ctrLo ctrHi blockLen flags : UInt32) : Digest32 :=
  let iv := blake3IV
  let st : State16 :=
    { v0 := cv.w0, v1 := cv.w1, v2 := cv.w2, v3 := cv.w3
      v4 := cv.w4, v5 := cv.w5, v6 := cv.w6, v7 := cv.w7
      v8 := iv.w0, v9 := iv.w1, v10 := iv.w2, v11 := iv.w3
      v12 := ctrLo, v13 := ctrHi, v14 := blockLen, v15 := flags }
  blake3CompressLoop 6 st m

/-- Pack 4 little-endian bytes (`0..255`) into a `UInt32`. -/
@[circuit_inline]
def u32OfBytes (b0 b1 b2 b3 : Nat) : UInt32 :=
  UInt32.ofNat (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)

/-- Unpack the 4 little-endian bytes of a `UInt32` onto `tail` (`StarkHash::b3_w4_onto`). -/
@[circuit_noinline]
def u32Onto (w : UInt32) (tail : ByteList) : ByteList :=
  let n := w.toNat
  let b0 := n % 256; let q1 := n / 256
  let b1 := q1 % 256; let q2 := q1 / 256
  let b2 := q2 % 256; let b3 := q2 / 256
  .cons b0 (.cons b1 (.cons b2 (.cons b3 tail)))

/-- Flatten an 8-word `Digest32` to 32 LE bytes onto `tail` (`StarkHash::b3_flatten_onto`). -/
@[circuit_inline]
def digest32Onto (h : Digest32) (tail : ByteList) : ByteList :=
  u32Onto h.w0 (u32Onto h.w1 (u32Onto h.w2 (u32Onto h.w3
    (u32Onto h.w4 (u32Onto h.w5 (u32Onto h.w6 (u32Onto h.w7 tail)))))))

/-- Convert two `UInt32` words to one `U64Bytes`. -/
@[circuit_noinline]
def u64OfTwoU32 (lo hi : UInt32) : U64Bytes :=
  let nl := lo.toNat
  let b0 := nl % 256; let ql1 := nl / 256
  let b1 := ql1 % 256; let ql2 := ql1 / 256
  let b2 := ql2 % 256; let b3 := ql2 / 256
  let nh := hi.toNat
  let b4 := nh % 256; let qh1 := nh / 256
  let b5 := qh1 % 256; let qh2 := qh1 / 256
  let b6 := qh2 % 256; let b7 := qh2 / 256
  { b0 := b0, b1 := b1, b2 := b2, b3 := b3, b4 := b4, b5 := b5, b6 := b6, b7 := b7 }

/-- Convert a `Digest32` to `DigestBytes` (`StarkHash::b3_to_digest`). -/
@[circuit_inline]
def digest32ToDigestBytes (h : Digest32) : DigestBytes :=
  { d0 := u64OfTwoU32 h.w0 h.w1
    d1 := u64OfTwoU32 h.w2 h.w3
    d2 := u64OfTwoU32 h.w4 h.w5
    d3 := u64OfTwoU32 h.w6 h.w7 }

/-- Prepend 32 bytes of `DigestBytes` onto `tail` (`StarkVerifier::digest_onto`). -/
@[circuit_inline]
def digestBytesOnto (d : DigestBytes) (tail : ByteList) : ByteList :=
  u64BytesOnto d.d0 (u64BytesOnto d.d1 (u64BytesOnto d.d2 (u64BytesOnto d.d3 tail)))

/-- Exact equality on `DigestBytes` (`StarkHash::digest_eq`). -/
@[circuit_inline]
def digestBytesEq (a b : DigestBytes) : Nat :=
  if u64BytesEq a.d0 b.d0 == 1 && u64BytesEq a.d1 b.d1 == 1 &&
     u64BytesEq a.d2 b.d2 == 1 && u64BytesEq a.d3 b.d3 == 1 then 1 else 0

/-- Exact equality on `Digest32`. -/
@[circuit_inline]
def digest32Eq (a b : Digest32) : Nat :=
  if a.w0 == b.w0 && a.w1 == b.w1 && a.w2 == b.w2 && a.w3 == b.w3 &&
     a.w4 == b.w4 && a.w5 == b.w5 && a.w6 == b.w6 && a.w7 == b.w7 then 1 else 0

/-- Pack 8 `UInt32` digest words into 8 `Nat` public words (`Blake3::pack_digest`,
matching `crates/stark-verifier/src/lib.rs::digest_words`). -/
@[circuit_inline]
def packDigest (h : Digest32) : Digest32Words :=
  { w0 := h.w0.toNat, w1 := h.w1.toNat, w2 := h.w2.toNat, w3 := h.w3.toNat
    w4 := h.w4.toNat, w5 := h.w5.toNat, w6 := h.w6.toNat, w7 := h.w7.toNat }

/-- Result of reading up to 4 bytes into one little-endian `UInt32` word (zero-padded). -/
structure TakeWordOut where
  word : UInt32
  got : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

/-- Structural-recursive helper popping up to `rem` LE bytes into a `UInt32` word
(zero nested join points in `takeBlock64`). -/
@[circuit_noinline]
def takeU32Aux (rem : Nat) (s : ByteList) (shift acc got : Nat) : TakeWordOut :=
  match rem with
  | 0 => { word := UInt32.ofNat acc, got := got, rest := s }
  | rem' + 1 =>
    match s with
    | .nil => { word := UInt32.ofNat acc, got := got, rest := .nil }
    | .cons b rest =>
      takeU32Aux rem' rest (shift * 256) (acc + (b % 256) * shift) (got + 1)
termination_by structural rem

/-- Pop up to 4 bytes from `s` into a zero-padded LE `UInt32` word. -/
@[circuit_inline]
def takeU32Word (s : ByteList) : TakeWordOut :=
  takeU32Aux 4 s 1 0 0

/-- Pop up to 64 bytes (16 LE `UInt32` words, zero-padded) from `s`. -/
@[circuit_noinline]
def takeBlock64 (s : ByteList) : BlockTakeResult :=
  let t0 := takeU32Word s;      let t1 := takeU32Word t0.rest
  let t2 := takeU32Word t1.rest; let t3 := takeU32Word t2.rest
  let t4 := takeU32Word t3.rest; let t5 := takeU32Word t4.rest
  let t6 := takeU32Word t5.rest; let t7 := takeU32Word t6.rest
  let t8 := takeU32Word t7.rest; let t9 := takeU32Word t8.rest
  let t10 := takeU32Word t9.rest; let t11 := takeU32Word t10.rest
  let t12 := takeU32Word t11.rest; let t13 := takeU32Word t12.rest
  let t14 := takeU32Word t13.rest; let t15 := takeU32Word t14.rest
  let len := t0.got + t1.got + t2.got + t3.got + t4.got + t5.got + t6.got + t7.got +
             t8.got + t9.got + t10.got + t11.got + t12.got + t13.got + t14.got + t15.got
  { block :=
      { m0 := t0.word, m1 := t1.word, m2 := t2.word, m3 := t3.word
        m4 := t4.word, m5 := t5.word, m6 := t6.word, m7 := t7.word
        m8 := t8.word, m9 := t9.word, m10 := t10.word, m11 := t11.word
        m12 := t12.word, m13 := t13.word, m14 := t14.word, m15 := t15.word }
    len := len
    rest := t15.rest }

/-- One tree-folding pass over `LayerStack`, matching `Blake3::next_layer` &
`StarkHash::b3_dk_next_layer`. -/
@[circuit_noinline]
def blake3NextLayer (keyCv : Digest32) (baseFlag : UInt32) (layer : LayerStack)
    (digest : Digest32) (isRoot : Nat) : NextLayerOut :=
  match layer with
  | .nil => { last := .some digest, layer := .nil }
  | .push rest other =>
    let recOut := blake3NextLayer keyCv baseFlag rest other 0
    match recOut.last with
    | .none => { last := .some digest, layer := recOut.layer }
    | .some prev =>
      let blk : Block16 :=
        { m0 := prev.w0, m1 := prev.w1, m2 := prev.w2, m3 := prev.w3
          m4 := prev.w4, m5 := prev.w5, m6 := prev.w6, m7 := prev.w7
          m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
          m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 }
      let flags :=
        match recOut.layer with
        | .nil =>
          if isRoot == 1 then UInt32.add baseFlag 12 else UInt32.add baseFlag 4
        | .push _ _ => UInt32.add baseFlag 4
      let merged := blake3Compress keyCv blk 0 0 64 flags
      { last := .none, layer := .push recOut.layer merged }
termination_by structural layer

/-- Fold a non-empty `LayerStack` to its single 8-word root digest
(`Blake3::compress_layer` / `StarkHash::b3_dk_compress_layer`). -/
@[circuit_noinline]
def blake3CompressLayerFuel (keyCv : Digest32) (baseFlag : UInt32) :
    Nat → LayerStack → Digest32
  | 0, layer =>
    match layer with
    | .nil => keyCv
    | .push _ d => d
  | fuel + 1, layer =>
    match layer with
    | .nil => keyCv
    | .push rest digest =>
      match rest with
      | .nil => digest
      | .push _ _ =>
        let step := blake3NextLayer keyCv baseFlag rest digest 1
        match step.last with
        | .none => blake3CompressLayerFuel keyCv baseFlag fuel step.layer
        | .some last => blake3CompressLayerFuel keyCv baseFlag fuel (.push step.layer last)
termination_by structural fuel => fuel

@[circuit_noinline]
def layerStackDepth : LayerStack → Nat
  | .nil => 0
  | .push rest _ => 1 + layerStackDepth rest
termination_by structural xs => xs

/-- Structural multi-block, multi-chunk BLAKE3 block loop matching
`Blake3::hash_blocks` & `StarkHash::b3_dk_hash_blocks`. -/
@[circuit_noinline]
def blake3HashBlocksFuel (keyCv : Digest32) (baseFlag : UInt32) :
    Nat → ByteList → Nat → UInt32 → UInt32 → Digest32 → LayerStack → LayerStack
  | 0, _, _, _, _, _, layer => layer
  | fuel + 1, input, blockNo, ctrLo, ctrHi, cv, layer =>
    let taken := takeBlock64 input
    let empty := match taken.rest with | .nil => 1 | .cons _ _ => 0
    let at15 := if blockNo == 15 then 1 else 0
    let startFlag := if blockNo == 0 then 1 else 0
    let endFlag := if empty == 1 || at15 == 1 then 2 else 0
    let isChunk0 := if ctrLo == 0 && ctrHi == 0 then 1 else 0
    let rootFlag := if empty == 1 && isChunk0 == 1 then 8 else 0
    let flags := UInt32.add baseFlag (UInt32.ofNat (startFlag + endFlag + rootFlag))
    let digest := blake3Compress cv taken.block ctrLo ctrHi (UInt32.ofNat taken.len) flags
    if empty == 1 then
      .push layer digest
    else if at15 == 1 then
      let nextLo := UInt32.add ctrLo 1
      let nextHi := if nextLo == 0 then UInt32.add ctrHi 1 else ctrHi
      blake3HashBlocksFuel keyCv baseFlag fuel taken.rest 0 nextLo nextHi keyCv (.push layer digest)
    else
      blake3HashBlocksFuel keyCv baseFlag fuel taken.rest (blockNo + 1) ctrLo ctrHi digest layer
termination_by structural fuel => fuel

/-- Full multi-block / multi-chunk BLAKE3 byte-stream hasher under arbitrary
chaining value `keyCv` and domain `baseFlag` (`0` for standard hash, `64` for
`derive_key_material`). -/
@[circuit_noinline]
def blake3HashBytesWithCv (keyCv : Digest32) (baseFlag : UInt32) (bytes : ByteList) : Digest32 :=
  let fuel := byteListLen bytes + 1
  let layer := blake3HashBlocksFuel keyCv baseFlag fuel bytes 0 0 0 keyCv .nil
  blake3CompressLayerFuel keyCv baseFlag (layerStackDepth layer + 1) layer

/-- Standard BLAKE3 hash of an arbitrary byte stream (`Blake3::hash`).
Annotated with `@[circuit_intrinsic "blake3.hash"]` so backends can either compile
the pure-Lean 7-round implementation directly or substitute a dedicated BLAKE3 chip. -/
@[circuit_intrinsic "blake3.hash"]
def blake3HashBytes (bytes : ByteList) : Digest32 :=
  blake3HashBytesWithCv blake3IV 0 bytes

/-- Protocol `v6` keyed transcript batch hash (`v6_transcript_batch_cv`, `baseFlag = 64`). -/
@[circuit_noinline]
def v6TranscriptBatchHash (bytes : ByteList) : Digest32 :=
  blake3HashBytesWithCv v6TranscriptBatchCv 64 bytes

/-- Flatten `rows : U64ListList` into canonical LE bytes while verifying every
word is `< p_GL` (`Pcs::rows_pop` + `StarkHash::b3_rows`). -/
structure FlattenRowsResult where
  ok : Nat
  bytes : ByteList
  deriving BEq, DecidableEq, Repr

@[circuit_noinline]
def flattenRowChecked (row : U64List) (tail : ByteList) : FlattenRowsResult :=
  match row with
  | .nil => { ok := 1, bytes := tail }
  | .cons x rest =>
    let r := flattenRowChecked rest tail
    let ok := if glLtPBytes x == 1 && r.ok == 1 then 1 else 0
    { ok := ok, bytes := u64BytesOnto x r.bytes }
termination_by structural row

@[circuit_noinline]
def flattenRowsChecked (rows : U64ListList) : FlattenRowsResult :=
  match rows with
  | .nil => { ok := 1, bytes := .nil }
  | .cons r rest =>
    let tailRes := flattenRowsChecked rest
    let rowRes := flattenRowChecked r tailRes.bytes
    let ok := if rowRes.ok == 1 && tailRes.ok == 1 then 1 else 0
    { ok := ok, bytes := rowRes.bytes }
termination_by structural rows

/-- Result of `v6MerkleLeafHashChecked`: `ok = 1` iff every opened Goldilocks word
in `rows` is canonical `< p_GL`, paired with its `v6_merkle_leaf_cv` digest. -/
structure LeafHashResult where
  ok : Nat
  digest : DigestBytes
  deriving BEq, DecidableEq, Repr

/-- Exact Protocol `v6` MMCS leaf hash (`StarkHash::b3_rows`, `v6_merkle_leaf_cv`, `baseFlag = 64`). -/
@[circuit_noinline]
def v6MerkleLeafHashChecked (rows : U64ListList) : LeafHashResult :=
  let flat := flattenRowsChecked rows
  let h := blake3HashBytesWithCv v6MerkleLeafCv 64 flat.bytes
  { ok := flat.ok, digest := digest32ToDigestBytes h }

/-- Unchecked convenience wrapper returning just the `v6` MMCS leaf digest. -/
@[circuit_inline]
def v6MerkleLeafHash (rows : U64ListList) : DigestBytes :=
  (v6MerkleLeafHashChecked rows).digest

/-- Pack two `U64Bytes` into four `UInt32` words (`Mmcs::mmcs_compress` block builder). -/
@[circuit_inline]
def u64LoU32 (x : U64Bytes) : UInt32 :=
  u32OfBytes x.b0 x.b1 x.b2 x.b3

@[circuit_inline]
def u64HiU32 (x : U64Bytes) : UInt32 :=
  u32OfBytes x.b4 x.b5 x.b6 x.b7

/-- Exact Protocol `v6` MMCS 2-to-1 compression (`Mmcs::mmcs_compress`):
1-block BLAKE3 compression of `a ‖ b` (64 bytes) under `v6MerkleCompressCv`, `flags = 75`. -/
@[circuit_noinline]
def v6MerkleCompress (a b : DigestBytes) : DigestBytes :=
  let blk : Block16 :=
    { m0 := u64LoU32 a.d0, m1 := u64HiU32 a.d0
      m2 := u64LoU32 a.d1, m3 := u64HiU32 a.d1
      m4 := u64LoU32 a.d2, m5 := u64HiU32 a.d2
      m6 := u64LoU32 a.d3, m7 := u64HiU32 a.d3
      m8 := u64LoU32 b.d0, m9 := u64HiU32 b.d0
      m10 := u64LoU32 b.d1, m11 := u64HiU32 b.d1
      m12 := u64LoU32 b.d2, m13 := u64HiU32 b.d2
      m14 := u64LoU32 b.d3, m15 := u64HiU32 b.d3 }
  digest32ToDigestBytes (blake3Compress v6MerkleCompressCv blk 0 0 64 75)

/-! ### Exact `CompressWrap` Statement Digest (`"ix/compress-wrap/v1\0"`) -/

/-- Exact 20-byte domain tag `"ix/compress-wrap/v1\0"` prepended onto `tail`,
matching `MultiStark/Modules/CompressWrap.lean` and `crates/stark-verifier/src/compress_wrap.rs`. -/
@[circuit_inline]
def statementDomainOnto (tail : ByteList) : ByteList :=
  .cons 105 (.cons 120 (.cons 47 (.cons 99 (.cons 111 (.cons 109 (.cons 112 (.cons 114
  (.cons 101 (.cons 115 (.cons 115 (.cons 45 (.cons 119 (.cons 114 (.cons 97 (.cons 112
  (.cons 47 (.cons 118 (.cons 49 (.cons 0 tail)))))))))))))))))))

/-- Exact 84-byte `CompressWrap` statement preimage:
`"ix/compress-wrap/v1\0" ‖ key_digest (32 B) ‖ claims_digest (32 B)`. -/
@[circuit_inline]
def statementPreimage (keyDigest claimsDigest : Digest32) : ByteList :=
  statementDomainOnto (digest32Onto keyDigest (digest32Onto claimsDigest .nil))

/-- Exact `CompressWrap` public statement digest words (`[Field; 8]` little-endian `UInt32`s). -/
@[circuit_noinline]
def computeStatementDigest (keyBytes claimsBytes : ByteList) : Digest32Words :=
  let keyDigest := blake3HashBytes keyBytes
  let claimsDigest := blake3HashBytes claimsBytes
  let pre := statementPreimage keyDigest claimsDigest
  packDigest (blake3HashBytes pre)

/-! ## Section 4: Exact Production `SystemDeserialize`, `Claims` & `ProofDeserialize` -/

/-! ### System Description ADTs (`SystemDeserialize.lean`) -/

/-- AIR constraint expression DAG node (`SystemDeserialize::SysNode`).
`var src off idx` encodes `src ∈ {0: prep, 1: main, 2: stage2}` and `off ∈ {0: cur, 1: next}`. -/
inductive SysNode where
  | const (val : Nat)
  | var (src off idx : Nat)
  | pub (idx : Nat)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving BEq, DecidableEq, Repr

inductive SysNodeList where
  | nil
  | cons (head : SysNode) (tail : SysNodeList)
  deriving BEq, DecidableEq, Repr

/-- One LogUp lookup descriptor (`SystemDeserialize::SysLookup`). -/
structure SysLookup where
  multNode : Nat
  args : NatList
  deriving BEq, DecidableEq, Repr

inductive SysLookupList where
  | nil
  | cons (head : SysLookup) (tail : SysLookupList)
  deriving BEq, DecidableEq, Repr

/-- Verified circuit descriptor (`SystemDeserialize::SysCircuit`). -/
structure SysCircuit where
  nodes : SysNodeList
  nodeCount : Nat
  zeros : NatList
  maxDegree : Nat
  lookups : SysLookupList
  lookupGroupSize : Nat
  mainWidth : Nat
  prepWidth : Nat
  prepHeight : Nat
  stage2Width : Nat
  deriving BEq, DecidableEq, Repr

inductive SysCircuitList where
  | nil
  | cons (head : SysCircuit) (tail : SysCircuitList)
  deriving BEq, DecidableEq, Repr

/-- Protocol `v6` FRI/STARK system parameters (`SystemDeserialize::SysParams`). -/
structure SysParams where
  logBlowup : Nat
  capHeight : Nat
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitPowBits : Nat
  queryPowBits : Nat
  deriving BEq, DecidableEq, Repr

inductive OptCommit where
  | noCommit
  | someCommit (cap : DigestBytesList)
  deriving BEq, DecidableEq, Repr

inductive OptIdx where
  | noIdx
  | someIdx (idx : Nat)
  deriving BEq, DecidableEq, Repr

inductive OptIdxList where
  | nil
  | cons (head : OptIdx) (tail : OptIdxList)
  deriving BEq, DecidableEq, Repr

/-- Complete deserialized verifying key (`SystemDeserialize::Sys`). -/
structure SysKey where
  params : SysParams
  transcriptLimbs : U64List
  circuits : SysCircuitList
  prepCommit : OptCommit
  prepIndices : OptIdxList
  deriving BEq, DecidableEq, Repr

/-! ### Batch Proof ADTs (`ProofDeserialize.lean`) -/

structure Commitments where
  stage1 : DigestBytesList
  stage2 : DigestBytesList
  quotient : DigestBytesList
  deriving BEq, DecidableEq, Repr

structure BatchMultiOpening where
  openedValues : U64List3
  openingProof : DigestBytesList
  deriving BEq, DecidableEq, Repr

inductive BatchMultiOpeningList where
  | nil
  | cons (head : BatchMultiOpening) (tail : BatchMultiOpeningList)
  deriving BEq, DecidableEq, Repr

structure CommitPhaseMultiStep where
  logArity : Nat
  siblingValues : ExtGlListList
  openingProof : DigestBytesList
  deriving BEq, DecidableEq, Repr

inductive CommitPhaseMultiStepList where
  | nil
  | cons (head : CommitPhaseMultiStep) (tail : CommitPhaseMultiStepList)
  deriving BEq, DecidableEq, Repr

structure FriProof where
  commitPhaseCommits : MerkleCapList
  commitPowWitnesses : U64List
  inputOpenings : BatchMultiOpeningList
  commitPhaseOpenings : CommitPhaseMultiStepList
  finalPoly : ExtGlList
  queryPowWitness : U64Bytes
  deriving BEq, DecidableEq, Repr

inductive PreprocessedOpt where
  | noPreprocessed
  | somePreprocessed (round : OpenedRound)
  deriving BEq, DecidableEq, Repr

structure ShardProof where
  active : NatList
  commitments : Commitments
  intermediateAccs : ExtGlList
  logDegrees : NatList
  openingProof : FriProof
  quotientOpened : OpenedRound
  preprocessedOpened : PreprocessedOpt
  stage1Opened : OpenedRound
  stage2Opened : OpenedRound
  deriving BEq, DecidableEq, Repr

inductive ShardProofList where
  | nil
  | cons (head : ShardProof) (tail : ShardProofList)
  deriving BEq, DecidableEq, Repr

structure ShardHeader where
  active : NatList
  stage1 : DigestBytesList
  logDegrees : NatList
  claims : U64ListList
  deriving BEq, DecidableEq, Repr

inductive ShardHeaderList where
  | nil
  | cons (head : ShardHeader) (tail : ShardHeaderList)
  deriving BEq, DecidableEq, Repr

structure BatchMessage where
  args : U64List
  multiplicity : U64Bytes
  deriving BEq, DecidableEq, Repr

inductive BatchMessageList where
  | nil
  | cons (head : BatchMessage) (tail : BatchMessageList)
  deriving BEq, DecidableEq, Repr

structure BatchProof where
  headers : ShardHeaderList
  messages : BatchMessageList
  proofs : ShardProofList
  deriving BEq, DecidableEq, Repr

/-! ### Monomorphic Parse-Result Structs (Zero Polymorphic `Option`/`Except`) -/

structure ParseNat where
  ok : Nat
  val : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseLimb where
  ok : Nat
  val : Nat
  limb : U64Bytes
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseU64 where
  ok : Nat
  val : U64Bytes
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseExt where
  ok : Nat
  val : ExtGl
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseDigest where
  ok : Nat
  val : DigestBytes
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseDigestList where
  ok : Nat
  val : DigestBytesList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCapList where
  ok : Nat
  val : MerkleCapList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseNatList where
  ok : Nat
  val : NatList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseU64List where
  ok : Nat
  val : U64List
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseU64ListList where
  ok : Nat
  val : U64ListList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseU64List3 where
  ok : Nat
  val : U64List3
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseExtList where
  ok : Nat
  val : ExtGlList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseExtListList where
  ok : Nat
  val : ExtGlListList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseOpenedRound where
  ok : Nat
  val : OpenedRound
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseNodes where
  ok : Nat
  val : SysNodeList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseLookup where
  ok : Nat
  val : SysLookup
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseLookups where
  ok : Nat
  val : SysLookupList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCircuit where
  ok : Nat
  val : SysCircuit
  limbs : U64List
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCircuits where
  ok : Nat
  val : SysCircuitList
  limbs : U64List
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseOptCommit where
  ok : Nat
  val : OptCommit
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseOptIdxs where
  ok : Nat
  val : OptIdxList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseSysParams where
  ok : Nat
  val : SysParams
  limbs : U64List
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseSysKey where
  ok : Nat
  val : SysKey
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCommitments where
  ok : Nat
  val : Commitments
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseBatchOpening where
  ok : Nat
  val : BatchMultiOpening
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseBatchOpenings where
  ok : Nat
  val : BatchMultiOpeningList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCommitStep where
  ok : Nat
  val : CommitPhaseMultiStep
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCommitSteps where
  ok : Nat
  val : CommitPhaseMultiStepList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseFriProof where
  ok : Nat
  val : FriProof
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParsePrepOpt where
  ok : Nat
  val : PreprocessedOpt
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseShardProof where
  ok : Nat
  val : ShardProof
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseShardProofs where
  ok : Nat
  val : ShardProofList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseShardHeader where
  ok : Nat
  val : ShardHeader
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseShardHeaders where
  ok : Nat
  val : ShardHeaderList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseBatchMessage where
  ok : Nat
  val : BatchMessage
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseBatchMessages where
  ok : Nat
  val : BatchMessageList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseBatchProof where
  ok : Nat
  val : BatchProof
  rest : ByteList
  deriving BEq, DecidableEq, Repr

/-! ### Default Dummy Values for Fail-Closed Error Paths -/

@[circuit_inline]
def dummyDigestBytes : DigestBytes :=
  { d0 := u64Zero, d1 := u64Zero, d2 := u64Zero, d3 := u64Zero }

@[circuit_inline]
def dummySysParams : SysParams :=
  { logBlowup := 0, capHeight := 0, logFinalPolyLen := 0, maxLogArity := 0
    numQueries := 0, commitPowBits := 0, queryPowBits := 0 }

@[circuit_inline]
def dummySysKey : SysKey :=
  { params := dummySysParams, transcriptLimbs := .nil, circuits := .nil
    prepCommit := .noCommit, prepIndices := .nil }

@[circuit_inline]
def dummySysCircuit : SysCircuit :=
  { nodes := .nil, nodeCount := 0, zeros := .nil, maxDegree := 0, lookups := .nil
    lookupGroupSize := 0, mainWidth := 0, prepWidth := 0, prepHeight := 0, stage2Width := 0 }

@[circuit_inline]
def dummyFriProof : FriProof :=
  { commitPhaseCommits := .nil, commitPowWitnesses := .nil, inputOpenings := .nil
    commitPhaseOpenings := .nil, finalPoly := .nil, queryPowWitness := u64Zero }

@[circuit_inline]
def dummyBatchProof : BatchProof :=
  { headers := .nil, messages := .nil, proofs := .nil }

/-! ### Primitive Byte-Stream Readers -/

/-- Structural-recursive LE reader of `rem` bytes (`< 256` each), avoiding ANF
multi-inline join-point fanout in `readU64LE`, `readDigest`, `readSysCircuit`, `readSystem`. -/
@[circuit_noinline]
def readLeNatAux (rem : Nat) (s : ByteList) (shift acc : Nat) : ParseNat :=
  match rem with
  | 0 => { ok := 1, val := acc, rest := s }
  | rem' + 1 =>
    match s with
    | .nil => { ok := 0, val := 0, rest := .nil }
    | .cons b rest =>
      if b < 256 then readLeNatAux rem' rest (shift * 256) (acc + b * shift)
      else { ok := 0, val := 0, rest := .nil }
termination_by structural rem

/-- Read one byte (`< 256`); fails closed on empty stream or non-byte `≥ 256`. -/
@[circuit_inline]
def readU8 (s : ByteList) : ParseNat :=
  readLeNatAux 1 s 1 0

/-- Read a little-endian `u16` (`SystemDeserialize::read_vk_u16`). -/
@[circuit_inline]
def readU16LE (s : ByteList) : ParseNat :=
  readLeNatAux 2 s 1 0

/-- Read a little-endian `u16` alongside its 8-byte transcript limb (`read_vk_u16_limb`). -/
@[circuit_noinline]
def readU16Limb (s : ByteList) : ParseLimb :=
  let r := readLeNatAux 2 s 1 0
  { ok := r.ok
    val := r.val
    limb := { b0 := r.val % 256, b1 := r.val / 256, b2 := 0, b3 := 0
              b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
    rest := r.rest }

/-- Read a little-endian `u32` alongside its 8-byte transcript limb (`read_vk_u32_limb`). -/
@[circuit_noinline]
def readU32Limb (s : ByteList) : ParseLimb :=
  let r := readLeNatAux 4 s 1 0
  { ok := r.ok, val := r.val, limb := u64BytesOfU32 r.val, rest := r.rest }

/-- Read a little-endian `u32` (`readU32LE`). -/
@[circuit_inline]
def readU32LE (s : ByteList) : ParseNat :=
  readLeNatAux 4 s 1 0

/-- Read an 8-byte little-endian `U64Bytes` (`read_vk_u64` / `ProofDeserialize::read_u64`). -/
@[circuit_noinline]
def readU64LE (s : ByteList) : ParseU64 :=
  let rLo := readLeNatAux 4 s 1 0
  let rHi := readLeNatAux 4 rLo.rest 1 0
  let lo := u64BytesOfU32 rLo.val
  let hi := u64BytesOfU32 rHi.val
  { ok := rLo.ok * rHi.ok
    val := { b0 := lo.b0, b1 := lo.b1, b2 := lo.b2, b3 := lo.b3
             b4 := hi.b0, b5 := hi.b1, b6 := hi.b2, b7 := hi.b3 }
    rest := rHi.rest }

/-- Read an 8-byte little-endian count (`ProofDeserialize::read_count`), rejecting
impossible counts (`hi32 != 0` or `count > remaining bytes`, protecting against DoS). -/
@[circuit_noinline]
def readCount (s : ByteList) : ParseNat :=
  let r := readU64LE s
  if r.ok == 0 then { ok := 0, val := 0, rest := .nil }
  else
    let u := r.val
    if u.b4 + u.b5 + u.b6 + u.b7 == 0 then
      let n := u.b0 + 256 * u.b1 + 65536 * u.b2 + 16777216 * u.b3
      if n ≤ byteListLen r.rest then
        { ok := 1, val := n, rest := r.rest }
      else
        { ok := 0, val := 0, rest := .nil }
    else
      { ok := 0, val := 0, rest := .nil }

/-- Read a canonical Goldilocks field element (`< p_GL`), rejecting `≥ p_GL`
(`SystemDeserialize::read_field`). -/
@[circuit_noinline]
def readGlCanonical (s : ByteList) : ParseNat :=
  let r := readU64LE s
  if r.ok * glLtPBytes r.val == 1 then
    { ok := 1, val := glValBytes r.val, rest := r.rest }
  else
    { ok := 0, val := 0, rest := .nil }

/-- Read a canonical cubic extension element `ExtGl` (3 canonical Goldilocks words,
matching `ProofDeserialize::read_ext_at`). -/
@[circuit_noinline]
def readExtGl (s : ByteList) : ParseExt :=
  let r0 := readGlCanonical s
  let r1 := readGlCanonical r0.rest
  let r2 := readGlCanonical r1.rest
  if r0.ok * r1.ok * r2.ok == 0 then { ok := 0, val := extZero, rest := .nil }
  else { ok := 1, val := { c0 := r0.val, c1 := r1.val, c2 := r2.val }, rest := r2.rest }

/-- Read a 32-byte digest (`4 × u64 LE`, `read_vk_digest` / `read_digest_at`). -/
@[circuit_noinline]
def readDigest (s : ByteList) : ParseDigest :=
  let r0 := readU64LE s
  let r1 := readU64LE r0.rest
  let r2 := readU64LE r1.rest
  let r3 := readU64LE r2.rest
  { ok := r0.ok * r1.ok * r2.ok * r3.ok
    val := { d0 := r0.val, d1 := r1.val, d2 := r2.val, d3 := r3.val }
    rest := r3.rest }

/-! ### Exact `SystemDeserialize` (`readSystem`) -/

@[circuit_noinline]
def readVkCapN (s : ByteList) : Nat → ParseDigestList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readDigest s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readVkCapN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

structure ParseOneNode where
  ok : Nat
  val : SysNode
  rest : ByteList
  deriving BEq, DecidableEq, Repr

@[circuit_noinline]
def readOneSysNode (s : ByteList) (nodeIdx : Nat) : ParseOneNode :=
  let bad : ParseOneNode := { ok := 0, val := .const 0, rest := .nil }
  let rt := readU8 s
  if rt.ok == 0 then bad
  else
    let tag := rt.val
    let s1 := rt.rest
    if tag == 0 then
      let rc := readU16LE s1
      { ok := rc.ok, val := .const rc.val, rest := rc.rest }
    else if tag == 1 then
      let rc := readGlCanonical s1
      { ok := rc.ok, val := .const rc.val, rest := rc.rest }
    else if tag == 2 then
      let ri := readU8 s1
      { ok := ri.ok, val := .pub ri.val, rest := ri.rest }
    else if tag == 3 then { ok := 1, val := .isFirstRow, rest := s1 }
    else if tag == 4 then { ok := 1, val := .isLastRow, rest := s1 }
    else if tag == 5 then { ok := 1, val := .isTransition, rest := s1 }
    else if tag < 9 then
      let ra := readU16LE s1
      let rb := readU16LE ra.rest
      if ra.ok * rb.ok == 1 && ra.val < nodeIdx && rb.val < nodeIdx then
        let nd := if tag == 6 then SysNode.add ra.val rb.val
                  else if tag == 7 then SysNode.sub ra.val rb.val
                  else SysNode.mul ra.val rb.val
        { ok := 1, val := nd, rest := rb.rest }
      else bad
    else if tag == 9 then
      let ra := readU16LE s1
      if ra.ok == 1 && ra.val < nodeIdx then
        { ok := 1, val := .neg ra.val, rest := ra.rest }
      else bad
    else if tag < 16 then
      let ri := readU16LE s1
      let d := tag - 10
      { ok := ri.ok, val := .var (d / 2) (d % 2) ri.val, rest := ri.rest }
    else bad

/-- Parse `n` `SysNode`s matching `SystemDeserialize::read_nodes_n` tags `0..15`
with strict DAG acyclicity (`a < nodeIdx`, `b < nodeIdx`) and canonical `Const` check. -/
@[circuit_noinline]
def readSysNodesN (s : ByteList) (n nodeIdx : Nat) : ParseNodes :=
  match n with
  | 0 => { ok := 1, val := .nil, rest := s }
  | n' + 1 =>
    let r := readOneSysNode s nodeIdx
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readSysNodesN r.rest n' (nodeIdx + 1)
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n

@[circuit_noinline]
def readNodeIdsN (s : ByteList) : Nat → ParseNatList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readU16LE s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readNodeIdsN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_noinline]
def readSysLookup (s : ByteList) : ParseLookup :=
  let rm := readU16LE s
  if rm.ok == 0 then { ok := 0, val := { multNode := 0, args := .nil }, rest := .nil }
  else
    let rac := readU16LE rm.rest
    if rac.ok == 0 then { ok := 0, val := { multNode := 0, args := .nil }, rest := .nil }
    else
      let rargs := readNodeIdsN rac.rest rac.val
      { ok := rargs.ok, val := { multNode := rm.val, args := rargs.val }, rest := rargs.rest }

@[circuit_noinline]
def readSysLookupsN (s : ByteList) : Nat → ParseLookups
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readSysLookup s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readSysLookupsN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

/-- Exact `SystemDeserialize::lookup_groups_count` (`ceil(n / k)`). -/
@[circuit_noinline]
def lookupGroupsCount : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, 0, k => 1 + lookupGroupsCount n (k - 1) k
  | n + 1, rem + 1, k => lookupGroupsCount n rem k
termination_by structural n => n

/-- Bit popcount of a byte (`0..255`), matching `SystemDeserialize::byte_popcount`. -/
@[circuit_inline]
def bytePopcount (b : Nat) : Nat :=
  let b0 := b % 2; let q1 := b / 2
  let b1 := q1 % 2; let q2 := q1 / 2
  let b2 := q2 % 2; let q3 := q2 / 2
  let b3 := q3 % 2; let q4 := q3 / 2
  let b4 := q4 % 2; let q5 := q4 / 2
  let b5 := q5 % 2; let q6 := q5 / 2
  let b6 := q6 % 2; let b7 := (q6 / 2) % 2
  b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7

/-- Exact `SystemDeserialize::read_sys_circuit` (branchless `ok` chaining -> O(1) join points). -/
@[circuit_noinline]
def readSysCircuit (s : ByteList) : ParseCircuit :=
  let bad : ParseCircuit := { ok := 0, val := dummySysCircuit, limbs := .nil, rest := .nil }
  let rmw := readU16Limb s
  let rpw := readU16Limb rmw.rest
  let rph := readU32Limb rpw.rest
  let rmd := readU16Limb rph.rest
  let rk  := readU8 rmd.rest
  let rnc := readU16LE rk.rest
  let rlp := readU16LE rnc.rest
  let hdrOk := rmw.ok * rpw.ok * rph.ok * rmd.ok * rk.ok * rnc.ok * rlp.ok
  let prepZeroMatch := (rpw.val == 0) == (rph.val == 0)
  let phPop :=
    bytePopcount rph.limb.b0 + bytePopcount rph.limb.b1 +
    bytePopcount rph.limb.b2 + bytePopcount rph.limb.b3
  if hdrOk == 0 || rk.val == 0 || rk.val ≥ 9 || rlp.val > rnc.val ||
      !prepZeroMatch || phPop > 1 then bad
  else
    let rnodes := readSysNodesN rlp.rest rnc.val 0
    let rzc := readU16LE rnodes.rest
    let rzeros := readNodeIdsN rzc.rest rzc.val
    let rlc := readU16LE rzeros.rest
    let rlks := readSysLookupsN rlc.rest rlc.val
    let bodyOk := rnodes.ok * rzc.ok * rzeros.ok * rlc.ok * rlks.ok
    if bodyOk == 0 then bad
    else
      let groups := lookupGroupsCount rlc.val 0 rk.val
      let gslots := if groups == 0 then 1 else groups
      let s2w := gslots + gslots + gslots
      let ccl := u64BytesOfU32 (rzc.val + s2w)
      let s2wl := u64BytesOfU32 s2w
      let kl := u64BytesOfU32 rk.val
      let shape7 : U64List :=
        .cons ccl (.cons rmd.limb (.cons rph.limb (.cons rpw.limb
          (.cons rmw.limb (.cons s2wl (.cons kl .nil))))))
      { ok := 1
        val :=
          { nodes := rnodes.val, nodeCount := rnc.val, zeros := rzeros.val
            maxDegree := rmd.val, lookups := rlks.val, lookupGroupSize := rk.val
            mainWidth := rmw.val, prepWidth := rpw.val, prepHeight := rph.val
            stage2Width := s2w }
        limbs := shape7
        rest := rlks.rest }

@[circuit_noinline]
def readSysCircuitsN (s : ByteList) : Nat → ParseCircuits
  | 0 => { ok := 1, val := .nil, limbs := .nil, rest := s }
  | n + 1 =>
    let rc := readSysCircuit s
    if rc.ok == 0 then { ok := 0, val := .nil, limbs := .nil, rest := .nil }
    else
      let t := readSysCircuitsN rc.rest n
      { ok := t.ok
        val := .cons rc.val t.val
        limbs := u64ListAppend rc.limbs t.limbs
        rest := t.rest }
termination_by structural n => n

@[circuit_noinline]
def readOptCommit (s : ByteList) : ParseOptCommit :=
  let rt := readU8 s
  if rt.ok == 0 then { ok := 0, val := .noCommit, rest := .nil }
  else if rt.val == 0 then
    { ok := 1, val := .noCommit, rest := rt.rest }
  else if rt.val == 1 then
    let rn := readU16LE rt.rest
    if rn.ok == 0 || rn.val != 1 then { ok := 0, val := .noCommit, rest := .nil }
    else
      let rc := readVkCapN rn.rest 1
      { ok := rc.ok, val := .someCommit rc.val, rest := rc.rest }
  else
    { ok := 0, val := .noCommit, rest := .nil }

@[circuit_noinline]
def readOptIdxN (s : ByteList) (hasCommit : Nat) : Nat → Nat → ParseOptIdxs
  | 0, _ => { ok := 1, val := .nil, rest := s }
  | n + 1, cnt =>
    let rv := readU16LE s
    if rv.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else if rv.val == 65535 then
      let t := readOptIdxN rv.rest hasCommit n cnt
      { ok := t.ok, val := .cons .noIdx t.val, rest := t.rest }
    else if hasCommit == 1 && rv.val == cnt then
      let t := readOptIdxN rv.rest hasCommit n (cnt + 1)
      { ok := t.ok, val := .cons (.someIdx rv.val) t.val, rest := t.rest }
    else
      { ok := 0, val := .nil, rest := .nil }
termination_by structural n => n

@[circuit_noinline]
def readSysParams (s : ByteList) : ParseSysParams :=
  let bad : ParseSysParams := { ok := 0, val := dummySysParams, limbs := .nil, rest := .nil }
  let r0 := readU16Limb s
  let r1 := readU16Limb r0.rest
  let r2 := readU16Limb r1.rest
  let r3 := readU16Limb r2.rest
  let r4 := readU16Limb r3.rest
  let r5 := readU16Limb r4.rest
  let r6 := readU16Limb r5.rest
  let ok := r0.ok * r1.ok * r2.ok * r3.ok * r4.ok * r5.ok * r6.ok
  if ok == 0 then bad
  else
    { ok := 1
      val :=
        { logBlowup := r0.val, capHeight := r1.val, logFinalPolyLen := r2.val
          maxLogArity := r3.val, numQueries := r4.val
          commitPowBits := r5.val, queryPowBits := r6.val }
      limbs :=
        .cons r0.limb (.cons r1.limb (.cons r2.limb (.cons r3.limb
          (.cons r4.limb (.cons r5.limb (.cons r6.limb .nil))))))
      rest := r6.rest }

/-- Exact `SystemDeserialize::read_system` with trailing-byte rejection.
Checks `proto_ver == 6`, `ext_deg == 3`, `fri_batching == 1`, constructs exact
`seed_head ++ shape_body` transcript limbs, and rejects any trailing bytes. -/
@[circuit_noinline]
def readSystem (s : ByteList) : ParseSysKey :=
  let bad : ParseSysKey := { ok := 0, val := dummySysKey, rest := .nil }
  let rProto := readU16LE s
  let rExt := readU16LE rProto.rest
  let rBatch := readU16LE rExt.rest
  let rVk := readDigest rBatch.rest
  let rParams := readSysParams rVk.rest
  let rn := readU16Limb rParams.rest
  let hdrOk := rProto.ok * rExt.ok * rBatch.ok * rVk.ok * rParams.ok * rn.ok
  if hdrOk == 0 || rProto.val != 6 || rExt.val != 3 || rBatch.val != 1 then bad
  else
    let rCircs := readSysCircuitsN rn.rest rn.val
    let rCommit := readOptCommit rCircs.rest
    let hasCommit := match rCommit.val with
      | .noCommit => 0
      | .someCommit _ => 1
    let rIdxs := readOptIdxN rCommit.rest hasCommit rn.val 0
    if rCircs.ok * rCommit.ok * rIdxs.ok == 0 then bad
    else
      -- Reject any trailing bytes!
      match rIdxs.rest with
      | .cons _ _ => bad
      | .nil =>
        let l0 := u64Zero
        let l1 : U64Bytes := { b0 := 1, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
        let l2 : U64Bytes := { b0 := 2, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
        let l3 : U64Bytes := { b0 := 3, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
        let seedHead : U64List :=
          .cons l3 (.cons l2 (.cons l0 (.cons l1 rParams.limbs)))
        let shapeBody : U64List :=
          .cons l3 (.cons l2 (.cons rVk.val.d0 (.cons rVk.val.d1
            (.cons rVk.val.d2 (.cons rVk.val.d3 (.cons rn.limb rCircs.limbs))))))
        { ok := 1
          val :=
            { params := rParams.val
              transcriptLimbs := u64ListAppend seedHead shapeBody
              circuits := rCircs.val
              prepCommit := rCommit.val
              prepIndices := rIdxs.val }
          rest := .nil }

/-! ### Exact `Claims` Deserializer (`StarkVerifier::read_claims` & `compress_wrap.rs::decode_claims`) -/

@[circuit_noinline]
def readCanonicalU64VecN (s : ByteList) : Nat → ParseU64List
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readU64LE s
    if r.ok == 0 || glLtPBytes r.val == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readCanonicalU64VecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_noinline]
def readClaimsN (s : ByteList) : Nat → ParseU64ListList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let rm := readCount s
    if rm.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let rv := readCanonicalU64VecN rm.rest rm.val
      if rv.ok == 0 then { ok := 0, val := .nil, rest := .nil }
      else
        let t := readClaimsN rv.rest n
        { ok := t.ok, val := .cons rv.val t.val, rest := t.rest }
termination_by structural n => n

/-- Exact `StarkVerifier::read_claims` with canonical `< p_GL` check & trailing-byte rejection. -/
@[circuit_noinline]
def readClaims (s : ByteList) : ParseU64ListList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else
    let rc := readClaimsN rn.rest rn.val
    if rc.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      match rc.rest with
      | .nil => rc
      | .cons _ _ => { ok := 0, val := .nil, rest := .nil }

/-! ### Exact `ProofDeserialize` (`readBatchProof`) -/

@[circuit_noinline]
def readU8VecN (s : ByteList) : Nat → ParseNatList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readU8 s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readU8VecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readU8Vec (s : ByteList) : ParseNatList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readU8VecN rn.rest rn.val

@[circuit_noinline]
def readU64VecN (s : ByteList) : Nat → ParseU64List
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readU64LE s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readU64VecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readU64Vec (s : ByteList) : ParseU64List :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readU64VecN rn.rest rn.val

@[circuit_noinline]
def readU64VecVecN (s : ByteList) : Nat → ParseU64ListList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readU64Vec s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readU64VecVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readU64VecVec (s : ByteList) : ParseU64ListList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readU64VecVecN rn.rest rn.val

@[circuit_noinline]
def readU64VecVecVecN (s : ByteList) : Nat → ParseU64List3
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readU64VecVec s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readU64VecVecVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readU64VecVecVec (s : ByteList) : ParseU64List3 :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readU64VecVecVecN rn.rest rn.val

@[circuit_noinline]
def readExtVecN (s : ByteList) : Nat → ParseExtList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readExtGl s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readExtVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readExtVec (s : ByteList) : ParseExtList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readExtVecN rn.rest rn.val

@[circuit_noinline]
def readExtVecVecN (s : ByteList) : Nat → ParseExtListList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readExtVec s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readExtVecVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readExtVecVec (s : ByteList) : ParseExtListList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readExtVecVecN rn.rest rn.val

@[circuit_noinline]
def readOpenedRoundN (s : ByteList) : Nat → ParseOpenedRound
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readExtVecVec s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readOpenedRoundN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readOpenedRound (s : ByteList) : ParseOpenedRound :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readOpenedRoundN rn.rest rn.val

@[circuit_noinline]
def readDigestVecN (s : ByteList) : Nat → ParseDigestList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readDigest s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readDigestVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readDigestVec (s : ByteList) : ParseDigestList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readDigestVecN rn.rest rn.val

/-- Exact `ProofDeserialize::read_merkle_cap_at` (enforces `n == 1`). -/
@[circuit_noinline]
def readMerkleCap (s : ByteList) : ParseDigestList :=
  let rn := readCount s
  if rn.ok == 0 || rn.val != 1 then { ok := 0, val := .nil, rest := .nil }
  else
    let rd := readDigest rn.rest
    if rd.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else { ok := 1, val := .cons rd.val .nil, rest := rd.rest }

@[circuit_noinline]
def readMerkleCapVecN (s : ByteList) : Nat → ParseCapList
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readMerkleCap s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readMerkleCapVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readMerkleCapVec (s : ByteList) : ParseCapList :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readMerkleCapVecN rn.rest rn.val

@[circuit_noinline]
def readCommitments (s : ByteList) : ParseCommitments :=
  let bad : ParseCommitments :=
    { ok := 0, val := { stage1 := .nil, stage2 := .nil, quotient := .nil }, rest := .nil }
  let r0 := readMerkleCap s;       if r0.ok == 0 then bad else
  let r1 := readMerkleCap r0.rest; if r1.ok == 0 then bad else
  let r2 := readMerkleCap r1.rest; if r2.ok == 0 then bad else
  { ok := 1, val := { stage1 := r0.val, stage2 := r1.val, quotient := r2.val }, rest := r2.rest }

@[circuit_noinline]
def readBatchOpening (s : ByteList) : ParseBatchOpening :=
  let bad : ParseBatchOpening :=
    { ok := 0, val := { openedValues := .nil, openingProof := .nil }, rest := .nil }
  let r0 := readU64VecVecVec s;   if r0.ok == 0 then bad else
  let r1 := readDigestVec r0.rest; if r1.ok == 0 then bad else
  { ok := 1, val := { openedValues := r0.val, openingProof := r1.val }, rest := r1.rest }

@[circuit_noinline]
def readBatchOpeningVecN (s : ByteList) : Nat → ParseBatchOpenings
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readBatchOpening s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readBatchOpeningVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readBatchOpeningVec (s : ByteList) : ParseBatchOpenings :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readBatchOpeningVecN rn.rest rn.val

@[circuit_noinline]
def readCommitPhaseStep (s : ByteList) : ParseCommitStep :=
  let bad : ParseCommitStep :=
    { ok := 0, val := { logArity := 0, siblingValues := .nil, openingProof := .nil }, rest := .nil }
  let r0 := readU8 s;              if r0.ok == 0 then bad else
  let r1 := readExtVecVec r0.rest; if r1.ok == 0 then bad else
  let r2 := readDigestVec r1.rest; if r2.ok == 0 then bad else
  { ok := 1
    val := { logArity := r0.val, siblingValues := r1.val, openingProof := r2.val }
    rest := r2.rest }

@[circuit_noinline]
def readCommitPhaseStepVecN (s : ByteList) : Nat → ParseCommitSteps
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readCommitPhaseStep s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readCommitPhaseStepVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readCommitPhaseStepVec (s : ByteList) : ParseCommitSteps :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readCommitPhaseStepVecN rn.rest rn.val

@[circuit_noinline]
def readFriProof (s : ByteList) : ParseFriProof :=
  let bad : ParseFriProof := { ok := 0, val := dummyFriProof, rest := .nil }
  let r0 := readMerkleCapVec s;        if r0.ok == 0 then bad else
  let r1 := readU64Vec r0.rest;        if r1.ok == 0 then bad else
  let r2 := readBatchOpeningVec r1.rest; if r2.ok == 0 then bad else
  let r3 := readCommitPhaseStepVec r2.rest; if r3.ok == 0 then bad else
  let r4 := readExtVec r3.rest;        if r4.ok == 0 then bad else
  let r5 := readU64LE r4.rest;         if r5.ok == 0 then bad else
  { ok := 1
    val :=
      { commitPhaseCommits := r0.val
        commitPowWitnesses := r1.val
        inputOpenings := r2.val
        commitPhaseOpenings := r3.val
        finalPoly := r4.val
        queryPowWitness := r5.val }
    rest := r5.rest }

@[circuit_noinline]
def readPreprocessedOpt (s : ByteList) : ParsePrepOpt :=
  let rt := readU8 s
  if rt.ok == 0 then { ok := 0, val := .noPreprocessed, rest := .nil }
  else if rt.val == 0 then { ok := 1, val := .noPreprocessed, rest := rt.rest }
  else if rt.val == 1 then
    let r := readOpenedRound rt.rest
    { ok := r.ok, val := .somePreprocessed r.val, rest := r.rest }
  else { ok := 0, val := .noPreprocessed, rest := .nil }

@[circuit_noinline]
def readShardProof (s : ByteList) : ParseShardProof :=
  let bad : ParseShardProof :=
    { ok := 0
      val :=
        { active := .nil, commitments := { stage1 := .nil, stage2 := .nil, quotient := .nil }
          intermediateAccs := .nil, logDegrees := .nil, openingProof := dummyFriProof
          quotientOpened := .nil, preprocessedOpened := .noPreprocessed
          stage1Opened := .nil, stage2Opened := .nil }
      rest := .nil }
  let ra := readU8Vec s;               if ra.ok == 0 then bad else
  let r0 := readCommitments ra.rest;   if r0.ok == 0 then bad else
  let r1 := readExtVec r0.rest;        if r1.ok == 0 then bad else
  let r2 := readU8Vec r1.rest;         if r2.ok == 0 then bad else
  let r3 := readFriProof r2.rest;      if r3.ok == 0 then bad else
  let r4 := readOpenedRound r3.rest;   if r4.ok == 0 then bad else
  let r5 := readPreprocessedOpt r4.rest; if r5.ok == 0 then bad else
  let r6 := readOpenedRound r5.rest;   if r6.ok == 0 then bad else
  let r7 := readOpenedRound r6.rest;   if r7.ok == 0 then bad else
  { ok := 1
    val :=
      { active := ra.val, commitments := r0.val, intermediateAccs := r1.val
        logDegrees := r2.val, openingProof := r3.val, quotientOpened := r4.val
        preprocessedOpened := r5.val, stage1Opened := r6.val, stage2Opened := r7.val }
    rest := r7.rest }

@[circuit_noinline]
def readShardProofVecN (s : ByteList) : Nat → ParseShardProofs
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readShardProof s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readShardProofVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readShardProofVec (s : ByteList) : ParseShardProofs :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readShardProofVecN rn.rest rn.val

@[circuit_noinline]
def u64ListAllLtP : U64List → Nat
  | .nil => 1
  | .cons x rest =>
    if glLtPBytes x == 1 then u64ListAllLtP rest else 0
termination_by structural xs => xs

@[circuit_noinline]
def u64ListListAllLtP : U64ListList → Nat
  | .nil => 1
  | .cons xs rest =>
    if u64ListAllLtP xs == 1 then u64ListListAllLtP rest else 0
termination_by structural xss => xss

@[circuit_noinline]
def readShardHeader (s : ByteList) : ParseShardHeader :=
  let bad : ParseShardHeader :=
    { ok := 0, val := { active := .nil, stage1 := .nil, logDegrees := .nil, claims := .nil }, rest := .nil }
  let r0 := readU8Vec s;           if r0.ok == 0 then bad else
  let r1 := readMerkleCap r0.rest; if r1.ok == 0 then bad else
  let r2 := readU8Vec r1.rest;     if r2.ok == 0 then bad else
  let r3 := readU64VecVec r2.rest; if r3.ok == 0 then bad else
  if u64ListListAllLtP r3.val == 0 then bad else
  { ok := 1
    val := { active := r0.val, stage1 := r1.val, logDegrees := r2.val, claims := r3.val }
    rest := r3.rest }

@[circuit_noinline]
def readShardHeaderVecN (s : ByteList) : Nat → ParseShardHeaders
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readShardHeader s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readShardHeaderVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readShardHeaderVec (s : ByteList) : ParseShardHeaders :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readShardHeaderVecN rn.rest rn.val

@[circuit_noinline]
def readBatchMessage (s : ByteList) : ParseBatchMessage :=
  let bad : ParseBatchMessage :=
    { ok := 0, val := { args := .nil, multiplicity := u64Zero }, rest := .nil }
  let r0 := readU64Vec s;     if r0.ok == 0 || u64ListAllLtP r0.val == 0 then bad else
  let r1 := readU64LE r0.rest; if r1.ok == 0 || glLtPBytes r1.val == 0 then bad else
  { ok := 1, val := { args := r0.val, multiplicity := r1.val }, rest := r1.rest }

@[circuit_noinline]
def readBatchMessageVecN (s : ByteList) : Nat → ParseBatchMessages
  | 0 => { ok := 1, val := .nil, rest := s }
  | n + 1 =>
    let r := readBatchMessage s
    if r.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else
      let t := readBatchMessageVecN r.rest n
      { ok := t.ok, val := .cons r.val t.val, rest := t.rest }
termination_by structural n => n

@[circuit_inline]
def readBatchMessageVec (s : ByteList) : ParseBatchMessages :=
  let rn := readCount s
  if rn.ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else readBatchMessageVecN rn.rest rn.val

/-- Exact `ProofDeserialize::read_batch` with canonicality checks & trailing-byte rejection. -/
@[circuit_noinline]
def readBatchProof (s : ByteList) : ParseBatchProof :=
  let bad : ParseBatchProof := { ok := 0, val := dummyBatchProof, rest := .nil }
  let r0 := readShardHeaderVec s;      if r0.ok == 0 then bad else
  let r1 := readBatchMessageVec r0.rest; if r1.ok == 0 then bad else
  let r2 := readShardProofVec r1.rest; if r2.ok == 0 then bad else
  match r2.rest with
  | .cons _ _ => bad
  | .nil =>
    { ok := 1
      val := { headers := r0.val, messages := r1.val, proofs := r2.val }
      rest := .nil }

/-! ### Canonical Binary Wire Serializers (for Round-Trip & Witness Construction) -/

def encodeU16LEOnto (v : Nat) (tail : ByteList) : ByteList :=
  .cons (v % 256) (.cons ((v / 256) % 256) tail)

def encodeU32LEOnto (v : Nat) (tail : ByteList) : ByteList :=
  let b0 := v % 256; let q1 := v / 256
  let b1 := q1 % 256; let q2 := q1 / 256
  let b2 := q2 % 256; let b3 := (q2 / 256) % 256
  .cons b0 (.cons b1 (.cons b2 (.cons b3 tail)))

def encodeCountOnto (n : Nat) (tail : ByteList) : ByteList :=
  u64BytesOnto (u64BytesOfU32 n) tail

def encodeExtGlOnto (e : ExtGl) (tail : ByteList) : ByteList :=
  u64BytesOnto (u64BytesOfNat e.c0)
    (u64BytesOnto (u64BytesOfNat e.c1)
      (u64BytesOnto (u64BytesOfNat e.c2) tail))

def encodeSysNodeOnto (nd : SysNode) (tail : ByteList) : ByteList :=
  match nd with
  | .const c =>
    if c < 65536 then .cons 0 (encodeU16LEOnto c tail)
    else .cons 1 (u64BytesOnto (u64BytesOfNat c) tail)
  | .pub idx => .cons 2 (.cons (idx % 256) tail)
  | .isFirstRow => .cons 3 tail
  | .isLastRow => .cons 4 tail
  | .isTransition => .cons 5 tail
  | .add a b => .cons 6 (encodeU16LEOnto a (encodeU16LEOnto b tail))
  | .sub a b => .cons 7 (encodeU16LEOnto a (encodeU16LEOnto b tail))
  | .mul a b => .cons 8 (encodeU16LEOnto a (encodeU16LEOnto b tail))
  | .neg a => .cons 9 (encodeU16LEOnto a tail)
  | .var src off idx =>
    let tag := 10 + src + src + off
    .cons tag (encodeU16LEOnto idx tail)

def encodeSysNodesOnto (ns : SysNodeList) (tail : ByteList) : ByteList :=
  match ns with
  | .nil => tail
  | .cons nd rest => encodeSysNodeOnto nd (encodeSysNodesOnto rest tail)
termination_by structural ns

def encodeNodeIdsOnto (ids : NatList) (tail : ByteList) : ByteList :=
  match ids with
  | .nil => tail
  | .cons id rest => encodeU16LEOnto id (encodeNodeIdsOnto rest tail)
termination_by structural ids

def encodeSysLookupsOnto (lks : SysLookupList) (tail : ByteList) : ByteList :=
  match lks with
  | .nil => tail
  | .cons lk rest =>
    encodeU16LEOnto lk.multNode
      (encodeU16LEOnto (natListLen lk.args)
        (encodeNodeIdsOnto lk.args (encodeSysLookupsOnto rest tail)))
termination_by structural lks

def sysNodeListLen : SysNodeList → Nat
  | .nil => 0
  | .cons _ rest => 1 + sysNodeListLen rest
termination_by structural xs => xs

def sysLookupListLen : SysLookupList → Nat
  | .nil => 0
  | .cons _ rest => 1 + sysLookupListLen rest
termination_by structural xs => xs

def sysCircuitListLen : SysCircuitList → Nat
  | .nil => 0
  | .cons _ rest => 1 + sysCircuitListLen rest
termination_by structural xs => xs

def encodeSysCircuitOnto (c : SysCircuit) (tail : ByteList) : ByteList :=
  let nc := sysNodeListLen c.nodes
  let zc := natListLen c.zeros
  let lc := sysLookupListLen c.lookups
  encodeU16LEOnto c.mainWidth
    (encodeU16LEOnto c.prepWidth
      (encodeU32LEOnto c.prepHeight
        (encodeU16LEOnto c.maxDegree
          (.cons (c.lookupGroupSize % 256)
            (encodeU16LEOnto nc
              (encodeU16LEOnto nc
                (encodeSysNodesOnto c.nodes
                  (encodeU16LEOnto zc
                    (encodeNodeIdsOnto c.zeros
                      (encodeU16LEOnto lc
                        (encodeSysLookupsOnto c.lookups tail)))))))))))

def encodeSysCircuitsOnto (cs : SysCircuitList) (tail : ByteList) : ByteList :=
  match cs with
  | .nil => tail
  | .cons c rest => encodeSysCircuitOnto c (encodeSysCircuitsOnto rest tail)
termination_by structural cs

def encodeOptCommitOnto (oc : OptCommit) (tail : ByteList) : ByteList :=
  match oc with
  | .noCommit => .cons 0 tail
  | .someCommit cap =>
    match cap with
    | .nil => .cons 0 tail
    | .cons d _ => .cons 1 (encodeU16LEOnto 1 (digestBytesOnto d tail))

def encodeOptIdxsOnto (ois : OptIdxList) (tail : ByteList) : ByteList :=
  match ois with
  | .nil => tail
  | .cons oi rest =>
    match oi with
    | .noIdx => encodeU16LEOnto 65535 (encodeOptIdxsOnto rest tail)
    | .someIdx idx => encodeU16LEOnto idx (encodeOptIdxsOnto rest tail)
termination_by structural ois

/-- Canonical binary encoding of a Protocol `v6` `SysKey` (`proto_ver=6, ext_deg=3, fri_batching=1`). -/
def encodeSystem (vkDigest : DigestBytes) (params : SysParams) (circuits : SysCircuitList)
    (commit : OptCommit) (prepIndices : OptIdxList) : ByteList :=
  let n := sysCircuitListLen circuits
  encodeU16LEOnto 6
    (encodeU16LEOnto 3
      (encodeU16LEOnto 1
        (digestBytesOnto vkDigest
          (encodeU16LEOnto params.logBlowup
            (encodeU16LEOnto params.capHeight
              (encodeU16LEOnto params.logFinalPolyLen
                (encodeU16LEOnto params.maxLogArity
                  (encodeU16LEOnto params.numQueries
                    (encodeU16LEOnto params.commitPowBits
                      (encodeU16LEOnto params.queryPowBits
                        (encodeU16LEOnto n
                          (encodeSysCircuitsOnto circuits
                            (encodeOptCommitOnto commit
                              (encodeOptIdxsOnto prepIndices .nil))))))))))))))

def encodeU64ListWithLenOnto (xs : U64List) (tail : ByteList) : ByteList :=
  encodeCountOnto (u64ListLen xs) (u64ListOnto xs tail)

def encodeClaimsBodyOnto (cs : U64ListList) (tail : ByteList) : ByteList :=
  match cs with
  | .nil => tail
  | .cons c rest => encodeU64ListWithLenOnto c (encodeClaimsBodyOnto rest tail)
termination_by structural cs

/-- Canonical binary encoding of public claims (`StarkVerifier::read_claims`). -/
def encodeClaims (cs : U64ListList) : ByteList :=
  encodeCountOnto (u64ListListLen cs) (encodeClaimsBodyOnto cs .nil)

def encodeU8VecBodyOnto (xs : NatList) (tail : ByteList) : ByteList :=
  match xs with
  | .nil => tail
  | .cons b rest => .cons (b % 256) (encodeU8VecBodyOnto rest tail)
termination_by structural xs

def encodeU8VecOnto (xs : NatList) (tail : ByteList) : ByteList :=
  encodeCountOnto (natListLen xs) (encodeU8VecBodyOnto xs tail)

def encodeDigestVecBodyOnto (ds : DigestBytesList) (tail : ByteList) : ByteList :=
  match ds with
  | .nil => tail
  | .cons d rest => digestBytesOnto d (encodeDigestVecBodyOnto rest tail)
termination_by structural ds

def encodeDigestVecOnto (ds : DigestBytesList) (tail : ByteList) : ByteList :=
  encodeCountOnto (digestBytesListLen ds) (encodeDigestVecBodyOnto ds tail)

def encodeCapVecBodyOnto (cs : MerkleCapList) (tail : ByteList) : ByteList :=
  match cs with
  | .nil => tail
  | .cons c rest => encodeDigestVecOnto c (encodeCapVecBodyOnto rest tail)
termination_by structural cs

def encodeCapVecOnto (cs : MerkleCapList) (tail : ByteList) : ByteList :=
  encodeCountOnto (merkleCapListLen cs) (encodeCapVecBodyOnto cs tail)

def encodeExtVecBodyOnto (es : ExtGlList) (tail : ByteList) : ByteList :=
  match es with
  | .nil => tail
  | .cons e rest => encodeExtGlOnto e (encodeExtVecBodyOnto rest tail)
termination_by structural es

def encodeExtVecOnto (es : ExtGlList) (tail : ByteList) : ByteList :=
  encodeCountOnto (extGlListLen es) (encodeExtVecBodyOnto es tail)

def encodeExtVecVecBodyOnto (ess : ExtGlListList) (tail : ByteList) : ByteList :=
  match ess with
  | .nil => tail
  | .cons es rest => encodeExtVecOnto es (encodeExtVecVecBodyOnto rest tail)
termination_by structural ess

def encodeExtVecVecOnto (ess : ExtGlListList) (tail : ByteList) : ByteList :=
  encodeCountOnto (extGlListListLen ess) (encodeExtVecVecBodyOnto ess tail)

def encodeOpenedRoundBodyOnto (r : OpenedRound) (tail : ByteList) : ByteList :=
  match r with
  | .nil => tail
  | .cons mat rest => encodeExtVecVecOnto mat (encodeOpenedRoundBodyOnto rest tail)
termination_by structural r

def encodeOpenedRoundOnto (r : OpenedRound) (tail : ByteList) : ByteList :=
  encodeCountOnto (openedRoundLen r) (encodeOpenedRoundBodyOnto r tail)

def encodeU64ListListOnto (xss : U64ListList) (tail : ByteList) : ByteList :=
  encodeCountOnto (u64ListListLen xss) (encodeClaimsBodyOnto xss tail)

def encodeU64List3BodyOnto (xsss : U64List3) (tail : ByteList) : ByteList :=
  match xsss with
  | .nil => tail
  | .cons xss rest => encodeU64ListListOnto xss (encodeU64List3BodyOnto rest tail)
termination_by structural xsss

def encodeU64List3Onto (xsss : U64List3) (tail : ByteList) : ByteList :=
  encodeCountOnto (u64List3Len xsss) (encodeU64List3BodyOnto xsss tail)

def batchOpeningListLen : BatchMultiOpeningList → Nat
  | .nil => 0
  | .cons _ rest => 1 + batchOpeningListLen rest
termination_by structural xs => xs

def encodeBatchOpeningsBodyOnto (bos : BatchMultiOpeningList) (tail : ByteList) : ByteList :=
  match bos with
  | .nil => tail
  | .cons bo rest =>
    encodeU64List3Onto bo.openedValues
      (encodeDigestVecOnto bo.openingProof (encodeBatchOpeningsBodyOnto rest tail))
termination_by structural bos

def encodeBatchOpeningsOnto (bos : BatchMultiOpeningList) (tail : ByteList) : ByteList :=
  encodeCountOnto (batchOpeningListLen bos) (encodeBatchOpeningsBodyOnto bos tail)

def commitStepListLen : CommitPhaseMultiStepList → Nat
  | .nil => 0
  | .cons _ rest => 1 + commitStepListLen rest
termination_by structural xs => xs

def encodeCommitStepsBodyOnto (cs : CommitPhaseMultiStepList) (tail : ByteList) : ByteList :=
  match cs with
  | .nil => tail
  | .cons st rest =>
    .cons (st.logArity % 256)
      (encodeExtVecVecOnto st.siblingValues
        (encodeDigestVecOnto st.openingProof (encodeCommitStepsBodyOnto rest tail)))
termination_by structural cs

def encodeCommitStepsOnto (cs : CommitPhaseMultiStepList) (tail : ByteList) : ByteList :=
  encodeCountOnto (commitStepListLen cs) (encodeCommitStepsBodyOnto cs tail)

def encodeFriProofOnto (fp : FriProof) (tail : ByteList) : ByteList :=
  encodeCapVecOnto fp.commitPhaseCommits
    (encodeU64ListWithLenOnto fp.commitPowWitnesses
      (encodeBatchOpeningsOnto fp.inputOpenings
        (encodeCommitStepsOnto fp.commitPhaseOpenings
          (encodeExtVecOnto fp.finalPoly
            (u64BytesOnto fp.queryPowWitness tail)))))

def encodePrepOptOnto (po : PreprocessedOpt) (tail : ByteList) : ByteList :=
  match po with
  | .noPreprocessed => .cons 0 tail
  | .somePreprocessed r => .cons 1 (encodeOpenedRoundOnto r tail)

def shardHeaderListLen : ShardHeaderList → Nat
  | .nil => 0
  | .cons _ rest => 1 + shardHeaderListLen rest
termination_by structural xs => xs

def encodeHeadersBodyOnto (hs : ShardHeaderList) (tail : ByteList) : ByteList :=
  match hs with
  | .nil => tail
  | .cons h rest =>
    encodeU8VecOnto h.active
      (encodeDigestVecOnto h.stage1
        (encodeU8VecOnto h.logDegrees
          (encodeU64ListListOnto h.claims (encodeHeadersBodyOnto rest tail))))
termination_by structural hs

def batchMessageListLen : BatchMessageList → Nat
  | .nil => 0
  | .cons _ rest => 1 + batchMessageListLen rest
termination_by structural xs => xs

def encodeMessagesBodyOnto (ms : BatchMessageList) (tail : ByteList) : ByteList :=
  match ms with
  | .nil => tail
  | .cons m rest =>
    encodeU64ListWithLenOnto m.args
      (u64BytesOnto m.multiplicity (encodeMessagesBodyOnto rest tail))
termination_by structural ms

def shardProofListLen : ShardProofList → Nat
  | .nil => 0
  | .cons _ rest => 1 + shardProofListLen rest
termination_by structural xs => xs

def encodeShardProofsBodyOnto (ps : ShardProofList) (tail : ByteList) : ByteList :=
  match ps with
  | .nil => tail
  | .cons p rest =>
    encodeU8VecOnto p.active
      (encodeDigestVecOnto p.commitments.stage1
        (encodeDigestVecOnto p.commitments.stage2
          (encodeDigestVecOnto p.commitments.quotient
            (encodeExtVecOnto p.intermediateAccs
              (encodeU8VecOnto p.logDegrees
                (encodeFriProofOnto p.openingProof
                  (encodeOpenedRoundOnto p.quotientOpened
                    (encodePrepOptOnto p.preprocessedOpened
                      (encodeOpenedRoundOnto p.stage1Opened
                        (encodeOpenedRoundOnto p.stage2Opened
                          (encodeShardProofsBodyOnto rest tail)))))))))))
termination_by structural ps

/-- Canonical binary encoding of a `BatchProof` (`ProofDeserialize::read_batch`). -/
def encodeBatchProof (b : BatchProof) : ByteList :=
  encodeCountOnto (shardHeaderListLen b.headers)
    (encodeHeadersBodyOnto b.headers
      (encodeCountOnto (batchMessageListLen b.messages)
        (encodeMessagesBodyOnto b.messages
          (encodeCountOnto (shardProofListLen b.proofs)
            (encodeShardProofsBodyOnto b.proofs .nil)))))

/-! ## Section 5: Pure-Lean Self-Checks (`#guard`) -/

-- 1. Exact Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$ constants & arithmetic
#guard glPrime == 18446744069414584321
#guard glInv2 == 9223372034707292161
#guard glMul 2 glInv2 == 1
#guard glGen32 == 1753635133440165772
#guard glExpPow2 glGen32 32 == 1
#guard glExpPow2 glGen32 31 == glPrime - 1
#guard glMul (glTwoAdicGen 2) glW2Inv == 1
#guard glMul (glTwoAdicGen 3) glW3Inv == 1
#guard glAdd (glPrime - 5) 12 == 7
#guard glSub 3 10 == glPrime - 7
#guard glMul (glPrime - 1) (glPrime - 1) == 1
#guard glMul 1234567890123456789 (glInv 1234567890123456789) == 1

-- 2. Canonical byte checks (< p_GL vs == p_GL vs == 2^64 - 1)
#guard glLtPBytes (u64BytesOfNat (glPrime - 1)) == 1
#guard glLtPBytes (u64BytesOfNat glPrime) == 0
#guard glLtPBytes { b0 := 255, b1 := 255, b2 := 255, b3 := 255, b4 := 255, b5 := 255, b6 := 255, b7 := 255 } == 0
#guard glValBytes (u64BytesOfNat (glPrime - 1)) == glPrime - 1
#guard glValBytes (u64BytesOfNat 12345678901234567890) == 12345678901234567890

-- 3. Cubic extension `ExtGl` & `checked def extInv` over real Goldilocks $p_{\mathrm{GL}}$
private def testExtA : ExtGl :=
  { c0 := 1234567890123456789, c1 := 9876543210987654321, c2 := 4242424242424242424 }
private def testExtB : ExtGl :=
  { c0 := 1111111111111111111, c1 := 2222222222222222222, c2 := 3333333333333333333 }

#guard extMul testExtA (extInv testExtA) == extOne
#guard extInv.check testExtA (extInv testExtA) == true
#guard extInv.check extZero (extInv extZero) == true
#guard extInv.check testExtA testExtB == false
#guard extMul testExtA testExtB == extMul testExtB testExtA

-- 4. Official BLAKE3 test vectors (0 B, 3 B "abc", 84 B `Statement::preimage`, 1025 B, 2049 B)
--    and all three Protocol `v6` `derive_key_context` CVs from first principles
private def zeroBlock16 : Block16 :=
  { m0 := 0, m1 := 0, m2 := 0, m3 := 0, m4 := 0, m5 := 0, m6 := 0, m7 := 0
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def v6LeafCtxBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x6d2f3676
    m4 := 0x6c6b7265, m5 := 0x656c2f65, m6 := 0x00006661, m7 := 0
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def v6CompressCtxBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x6d2f3676
    m4 := 0x6c6b7265, m5 := 0x6f632f65, m6 := 0x6572706d, m7 := 0x00007373
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def v6TranscriptCtxBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x742f3676
    m4 := 0x736e6172, m5 := 0x70697263, m6 := 0x61622f74, m7 := 0x00686374
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

#guard blake3Compress blake3IV v6LeafCtxBlock 0 0 26 43 == v6MerkleLeafCv
#guard blake3Compress blake3IV v6CompressCtxBlock 0 0 30 43 == v6MerkleCompressCv
#guard blake3Compress blake3IV v6TranscriptCtxBlock 0 0 31 43 == v6TranscriptBatchCv

private def officialEmptyDigest : Digest32 :=
  { w0 := 0xb94913af, w1 := 0xa6a1f9f5, w2 := 0xea4d40a0, w3 := 0x49c9dc36
    w4 := 0xc925cb9b, w5 := 0xb712c1ad, w6 := 0xca939acc, w7 := 0x62321fe4 }

private def officialAbcDigest : Digest32 :=
  { w0 := 0xacb33764, w1 := 0x33514638, w2 := 0x753bb6ff, w3 := 0xb58d3a27
    w4 := 0x4658c548, w5 := 0x03db795d, w6 := 0x6c9c35fd, w7 := 0x859dbdd5 }

-- Official 84-byte `CompressWrap::Statement::preimage` for `(BLAKE3(""), BLAKE3(""))`
private def officialEmptyStmtWords : Digest32Words :=
  { w0 := 0x56c3c91d, w1 := 0x981734c9, w2 := 0x064ca7e8, w3 := 0x7263304b
    w4 := 0x868f8d1e, w5 := 0xbc2fa8d9, w6 := 0xbc4def91, w7 := 0xf7f34a40 }

#guard blake3HashBytes .nil == officialEmptyDigest
#guard blake3HashBytes (.cons 97 (.cons 98 (.cons 99 .nil))) == officialAbcDigest
#guard byteListLen (statementPreimage officialEmptyDigest officialEmptyDigest) == 84
#guard computeStatementDigest .nil .nil == officialEmptyStmtWords

-- Multi-chunk BLAKE3 (1025 bytes = 2 chunks, 2049 bytes = 3 chunks)
private def seqBytesMod251Aux : Nat → Nat → ByteList → ByteList
  | 0, _, acc => acc
  | n + 1, idx, acc => seqBytesMod251Aux n (idx - 1) (.cons ((idx - 1) % 251) acc)
termination_by structural n => n

private def seqBytesMod251 (n : Nat) : ByteList :=
  seqBytesMod251Aux n n .nil

private def official1025Digest : Digest32 :=
  { w0 := 0xae7802d0, w1 := 0xb327eb47, w2 := 0x67cfae4f, w3 := 0x3f26feb4
    w4 := 0x2941d582, w5 := 0xd9ffc116, w6 := 0xfbb78c7c, w7 := 0x44844b81 }

private def official2049Digest : Digest32 :=
  { w0 := 0xf4724d5f, w1 := 0x825f7a0d, w2 := 0xb2a25cb1, w3 := 0xe31d4be4
    w4 := 0xc486efc2, w5 := 0x1a5cc926, w6 := 0x9587b6f0, w7 := 0x30305622 }

#guard blake3HashBytes (seqBytesMod251 1025) == official1025Digest
#guard blake3HashBytes (seqBytesMod251 2049) == official2049Digest

-- 5. Binary wire round-trip & negative rejection tests (`readSystem`, `readClaims`, `readBatchProof`)
private def sampleSysBytes : ByteList :=
  let vk : DigestBytes :=
    { d0 := u64BytesOfU32 11, d1 := u64BytesOfU32 22, d2 := u64BytesOfU32 33, d3 := u64BytesOfU32 44 }
  let params : SysParams :=
    { logBlowup := 1, capHeight := 0, logFinalPolyLen := 0, maxLogArity := 1
      numQueries := 1, commitPowBits := 0, queryPowBits := 0 }
  let nodes : SysNodeList :=
    .cons (.var 1 0 0) (.cons (.const (glPrime - 7)) (.cons (.sub 0 1) .nil))
  let circ : SysCircuit :=
    { nodes := nodes, nodeCount := 3, zeros := .cons 2 .nil, maxDegree := 2
      lookups := .nil, lookupGroupSize := 1, mainWidth := 1, prepWidth := 0
      prepHeight := 0, stage2Width := 3 }
  encodeSystem vk params (.cons circ .nil) .noCommit (.cons .noIdx .nil)

#guard (readSystem sampleSysBytes).ok == 1
#guard (readSystem (.cons 5 (match sampleSysBytes with | .nil => .nil | .cons _ t => t))).ok == 0  -- bad proto_ver
#guard (readSystem (byteListAppend sampleSysBytes (.cons 0 .nil))).ok == 0                          -- trailing byte

-- Structural preprocessed invariants (`prepWidth == 0 <=> prepHeight == 0`, power-of-two `prepHeight`,
-- and `NoCommit => NoIdx`)
private def mkPrepTestSysBytes (pw ph : Nat) (oc : OptCommit) (oi : OptIdx) : ByteList :=
  let vk : DigestBytes :=
    { d0 := u64BytesOfU32 11, d1 := u64BytesOfU32 22, d2 := u64BytesOfU32 33, d3 := u64BytesOfU32 44 }
  let params : SysParams :=
    { logBlowup := 1, capHeight := 0, logFinalPolyLen := 0, maxLogArity := 1
      numQueries := 1, commitPowBits := 0, queryPowBits := 0 }
  let nodes : SysNodeList :=
    .cons (.var 1 0 0) (.cons (.const (glPrime - 7)) (.cons (.sub 0 1) .nil))
  let circ : SysCircuit :=
    { nodes := nodes, nodeCount := 3, zeros := .cons 2 .nil, maxDegree := 2
      lookups := .nil, lookupGroupSize := 1, mainWidth := 1, prepWidth := pw
      prepHeight := ph, stage2Width := 3 }
  encodeSystem vk params (.cons circ .nil) oc (.cons oi .nil)

private def samplePrepCap : DigestBytesList :=
  .cons { d0 := u64BytesOfU32 1, d1 := u64BytesOfU32 2, d2 := u64BytesOfU32 3, d3 := u64BytesOfU32 4 } .nil

#guard (readSystem (mkPrepTestSysBytes 1 0 .noCommit .noIdx)).ok == 0                     -- prepWidth > 0, prepHeight = 0
#guard (readSystem (mkPrepTestSysBytes 0 4 .noCommit .noIdx)).ok == 0                     -- prepWidth = 0, prepHeight > 0
#guard (readSystem (mkPrepTestSysBytes 1 3 (.someCommit samplePrepCap) (.someIdx 0))).ok == 0 -- non-pow2 prepHeight
#guard (readSystem (mkPrepTestSysBytes 1 4 .noCommit (.someIdx 0))).ok == 0               -- SomeIdx without commit
#guard (readSystem (mkPrepTestSysBytes 1 4 (.someCommit samplePrepCap) (.someIdx 0))).ok == 1 -- valid preprocessed key

private def sampleClaimsBytes : ByteList :=
  encodeClaims (.cons (.cons (u64BytesOfNat 42) (.cons (u64BytesOfNat (glPrime - 1)) .nil)) .nil)

#guard (readClaims sampleClaimsBytes).ok == 1
#guard (readClaims (byteListAppend sampleClaimsBytes (.cons 1 .nil))).ok == 0 -- trailing byte
#guard (readClaims (encodeClaims (.cons (.cons (u64BytesOfNat glPrime) .nil) .nil))).ok == 0 -- non-canonical >= p_GL

end StarkWire
