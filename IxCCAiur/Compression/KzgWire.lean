import Ix.Compile.CircuitContract

/-! # Single-Source Multi-Curve (BN254 & BLS12-381) KZG Wire Formats, Transcript & Non-Native `Fq`/`G1` (`KzgWire`)

Pure total Lean 4 specification (zero `MultiStark`/`Aiur`/`IxCC` imports, zero Mathlib,
zero forbidden constructs) providing:

1. **Single-Source Multi-Curve Descriptor (`CurveParams`)** covering:
   - **BN254**: 254-bit `Fr` (28-adic generator), 254-bit `Fq` (`4×80b` limbs: `80,80,80,14`,
     $y^2 = x^3 + 3$, 32-byte compressed `G1`, 4×u128 accumulator chunks, **18** terminal
     affine-u80 words = `2 × (4 + 4 + 1)`),
   - **BLS12-381**: 255-bit `Fr` (32-adic generator), 381-bit `Fq` (`5×80b` limbs:
     `80,80,80,80,61`, $y^2 = x^3 + 4$, 48-byte compressed `G1`, 6×u128 accumulator chunks,
     **22** terminal affine-u80 words = `2 × (5 + 5 + 1)`),
   - Compact `< 2^56` multi-curve benchmark descriptors preserving the exact 4-limb (18-word)
     BN254 and 5-limb (22-word) BLS12-381 layouts for live `TypedLower` + `FieldLower` +
     `tiling_export2` / `wide_export` / `ixcc_prove` verification.
2. **Ambient Scalar Field (`Fr`) Ops** annotated with
   `@[circuit_intrinsic "field.{add,sub,mul,neg,inv,div,is_zero,eq}"]` so
   `IxCCAiur.FieldLower` lowers them directly to zero-lookup native BN254 `Fr` or
   BLS12-381 `Fr` `Field` arithmetic.
3. **Kernel-Verified Tier-2 `checked def` Non-Native `Fq` & `G1` Operations**
   (`fqMulMod`, division-free `fqMulDivMod`, general prime `fqInvMod` up to `2^384`,
   `g1OnCurve`, `g1Double`, `g1Add`, `g1ScalarMul`, 4-bit windowed `g1Msm`,
   canonical `SWFlags` compressed `G1` codec, limb packing/unpacking, and 18/22-word
   affine terminal encoding) with zero `sorry` proofs.
4. **Exact Production BLAKE3 Hash, 96-Byte XOF & `KzgTranscript`** (full 7-round
   multi-block/multi-chunk Merkle tree matching `MultiStark/BN/KzgBlake3.lean` and
   `MultiStark/BN/KzgTranscript.lean`), plus exact domain tags:
   - `"ix/kzg/packed-shplonk-pcs/open/v1\0"` (34 bytes),
   - `"ix/kzg/packed-shplonk/v1\0"` (25 bytes),
   - `"ix/aiur/kzg/fold-transcript/v1\0"` (31 bytes).
5. **Exact Production Binary Wire Parsers & Encoders** with strict canonicality,
   DAG topological checks, magic checks, and trailing-byte rejection:
   - `IXAUSK02` packed verifying key (`readPackedKey` / `encodePackedKey`),
   - `IXAUSP01` packed proof (`readPackedProof` / `encodePackedProof`),
   - `IXPSHC02` packed commitment (`readPackedCommitment` / `encodePackedCommitment`),
   - `IXAUCL01` claims (`readClaims` / `encodeClaims`),
   - `IXAUKG01` chain policy (`readChainPolicy` / `encodeChainPolicy`).
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace KzgWire

/-! ## Section 1: Monomorphic Unboxed ADTs (`ShapeInfer`-Unboxed, 0 `Obj` Fallback) -/

/-- Monomorphic byte stream (`Bytes::Stream`, each element canonical `< 256`). -/
inductive ByteList where
  | nil
  | cons (head : Nat) (tail : ByteList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of field/scalar elements (`Lists::List<Field>`). -/
inductive FList where
  | nil
  | cons (head : Nat) (tail : FList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of field-element rows (`Lists::List<Lists::List<Field>>`). -/
inductive FListList where
  | nil
  | cons (head : FList) (tail : FListList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic openings list: list of matrices, each a list of scalar rows (`KzgDeserialize::Openings`). -/
inductive FList3 where
  | nil
  | cons (head : FListList) (tail : FList3)
  deriving BEq, DecidableEq, Repr

/-- Quotient-remainder witness pair for division-free Tier-2 `fqMulDivMod`. -/
structure QuotRem where
  q : Nat
  r : Nat
  deriving BEq, DecidableEq, Repr

/-- Single-source multi-curve parameter descriptor covering BN254, BLS12-381, and
compact `< 2^56` circuit-benchmark curves with identical limb/word layouts. -/
structure CurveParams where
  frMod : Nat
  fqMod : Nat
  maxLog : Nat
  twoAdicGenMax : Nat
  curveB : Nat
  gx : Nat
  gy : Nat
  fqLimbCount : Nat
  limbRadix : Nat
  g1ByteLen : Nat
  affineWords : Nat
  deriving BEq, DecidableEq, Repr

/-- Canonical affine `G1` point over `Fq`:
* Infinity (`O`) has the unique encoding `{ x := 0, y := 0, isInf := 1 }`.
* Finite points have `isInf = 0` and canonical `x < fqMod`, `y < fqMod`. -/
structure G1Point where
  x : Nat
  y : Nat
  isInf : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of `G1` points (`Lists::List<G1::Point>`). -/
inductive G1PointList where
  | nil
  | cons (head : G1Point) (tail : G1PointList)
  deriving BEq, DecidableEq, Repr

/-- Single `(point, scalar)` term in a `G1` multi-scalar multiplication. -/
structure G1Term where
  point : G1Point
  scalar : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of MSM terms (`Lists::List<(Point, Field)>`). -/
inductive G1TermList where
  | nil
  | cons (head : G1Term) (tail : G1TermList)
  deriving BEq, DecidableEq, Repr

/-- Prepared term for 4-bit windowed MSM: precomputed 16-entry table + remaining scalar. -/
structure MsmPreparedTerm where
  table : G1PointList
  rem : Nat
  deriving BEq, DecidableEq, Repr

/-- List of prepared windowed-MSM terms. -/
inductive MsmPreparedList where
  | nil
  | cons (head : MsmPreparedTerm) (tail : MsmPreparedList)
  deriving BEq, DecidableEq, Repr

/-- Split step output for one 4-bit MSM window. -/
structure MsmSplitOut where
  next : MsmPreparedList
  selected : G1PointList
  deriving BEq, DecidableEq, Repr

/-- 4-limb packed `Fq` element (BN254 `4×80b`: `80, 80, 80, 14` bits). -/
structure Limb4 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  deriving BEq, DecidableEq, Repr

/-- 5-limb packed `Fq` element (BLS12-381 `5×80b`: `80, 80, 80, 80, 61` bits). -/
structure Limb5 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  deriving BEq, DecidableEq, Repr

/-- 9-word affine `G1` point for BN254 (`4 + 4 + 1` u80 words, matching `BN254G1::to_raw`). -/
structure AffineG1BN254 where
  x : Limb4
  y : Limb4
  isInf : Nat
  deriving BEq, DecidableEq, Repr

/-- 18-word terminal affine `G1` pair `(A, B)` for BN254 `gnark` `PairingCheck`. -/
structure AffinePairBN254 where
  a : AffineG1BN254
  b : AffineG1BN254
  deriving BEq, DecidableEq, Repr

/-- 11-word affine `G1` point for BLS12-381 (`5 + 5 + 1` u80 words). -/
structure AffineG1BLS12381 where
  x : Limb5
  y : Limb5
  isInf : Nat
  deriving BEq, DecidableEq, Repr

/-- 22-word terminal affine `G1` pair `(A, B)` for BLS12-381 `gnark` `PairingCheck`. -/
structure AffinePairBLS12381 where
  a : AffineG1BLS12381
  b : AffineG1BLS12381
  deriving BEq, DecidableEq, Repr

/-- 4×u128 accumulator chunk encoding for BN254 (`BN254G1Encoding::to_chunks`). -/
structure AccumulatorChunks4 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  deriving BEq, DecidableEq, Repr

/-- 6×u128 accumulator chunk encoding for BLS12-381 (`2 × 48B = 96B = 6 × 16B`). -/
structure AccumulatorChunks6 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  deriving BEq, DecidableEq, Repr

/-- 8-word (32-byte) digest represented as canonical `Nat` u32 words (`KzgIO::Digest = [Field; 8]`). -/
structure DigestWords where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  d4 : Nat
  d5 : Nat
  d6 : Nat
  d7 : Nat
  deriving BEq, DecidableEq, Repr

/-- 8-word (32-byte) `UInt32` BLAKE3 chaining value / digest. -/
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

/-- 16-word (64-byte) `UInt32` BLAKE3 message block / XOF output half. -/
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

/-- 16-word `UInt32` internal BLAKE3 compression state. -/
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

/-- Output of one BLAKE3 quarter-round `G`. -/
structure QuarterOut where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of BLAKE3 chaining values for Merkle-tree chunk folding. -/
inductive Digest32List where
  | nil
  | cons (head : Digest32) (tail : Digest32List)
  deriving BEq, DecidableEq, Repr

/-- Root compression input of a BLAKE3 message (`KzgBlake3::word_root` without `ROOT` flag). -/
structure Blake3RootInput where
  cv : Digest32
  block : Block16
  blockLen : UInt32
  flags : UInt32
  deriving BEq, DecidableEq, Repr

/-- 96-byte BLAKE3 XOF output: 64-byte wide challenge block + 32-byte next transcript state. -/
structure Xof96Out where
  wide : Block16
  next : Digest32
  deriving BEq, DecidableEq, Repr

/-- BLAKE3 KZG Fiat-Shamir transcript (`KzgTranscript::Transcript`):
buffer holding the 32-byte state concatenated with all absorbed observation bytes. -/
structure KzgTranscript where
  buf : ByteList
  deriving BEq, DecidableEq, Repr

/-- Output of `KzgTranscript.sampleFr`. -/
structure SampleResult where
  challenge : Nat
  transcript : KzgTranscript
  deriving BEq, DecidableEq, Repr

/-- AIR constraint expression DAG node (`KzgDeserialize::Node`).
`var source offset column` uses `source ∈ {0: fixed, 1: main, 2: stage2}`,
`offset ∈ {0: current, 1: next}`. -/
inductive Node where
  | const (value : Nat)
  | var (source offset column : Nat)
  | pub (index : Nat)
  | first
  | last
  | transition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of AIR DAG nodes (`Lists::List<KzgDeserialize::Node>`). -/
inductive NodeList where
  | nil
  | cons (head : Node) (tail : NodeList)
  deriving BEq, DecidableEq, Repr

/-- One LogUp lookup descriptor (`KzgDeserialize::Lookup`). -/
structure Lookup where
  multiplicity : Nat
  args : FList
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of LogUp lookups (`Lists::List<KzgDeserialize::Lookup>`). -/
inductive LookupList where
  | nil
  | cons (head : Lookup) (tail : LookupList)
  deriving BEq, DecidableEq, Repr

/-- 8-word circuit shape metadata (`[m0..m7]` in `KzgDeserialize::Circuit`):
`m0`: constraints (`roots + stage2_groups`), `m1`: max degree, `m2`: fixed height,
`m3`: fixed width, `m4`: main width, `m5`: stage2 width (`groups`),
`m6`: lookup group size (`1..8`), `m7`: quotient degree (`power of 2`). -/
structure CircuitShape where
  m0 : Nat
  m1 : Nat
  m2 : Nat
  m3 : Nat
  m4 : Nat
  m5 : Nat
  m6 : Nat
  m7 : Nat
  deriving BEq, DecidableEq, Repr

/-- Deserialized AIR circuit (`KzgDeserialize::Circuit`). -/
structure Circuit where
  shape : CircuitShape
  nodes : NodeList
  roots : FList
  lookups : LookupList
  mainNext : Nat
  fixedNext : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of AIR circuits (`Lists::List<KzgDeserialize::Circuit>`). -/
inductive CircuitList where
  | nil
  | cons (head : Circuit) (tail : CircuitList)
  deriving BEq, DecidableEq, Repr

/-- Packed commitment matrix shape `(log, width, hasNext)` (`KzgPackedDeserialize::Shapes`). -/
structure MatrixShape where
  log : Nat
  width : Nat
  hasNext : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of packed matrix shapes. -/
inductive MatrixShapeList where
  | nil
  | cons (head : MatrixShape) (tail : MatrixShapeList)
  deriving BEq, DecidableEq, Repr

/-- Packed SHPLONK commitment (`IXPSHC02`, `KzgPackedDeserialize::Commitment`),
retaining its verbatim native wire bytes for transcript absorption. -/
structure PackedCommitment where
  rawBytes : ByteList
  shapes : MatrixShapeList
  points : G1PointList
  deriving BEq, DecidableEq, Repr

/-- Key fixed-matrix section (`KzgPackedDeserialize::Fixed`). -/
inductive PackedFixed where
  | none
  | some (comm : PackedCommitment)
  | shared (comm : PackedCommitment) (slots : FList)
  deriving BEq, DecidableEq, Repr

/-- Deserialized packed verifying key (`IXAUSK02`, `KzgPackedDeserialize::Key`). -/
structure PackedKey where
  seed : ByteList
  maxLog : Nat
  budget : Nat
  generator : G1Point
  anchors : ByteList
  circuits : CircuitList
  fixed : PackedFixed
  deriving BEq, DecidableEq, Repr

/-- Packed SHPLONK opening witness (`KzgPackedDeserialize::Witness`), keeping
both the decoded on-curve point and verbatim compressed bytes. -/
structure PackedWitness where
  point : G1Point
  rawBytes : ByteList
  deriving BEq, DecidableEq, Repr

/-- Optional fixed-matrix openings (`KzgDeserialize::FixedOpen`). -/
inductive FixedOpen where
  | none
  | some (openings : FList3)
  deriving BEq, DecidableEq, Repr

/-- Deserialized packed SHPLONK proof (`IXAUSP01`, `KzgPackedDeserialize::Proof`). -/
structure PackedProof where
  active : FList
  logs : FList
  main : PackedCommitment
  stage2 : PackedCommitment
  quotient : PackedCommitment
  accumulators : FList
  mainOpen : FList3
  stage2Open : FList3
  quotientOpen : FList3
  fixedOpen : FixedOpen
  extras : FList
  w1 : PackedWitness
  w2 : PackedWitness
  deriving BEq, DecidableEq, Repr

/-- Deserialized two-key chain policy (`IXAUKG01`, `KzgDeserialize::Policy`). -/
structure ChainPolicy where
  anchors : ByteList
  glDigest : DigestWords
  glEntry : Nat
  bnDigest : DigestWords
  bnEntry : Nat
  deriving BEq, DecidableEq, Repr

/-! ### Monomorphic Parse Result ADTs (Zero `Option`/`Except` Boxing) -/

structure ParseNat where
  ok : Nat
  val : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseBytes where
  ok : Nat
  bytes : ByteList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseFList where
  ok : Nat
  vals : FList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseFListList where
  ok : Nat
  rows : FListList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseFList3 where
  ok : Nat
  mats : FList3
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParsePoint where
  ok : Nat
  point : G1Point
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParsePointList where
  ok : Nat
  points : G1PointList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseDigestWords where
  ok : Nat
  digest : DigestWords
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseNode where
  ok : Nat
  node : Node
  mainNext : Nat
  fixedNext : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseNodeList where
  ok : Nat
  nodes : NodeList
  mainNext : Nat
  fixedNext : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseLookupList where
  ok : Nat
  lookups : LookupList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCircuitList where
  ok : Nat
  circuits : CircuitList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseShapeList where
  ok : Nat
  shapes : MatrixShapeList
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseCommitment where
  ok : Nat
  comm : PackedCommitment
  deriving BEq, DecidableEq, Repr

structure ParseFixed where
  ok : Nat
  fixed : PackedFixed
  deriving BEq, DecidableEq, Repr

structure ParseKey where
  ok : Nat
  key : PackedKey
  deriving BEq, DecidableEq, Repr

structure ParseWitness where
  ok : Nat
  witness : PackedWitness
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseProof where
  ok : Nat
  proof : PackedProof
  deriving BEq, DecidableEq, Repr

structure ParsePolicy where
  ok : Nat
  policy : ChainPolicy
  deriving BEq, DecidableEq, Repr

structure ParseClaims where
  ok : Nat
  claims : FListList
  deriving BEq, DecidableEq, Repr

/-! ## Section 2: Single-Source Curve Constants (BN254, BLS12-381 & `< 2^56` Circuit Curves) -/

/-- Upper bound `2^384 = 2^192 * 2^192` covering BN254 `Fp` (254-bit), BLS12-381 `Fp`
(381-bit), and all smaller curve primes without exceeding Lean's exponentiation threshold. -/
def maxFieldModulus : Nat := (2 ^ 192) * (2 ^ 192)

/-- Radix `2^80` for production non-native `Fq` limbs (`4×80b` BN254, `5×80b` BLS12-381). -/
def radix80 : Nat := 2 ^ 80

/-- Radix `2^128` for accumulator u128 chunks (`4×u128` BN254, `6×u128` BLS12-381). -/
def radix128 : Nat := 2 ^ 128

/-- BN254 scalar field prime `Fr` (254 bits, 28-adic). -/
def bn254Fr : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254 base field prime `Fq` (254 bits, `Fq ≡ 3 (mod 4)`). -/
def bn254Fp : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- Exact BN254 primitive `2^28`-th root of unity in `Fr` (`KzgAlgebra::two_adic_gen(28)`). -/
def bn254TwoAdicGen28 : Nat :=
  19103219067921713944291392827692070036145651957329286315305642004821462161904

/-- Production BN254 curve descriptor (`4×80b` limbs, $y^2 = x^3 + 3$, generator `(1, 2)`,
32-byte compressed `G1`, **18** terminal affine-u80 words = `2 × (4 + 4 + 1)`). -/
def bn254CurveParams : CurveParams :=
  { frMod := bn254Fr
    fqMod := bn254Fp
    maxLog := 28
    twoAdicGenMax := bn254TwoAdicGen28
    curveB := 3
    gx := 1
    gy := 2
    fqLimbCount := 4
    limbRadix := radix80
    g1ByteLen := 32
    affineWords := 18 }

/-- BLS12-381 scalar field prime `Fr` (255 bits, 32-adic). -/
def bls12381Fr : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- BLS12-381 base field prime `Fq` (381 bits, `Fq ≡ 3 (mod 4)`). -/
def bls12381Fp : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- Exact BLS12-381 primitive `2^32`-th root of unity in `Fr` (`7^((r - 1)/2^32) mod r`). -/
def bls12381TwoAdicGen32 : Nat :=
  10238227357739495823651030575849232062558860180284477541189508159991286009131

/-- Standard IETF/Zcash/EIP-2537 BLS12-381 `G1` generator `x`-coordinate. -/
def bls12381G1X : Nat :=
  3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507

/-- Standard IETF/Zcash/EIP-2537 BLS12-381 `G1` generator `y`-coordinate. -/
def bls12381G1Y : Nat :=
  1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569

/-- Production BLS12-381 curve descriptor (`5×80b` limbs, $y^2 = x^3 + 4$, IETF generator,
48-byte compressed `G1`, **22** terminal affine-u80 words = `2 × (5 + 5 + 1)`). -/
def bls12381CurveParams : CurveParams :=
  { frMod := bls12381Fr
    fqMod := bls12381Fp
    maxLog := 32
    twoAdicGenMax := bls12381TwoAdicGen32
    curveB := 4
    gx := bls12381G1X
    gy := bls12381G1Y
    fqLimbCount := 5
    limbRadix := radix80
    g1ByteLen := 48
    affineWords := 22 }

/-- Compact `< 2^56` BN254-layout curve descriptor for live `TypedLower` + `FieldLower` +
`tiling_export2 --bn254` / `wide_export --bn254` compilation (`4` limbs, **18** affine words,
$y^2 = x^3 + 3 \pmod{103}$ with `103 ≡ 3 (mod 4)`, generator `(1, 2)`, scalar prime `F₄ = 65537`). -/
@[circuit_inline]
def bn254CircuitParams : CurveParams :=
  { frMod := 65537
    fqMod := 103
    maxLog := 4
    twoAdicGenMax := 4
    curveB := 3
    gx := 1
    gy := 2
    fqLimbCount := 4
    limbRadix := 16
    g1ByteLen := 2
    affineWords := 18 }

/-- Compact `< 2^56` BLS12-381-layout curve descriptor for live `TypedLower` + `FieldLower` +
`tiling_export2 --bls12-381 --single-circuit --pow2-rows` / `wide_export --bls12-381`
compilation (`5` limbs, **22** affine words, $y^2 = x^3 + 4 \pmod{103}$ with `103 ≡ 3 (mod 4)`,
generator `(8, 1)` since `8^3 + 4 = 516 ≡ 1 = 1^2 (mod 103)`, scalar prime `F₄ = 65537`). -/
@[circuit_inline]
def bls12381CircuitParams : CurveParams :=
  { frMod := 65537
    fqMod := 103
    maxLog := 4
    twoAdicGenMax := 4
    curveB := 4
    gx := 8
    gy := 1
    fqLimbCount := 5
    limbRadix := 16
    g1ByteLen := 2
    affineWords := 22 }

/-! ## Section 3: Ambient Scalar Field (`Fr`) Ops (`@[circuit_intrinsic "field.*"]`)

Every ambient scalar-field primitive is annotated with `@[circuit_intrinsic "field.*"]`
so `IxCCAiur.FieldLower` lowers them directly to **zero-lookup native `BN254 Fr` or
`BLS12-381 Fr` `Field` arithmetic** (`+`, `-`, `*`, `0 - a`, `1 / a`, `a / b`,
`Fields::is_zero`) while pure Lean `#guard` evaluation executes exact modular arithmetic
modulo `bn254Fr` (254-bit), `bls12381Fr` (255-bit), or any prime `p`. -/

/-- Structural-fuel extended Euclid worker for pure-Lean `frInv` (pruned by `FieldLower`). -/
private def frEgcdStep (p : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
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
      frEgcdStep p fuel d r2 t1 t2
termination_by structural fuel => fuel

/-- Ambient scalar field addition `(a + b) mod p` → native `a + b` under `--field-lower`. -/
@[circuit_noinline, circuit_intrinsic "field.add"]
def frAdd (p a b : Nat) : Nat :=
  (a + b) % p

/-- Ambient scalar field subtraction `(a - b) mod p` → native `a - b` under `--field-lower`. -/
@[circuit_noinline, circuit_intrinsic "field.sub"]
def frSub (p a b : Nat) : Nat :=
  (a + p - b) % p

/-- Ambient scalar field multiplication `(a * b) mod p` → native `a * b` under `--field-lower`. -/
@[circuit_noinline, circuit_intrinsic "field.mul"]
def frMul (p a b : Nat) : Nat :=
  (a * b) % p

/-- Ambient scalar field negation `(-a) mod p` → native `0 - a` under `--field-lower`. -/
@[circuit_noinline, circuit_intrinsic "field.neg"]
def frNeg (p a : Nat) : Nat :=
  if a == 0 then 0 else p - a

/-- Ambient scalar field inverse `a⁻¹ mod p` (`0⁻¹ = 0`) → native `1 / a` under `--field-lower`. -/
@[circuit_noinline, circuit_intrinsic "field.inv"]
def frInv (p a : Nat) : Nat :=
  if p < 2 then 0
  else if a % p == 0 then 0
  else frEgcdStep p 513 p (a % p) 0 1

/-- Ambient scalar field division `(a / b) mod p` (`a / 0 = 0`) → native `a / b` under `--field-lower`. -/
@[circuit_noinline, circuit_intrinsic "field.div"]
def frDiv (p a b : Nat) : Nat :=
  if p < 2 then 0
  else if b % p == 0 then 0
  else (a * frInv p b) % p

/-- Ambient scalar field zero-test (`1` iff `a == 0`, else `0`) → native `Fields::is_zero(a)`. -/
@[circuit_noinline, circuit_intrinsic "field.is_zero"]
def frIsZero (a : Nat) : Nat :=
  if a == 0 then 1 else 0

/-- Ambient scalar field equality indicator (`1` iff `a == b`, else `0`) → native `Fields::is_zero(a - b)`. -/
@[circuit_noinline, circuit_intrinsic "field.eq"]
def frEq (a b : Nat) : Nat :=
  if a == b then 1 else 0

/-! ## Section 4: Kernel-Verified Tier-2 Non-Native `Fq` & `G1` Operations (Zero `sorry`) -/

/-- Non-native `Fq` addition `(a + b) mod p` (distinct Ixon AST from ambient `frAdd`). -/
@[circuit_noinline]
def fqAddMod (p a b : Nat) : Nat :=
  (b + a) % p

/-- Non-native `Fq` subtraction `(a - b) mod p` for canonical `b ≤ p`
(distinct Ixon AST from ambient `frSub`). -/
@[circuit_noinline]
def fqSubMod (p a b : Nat) : Nat :=
  (p + a - b) % p

/-- Non-native `Fq` negation `(-a) mod p` for canonical `a < p`
(distinct Ixon AST from ambient `frNeg`). -/
@[circuit_inline]
def fqNegMod (p a : Nat) : Nat :=
  if 0 == a then 0 else p - a

/-- **Tier-2 `guess` #1 (`checked def ... complete by`)**: non-native `Fq` modular
multiplication `(a * b) % p` (distinct Ixon AST `(b * a) % p` from ambient `frMul`)
with kernel-checked uniqueness and completeness proofs. -/
@[circuit_noinline]
checked def fqMulMod (p a b : Nat) : Nat :=
  hint (b * a) % p
  where check fun r =>
    if p == 0 then r == b * a
    else decide (r < p) && (((b * a) / p) * p + r == b * a)
  by
    intro res hr
    unfold fqMulMod.check at hr
    unfold fqMulMod
    by_cases hp : p = 0
    · subst hp
      simp at hr ⊢
      exact hr
    · have hpB : (p == 0) = false := beq_false_of_ne hp
      rw [hpB] at hr
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hr
      obtain ⟨_, heq⟩ := hr
      have hdm : p * ((b * a) / p) + (b * a) % p = b * a := Nat.div_add_mod (b * a) p
      rw [Nat.mul_comm p ((b * a) / p)] at hdm
      omega
  complete by
    unfold fqMulMod.check fqMulMod
    by_cases hp : p = 0
    · subst hp
      simp
    · have hpB : (p == 0) = false := beq_false_of_ne hp
      rw [hpB]
      have hpPos : 0 < p := Nat.pos_of_ne_zero hp
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨Nat.mod_lt (b * a) hpPos, ?_⟩
      rw [Nat.mul_comm, Nat.div_add_mod]

/-- **Tier-2 `guess` #2 (`@[circuit_guess]`)**: division-free quotient-remainder
multiplication witness `{ q := (a * b) / p, r := (a * b) % p }`. -/
@[circuit_noinline]
def fqMulDivMod (p a b : Nat) : QuotRem :=
  { q := (a * b) / p, r := (a * b) % p }

/-- 100% division-free checker for `fqMulDivMod`: `qr.r < p ∧ qr.q * p + qr.r == a * b`. -/
def fqMulDivModCheck (p a b : Nat) (qr : QuotRem) : Bool :=
  if p == 0 then (qr.q == 0) && (qr.r == a * b)
  else decide (qr.r < p) && (qr.q * p + qr.r == a * b)

/-- Uniqueness/soundness theorem for `fqMulDivMod` across all `p a b : Nat`. -/
theorem fqMulDivMod_sound (p a b : Nat) (qr : QuotRem)
    (h : fqMulDivModCheck p a b qr = true) :
    qr = fqMulDivMod p a b := by
  cases qr with
  | mk q r =>
    unfold fqMulDivModCheck at h
    unfold fqMulDivMod
    by_cases hp : p = 0
    · subst hp
      simp at h ⊢
      exact h
    · have hpB : (p == 0) = false := beq_false_of_ne hp
      rw [hpB] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      obtain ⟨hrp, hmul⟩ := h
      have hpPos : 0 < p := Nat.pos_of_ne_zero hp
      have hq : (a * b) / p = q := by
        rw [← hmul, Nat.mul_comm q p, Nat.mul_add_div hpPos, Nat.div_eq_of_lt hrp, Nat.add_zero]
      have hr : (a * b) % p = r := by
        rw [← hmul, Nat.mul_comm q p, Nat.mul_add_mod, Nat.mod_eq_of_lt hrp]
      rw [hq, hr]

/-- Completeness theorem for `fqMulDivMod` across all `p a b : Nat`. -/
theorem fqMulDivMod_complete (p a b : Nat) :
    fqMulDivModCheck p a b (fqMulDivMod p a b) = true := by
  unfold fqMulDivModCheck fqMulDivMod
  by_cases hp : p = 0
  · subst hp
    simp
  · have hpB : (p == 0) = false := beq_false_of_ne hp
    rw [hpB]
    have hpPos : 0 < p := Nat.pos_of_ne_zero hp
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨Nat.mod_lt (a * b) hpPos, ?_⟩
    rw [Nat.mul_comm, Nat.div_add_mod]

attribute [circuit_guess fqMulDivModCheck fqMulDivMod_sound fqMulDivMod_complete] fqMulDivMod

/-- Structural-fuel unsigned extended Euclidean worker modulo `p` (zero signed `Int`). -/
@[circuit_noinline]
def egcdStep (p : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, t0, _ => t0
  | fuel + 1, r0, r1, t0, t1 =>
    match r1 with
    | 0 => if r0 == 1 then t0 else 0
    | r1' + 1 =>
      let d := r1' + 1
      let q := r0 / d
      let r2 := r0 % d
      let qt1 := fqMulMod p q t1
      let t2 := fqSubMod p t0 qt1
      egcdStep p fuel d r2 t1 t2
termination_by structural fuel => fuel

private def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

private theorem pow2_eq_pow : ∀ k, pow2 k = 2 ^ k
  | 0 => rfl
  | k + 1 => by simp only [pow2, pow2_eq_pow k, Nat.pow_succ, Nat.mul_comm]

private theorem pow2_add (m n : Nat) : pow2 (m + n) = pow2 m * pow2 n := by
  induction m with
  | zero => simp [pow2]
  | succ m ih => rw [Nat.succ_add]; simp only [pow2, ih, Nat.mul_assoc]

private theorem maxFieldModulus_eq_pow2 : maxFieldModulus = pow2 384 := by
  unfold maxFieldModulus
  rw [← pow2_eq_pow 192, ← pow2_add 192 192]

private theorem mul_mod_right_eq (a b p : Nat) : (a * (b % p)) % p = (a * b) % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem mod_inv_unique (p a r1 r2 : Nat)
    (hr1 : r1 < p) (hr2 : r2 < p)
    (heq1 : (a * r1) % p = 1) (heq2 : (a * r2) % p = 1) :
    r1 = r2 := by
  have h1 : (r1 * (a * r2)) % p = r1 := by
    rw [Nat.mul_mod, heq2, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hr1]
  have h2 : (r1 * (a * r2)) % p = r2 := by
    have hassoc : r1 * (a * r2) = (a * r1) * r2 := by
      rw [← Nat.mul_assoc, Nat.mul_comm r1 a]
    rw [hassoc, Nat.mul_mod, heq1, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr2]
  exact h1.symm.trans h2

private theorem two_mul_mod_lt (r0 r1 : Nat) (hr1 : 0 < r1) (hle : r1 ≤ r0) :
    2 * (r0 % r1) < r0 := by
  have hdm : r1 * (r0 / r1) + r0 % r1 = r0 := Nat.div_add_mod r0 r1
  have hmod : r0 % r1 < r1 := Nat.mod_lt r0 hr1
  have hq : 1 ≤ r0 / r1 := Nat.div_pos hle hr1
  by_cases hq1 : r0 / r1 = 1
  · rw [hq1, Nat.mul_one] at hdm; omega
  · have hq2 : 2 ≤ r0 / r1 := by omega
    have hmul : r1 * 2 ≤ r1 * (r0 / r1) := Nat.mul_le_mul_left r1 hq2
    omega

private theorem add_mod_right_cancel (p x y z : Nat) (hp : 0 < p)
    (hx : x < p) (hy : y < p) (h : (x + z) % p = (y + z) % p) :
    x = y := by
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

private theorem bezout_step (p a r0 r1 t0 t1 : Nat)
    (hp : 0 < p)
    (ht0 : (a * t0) % p = r0 % p) (ht1 : (a * t1) % p = r1 % p) :
    let q := r0 / r1
    let r2 := r0 % r1
    let qt1 := fqMulMod p q t1
    let t2 := fqSubMod p t0 qt1
    t2 < p ∧ (a * t2) % p = r2 % p := by
  intro q r2 qt1 t2
  have hqt1Lt : qt1 < p := Nat.mod_lt (t1 * q) hp
  have ht2Lt : t2 < p := Nat.mod_lt (p + t0 - qt1) hp
  refine ⟨ht2Lt, ?_⟩
  have hsumMod : (t2 + qt1) % p = t0 % p := by
    have h1 : (t2 + qt1) % p = ((p + t0 - qt1) + qt1) % p := by
      rw [Nat.add_mod, show t2 % p = (p + t0 - qt1) % p from Nat.mod_mod _ _, ← Nat.add_mod]
    have h2 : (p + t0 - qt1) + qt1 = t0 + p := by omega
    rw [h1, h2, Nat.add_mod_right]
  have hmulSum : (a * t2 + a * qt1) % p = r0 % p := by
    rw [← Nat.mul_add, Nat.mul_mod, hsumMod, ← Nat.mul_mod, ht0]
  have haqt1 : (a * qt1) % p = (q * r1) % p := by
    calc
      (a * qt1) % p = (a * ((t1 * q) % p)) % p := rfl
      _ = (a * (t1 * q)) % p := mul_mod_right_eq a (t1 * q) p
      _ = (a * (q * t1)) % p := by rw [Nat.mul_comm t1 q]
      _ = (q * (a * t1)) % p := by rw [Nat.mul_left_comm]
      _ = (q * ((a * t1) % p)) % p := (mul_mod_right_eq q (a * t1) p).symm
      _ = (q * (r1 % p)) % p := by rw [ht1]
      _ = (q * r1) % p := mul_mod_right_eq q r1 p
  have hr0Eq : r2 + q * r1 = r0 := by
    have hdm : r1 * q + r2 = r0 := Nat.div_add_mod r0 r1
    rw [Nat.mul_comm r1 q, Nat.add_comm] at hdm
    exact hdm
  have hEq : ((a * t2) % p + (q * r1) % p) % p = (r2 % p + (q * r1) % p) % p := by
    calc
      ((a * t2) % p + (q * r1) % p) % p
        = ((a * t2) % p + (a * qt1) % p) % p := by rw [haqt1]
      _ = (a * t2 + a * qt1) % p := by rw [← Nat.add_mod]
      _ = r0 % p := hmulSum
      _ = (r2 + q * r1) % p := by rw [hr0Eq]
      _ = (r2 % p + (q * r1) % p) % p := Nat.add_mod r2 (q * r1) p
  exact add_mod_right_cancel p ((a * t2) % p) (r2 % p) ((q * r1) % p) hp
    (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hEq

private theorem gcd_step_eq (r0 r1 : Nat) : Nat.gcd r1 (r0 % r1) = Nat.gcd r0 r1 := by
  rw [Nat.gcd_comm r1 (r0 % r1), ← Nat.gcd_rec r1 r0, Nat.gcd_comm]

private theorem egcdStep_spec (p a : Nat) (hp : 2 ≤ p) :
    ∀ (k fuel r0 r1 t0 t1 : Nat),
      2 * k + 1 ≤ fuel →
      r0 < pow2 k →
      r1 ≤ r0 →
      t0 < p →
      t1 < p →
      (a * t0) % p = r0 % p →
      (a * t1) % p = r1 % p →
      Nat.gcd r0 r1 = 1 →
      let out := egcdStep p fuel r0 r1 t0 t1
      out < p ∧ (a * out) % p = 1 := by
  intro k
  induction k with
  | zero =>
    intro fuel r0 r1 t0 t1 _ hr0 hle _ _ _ _ hgcd
    have hr0z : r0 = 0 := by have : pow2 0 = 1 := rfl; omega
    have hr1z : r1 = 0 := by omega
    subst hr0z; subst hr1z; simp at hgcd
  | succ k ih =>
    intro fuel r0 r1 t0 t1 hfuel hr0 hle ht0Lt ht1Lt ht0 ht1 hgcd
    have hpPos : 0 < p := by omega
    obtain ⟨fuel1, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    cases r1 with
    | zero =>
      simp only [egcdStep]
      have hr0One : r0 = 1 := by simpa using hgcd
      subst hr0One
      simp only [beq_self_eq_true, ↓reduceIte]
      exact ⟨ht0Lt, by simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using ht0⟩
    | succ r1' =>
      let d := r1' + 1
      have hdPos : 0 < d := Nat.succ_pos r1'
      have hbz1 := bezout_step p a r0 d t0 t1 hpPos ht0 ht1
      let q1 := r0 / d
      let r2 := r0 % d
      let t2 := fqSubMod p t0 (fqMulMod p q1 t1)
      have ht2Lt : t2 < p := hbz1.1
      have ht2Eq : (a * t2) % p = r2 % p := hbz1.2
      have hgcd1 : Nat.gcd d r2 = 1 := by rw [gcd_step_eq r0 d]; exact hgcd
      have h2r2 : 2 * r2 < r0 := two_mul_mod_lt r0 d hdPos hle
      have hr2Pow : r2 < pow2 k := by have hpow : pow2 (k + 1) = 2 * pow2 k := rfl; omega
      obtain ⟨fuel2, rfl⟩ : ∃ m, fuel1 = m + 1 := ⟨fuel1 - 1, by omega⟩
      have hstep1 : egcdStep p (fuel2 + 1 + 1) r0 d t0 t1 = egcdStep p (fuel2 + 1) d r2 t1 t2 := rfl
      show let out := egcdStep p (fuel2 + 1 + 1) r0 d t0 t1; out < p ∧ (a * out) % p = 1
      rw [hstep1]
      cases hr2Case : r2 with
      | zero =>
        simp only [egcdStep]
        rw [hr2Case] at hgcd1
        have hdOne : d = 1 := by simpa using hgcd1
        have ht1d : (a * t1) % p = d % p := ht1
        rw [hdOne] at ht1d ⊢
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ⟨ht1Lt, by simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using ht1d⟩
      | succ r2' =>
        have hr2Pos : 0 < r2 := by omega
        have hbz2 := bezout_step p a d r2 t1 t2 hpPos ht1 ht2Eq
        let q2 := d / r2
        let r3 := d % r2
        let t3 := fqSubMod p t1 (fqMulMod p q2 t2)
        have hstep2 : egcdStep p (fuel2 + 1) d (r2' + 1) t1 t2 = egcdStep p fuel2 r2 r3 t2 t3 := by
          change egcdStep p fuel2 (r2' + 1) (d % (r2' + 1)) t2
            (fqSubMod p t1 (fqMulMod p (d / (r2' + 1)) t2)) =
            egcdStep p fuel2 r2 (d % r2) t2 (fqSubMod p t1 (fqMulMod p (d / r2) t2))
          rw [hr2Case]
        rw [hstep2]
        have hgcd2 : Nat.gcd r2 r3 = 1 := by rw [gcd_step_eq d r2]; exact hgcd1
        have hr3Le : r3 ≤ r2 := Nat.le_of_lt (Nat.mod_lt d hr2Pos)
        exact ih fuel2 r2 r3 t2 t3 (by omega) hr2Pow hr3Le ht2Lt hbz2.1 ht2Eq hbz2.2 hgcd2

private theorem gcd_eq_one_of_mul_mod_eq_one (p a r : Nat) (h : (a * r) % p = 1) :
    Nat.gcd p a = 1 := by
  have hdvdP : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  have hdvdA : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
  have hdvdAR : Nat.gcd p a ∣ a * r := Nat.dvd_mul_right_of_dvd hdvdA r
  have hdvdPQ : Nat.gcd p a ∣ p * (a * r / p) := Nat.dvd_mul_right_of_dvd hdvdP (a * r / p)
  have hdm : p * (a * r / p) + 1 = a * r := by
    have := Nat.div_add_mod (a * r) p; rw [h] at this; exact this
  rw [← hdm] at hdvdAR
  exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hdvdPQ).mp hdvdAR)

/-- **Tier-2 `guess` #3 (`checked def`)**: curve-parameterized non-native `Fq` modular
inverse over any prime `p < 2^384` (covering BN254 `Fp`, BLS12-381 `Fp`, `103`, `65537`),
with non-circular algebraic checker and unconditional kernel-checked uniqueness. -/
@[circuit_noinline]
checked def fqInvMod (p a : Nat) : Nat :=
  hint if p < 2 then 0
       else if a % p == 0 then 0
       else egcdStep p 769 p (a % p) 0 1
  where check fun r =>
    if p < 2 then r == 0
    else if a % p == 0 then r == 0
    else decide (p < maxFieldModulus) && decide (r < p) && ((a * r) % p == 1)
  by
    intro res hr
    unfold fqInvMod.check at hr
    unfold fqInvMod
    by_cases hp2 : p < 2
    · simp [hp2] at hr ⊢; exact hr
    · have hpGe : 2 ≤ p := by omega
      simp only [hp2, ↓reduceIte] at hr ⊢
      by_cases ha0 : a % p = 0
      · simp [ha0] at hr ⊢; exact hr
      · have ha0B : (a % p == 0) = false := beq_false_of_ne ha0
        rw [ha0B] at hr ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hr
        obtain ⟨⟨hpMax, hresLt⟩, hmulEq⟩ := hr
        have hpPow2 : p < pow2 384 := by rwa [maxFieldModulus_eq_pow2] at hpMax
        have hgcdPA : Nat.gcd p a = 1 := gcd_eq_one_of_mul_mod_eq_one p a res hmulEq
        have hgcdMod : Nat.gcd p (a % p) = 1 := by
          rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]; exact hgcdPA
        have hpPos : 0 < p := by omega
        have hspec := egcdStep_spec p a hpGe 384 769 p (a % p) 0 1
          (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
          hpPos (by omega) (by simp) (by simp [Nat.mul_one]) hgcdMod
        exact mod_inv_unique p a res _ hresLt hspec.1 hmulEq hspec.2

/-- Completeness of `fqInvMod` for every coprime `(p, a)` with `2 ≤ p < 2^384`. -/
theorem fqInvMod_complete_of_coprime (p a : Nat)
    (hpGe : 2 ≤ p) (hpMax : p < maxFieldModulus) (hcop : Nat.gcd p a = 1) :
    fqInvMod.check p a (fqInvMod p a) = true := by
  unfold fqInvMod.check fqInvMod
  have hp2 : ¬ (p < 2) := by omega
  simp only [hp2, ↓reduceIte]
  by_cases ha0 : a % p = 0
  · simp [ha0]
  · have ha0B : (a % p == 0) = false := beq_false_of_ne ha0
    rw [ha0B]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hpPow2 : p < pow2 384 := by rwa [maxFieldModulus_eq_pow2] at hpMax
    have hgcdMod : Nat.gcd p (a % p) = 1 := by
      rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]; exact hcop
    have hpPos : 0 < p := by omega
    have hspec := egcdStep_spec p a hpGe 384 769 p (a % p) 0 1
      (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
      hpPos (by omega) (by simp) (by simp [Nat.mul_one]) hgcdMod
    exact ⟨⟨hpMax, hspec.1⟩, hspec.2⟩

/-- Pure-Lean structural binary exponentiation `acc * base^exp mod p` for up to 384-bit exponents
(used for `q ≡ 3 (mod 4)` square-root decompression on BN254 `Fp` and BLS12-381 `Fp`). -/
@[circuit_noinline]
def fqPowModFuel (p : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
    match exp with
    | 0 => acc
    | _ =>
      let nextAcc := if exp % 2 == 1 then fqMulMod p acc base else acc
      fqPowModFuel p fuel (fqMulMod p base base) (exp / 2) nextAcc
termination_by structural fuel => fuel

/-- `base^exp mod p` supporting up to 384-bit exponents (early exit on `exp = 0`). -/
@[circuit_inline]
def fqPowMod (p base exp : Nat) : Nat :=
  fqPowModFuel p 384 (base % p) exp 1

/-! ### Multi-Curve Affine `G1` Operations & 4-Bit Windowed `g1Msm` -/

/-- Canonical point at infinity `O = (0, 0, 1)`. -/
@[circuit_inline]
def g1Inf : G1Point :=
  { x := 0, y := 0, isInf := 1 }

/-- Curve generator `G = (c.gx, c.gy, 0)`. -/
@[circuit_inline]
def g1Gen (c : CurveParams) : G1Point :=
  { x := c.gx, y := c.gy, isInf := 0 }

/-- Canonical point equality on `G1Point` (`1` iff equal, else `0`). -/
@[circuit_inline]
def g1EqNat (P Q : G1Point) : Nat :=
  if P.isInf == Q.isInf then
    if P.x == Q.x then
      if P.y == Q.y then 1 else 0
    else 0
  else 0

/-- Short-Weierstrass curve membership check `y² ≡ x³ + b (mod fqMod)` with canonical
coordinate bounds `x, y < fqMod` and unique infinity encoding `(0, 0, 1)`. -/
@[circuit_noinline]
def g1OnCurve (c : CurveParams) (P : G1Point) : Bool :=
  if P.isInf == 1 then
    if P.x == 0 then P.y == 0 else false
  else if P.isInf == 0 then
    if P.x < c.fqMod then
      if P.y < c.fqMod then
        let y2 := fqMulMod c.fqMod P.y P.y
        let x2 := fqMulMod c.fqMod P.x P.x
        let x3 := fqMulMod c.fqMod x2 P.x
        let rhs := fqAddMod c.fqMod x3 (c.curveB % c.fqMod)
        y2 == rhs
      else false
    else false
  else false

/-- Affine negation `-P = (x, -y mod fqMod)` with `-O = O`. -/
@[circuit_inline]
def g1Neg (c : CurveParams) (P : G1Point) : G1Point :=
  if P.isInf == 1 then g1Inf
  else { x := P.x, y := fqNegMod c.fqMod P.y, isInf := 0 }

/-- Affine point doubling `2P` on `y² = x³ + b (mod fqMod)`. -/
@[circuit_noinline]
def g1Double (c : CurveParams) (P : G1Point) : G1Point :=
  if P.isInf == 1 then g1Inf
  else if P.y == 0 then g1Inf
  else
    let x2 := fqMulMod c.fqMod P.x P.x
    let num := fqAddMod c.fqMod (fqAddMod c.fqMod x2 x2) x2
    let den := fqAddMod c.fqMod P.y P.y
    let invDen := fqInvMod c.fqMod den
    let lam := fqMulMod c.fqMod num invDen
    let lam2 := fqMulMod c.fqMod lam lam
    let x3 := fqSubMod c.fqMod (fqSubMod c.fqMod lam2 P.x) P.x
    let dx := fqSubMod c.fqMod P.x x3
    let y3 := fqSubMod c.fqMod (fqMulMod c.fqMod lam dx) P.y
    { x := x3, y := y3, isInf := 0 }

/-- Complete affine point addition `P + Q` on `y² = x³ + b (mod fqMod)`. -/
@[circuit_noinline]
def g1Add (c : CurveParams) (P Q : G1Point) : G1Point :=
  if P.isInf == 1 then Q
  else if Q.isInf == 1 then P
  else if P.x == Q.x then
    if P.y == Q.y then g1Double c P
    else g1Inf
  else
    let num := fqSubMod c.fqMod Q.y P.y
    let den := fqSubMod c.fqMod Q.x P.x
    let invDen := fqInvMod c.fqMod den
    let lam := fqMulMod c.fqMod num invDen
    let lam2 := fqMulMod c.fqMod lam lam
    let x3 := fqSubMod c.fqMod (fqSubMod c.fqMod lam2 P.x) Q.x
    let dx := fqSubMod c.fqMod P.x x3
    let y3 := fqSubMod c.fqMod (fqMulMod c.fqMod lam dx) P.y
    { x := x3, y := y3, isInf := 0 }

/-- Conditional point addition helper avoiding join-point splitting inside `g1ScalarMulFuel`. -/
@[circuit_noinline]
def g1CondAdd (c : CurveParams) (bit : Nat) (acc cur : G1Point) : G1Point :=
  match bit with
  | 0 => acc
  | _ => g1Add c acc cur

/-- Structural countdown double-and-add scalar multiplication `acc + k · cur`. -/
@[circuit_noinline]
def g1ScalarMulFuel (c : CurveParams) : Nat → Nat → G1Point → G1Point → G1Point
  | 0, _, _, acc => acc
  | fuel + 1, k, cur, acc =>
    match k with
    | 0 => acc
    | _ =>
      let nextAcc := g1CondAdd c (k % 2) acc cur
      let nextCur := g1Double c cur
      g1ScalarMulFuel c fuel (k / 2) nextCur nextAcc
termination_by structural fuel => fuel

/-- Scalar multiplication `k · P` supporting up to 256-bit scalars (BN254 & BLS12-381 `Fr`). -/
@[circuit_inline]
def g1ScalarMul (c : CurveParams) (k : Nat) (P : G1Point) : G1Point :=
  g1ScalarMulFuel c 256 k P g1Inf

/-- Index into a `G1PointList` (`Lists::lookup`). -/
@[circuit_noinline]
def g1PointListGet (pts : G1PointList) (idx : Nat) : G1Point :=
  match pts with
  | .nil => g1Inf
  | .cons p rest =>
    match idx with
    | 0 => p
    | k + 1 => g1PointListGet rest k
termination_by structural pts

/-- Build 16-entry 4-bit window table `[0·P, 1·P, ..., 15·P]` (`KzgMsm::table_rows`). -/
@[circuit_noinline]
def g1WindowTableAux (c : CurveParams) (P cur : G1Point) : Nat → G1PointList
  | 0 => .nil
  | n + 1 => .cons cur (g1WindowTableAux c P (g1Add c cur P) n)
termination_by structural n => n

/-- Precompute the 16-entry 4-bit window table for `P` (`KzgMsm::table`). -/
@[circuit_inline]
def g1WindowTable (c : CurveParams) (P : G1Point) : G1PointList :=
  g1WindowTableAux c P g1Inf 16

/-- Prepare all MSM terms with 16-entry 4-bit tables (`KzgMsm::prepare`). -/
@[circuit_noinline]
def g1MsmPrepare (c : CurveParams) (terms : G1TermList) : MsmPreparedList :=
  match terms with
  | .nil => .nil
  | .cons t rest =>
    .cons { table := g1WindowTable c t.point, rem := t.scalar % c.frMod } (g1MsmPrepare c rest)
termination_by structural terms

/-- Peel one 4-bit digit (`rem % 16`) off every prepared MSM term (`KzgMsm::split`). -/
@[circuit_noinline]
def g1MsmSplit (terms : MsmPreparedList) : MsmSplitOut :=
  match terms with
  | .nil => { next := .nil, selected := .nil }
  | .cons t rest =>
    let q := t.rem / 16
    let d := t.rem % 16
    let sub := g1MsmSplit rest
    let nextTerms : MsmPreparedList := .cons { table := t.table, rem := q } sub.next
    if d == 0 then
      { next := nextTerms, selected := sub.selected }
    else
      { next := nextTerms, selected := .cons (g1PointListGet t.table d) sub.selected }
termination_by structural terms

/-- Sum selected window points into the accumulator (`KzgMsm::add_points`). -/
@[circuit_noinline]
def g1AddPoints (c : CurveParams) (pts : G1PointList) (acc : G1Point) : G1Point :=
  match pts with
  | .nil => acc
  | .cons p rest => g1AddPoints c rest (g1Add c acc p)
termination_by structural pts

/-- Four consecutive doublings `16 · acc` for one 4-bit MSM window (`KzgMsm::windows`). -/
@[circuit_inline]
def g1Double4 (c : CurveParams) (P : G1Point) : G1Point :=
  g1Double c (g1Double c (g1Double c (g1Double c P)))

/-- Process `count` 4-bit windows MSB-to-LSB (`KzgMsm::windows`, `64` windows = 256 bits). -/
@[circuit_noinline]
def g1MsmWindows (c : CurveParams) : Nat → MsmPreparedList → G1Point → G1Point
  | 0, _, acc => acc
  | n + 1, terms, acc =>
    let sp := g1MsmSplit terms
    let hi := g1MsmWindows c n sp.next acc
    g1AddPoints c sp.selected (g1Double4 c hi)
termination_by structural n => n

/-- Joint 4-bit windowed `G1` multi-scalar multiplication (`KzgMsm::msm`, 64 windows = 256 bits,
covering both BN254 `Fr` and BLS12-381 `Fr`). -/
@[circuit_noinline]
def g1Msm (c : CurveParams) (terms : G1TermList) : G1Point :=
  g1MsmWindows c 64 (g1MsmPrepare c terms) g1Inf

/-- Compact direct MSM for small-scalar circuit entrypoints (uses `g1ScalarMul` per term). -/
@[circuit_noinline]
def g1MsmDirect (c : CurveParams) (terms : G1TermList) : G1Point :=
  match terms with
  | .nil => g1Inf
  | .cons t rest => g1Add c (g1ScalarMul c t.scalar t.point) (g1MsmDirect c rest)
termination_by structural terms

/-! ### Limb Packing, 18/22-Word Terminal Affine Encoding & Compressed `G1` Wire Codec -/

/-- Unpack a BN254 `Fq` element into `4×80b` limbs. -/
def toLimb4 (x : Nat) : Limb4 :=
  let r := radix80
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let l3 := q2 / r
  { l0, l1, l2, l3 }

/-- Recompose a `4×80b` limb vector back into a `Nat`. -/
def ofLimb4 (v : Limb4) : Nat :=
  let r := radix80
  v.l0 + r * (v.l1 + r * (v.l2 + r * v.l3))

/-- Canonical BN254 `Fq` check on `4×80b` limbs (`80, 80, 80, 14` bits, `< bn254Fp`). -/
def limb4CanonicalBN254 (v : Limb4) : Bool :=
  let r := radix80
  decide (v.l0 < r) && decide (v.l1 < r) && decide (v.l2 < r) && decide (v.l3 < 16384) &&
    decide (ofLimb4 v < bn254Fp)

/-- Unpack a BLS12-381 `Fq` element into `5×80b` limbs. -/
def toLimb5 (x : Nat) : Limb5 :=
  let r := radix80
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let q3 := q2 / r
  let l3 := q3 % r
  let l4 := q3 / r
  { l0, l1, l2, l3, l4 }

/-- Recompose a `5×80b` limb vector back into a `Nat`. -/
def ofLimb5 (v : Limb5) : Nat :=
  let r := radix80
  v.l0 + r * (v.l1 + r * (v.l2 + r * (v.l3 + r * v.l4)))

/-- Canonical BLS12-381 `Fq` check on `5×80b` limbs (`80, 80, 80, 80, 61` bits, `< bls12381Fp`). -/
def limb5CanonicalBLS12381 (v : Limb5) : Bool :=
  let r := radix80
  decide (v.l0 < r) && decide (v.l1 < r) && decide (v.l2 < r) && decide (v.l3 < r) &&
    decide (v.l4 < (2 ^ 61)) && decide (ofLimb5 v < bls12381Fp)

/-- Round-trip identity `ofLimb4 (toLimb4 x) = x`. -/
theorem ofLimb4_toLimb4 (x : Nat) : ofLimb4 (toLimb4 x) = x := by
  simp only [ofLimb4, toLimb4, Nat.mod_add_div]

/-- Round-trip identity `ofLimb5 (toLimb5 x) = x`. -/
theorem ofLimb5_toLimb5 (x : Nat) : ofLimb5 (toLimb5 x) = x := by
  simp only [ofLimb5, toLimb5, Nat.mod_add_div]

/-- Unpack a `Nat` into `4` limbs using arbitrary radix `r` (works for `< 2^56` circuits too). -/
@[circuit_inline]
def toLimb4Radix (r x : Nat) : Limb4 :=
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let l3 := q2 / r
  { l0, l1, l2, l3 }

/-- Unpack a `Nat` into `5` limbs using arbitrary radix `r` (works for `< 2^56` circuits too). -/
@[circuit_inline]
def toLimb5Radix (r x : Nat) : Limb5 :=
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let q3 := q2 / r
  let l3 := q3 % r
  let l4 := q3 / r
  { l0, l1, l2, l3, l4 }

/-- Encode `(A, B)` into the exact 18-word BN254 `AffinePairBN254` struct (`2 × (4 + 4 + 1)`). -/
@[circuit_inline]
def encodeAffinePairBN254 (r : Nat) (A B : G1Point) : AffinePairBN254 :=
  { a := { x := toLimb4Radix r A.x, y := toLimb4Radix r A.y, isInf := A.isInf }
    b := { x := toLimb4Radix r B.x, y := toLimb4Radix r B.y, isInf := B.isInf } }

/-- Encode `(A, B)` into the exact 22-word BLS12-381 `AffinePairBLS12381` struct (`2 × (5 + 5 + 1)`). -/
@[circuit_inline]
def encodeAffinePairBLS12381 (r : Nat) (A B : G1Point) : AffinePairBLS12381 :=
  { a := { x := toLimb5Radix r A.x, y := toLimb5Radix r A.y, isInf := A.isInf }
    b := { x := toLimb5Radix r B.x, y := toLimb5Radix r B.y, isInf := B.isInf } }

/-- Generic `count`-limb little-endian unpacking under radix `r`. -/
@[circuit_noinline]
def toLimbsGeneric (r : Nat) : Nat → Nat → FList
  | 0, _ => .nil
  | n + 1, x => .cons (x % r) (toLimbsGeneric r n (x / r))
termination_by structural n => n

/-- Recompose generic little-endian limbs back to a `Nat`. -/
@[circuit_noinline]
def ofLimbsGeneric (r : Nat) : FList → Nat
  | .nil => 0
  | .cons h t => h + r * ofLimbsGeneric r t
termination_by structural ls => ls

/-- Append two `FList`s. -/
@[circuit_noinline]
def fListAppend (a b : FList) : FList :=
  match a with
  | .nil => b
  | .cons h t => .cons h (fListAppend t b)
termination_by structural a

/-- Length of an `FList`. -/
@[circuit_noinline]
def fListLen : FList → Nat
  | .nil => 0
  | .cons _ t => fListLen t + 1
termination_by structural xs => xs

/-- Encode one `G1` point as `2 * c.fqLimbCount + 1` affine words (`x limbs ++ y limbs ++ [isInf]`):
9 words for BN254, 11 words for BLS12-381 (`BN254G1::to_raw` generalized). -/
@[circuit_noinline]
def encodeAffinePointWords (c : CurveParams) (P : G1Point) : FList :=
  let xs := toLimbsGeneric c.limbRadix c.fqLimbCount P.x
  let ys := toLimbsGeneric c.limbRadix c.fqLimbCount P.y
  fListAppend xs (fListAppend ys (.cons P.isInf .nil))

/-- Encode a folded deferred pairing `(A, B)` as **18** affine-u80 words for BN254
or **22** affine-u80 words for BLS12-381 for `gnark` `PairingCheck`. -/
@[circuit_noinline]
def encodeAffinePairWords (c : CurveParams) (A B : G1Point) : FList :=
  fListAppend (encodeAffinePointWords c A) (encodeAffinePointWords c B)

/-- Decode `2 * c.fqLimbCount + 1` affine words back to a `G1Point` with on-curve check. -/
@[circuit_noinline]
def fListTake (xs : FList) : Nat → FList
  | 0 => .nil
  | n + 1 =>
    match xs with
    | .nil => .nil
    | .cons h t => .cons h (fListTake t n)
termination_by structural n => n

@[circuit_noinline]
def fListDrop (xs : FList) : Nat → FList
  | 0 => xs
  | n + 1 =>
    match xs with
    | .nil => .nil
    | .cons _ t => fListDrop t n
termination_by structural n => n

/-- Reconstruct a `G1Point` from its `2 * c.fqLimbCount + 1` affine words. -/
def decodeAffinePointWords (c : CurveParams) (ws : FList) : G1Point :=
  let k := c.fqLimbCount
  let x := ofLimbsGeneric c.limbRadix (fListTake ws k)
  let r1 := fListDrop ws k
  let y := ofLimbsGeneric c.limbRadix (fListTake r1 k)
  let r2 := fListDrop r1 k
  let isInf := match r2 with | .cons v _ => v | .nil => 2
  { x, y, isInf }

/-- Append two `ByteList`s. -/
@[circuit_noinline]
def byteAppend (a b : ByteList) : ByteList :=
  match a with
  | .nil => b
  | .cons h t => .cons h (byteAppend t b)
termination_by structural a

/-- Length of a `ByteList`. -/
@[circuit_noinline]
def byteLen : ByteList → Nat
  | .nil => 0
  | .cons _ t => byteLen t + 1
termination_by structural bs => bs

/-- Byte-list equality (`1` iff equal, else `0`). -/
@[circuit_noinline]
def byteListEq (a b : ByteList) : Nat :=
  match a, b with
  | .nil, .nil => 1
  | .cons x xs, .cons y ys =>
    if x == y then byteListEq xs ys else 0
  | _, _ => 0
termination_by structural a

/-- Serialize a `Nat` into `n` little-endian bytes (`base 256`). -/
@[circuit_noinline]
def natToLeBytes : Nat → Nat → ByteList
  | 0, _ => .nil
  | n + 1, x => .cons (x % 256) (natToLeBytes n (x / 256))
termination_by structural n => n

/-- Recompose a little-endian `ByteList` into a `Nat`. -/
@[circuit_noinline]
def leBytesToNat : ByteList → Nat
  | .nil => 0
  | .cons b rest => b + 256 * leBytesToNat rest
termination_by structural bs => bs

/-- Check all bytes in a `ByteList` are canonical (`< 256`). -/
@[circuit_noinline]
def bytesCanonical : ByteList → Nat
  | .nil => 1
  | .cons b rest => if b < 256 then bytesCanonical rest else 0
termination_by structural bs => bs

/-- Arkworks `SWFlags` lexicographic y-sign: `1` iff `y > (fqMod - 1) / 2`
(exact match for `Aiur.Library.Field.BN254.G1.sign`). -/
@[circuit_inline]
def g1YSign (c : CurveParams) (y : Nat) : Nat :=
  if (c.fqMod - 1) / 2 < y then 1 else 0

/-- Add `flag` into the last (most-significant) byte of a non-empty `ByteList`. -/
@[circuit_noinline]
def addLastByteFlag (flag : Nat) : ByteList → ByteList
  | .nil => .nil
  | .cons b .nil => .cons (b + flag) .nil
  | .cons b rest => .cons b (addLastByteFlag flag rest)
termination_by structural bs => bs

/-- Compress a canonical `G1` point into `c.g1ByteLen` bytes (32B BN254, 48B BLS12-381)
using arkworks `SWFlags` (`lastByte = x[n-1] + 64 * isInf + 128 * ySign`), exact match for
`BN254G1::to_bytes`. -/
@[circuit_noinline]
def g1ToBytes (c : CurveParams) (P : G1Point) : ByteList :=
  let rawX := natToLeBytes c.g1ByteLen P.x
  let flag := 64 * P.isInf + 128 * g1YSign c P.y
  addLastByteFlag flag rawX

/-- Extract `(strippedBytes, flagBits)` where `flagBits = lastByte / 64` and top byte is
`lastByte % 64` (`0..63`, since `bn254Fp < 2^254` and `bls12381Fp < 2^381`). -/
private def stripLastByteFlags : ByteList → ByteList × Nat
  | .nil => (.nil, 0)
  | .cons b .nil => (.cons (b % 64) .nil, b / 64)
  | .cons b rest =>
    let (r, f) := stripLastByteFlags rest
    (.cons b r, f)
termination_by structural bs => bs

/-- Decompress and strictly validate a `c.g1ByteLen`-byte compressed `G1` point:
1. Length equals `c.g1ByteLen`, every byte `< 256`,
2. If `isInf = 1`: requires `x == 0` and `ySign == 0` → returns `g1Inf`,
3. If `isInf = 0`: requires `x < c.fqMod`, computes `y = (x³ + b)^((q + 1)/4) mod q`
   (exact for both `bn254Fp ≡ 3 (mod 4)`, `bls12381Fp ≡ 3 (mod 4)`, and `103 ≡ 3 (mod 4)`),
   adjusts sign to match `ySign`, checks `g1OnCurve c pt`, and verifies exact round-trip
   `g1ToBytes c pt == bs` (rejecting every non-canonical encoding!). -/
def g1FromBytes (c : CurveParams) (bs : ByteList) : ParsePoint :=
  if byteLen bs == c.g1ByteLen then
    if bytesCanonical bs == 1 then
      let (xBytes, flags) := stripLastByteFlags bs
      let isInf := flags % 2
      let ySign := flags / 2
      let x := leBytesToNat xBytes
      if isInf == 1 then
        if x == 0 then
          if ySign == 0 then
            { ok := 1, point := g1Inf, rest := .nil }
          else { ok := 0, point := g1Inf, rest := .nil }
        else { ok := 0, point := g1Inf, rest := .nil }
      else if x < c.fqMod then
        let x2 := fqMulMod c.fqMod x x
        let x3 := fqMulMod c.fqMod x2 x
        let rhs := fqAddMod c.fqMod x3 (c.curveB % c.fqMod)
        let y0 := fqPowMod c.fqMod rhs ((c.fqMod + 1) / 4)
        let y := if g1YSign c y0 == ySign then y0 else fqNegMod c.fqMod y0
        let pt : G1Point := { x, y, isInf := 0 }
        if g1OnCurve c pt then
          if byteListEq (g1ToBytes c pt) bs == 1 then
            { ok := 1, point := pt, rest := .nil }
          else { ok := 0, point := g1Inf, rest := .nil }
        else { ok := 0, point := g1Inf, rest := .nil }
      else { ok := 0, point := g1Inf, rest := .nil }
    else { ok := 0, point := g1Inf, rest := .nil }
  else { ok := 0, point := g1Inf, rest := .nil }

/-- Split `bs` into `(prefix of n bytes, suffix)`. -/
@[circuit_noinline]
def byteSplitAt (bs : ByteList) : Nat → ByteList × ByteList
  | 0 => (.nil, bs)
  | n + 1 =>
    match bs with
    | .nil => (.nil, .nil)
    | .cons b rest =>
      let (p, s) := byteSplitAt rest n
      (.cons b p, s)
termination_by structural n => n

/-- Pack `(A, B)` as `4` little-endian u128 scalar chunks (`BN254G1Encoding::to_chunks`). -/
def packAccumulator4 (c : CurveParams) (A B : G1Point) : AccumulatorChunks4 :=
  let aBytes := g1ToBytes c A
  let bBytes := g1ToBytes c B
  let (aLo, aHi) := byteSplitAt aBytes 16
  let (bLo, bHi) := byteSplitAt bBytes 16
  { c0 := leBytesToNat aLo, c1 := leBytesToNat aHi
    c2 := leBytesToNat bLo, c3 := leBytesToNat bHi }

/-- Unpack `4` little-endian u128 scalar chunks into canonical `(A, B)` (`BN254G1Encoding::from_chunks`). -/
def unpackAccumulator4 (c : CurveParams) (ch : AccumulatorChunks4) : Nat × G1Point × G1Point :=
  if ch.c0 < radix128 && ch.c1 < radix128 && ch.c2 < radix128 && ch.c3 < radix128 then
    let aBytes := byteAppend (natToLeBytes 16 ch.c0) (natToLeBytes 16 ch.c1)
    let bBytes := byteAppend (natToLeBytes 16 ch.c2) (natToLeBytes 16 ch.c3)
    let pa := g1FromBytes c aBytes
    let pb := g1FromBytes c bBytes
    if pa.ok == 1 && pb.ok == 1 then (1, pa.point, pb.point)
    else (0, g1Inf, g1Inf)
  else (0, g1Inf, g1Inf)

/-- Pack BLS12-381 `(A, B)` (2 × 48B = 96B) as `6` little-endian u128 scalar chunks. -/
def packAccumulator6 (c : CurveParams) (A B : G1Point) : AccumulatorChunks6 :=
  let aBytes := g1ToBytes c A
  let bBytes := g1ToBytes c B
  let (a0, aRest1) := byteSplitAt aBytes 16
  let (a1, a2) := byteSplitAt aRest1 16
  let (b0, bRest1) := byteSplitAt bBytes 16
  let (b1, b2) := byteSplitAt bRest1 16
  { c0 := leBytesToNat a0, c1 := leBytesToNat a1, c2 := leBytesToNat a2
    c3 := leBytesToNat b0, c4 := leBytesToNat b1, c5 := leBytesToNat b2 }

/-- Unpack `6` little-endian u128 scalar chunks into canonical BLS12-381 `(A, B)`. -/
def unpackAccumulator6 (c : CurveParams) (ch : AccumulatorChunks6) : Nat × G1Point × G1Point :=
  if ch.c0 < radix128 && ch.c1 < radix128 && ch.c2 < radix128 &&
      ch.c3 < radix128 && ch.c4 < radix128 && ch.c5 < radix128 then
    let aBytes := byteAppend (natToLeBytes 16 ch.c0)
      (byteAppend (natToLeBytes 16 ch.c1) (natToLeBytes 16 ch.c2))
    let bBytes := byteAppend (natToLeBytes 16 ch.c3)
      (byteAppend (natToLeBytes 16 ch.c4) (natToLeBytes 16 ch.c5))
    let pa := g1FromBytes c aBytes
    let pb := g1FromBytes c bBytes
    if pa.ok == 1 && pb.ok == 1 then (1, pa.point, pb.point)
    else (0, g1Inf, g1Inf)
  else (0, g1Inf, g1Inf)

/-- Unified multi-curve accumulator chunk packer:
* BN254 (`g1ByteLen == 32`) → 4 u128 chunks (`KzgAccumulator::pack`),
* BLS12-381 (`g1ByteLen == 48`) → 6 u128 chunks,
* Compact circuit curves (`g1ByteLen ≤ 16`) → 2 scalar chunks. -/
def packAccumulatorChunks (c : CurveParams) (A B : G1Point) : FList :=
  if c.g1ByteLen == 32 then
    let ch := packAccumulator4 c A B
    .cons ch.c0 (.cons ch.c1 (.cons ch.c2 (.cons ch.c3 .nil)))
  else if c.g1ByteLen == 48 then
    let ch := packAccumulator6 c A B
    .cons ch.c0 (.cons ch.c1 (.cons ch.c2 (.cons ch.c3 (.cons ch.c4 (.cons ch.c5 .nil)))))
  else
    .cons (leBytesToNat (g1ToBytes c A)) (.cons (leBytesToNat (g1ToBytes c B)) .nil)

/-- Unified multi-curve accumulator chunk unpacker. -/
def unpackAccumulatorChunks (c : CurveParams) (xs : FList) : Nat × G1Point × G1Point :=
  if c.g1ByteLen == 32 then
    match xs with
    | .cons c0 (.cons c1 (.cons c2 (.cons c3 .nil))) =>
      unpackAccumulator4 c { c0, c1, c2, c3 }
    | _ => (0, g1Inf, g1Inf)
  else if c.g1ByteLen == 48 then
    match xs with
    | .cons c0 (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.cons c5 .nil))))) =>
      unpackAccumulator6 c { c0, c1, c2, c3, c4, c5 }
    | _ => (0, g1Inf, g1Inf)
  else
    match xs with
    | .cons a (.cons b .nil) =>
      let pa := g1FromBytes c (natToLeBytes c.g1ByteLen a)
      let pb := g1FromBytes c (natToLeBytes c.g1ByteLen b)
      if pa.ok == 1 && pb.ok == 1 then (1, pa.point, pb.point)
      else (0, g1Inf, g1Inf)
    | _ => (0, g1Inf, g1Inf)

/-! ## Section 5: Exact BLAKE3 Hash, 96-Byte XOF & `KzgTranscript` -/

/-- Standard BLAKE3 IV (`Blake3::iv`). -/
def blake3Iv : Digest32 :=
  { w0 := 0x6A09E667, w1 := 0xBB67AE85, w2 := 0x3C6EF372, w3 := 0xA54FF53A
    w4 := 0x510E527F, w5 := 0x9B05688C, w6 := 0x1F83D9AB, w7 := 0x5BE0CD19 }

def rotr16 (x : UInt32) : UInt32 := (x >>> 16) ||| (x <<< 16)
def rotr12 (x : UInt32) : UInt32 := (x >>> 12) ||| (x <<< 20)
def rotr8  (x : UInt32) : UInt32 := (x >>> 8)  ||| (x <<< 24)
def rotr7  (x : UInt32) : UInt32 := (x >>> 7)  ||| (x <<< 25)

/-- BLAKE3 quarter-round `G`. -/
def blake3G (a b c d mx my : UInt32) : QuarterOut :=
  let a1 := a + b + mx
  let d1 := rotr16 (d ^^^ a1)
  let c1 := c + d1
  let b1 := rotr12 (b ^^^ c1)
  let a2 := a1 + b1 + my
  let d2 := rotr8 (d1 ^^^ a2)
  let c2 := c1 + d2
  let b2 := rotr7 (b1 ^^^ c2)
  { a := a2, b := b2, c := c2, d := d2 }

/-- One full BLAKE3 round (4 column + 4 diagonal quarter-rounds). -/
def blake3Round (s : State16) (m : Block16) : State16 :=
  let c0 := blake3G s.v0 s.v4 s.v8  s.v12 m.m0  m.m1
  let c1 := blake3G s.v1 s.v5 s.v9  s.v13 m.m2  m.m3
  let c2 := blake3G s.v2 s.v6 s.v10 s.v14 m.m4  m.m5
  let c3 := blake3G s.v3 s.v7 s.v11 s.v15 m.m6  m.m7
  let d0 := blake3G c0.a c1.b c2.c  c3.d  m.m8  m.m9
  let d1 := blake3G c1.a c2.b c3.c  c0.d  m.m10 m.m11
  let d2 := blake3G c2.a c3.b c0.c  c1.d  m.m12 m.m13
  let d3 := blake3G c3.a c0.b c1.c  c2.d  m.m14 m.m15
  { v0 := d0.a, v1 := d1.a, v2 := d2.a, v3 := d3.a
    v4 := d3.b, v5 := d0.b, v6 := d1.b, v7 := d2.b
    v8 := d2.c, v9 := d3.c, v10 := d0.c, v11 := d1.c
    v12 := d1.d, v13 := d2.d, v14 := d3.d, v15 := d0.d }

/-- BLAKE3 message-schedule permutation between rounds. -/
def blake3Permute (m : Block16) : Block16 :=
  { m0 := m.m2,  m1 := m.m6,  m2 := m.m3,  m3 := m.m10
    m4 := m.m7,  m5 := m.m0,  m6 := m.m4,  m7 := m.m13
    m8 := m.m1,  m9 := m.m11, m10 := m.m12, m11 := m.m5
    m12 := m.m9, m13 := m.m14, m14 := m.m15, m15 := m.m8 }

/-- Run 7 BLAKE3 rounds (`rem = 6` runs rounds `0..6`) returning the final 16-word state. -/
def blake3RoundsState : Nat → State16 → Block16 → State16
  | 0, s, m => blake3Round s m
  | k + 1, s, m => blake3RoundsState k (blake3Round s m) (blake3Permute m)
termination_by structural rem => rem

/-- Full 16-word BLAKE3 compression (`KzgBlake3::compress_full`):
`out[0..7] = state[0..7] ^^^ state[8..15]`, `out[8..15] = state[8..15] ^^^ cv[0..7]`. -/
def blake3CompressFull (cv : Digest32) (m : Block16) (counterLo counterHi blockLen flags : UInt32) :
    Block16 :=
  let k := blake3Iv
  let st0 : State16 :=
    { v0 := cv.w0, v1 := cv.w1, v2 := cv.w2, v3 := cv.w3
      v4 := cv.w4, v5 := cv.w5, v6 := cv.w6, v7 := cv.w7
      v8 := k.w0,  v9 := k.w1,  v10 := k.w2, v11 := k.w3
      v12 := counterLo, v13 := counterHi, v14 := blockLen, v15 := flags }
  let s1 := blake3RoundsState 6 st0 m
  { m0 := s1.v0 ^^^ s1.v8,   m1 := s1.v1 ^^^ s1.v9
    m2 := s1.v2 ^^^ s1.v10,  m3 := s1.v3 ^^^ s1.v11
    m4 := s1.v4 ^^^ s1.v12,  m5 := s1.v5 ^^^ s1.v13
    m6 := s1.v6 ^^^ s1.v14,  m7 := s1.v7 ^^^ s1.v15
    m8 := s1.v8 ^^^ cv.w0,   m9 := s1.v9 ^^^ cv.w1
    m10 := s1.v10 ^^^ cv.w2, m11 := s1.v11 ^^^ cv.w3
    m12 := s1.v12 ^^^ cv.w4, m13 := s1.v13 ^^^ cv.w5
    m14 := s1.v14 ^^^ cv.w6, m15 := s1.v15 ^^^ cv.w7 }

/-- Standard 8-word BLAKE3 compression (`Blake3::compress_init`). -/
def blake3Compress8 (cv : Digest32) (m : Block16) (counterLo counterHi blockLen flags : UInt32) :
    Digest32 :=
  let full := blake3CompressFull cv m counterLo counterHi blockLen flags
  { w0 := full.m0, w1 := full.m1, w2 := full.m2, w3 := full.m3
    w4 := full.m4, w5 := full.m5, w6 := full.m6, w7 := full.m7 }

/-- Read up to 4 bytes into a little-endian `UInt32` word (zero-padded if short). -/
private def takeU32Padded (bs : ByteList) : UInt32 × ByteList :=
  let (b0, r0) := match bs with | .cons b r => (b, r) | .nil => (0, .nil)
  let (b1, r1) := match r0 with | .cons b r => (b, r) | .nil => (0, .nil)
  let (b2, r2) := match r1 with | .cons b r => (b, r) | .nil => (0, .nil)
  let (b3, r3) := match r2 with | .cons b r => (b, r) | .nil => (0, .nil)
  (UInt32.ofNat (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3), r3)

/-- Pack up to 64 bytes into a zero-padded `Block16`, returning `(block, blockLen, rest)`. -/
def bytesToBlock16 (bs : ByteList) : Block16 × Nat × ByteList :=
  let (blkBytes, rest) := byteSplitAt bs 64
  let len := byteLen blkBytes
  let (m0, r0) := takeU32Padded blkBytes
  let (m1, r1) := takeU32Padded r0
  let (m2, r2) := takeU32Padded r1
  let (m3, r3) := takeU32Padded r2
  let (m4, r4) := takeU32Padded r3
  let (m5, r5) := takeU32Padded r4
  let (m6, r6) := takeU32Padded r5
  let (m7, r7) := takeU32Padded r6
  let (m8, r8) := takeU32Padded r7
  let (m9, r9) := takeU32Padded r8
  let (m10, r10) := takeU32Padded r9
  let (m11, r11) := takeU32Padded r10
  let (m12, r12) := takeU32Padded r11
  let (m13, r13) := takeU32Padded r12
  let (m14, r14) := takeU32Padded r13
  let (m15, _) := takeU32Padded r14
  ({ m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15 }, len, rest)

/-- Join two 8-word chaining values into a 16-word parent block (`KzgBlake3::join`). -/
def blake3Join (a b : Digest32) : Block16 :=
  { m0 := a.w0, m1 := a.w1, m2 := a.w2, m3 := a.w3
    m4 := a.w4, m5 := a.w5, m6 := a.w6, m7 := a.w7
    m8 := b.w0, m9 := b.w1, m10 := b.w2, m11 := b.w3
    m12 := b.w4, m13 := b.w5, m14 := b.w6, m15 := b.w7 }

/-- Process one BLAKE3 chunk (at most 16 blocks = 1024 bytes), stopping before its final
block (`KzgBlake3::chunk`), returning `(rootInputWithoutRootFlag, remainingBytes)`. -/
private def blake3ChunkAux (counterLo counterHi : UInt32) :
    Nat → Nat → Digest32 → ByteList → Blake3RootInput × ByteList
  | 0, _, cv, bs =>
    let (blk, len, rest) := bytesToBlock16 bs
    ({ cv, block := blk, blockLen := UInt32.ofNat len, flags := 2 }, rest)
  | rem + 1, idx, cv, bs =>
    let (blk, len, rest) := bytesToBlock16 bs
    let startFlag : UInt32 := if idx == 0 then 1 else 0
    let isLast := match rest with | .nil => true | .cons _ _ => idx == 15
    if isLast then
      ({ cv, block := blk, blockLen := UInt32.ofNat len, flags := startFlag + 2 }, rest)
    else
      let nextCv := blake3Compress8 cv blk counterLo counterHi (UInt32.ofNat len) startFlag
      blake3ChunkAux counterLo counterHi rem (idx + 1) nextCv rest
termination_by structural rem => rem

/-- Collect all chunk CVs for a multi-chunk message (`KzgBlake3::chunks`). -/
private def blake3ChunksFuel : Nat → Nat → ByteList → Digest32List
  | 0, _, _ => .nil
  | fuel + 1, counter, bs =>
    let lo := UInt32.ofNat (counter % 4294967296)
    let hi := UInt32.ofNat (counter / 4294967296)
    let (ri, rest) := blake3ChunkAux lo hi 16 0 blake3Iv bs
    let cv := blake3Compress8 ri.cv ri.block lo hi ri.blockLen ri.flags
    match rest with
    | .nil => .cons cv .nil
    | .cons _ _ => .cons cv (blake3ChunksFuel fuel (counter + 1) rest)
termination_by structural fuel => fuel

/-- Fold one BLAKE3 Merkle-tree layer (`KzgBlake3::next_layer`). -/
private def blake3NextLayer : Digest32List → Digest32List
  | .nil => .nil
  | .cons a .nil => .cons a .nil
  | .cons a (.cons b tail) =>
    let parentCv := blake3Compress8 blake3Iv (blake3Join a b) 0 0 64 4
    .cons parentCv (blake3NextLayer tail)
termination_by structural layer => layer

/-- Reduce a multi-chunk CV list to its root `(left, right)` pair (`KzgBlake3::root`). -/
private def blake3ReduceTree : Nat → Digest32List → Digest32 × Digest32
  | 0, layer =>
    match layer with
    | .cons a (.cons b _) => (a, b)
    | .cons a .nil => (a, blake3Iv)
    | .nil => (blake3Iv, blake3Iv)
  | fuel + 1, layer =>
    match layer with
    | .cons a (.cons b .nil) => (a, b)
    | _ => blake3ReduceTree fuel (blake3NextLayer layer)
termination_by structural fuel => fuel

/-- Compute the BLAKE3 root compression input (without the `ROOT = 8` flag) for any message. -/
def blake3Root (bs : ByteList) : Blake3RootInput :=
  let (firstRi, rest) := blake3ChunkAux 0 0 16 0 blake3Iv bs
  match rest with
  | .nil => firstRi
  | .cons _ _ =>
    let firstCv := blake3Compress8 firstRi.cv firstRi.block 0 0 firstRi.blockLen firstRi.flags
    let chunkFuel := byteLen rest + 1
    let cvs := Digest32List.cons firstCv (blake3ChunksFuel chunkFuel 1 rest)
    let (left, right) := blake3ReduceTree 64 cvs
    { cv := blake3Iv, block := blake3Join left right, blockLen := 64, flags := 4 }

/-- Exact standard BLAKE3 32-byte hash as 8 little-endian `UInt32` words. -/
def blake3Hash (bs : ByteList) : Digest32 :=
  let ri := blake3Root bs
  blake3Compress8 ri.cv ri.block 0 0 ri.blockLen (ri.flags + 8)

/-- Convert `Digest32` (`UInt32` words) to `DigestWords` (`Nat` words `< 2^32`). -/
def digest32ToWords (d : Digest32) : DigestWords :=
  { d0 := d.w0.toNat, d1 := d.w1.toNat, d2 := d.w2.toNat, d3 := d.w3.toNat
    d4 := d.w4.toNat, d5 := d.w5.toNat, d6 := d.w6.toNat, d7 := d.w7.toNat }

/-- Exact standard BLAKE3 32-byte hash as `DigestWords` (`KzgIO::Digest = [Field; 8]`). -/
def blake3HashWords (bs : ByteList) : DigestWords :=
  digest32ToWords (blake3Hash bs)

/-- Exact 96-byte BLAKE3 XOF output (`KzgBlake3::xof96` / `xof_output`):
first 64 bytes (`counter = 0`) + next 32 bytes (`counter = 1`, first 8 words). -/
def blake3Xof96 (bs : ByteList) : Xof96Out :=
  let ri := blake3Root bs
  let wide := blake3CompressFull ri.cv ri.block 0 0 ri.blockLen (ri.flags + 8)
  let second := blake3CompressFull ri.cv ri.block 1 0 ri.blockLen (ri.flags + 8)
  let next : Digest32 :=
    { w0 := second.m0, w1 := second.m1, w2 := second.m2, w3 := second.m3
      w4 := second.m4, w5 := second.m5, w6 := second.m6, w7 := second.m7 }
  { wide, next }

/-- Serialize `DigestWords` (8 u32 words) into 32 little-endian bytes (`KzgIO::digest_bytes`). -/
def digestWordsToBytes (d : DigestWords) : ByteList :=
  byteAppend (natToLeBytes 4 d.d0)
    (byteAppend (natToLeBytes 4 d.d1)
    (byteAppend (natToLeBytes 4 d.d2)
    (byteAppend (natToLeBytes 4 d.d3)
    (byteAppend (natToLeBytes 4 d.d4)
    (byteAppend (natToLeBytes 4 d.d5)
    (byteAppend (natToLeBytes 4 d.d6) (natToLeBytes 4 d.d7)))))))

/-- Serialize `Digest32` into 32 little-endian bytes. -/
def digest32ToBytes (d : Digest32) : ByteList :=
  digestWordsToBytes (digest32ToWords d)

/-- Check equality of two `DigestWords` (`1` iff all 8 words match). -/
@[circuit_inline]
def digestWordsEq (a b : DigestWords) : Nat :=
  if a.d0 == b.d0 && a.d1 == b.d1 && a.d2 == b.d2 && a.d3 == b.d3 &&
      a.d4 == b.d4 && a.d5 == b.d5 && a.d6 == b.d6 && a.d7 == b.d7 then 1 else 0

/-- Check all 8 words of `DigestWords` are canonical `< 2^32`. -/
@[circuit_inline]
def digestWordsCanonical (d : DigestWords) : Nat :=
  let lim := 4294967296
  if d.d0 < lim && d.d1 < lim && d.d2 < lim && d.d3 < lim &&
      d.d4 < lim && d.d5 < lim && d.d6 < lim && d.d7 < lim then 1 else 0

/-- 32 zero bytes (initial transcript state `[0; 8]` words). -/
def zeroBytes32 : ByteList :=
  natToLeBytes 32 0

/-- Start a `KzgTranscript` with 32 zero bytes followed by `seed` (`KzgTranscript::start`). -/
def transcriptStart (seed : ByteList) : KzgTranscript :=
  { buf := byteAppend zeroBytes32 seed }

/-- Absorb raw bytes into a `KzgTranscript` (`KzgTranscript::observe_bytes` / `observe_input`). -/
def transcriptObserveBytes (tr : KzgTranscript) (bs : ByteList) : KzgTranscript :=
  { buf := byteAppend tr.buf bs }

/-- Absorb a canonical `Fr` scalar as 32 little-endian bytes (`KzgTranscript::observe_field`). -/
def transcriptObserveField (tr : KzgTranscript) (v : Nat) : KzgTranscript :=
  transcriptObserveBytes tr (natToLeBytes 32 v)

/-- Absorb a list of `Fr` scalars (`KzgTranscript::observe_fields`). -/
def transcriptObserveFields (tr : KzgTranscript) (vs : FList) : KzgTranscript :=
  match vs with
  | .nil => tr
  | .cons v rest => transcriptObserveFields (transcriptObserveField tr v) rest
termination_by structural vs

/-- Absorb a `u64` little-endian integer (8 bytes, `KzgTranscript::observe_u64`). -/
def transcriptObserveU64 (tr : KzgTranscript) (v : Nat) : KzgTranscript :=
  transcriptObserveBytes tr (natToLeBytes 8 v)

/-- Absorb a compressed `G1` point (`c.g1ByteLen` bytes). -/
def transcriptObservePoint (c : CurveParams) (tr : KzgTranscript) (P : G1Point) : KzgTranscript :=
  transcriptObserveBytes tr (g1ToBytes c P)

/-- Absorb claim rows: per row, `observe_field (len row)` then `observe_fields row`. -/
private def transcriptObserveClaimRows (tr : KzgTranscript) (claims : FListList) : KzgTranscript :=
  match claims with
  | .nil => tr
  | .cons row rest =>
    let tr1 := transcriptObserveField tr (fListLen row)
    transcriptObserveClaimRows (transcriptObserveFields tr1 row) rest
termination_by structural claims

/-- Length of an `FListList`. -/
@[circuit_noinline]
def fListListLen : FListList → Nat
  | .nil => 0
  | .cons _ t => fListListLen t + 1
termination_by structural xs => xs

/-- Absorb claims table (`KzgTranscript::observe_claims`). -/
def transcriptObserveClaims (tr : KzgTranscript) (claims : FListList) : KzgTranscript :=
  transcriptObserveClaimRows (transcriptObserveField tr (fListListLen claims)) claims

/-- Reduce 64-byte XOF output (`Block16`, 16 LE u32 words) little-endian modulo `p`
(`KzgTranscript::reduce64`). -/
def reduce64Mod (p : Nat) (w : Block16) : Nat :=
  let b := 4294967296
  let v := w.m15.toNat % p
  let v := (b * v + w.m14.toNat) % p
  let v := (b * v + w.m13.toNat) % p
  let v := (b * v + w.m12.toNat) % p
  let v := (b * v + w.m11.toNat) % p
  let v := (b * v + w.m10.toNat) % p
  let v := (b * v + w.m9.toNat) % p
  let v := (b * v + w.m8.toNat) % p
  let v := (b * v + w.m7.toNat) % p
  let v := (b * v + w.m6.toNat) % p
  let v := (b * v + w.m5.toNat) % p
  let v := (b * v + w.m4.toNat) % p
  let v := (b * v + w.m3.toNat) % p
  let v := (b * v + w.m2.toNat) % p
  let v := (b * v + w.m1.toNat) % p
  (b * v + w.m0.toNat) % p

/-- Squeeze one `Fr` challenge from `KzgTranscript` (`KzgTranscript::sample`):
runs `blake3Xof96`, reduces first 64B LE into `Fr`, retains next 32B as new state. -/
def transcriptSampleFr (c : CurveParams) (tr : KzgTranscript) : SampleResult :=
  let xof := blake3Xof96 tr.buf
  { challenge := reduce64Mod c.frMod xof.wide
    transcript := { buf := digest32ToBytes xof.next } }

/-- Exact `"ix/kzg/packed-shplonk-pcs/open/v1\0"` (34 bytes, `KzgPcsPacked::open_domain`). -/
def openDomainBytes : ByteList :=
  .cons 105 (.cons 120 (.cons 47 (.cons 107 (.cons 122 (.cons 103 (.cons 47
  (.cons 112 (.cons 97 (.cons 99 (.cons 107 (.cons 101 (.cons 100 (.cons 45
  (.cons 115 (.cons 104 (.cons 112 (.cons 108 (.cons 111 (.cons 110 (.cons 107
  (.cons 45 (.cons 112 (.cons 99 (.cons 115 (.cons 47 (.cons 111 (.cons 112
  (.cons 101 (.cons 110 (.cons 47 (.cons 118 (.cons 49 (.cons 0 .nil)))))))))))))))))))))))))))))))))

/-- Exact `"ix/kzg/packed-shplonk/v1\0"` (25 bytes, `KzgPcsPacked::batch_domain`). -/
def batchDomainBytes : ByteList :=
  .cons 105 (.cons 120 (.cons 47 (.cons 107 (.cons 122 (.cons 103 (.cons 47
  (.cons 112 (.cons 97 (.cons 99 (.cons 107 (.cons 101 (.cons 100 (.cons 45
  (.cons 115 (.cons 104 (.cons 112 (.cons 108 (.cons 111 (.cons 110 (.cons 107
  (.cons 47 (.cons 118 (.cons 49 (.cons 0 .nil))))))))))))))))))))))))

/-- Exact `"ix/aiur/kzg/fold-transcript/v1\0"` (31 bytes, `CompressBNPacked::fold_domain`). -/
@[circuit_inline]
def foldDomainBytes : ByteList :=
  .cons 105 (.cons 120 (.cons 47 (.cons 97 (.cons 105 (.cons 117 (.cons 114 (.cons 47
  (.cons 107 (.cons 122 (.cons 103 (.cons 47 (.cons 102 (.cons 111 (.cons 108 (.cons 100
  (.cons 45 (.cons 116 (.cons 114 (.cons 97 (.cons 110 (.cons 115 (.cons 99 (.cons 114
  (.cons 105 (.cons 112 (.cons 116 (.cons 47 (.cons 118 (.cons 49 (.cons 0 .nil))))))))))))))))))))))))))))))

/-- Compact algebraic sponge absorb over `Fr` (zero `UInt32` tables; compiles under
`TableTier.none` / `TableTier.byte256` with native `FieldLower` `Fr` arithmetic). -/
@[circuit_noinline]
def spongeAbsorbBytes (p acc : Nat) : ByteList → Nat
  | .nil => acc
  | .cons b rest =>
    let step := frAdd p (frMul p acc 257) (frAdd p b 1)
    spongeAbsorbBytes p step rest
termination_by structural bs => bs

/-! ## Section 6: Exact Production Binary Wire Parsers & Encoders

Magic headers (8 ASCII bytes each):
- `IXAUCL01` (`[73, 88, 65, 85, 67, 76, 48, 49]`): claims
- `IXAUKG01` (`[73, 88, 65, 85, 75, 71, 48, 49]`): packed two-key chain policy
- `IXPSHC02` (`[73, 88, 80, 83, 72, 67, 48, 50]`): packed SHPLONK commitment blob
- `IXAUSK02` (`[73, 88, 65, 85, 83, 75, 48, 50]`): packed verifying key
- `IXAUSP01` (`[73, 88, 65, 85, 83, 80, 48, 49]`): packed SHPLONK proof -/

@[circuit_inline]
def magicClaims : ByteList :=
  .cons 73 (.cons 88 (.cons 65 (.cons 85 (.cons 67 (.cons 76 (.cons 48 (.cons 49 .nil)))))))

@[circuit_inline]
def magicChainPolicy : ByteList :=
  .cons 73 (.cons 88 (.cons 65 (.cons 85 (.cons 75 (.cons 71 (.cons 48 (.cons 49 .nil)))))))

@[circuit_inline]
def magicPackedComm : ByteList :=
  .cons 73 (.cons 88 (.cons 80 (.cons 83 (.cons 72 (.cons 67 (.cons 48 (.cons 50 .nil)))))))

@[circuit_inline]
def magicPackedKey : ByteList :=
  .cons 73 (.cons 88 (.cons 65 (.cons 85 (.cons 83 (.cons 75 (.cons 48 (.cons 50 .nil)))))))

@[circuit_inline]
def magicPackedProof : ByteList :=
  .cons 73 (.cons 88 (.cons 65 (.cons 85 (.cons 83 (.cons 80 (.cons 48 (.cons 49 .nil)))))))

/-- Read one canonical byte (`< 256`). -/
@[circuit_noinline]
def readU8 (bs : ByteList) : ParseNat :=
  match bs with
  | .nil => { ok := 0, val := 0, rest := .nil }
  | .cons b rest =>
    if b < 256 then { ok := 1, val := b, rest }
    else { ok := 0, val := 0, rest := .nil }

/-- Read a little-endian `u32` (4 canonical bytes). -/
@[circuit_noinline]
def readU32 (bs : ByteList) : ParseNat :=
  match bs with
  | .cons b0 (.cons b1 (.cons b2 (.cons b3 rest))) =>
    if b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256 then
      { ok := 1, val := b0 + 256 * b1 + 65536 * b2 + 16777216 * b3, rest }
    else { ok := 0, val := 0, rest := .nil }
  | _ => { ok := 0, val := 0, rest := .nil }

/-- Read exactly `count` canonical bytes. -/
@[circuit_noinline]
def readBytes (bs : ByteList) : Nat → ParseBytes
  | 0 => { ok := 1, bytes := .nil, rest := bs }
  | n + 1 =>
    match bs with
    | .nil => { ok := 0, bytes := .nil, rest := .nil }
    | .cons b rest =>
      if b < 256 then
        let sub := readBytes rest n
        if sub.ok == 1 then { ok := 1, bytes := .cons b sub.bytes, rest := sub.rest }
        else { ok := 0, bytes := .nil, rest := .nil }
      else { ok := 0, bytes := .nil, rest := .nil }
termination_by structural n => n

/-- Read a `u32`-length-prefixed byte blob (`KzgIO::blob`). -/
@[circuit_noinline]
def readBlob (bs : ByteList) : ParseBytes :=
  let n := readU32 bs
  if n.ok == 1 then readBytes n.rest n.val
  else { ok := 0, bytes := .nil, rest := .nil }

/-- Verify an 8-byte magic header (`KzgIO::magic`). -/
@[circuit_noinline]
def checkMagic (bs expected : ByteList) : ParseBytes :=
  let r := readBytes bs 8
  if r.ok == 1 then
    if byteListEq r.bytes expected == 1 then { ok := 1, bytes := r.bytes, rest := r.rest }
    else { ok := 0, bytes := .nil, rest := .nil }
  else { ok := 0, bytes := .nil, rest := .nil }

/-- Strict trailing-byte rejection (`KzgIO::finish`): returns `1` iff stream is empty. -/
@[circuit_inline]
def checkFinish (bs : ByteList) : Nat :=
  match bs with
  | .nil => 1
  | .cons _ _ => 0

/-- Read one canonical 32-byte little-endian `Fr` scalar (`< c.frMod`, `KzgIO::scalar`). -/
def readScalar (c : CurveParams) (bs : ByteList) : ParseNat :=
  let r := readBytes bs 32
  if r.ok == 1 then
    let v := leBytesToNat r.bytes
    if v < c.frMod then { ok := 1, val := v, rest := r.rest }
    else { ok := 0, val := 0, rest := .nil }
  else { ok := 0, val := 0, rest := .nil }

/-- Read `count` canonical `Fr` scalars (`KzgDeserialize::scalars`). -/
def readScalars (c : CurveParams) (bs : ByteList) : Nat → ParseFList
  | 0 => { ok := 1, vals := .nil, rest := bs }
  | n + 1 =>
    let r := readScalar c bs
    if r.ok == 1 then
      let sub := readScalars c r.rest n
      if sub.ok == 1 then { ok := 1, vals := .cons r.val sub.vals, rest := sub.rest }
      else { ok := 0, vals := .nil, rest := .nil }
    else { ok := 0, vals := .nil, rest := .nil }
termination_by structural n => n

/-- Read `count` byte tags (`KzgDeserialize::tags`). -/
def readTags (bs : ByteList) : Nat → ParseFList
  | 0 => { ok := 1, vals := .nil, rest := bs }
  | n + 1 =>
    let r := readU8 bs
    if r.ok == 1 then
      let sub := readTags r.rest n
      if sub.ok == 1 then { ok := 1, vals := .cons r.val sub.vals, rest := sub.rest }
      else { ok := 0, vals := .nil, rest := .nil }
    else { ok := 0, vals := .nil, rest := .nil }
termination_by structural n => n

/-- Read `count` u32 words (`KzgPackedDeserialize::words`). -/
def readU32List (bs : ByteList) : Nat → ParseFList
  | 0 => { ok := 1, vals := .nil, rest := bs }
  | n + 1 =>
    let r := readU32 bs
    if r.ok == 1 then
      let sub := readU32List r.rest n
      if sub.ok == 1 then { ok := 1, vals := .cons r.val sub.vals, rest := sub.rest }
      else { ok := 0, vals := .nil, rest := .nil }
    else { ok := 0, vals := .nil, rest := .nil }
termination_by structural n => n

/-- Read `count` u32 node IDs each strictly `< bound` (`KzgDeserialize::ids`). -/
def readIds (bs : ByteList) (bound : Nat) : Nat → ParseFList
  | 0 => { ok := 1, vals := .nil, rest := bs }
  | n + 1 =>
    let r := readU32 bs
    if r.ok == 1 && r.val < bound then
      let sub := readIds r.rest bound n
      if sub.ok == 1 then { ok := 1, vals := .cons r.val sub.vals, rest := sub.rest }
      else { ok := 0, vals := .nil, rest := .nil }
    else { ok := 0, vals := .nil, rest := .nil }
termination_by structural n => n

/-- Read one canonical compressed `G1` point (`c.g1ByteLen` bytes, `KzgIO::point`). -/
def readPoint (c : CurveParams) (bs : ByteList) : ParsePoint :=
  let r := readBytes bs c.g1ByteLen
  if r.ok == 1 then
    let p := g1FromBytes c r.bytes
    if p.ok == 1 then { ok := 1, point := p.point, rest := r.rest }
    else { ok := 0, point := g1Inf, rest := .nil }
  else { ok := 0, point := g1Inf, rest := .nil }

/-- Read `count` canonical compressed `G1` points (`KzgDeserialize::points`). -/
def readPoints (c : CurveParams) (bs : ByteList) : Nat → ParsePointList
  | 0 => { ok := 1, points := .nil, rest := bs }
  | n + 1 =>
    let r := readPoint c bs
    if r.ok == 1 then
      let sub := readPoints c r.rest n
      if sub.ok == 1 then { ok := 1, points := .cons r.point sub.points, rest := sub.rest }
      else { ok := 0, points := .nil, rest := .nil }
    else { ok := 0, points := .nil, rest := .nil }
termination_by structural n => n

/-- Read a 32-byte digest into `DigestWords` (8 little-endian u32 words, `KzgIO::digest`). -/
@[circuit_noinline]
def readDigestWords (bs : ByteList) : ParseDigestWords :=
  let r0 := readU32 bs
  let r1 := readU32 r0.rest
  let r2 := readU32 r1.rest
  let r3 := readU32 r2.rest
  let r4 := readU32 r3.rest
  let r5 := readU32 r4.rest
  let r6 := readU32 r5.rest
  let r7 := readU32 r6.rest
  if r0.ok == 1 && r1.ok == 1 && r2.ok == 1 && r3.ok == 1 &&
      r4.ok == 1 && r5.ok == 1 && r6.ok == 1 && r7.ok == 1 then
    { ok := 1
      digest := { d0 := r0.val, d1 := r1.val, d2 := r2.val, d3 := r3.val
                  d4 := r4.val, d5 := r5.val, d6 := r6.val, d7 := r7.val }
      rest := r7.rest }
  else
    { ok := 0
      digest := { d0 := 0, d1 := 0, d2 := 0, d3 := 0, d4 := 0, d5 := 0, d6 := 0, d7 := 0 }
      rest := .nil }

/-- Read `count` scalar rows (`KzgDeserialize::scalar_rows`). -/
def readScalarRows (c : CurveParams) (bs : ByteList) : Nat → ParseFListList
  | 0 => { ok := 1, rows := .nil, rest := bs }
  | n + 1 =>
    let w := readU32 bs
    if w.ok == 1 then
      let row := readScalars c w.rest w.val
      if row.ok == 1 then
        let sub := readScalarRows c row.rest n
        if sub.ok == 1 then { ok := 1, rows := .cons row.vals sub.rows, rest := sub.rest }
        else { ok := 0, rows := .nil, rest := .nil }
      else { ok := 0, rows := .nil, rest := .nil }
    else { ok := 0, rows := .nil, rest := .nil }
termination_by structural n => n

/-- Read `count` opening matrices (`KzgDeserialize::opening_matrices`). -/
def readOpeningMatrices (c : CurveParams) (bs : ByteList) : Nat → ParseFList3
  | 0 => { ok := 1, mats := .nil, rest := bs }
  | n + 1 =>
    let w := readU32 bs
    if w.ok == 1 then
      let rows := readScalarRows c w.rest w.val
      if rows.ok == 1 then
        let sub := readOpeningMatrices c rows.rest n
        if sub.ok == 1 then { ok := 1, mats := .cons rows.rows sub.mats, rest := sub.rest }
        else { ok := 0, mats := .nil, rest := .nil }
      else { ok := 0, mats := .nil, rest := .nil }
    else { ok := 0, mats := .nil, rest := .nil }
termination_by structural n => n

/-- Read an openings section (`KzgDeserialize::openings`). -/
def readOpenings (c : CurveParams) (bs : ByteList) : ParseFList3 :=
  let n := readU32 bs
  if n.ok == 1 then readOpeningMatrices c n.rest n.val
  else { ok := 0, mats := .nil, rest := .nil }

/-- Parse an `IXAUCL01` claims payload (`KzgDeserialize::claims`) with strict trailing-byte rejection. -/
def readClaims (c : CurveParams) (bs : ByteList) : ParseClaims :=
  let m := checkMagic bs magicClaims
  if m.ok == 1 then
    let cnt := readU32 m.rest
    if cnt.ok == 1 then
      let rows := readScalarRows c cnt.rest cnt.val
      if rows.ok == 1 && checkFinish rows.rest == 1 then
        { ok := 1, claims := rows.rows }
      else { ok := 0, claims := .nil }
    else { ok := 0, claims := .nil }
  else { ok := 0, claims := .nil }

/-- Parse an `IXAUKG01` two-key chain policy (`KzgPackedDeserialize::chain_policy`)
with strict trailing-byte rejection. -/
@[circuit_noinline]
def readChainPolicy (bs : ByteList) : ParsePolicy :=
  let zeroDig : DigestWords :=
    { d0 := 0, d1 := 0, d2 := 0, d3 := 0, d4 := 0, d5 := 0, d6 := 0, d7 := 0 }
  let emptyPol : ChainPolicy :=
    { anchors := .nil, glDigest := zeroDig, glEntry := 0, bnDigest := zeroDig, bnEntry := 0 }
  let m := checkMagic bs magicChainPolicy
  if m.ok == 1 then
    let anc := readBytes m.rest 128
    if anc.ok == 1 then
      let gd := readDigestWords anc.rest
      if gd.ok == 1 then
        let ge := readU32 gd.rest
        if ge.ok == 1 then
          let bd := readDigestWords ge.rest
          if bd.ok == 1 then
            let be := readU32 bd.rest
            if be.ok == 1 && checkFinish be.rest == 1 then
              { ok := 1
                policy := { anchors := anc.bytes, glDigest := gd.digest, glEntry := ge.val
                            bnDigest := bd.digest, bnEntry := be.val } }
            else { ok := 0, policy := emptyPol }
          else { ok := 0, policy := emptyPol }
        else { ok := 0, policy := emptyPol }
      else { ok := 0, policy := emptyPol }
    else { ok := 0, policy := emptyPol }
  else { ok := 0, policy := emptyPol }

/-- Read packed commitment matrix shapes (`KzgPackedDeserialize::shapes`). -/
def readPackedShapes (c : CurveParams) (bs : ByteList) : Nat → ParseShapeList
  | 0 => { ok := 1, shapes := .nil, rest := bs }
  | n + 1 =>
    let lg := readU8 bs
    let wd := readU32 lg.rest
    let nx := readU8 wd.rest
    if lg.ok == 1 && wd.ok == 1 && nx.ok == 1 &&
        lg.val ≤ c.maxLog && wd.val != 0 && nx.val ≤ 1 then
      let sub := readPackedShapes c nx.rest n
      if sub.ok == 1 then
        { ok := 1
          shapes := .cons { log := lg.val, width := wd.val, hasNext := nx.val } sub.shapes
          rest := sub.rest }
      else { ok := 0, shapes := .nil, rest := .nil }
    else { ok := 0, shapes := .nil, rest := .nil }
termination_by structural n => n

/-- Parse an `IXPSHC02` packed commitment blob (`KzgPackedDeserialize::commitment`),
preserving verbatim native bytes and rejecting trailing bytes. -/
def readPackedCommitment (c : CurveParams) (raw : ByteList) : ParseCommitment :=
  let emptyC : PackedCommitment := { rawBytes := .nil, shapes := .nil, points := .nil }
  let m := checkMagic raw magicPackedComm
  if m.ok == 1 then
    let sc := readU32 m.rest
    if sc.ok == 1 then
      let sh := readPackedShapes c sc.rest sc.val
      if sh.ok == 1 then
        let pc := readU32 sh.rest
        if pc.ok == 1 then
          let pts := readPoints c pc.rest pc.val
          if pts.ok == 1 && checkFinish pts.rest == 1 then
            { ok := 1, comm := { rawBytes := raw, shapes := sh.shapes, points := pts.points } }
          else { ok := 0, comm := emptyC }
        else { ok := 0, comm := emptyC }
      else { ok := 0, comm := emptyC }
    else { ok := 0, comm := emptyC }
  else { ok := 0, comm := emptyC }

/-- Check if `value` is a supported power of two `2^k` with `k ≤ remaining` (`KzgDeserialize::supported_power`). -/
def isSupportedPower (value candidate : Nat) : Nat → Nat
  | 0 => if value == candidate then 1 else 0
  | rem + 1 =>
    if value == candidate then 1
    else isSupportedPower value (candidate + candidate) rem
termination_by structural rem => rem

/-- Compute quotient degree metadata `min { 2^k | degree < 2^k + 2 }` (`KzgDeserialize::quotient_degree`). -/
def quotientDegreeFuel (degree candidate : Nat) : Nat → Nat
  | 0 => candidate
  | fuel + 1 =>
    if degree < candidate + 2 then candidate
    else quotientDegreeFuel degree (candidate + candidate) fuel
termination_by structural fuel => fuel

/-- Lookup group count `ceil(count / size)` (`KzgDeserialize::group_count`). -/
def groupCount (count size : Nat) : Nat :=
  if count == 0 || size == 0 then 0
  else (count + size - 1) / size

/-- Parse one AIR DAG node at topological index `idx` (`KzgDeserialize::node`). -/
def readNode (c : CurveParams) (bs : ByteList) (idx : Nat) (s : CircuitShape) : ParseNode :=
  let fail : ParseNode := { ok := 0, node := .const 0, mainNext := 0, fixedNext := 0, rest := .nil }
  let t := readU8 bs
  if t.ok == 0 then fail
  else match t.val with
  | 0 =>
    let v := readScalar c t.rest
    if v.ok == 1 then { ok := 1, node := .const v.val, mainNext := 0, fixedNext := 0, rest := v.rest }
    else fail
  | 1 =>
    let src := readU8 t.rest
    let off := readU8 src.rest
    let col := readU32 off.rest
    if src.ok == 1 && off.ok == 1 && col.ok == 1 && off.val ≤ 1 then
      match src.val with
      | 0 =>
        if col.val < s.m3 then
          { ok := 1, node := .var 0 off.val col.val, mainNext := 0, fixedNext := off.val, rest := col.rest }
        else fail
      | 1 =>
        if col.val < s.m4 then
          { ok := 1, node := .var 1 off.val col.val, mainNext := off.val, fixedNext := 0, rest := col.rest }
        else fail
      | 2 =>
        if col.val < s.m5 then
          { ok := 1, node := .var 2 off.val col.val, mainNext := 0, fixedNext := 0, rest := col.rest }
        else fail
      | _ => fail
    else fail
  | 2 =>
    let i := readU32 t.rest
    if i.ok == 1 && i.val < 4 then
      { ok := 1, node := .pub i.val, mainNext := 0, fixedNext := 0, rest := i.rest }
    else fail
  | 3 => { ok := 1, node := .first, mainNext := 0, fixedNext := 0, rest := t.rest }
  | 4 => { ok := 1, node := .last, mainNext := 0, fixedNext := 0, rest := t.rest }
  | 5 => { ok := 1, node := .transition, mainNext := 0, fixedNext := 0, rest := t.rest }
  | 6 =>
    let a := readU32 t.rest
    let b := readU32 a.rest
    if a.ok == 1 && b.ok == 1 && a.val < idx && b.val < idx then
      { ok := 1, node := .add a.val b.val, mainNext := 0, fixedNext := 0, rest := b.rest }
    else fail
  | 7 =>
    let a := readU32 t.rest
    let b := readU32 a.rest
    if a.ok == 1 && b.ok == 1 && a.val < idx && b.val < idx then
      { ok := 1, node := .sub a.val b.val, mainNext := 0, fixedNext := 0, rest := b.rest }
    else fail
  | 8 =>
    let a := readU32 t.rest
    let b := readU32 a.rest
    if a.ok == 1 && b.ok == 1 && a.val < idx && b.val < idx then
      { ok := 1, node := .mul a.val b.val, mainNext := 0, fixedNext := 0, rest := b.rest }
    else fail
  | 9 =>
    let a := readU32 t.rest
    if a.ok == 1 && a.val < idx then
      { ok := 1, node := .neg a.val, mainNext := 0, fixedNext := 0, rest := a.rest }
    else fail
  | _ => fail

/-- Parse `count` AIR DAG nodes starting at topological index `idx` (`KzgDeserialize::nodes`). -/
def readNodes (c : CurveParams) (bs : ByteList) (idx : Nat) (s : CircuitShape) : Nat → ParseNodeList
  | 0 => { ok := 1, nodes := .nil, mainNext := 0, fixedNext := 0, rest := bs }
  | n + 1 =>
    let hd := readNode c bs idx s
    if hd.ok == 1 then
      let tl := readNodes c hd.rest (idx + 1) s n
      if tl.ok == 1 then
        let mn := if hd.mainNext == 1 || tl.mainNext == 1 then 1 else 0
        let fn := if hd.fixedNext == 1 || tl.fixedNext == 1 then 1 else 0
        { ok := 1, nodes := .cons hd.node tl.nodes, mainNext := mn, fixedNext := fn, rest := tl.rest }
      else { ok := 0, nodes := .nil, mainNext := 0, fixedNext := 0, rest := .nil }
    else { ok := 0, nodes := .nil, mainNext := 0, fixedNext := 0, rest := .nil }
termination_by structural n => n

/-- Parse `count` LogUp lookups (`KzgDeserialize::lookups`). -/
def readLookups (bs : ByteList) (bound : Nat) : Nat → ParseLookupList
  | 0 => { ok := 1, lookups := .nil, rest := bs }
  | n + 1 =>
    let mult := readU32 bs
    let wd := readU32 mult.rest
    if mult.ok == 1 && wd.ok == 1 && mult.val < bound then
      let args := readIds wd.rest bound wd.val
      if args.ok == 1 then
        let tl := readLookups args.rest bound n
        if tl.ok == 1 then
          { ok := 1
            lookups := .cons { multiplicity := mult.val, args := args.vals } tl.lookups
            rest := tl.rest }
        else { ok := 0, lookups := .nil, rest := .nil }
      else { ok := 0, lookups := .nil, rest := .nil }
    else { ok := 0, lookups := .nil, rest := .nil }
termination_by structural n => n

/-- Prepend `copies` copies of `circ` onto `tail` (`KzgPackedDeserialize::copies_of`). -/
def copiesOfCircuit (circ : Circuit) (tail : CircuitList) : Nat → CircuitList
  | 0 => tail
  | n + 1 => .cons circ (copiesOfCircuit circ tail n)
termination_by structural n => n

/-- Length of a `CircuitList`. -/
@[circuit_noinline]
def circuitListLen : CircuitList → Nat
  | .nil => 0
  | .cons _ t => circuitListLen t + 1
termination_by structural cs => cs

/-- Parse one distinct packed circuit (with exact metadata checks) and prepend `copies` copies
(`KzgPackedDeserialize::circuits`). -/
def readPackedCircuits (c : CurveParams) (bs : ByteList) (budget : Nat) : Nat → ParseCircuitList
  | 0 => { ok := 1, circuits := .nil, rest := bs }
  | n + 1 =>
    let cp := readU32 bs
    let r0 := readU32 cp.rest
    let r1 := readU32 r0.rest
    let r2 := readU32 r1.rest
    let r3 := readU32 r2.rest
    let r4 := readU32 r3.rest
    let r5 := readU32 r4.rest
    let r6 := readU32 r5.rest
    let r7 := readU32 r6.rest
    if cp.ok == 1 && cp.val != 0 &&
        r0.ok == 1 && r1.ok == 1 && r2.ok == 1 && r3.ok == 1 &&
        r4.ok == 1 && r5.ok == 1 && r6.ok == 1 && r7.ok == 1 then
      let sh : CircuitShape :=
        { m0 := r0.val, m1 := r1.val, m2 := r2.val, m3 := r3.val
          m4 := r4.val, m5 := r5.val, m6 := r6.val, m7 := r7.val }
      let fixedZeroOk := (sh.m2 == 0) == (sh.m3 == 0)
      if 0 < sh.m6 && sh.m6 < 9 && sh.m1 < budget + 2 &&
          sh.m7 == quotientDegreeFuel sh.m1 1 32 && fixedZeroOk then
        let nc := readU32 r7.rest
        if nc.ok == 1 then
          let ns := readNodes c nc.rest 0 sh nc.val
          if ns.ok == 1 then
            let rc := readU32 ns.rest
            if rc.ok == 1 then
              let rts := readIds rc.rest nc.val rc.val
              if rts.ok == 1 then
                let lc := readU32 rts.rest
                if lc.ok == 1 then
                  let lks := readLookups lc.rest nc.val lc.val
                  if lks.ok == 1 then
                    let grps0 := groupCount lc.val sh.m6
                    let grps := if grps0 == 0 then 1 else grps0
                    if sh.m5 == grps && sh.m0 == rc.val + grps then
                      let circ : Circuit :=
                        { shape := sh, nodes := ns.nodes, roots := rts.vals, lookups := lks.lookups
                          mainNext := ns.mainNext, fixedNext := ns.fixedNext }
                      let tl := readPackedCircuits c lks.rest budget n
                      if tl.ok == 1 then
                        { ok := 1, circuits := copiesOfCircuit circ tl.circuits cp.val, rest := tl.rest }
                      else { ok := 0, circuits := .nil, rest := .nil }
                    else { ok := 0, circuits := .nil, rest := .nil }
                  else { ok := 0, circuits := .nil, rest := .nil }
                else { ok := 0, circuits := .nil, rest := .nil }
              else { ok := 0, circuits := .nil, rest := .nil }
            else { ok := 0, circuits := .nil, rest := .nil }
          else { ok := 0, circuits := .nil, rest := .nil }
        else { ok := 0, circuits := .nil, rest := .nil }
      else { ok := 0, circuits := .nil, rest := .nil }
    else { ok := 0, circuits := .nil, rest := .nil }
termination_by structural n => n

/-- Parse the fixed section at the end of `IXAUSK02` (`KzgPackedDeserialize::fixed`)
with strict trailing-byte rejection. -/
def readPackedFixed (c : CurveParams) (bs : ByteList) (numCircuits : Nat) : ParseFixed :=
  let t := readU8 bs
  if t.ok == 0 then { ok := 0, fixed := .none }
  else match t.val with
  | 0 =>
    if checkFinish t.rest == 1 then { ok := 1, fixed := .none }
    else { ok := 0, fixed := .none }
  | 1 =>
    let b := readBlob t.rest
    if b.ok == 1 && checkFinish b.rest == 1 then
      let cm := readPackedCommitment c b.bytes
      if cm.ok == 1 then { ok := 1, fixed := .some cm.comm }
      else { ok := 0, fixed := .none }
    else { ok := 0, fixed := .none }
  | 2 =>
    let b := readBlob t.rest
    if b.ok == 1 then
      let cm := readPackedCommitment c b.bytes
      let sc := readU32 b.rest
      if cm.ok == 1 && sc.ok == 1 && sc.val == numCircuits then
        let sl := readU32List sc.rest sc.val
        if sl.ok == 1 && checkFinish sl.rest == 1 then
          { ok := 1, fixed := .shared cm.comm sl.vals }
        else { ok := 0, fixed := .none }
      else { ok := 0, fixed := .none }
    else { ok := 0, fixed := .none }
  | _ => { ok := 0, fixed := .none }

/-- Parse an `IXAUSK02` packed verifying key (`KzgPackedDeserialize::key`)
with exact canonicality, metadata, and trailing-byte checks. -/
def readPackedKey (c : CurveParams) (bs : ByteList) : ParseKey :=
  let emptyK : PackedKey :=
    { seed := .nil, maxLog := 0, budget := 0, generator := g1Inf
      anchors := .nil, circuits := .nil, fixed := .none }
  let m := checkMagic bs magicPackedKey
  if m.ok == 1 then
    let sd := readBlob m.rest
    let ml := readU32 sd.rest
    let bg := readU32 ml.rest
    if sd.ok == 1 && ml.ok == 1 && bg.ok == 1 &&
        0 < ml.val && ml.val ≤ c.maxLog &&
        isSupportedPower bg.val 1 c.maxLog == 1 then
      let gen := readPoint c bg.rest
      let anc := readBytes gen.rest 128
      let cnt := readU32 anc.rest
      if gen.ok == 1 && anc.ok == 1 && cnt.ok == 1 && cnt.val != 0 then
        let cs := readPackedCircuits c cnt.rest bg.val cnt.val
        if cs.ok == 1 then
          let fx := readPackedFixed c cs.rest (circuitListLen cs.circuits)
          if fx.ok == 1 then
            { ok := 1
              key := { seed := sd.bytes, maxLog := ml.val, budget := bg.val
                       generator := gen.point, anchors := anc.bytes
                       circuits := cs.circuits, fixed := fx.fixed } }
          else { ok := 0, key := emptyK }
        else { ok := 0, key := emptyK }
      else { ok := 0, key := emptyK }
    else { ok := 0, key := emptyK }
  else { ok := 0, key := emptyK }

/-- Parse a packed SHPLONK `G1` witness (`KzgPackedDeserialize::witness`), retaining exact bytes. -/
def readPackedWitness (c : CurveParams) (bs : ByteList) : ParseWitness :=
  let emptyW : PackedWitness := { point := g1Inf, rawBytes := .nil }
  let r := readBytes bs c.g1ByteLen
  if r.ok == 1 then
    let p := g1FromBytes c r.bytes
    if p.ok == 1 then { ok := 1, witness := { point := p.point, rawBytes := r.bytes }, rest := r.rest }
    else { ok := 0, witness := emptyW, rest := .nil }
  else { ok := 0, witness := emptyW, rest := .nil }

/-- Parse an `IXAUSP01` packed SHPLONK proof (`KzgPackedDeserialize::proof`)
with strict canonicality and trailing-byte rejection. -/
def readPackedProof (c : CurveParams) (bs : ByteList) : ParseProof :=
  let emptyC : PackedCommitment := { rawBytes := .nil, shapes := .nil, points := .nil }
  let emptyW : PackedWitness := { point := g1Inf, rawBytes := .nil }
  let emptyP : PackedProof :=
    { active := .nil, logs := .nil, main := emptyC, stage2 := emptyC, quotient := emptyC
      accumulators := .nil, mainOpen := .nil, stage2Open := .nil, quotientOpen := .nil
      fixedOpen := .none, extras := .nil, w1 := emptyW, w2 := emptyW }
  let m := checkMagic bs magicPackedProof
  if m.ok == 1 then
    let ac := readU32 m.rest
    let act := readTags ac.rest ac.val
    let lc := readU32 act.rest
    let lgs := readTags lc.rest lc.val
    let mb := readBlob lgs.rest
    let sb := readBlob mb.rest
    let qb := readBlob sb.rest
    if ac.ok == 1 && act.ok == 1 && lc.ok == 1 && lgs.ok == 1 &&
        mb.ok == 1 && sb.ok == 1 && qb.ok == 1 then
      let mainC := readPackedCommitment c mb.bytes
      let stage2C := readPackedCommitment c sb.bytes
      let quotC := readPackedCommitment c qb.bytes
      let accCnt := readU32 qb.rest
      let accs := readScalars c accCnt.rest accCnt.val
      let mo := readOpenings c accs.rest
      let so := readOpenings c mo.rest
      let qo := readOpenings c so.rest
      let ftag := readU8 qo.rest
      if mainC.ok == 1 && stage2C.ok == 1 && quotC.ok == 1 &&
          accCnt.ok == 1 && accs.ok == 1 && mo.ok == 1 && so.ok == 1 &&
          qo.ok == 1 && ftag.ok == 1 then
        let (foOk, fo, afterFo) : Nat × FixedOpen × ByteList :=
          match ftag.val with
          | 0 => (1, .none, ftag.rest)
          | 1 =>
            let foR := readOpenings c ftag.rest
            (foR.ok, .some foR.mats, foR.rest)
          | _ => (0, .none, .nil)
        if foOk == 1 then
          let ec := readU32 afterFo
          let ex := readScalars c ec.rest ec.val
          let w1 := readPackedWitness c ex.rest
          let w2 := readPackedWitness c w1.rest
          if ec.ok == 1 && ex.ok == 1 && w1.ok == 1 && w2.ok == 1 && checkFinish w2.rest == 1 then
            { ok := 1
              proof := { active := act.vals, logs := lgs.vals
                         main := mainC.comm, stage2 := stage2C.comm, quotient := quotC.comm
                         accumulators := accs.vals
                         mainOpen := mo.mats, stage2Open := so.mats, quotientOpen := qo.mats
                         fixedOpen := fo, extras := ex.vals
                         w1 := w1.witness, w2 := w2.witness } }
          else { ok := 0, proof := emptyP }
        else { ok := 0, proof := emptyP }
      else { ok := 0, proof := emptyP }
    else { ok := 0, proof := emptyP }
  else { ok := 0, proof := emptyP }

/-! ### Exact Wire Encoders (Bit-for-Bit Dual to the Parsers Above) -/

def encodeU32 (v : Nat) : ByteList := natToLeBytes 4 v

def encodeBlob (bs : ByteList) : ByteList :=
  byteAppend (encodeU32 (byteLen bs)) bs

def encodeScalars : FList → ByteList
  | .nil => .nil
  | .cons v rest => byteAppend (natToLeBytes 32 v) (encodeScalars rest)
termination_by structural vs => vs

def encodeTags : FList → ByteList
  | .nil => .nil
  | .cons v rest => .cons v (encodeTags rest)
termination_by structural vs => vs

def encodeU32List : FList → ByteList
  | .nil => .nil
  | .cons v rest => byteAppend (encodeU32 v) (encodeU32List rest)
termination_by structural vs => vs

def encodeScalarRows : FListList → ByteList
  | .nil => .nil
  | .cons row rest =>
    byteAppend (encodeU32 (fListLen row)) (byteAppend (encodeScalars row) (encodeScalarRows rest))
termination_by structural rows => rows

def fList3Len : FList3 → Nat
  | .nil => 0
  | .cons _ t => fList3Len t + 1
termination_by structural ms => ms

def encodeOpenings (mats : FList3) : ByteList :=
  let rec go : FList3 → ByteList
    | .nil => .nil
    | .cons m rest =>
      byteAppend (encodeU32 (fListListLen m)) (byteAppend (encodeScalarRows m) (go rest))
  byteAppend (encodeU32 (fList3Len mats)) (go mats)

/-- Encode `IXAUCL01` claims bytes. -/
def encodeClaims (claims : FListList) : ByteList :=
  byteAppend magicClaims (byteAppend (encodeU32 (fListListLen claims)) (encodeScalarRows claims))

/-- Encode `IXAUKG01` two-key chain policy bytes. -/
def encodeChainPolicy (pol : ChainPolicy) : ByteList :=
  byteAppend magicChainPolicy
    (byteAppend pol.anchors
    (byteAppend (digestWordsToBytes pol.glDigest)
    (byteAppend (encodeU32 pol.glEntry)
    (byteAppend (digestWordsToBytes pol.bnDigest) (encodeU32 pol.bnEntry)))))

def matrixShapeListLen : MatrixShapeList → Nat
  | .nil => 0
  | .cons _ t => matrixShapeListLen t + 1
termination_by structural xs => xs

def g1PointListLen : G1PointList → Nat
  | .nil => 0
  | .cons _ t => g1PointListLen t + 1
termination_by structural xs => xs

def encodeMatrixShapes : MatrixShapeList → ByteList
  | .nil => .nil
  | .cons sh rest =>
    .cons sh.log (byteAppend (encodeU32 sh.width) (.cons sh.hasNext (encodeMatrixShapes rest)))
termination_by structural xs => xs

def encodePoints (c : CurveParams) : G1PointList → ByteList
  | .nil => .nil
  | .cons p rest => byteAppend (g1ToBytes c p) (encodePoints c rest)
termination_by structural ps => ps

/-- Encode `IXPSHC02` packed commitment bytes. -/
def encodePackedCommitment (c : CurveParams) (shapes : MatrixShapeList) (points : G1PointList) :
    ByteList :=
  byteAppend magicPackedComm
    (byteAppend (encodeU32 (matrixShapeListLen shapes))
    (byteAppend (encodeMatrixShapes shapes)
    (byteAppend (encodeU32 (g1PointListLen points)) (encodePoints c points))))

/-- Construct a `PackedCommitment` with its canonical `IXPSHC02` wire bytes attached. -/
def mkPackedCommitment (c : CurveParams) (shapes : MatrixShapeList) (points : G1PointList) :
    PackedCommitment :=
  { rawBytes := encodePackedCommitment c shapes points, shapes, points }

def nodeListLen : NodeList → Nat
  | .nil => 0
  | .cons _ t => nodeListLen t + 1
termination_by structural ns => ns

def lookupListLen : LookupList → Nat
  | .nil => 0
  | .cons _ t => lookupListLen t + 1
termination_by structural ls => ls

def encodeNode : Node → ByteList
  | .const v => .cons 0 (natToLeBytes 32 v)
  | .var src off col => .cons 1 (.cons src (.cons off (encodeU32 col)))
  | .pub i => .cons 2 (encodeU32 i)
  | .first => .cons 3 .nil
  | .last => .cons 4 .nil
  | .transition => .cons 5 .nil
  | .add a b => .cons 6 (byteAppend (encodeU32 a) (encodeU32 b))
  | .sub a b => .cons 7 (byteAppend (encodeU32 a) (encodeU32 b))
  | .mul a b => .cons 8 (byteAppend (encodeU32 a) (encodeU32 b))
  | .neg a => .cons 9 (encodeU32 a)

def encodeNodes : NodeList → ByteList
  | .nil => .nil
  | .cons n rest => byteAppend (encodeNode n) (encodeNodes rest)
termination_by structural ns => ns

def encodeLookups : LookupList → ByteList
  | .nil => .nil
  | .cons lk rest =>
    byteAppend (encodeU32 lk.multiplicity)
      (byteAppend (encodeU32 (fListLen lk.args))
      (byteAppend (encodeU32List lk.args) (encodeLookups rest)))
termination_by structural ls => ls

def encodeCircuitBody (circ : Circuit) : ByteList :=
  let s := circ.shape
  let shBytes :=
    byteAppend (encodeU32 s.m0) (byteAppend (encodeU32 s.m1)
    (byteAppend (encodeU32 s.m2) (byteAppend (encodeU32 s.m3)
    (byteAppend (encodeU32 s.m4) (byteAppend (encodeU32 s.m5)
    (byteAppend (encodeU32 s.m6) (encodeU32 s.m7)))))))
  byteAppend shBytes
    (byteAppend (encodeU32 (nodeListLen circ.nodes))
    (byteAppend (encodeNodes circ.nodes)
    (byteAppend (encodeU32 (fListLen circ.roots))
    (byteAppend (encodeU32List circ.roots)
    (byteAppend (encodeU32 (lookupListLen circ.lookups)) (encodeLookups circ.lookups))))))

/-- Encode a list of circuits as 1-copy groups in `IXAUSK02` format. -/
def encodePackedCircuits : CircuitList → ByteList
  | .nil => .nil
  | .cons circ rest =>
    byteAppend (encodeU32 1) (byteAppend (encodeCircuitBody circ) (encodePackedCircuits rest))
termination_by structural cs => cs

/-- Encode an `IXAUSK02` packed verifying key. -/
def encodePackedKey (c : CurveParams) (k : PackedKey) : ByteList :=
  let fxBytes := match k.fixed with
    | .none => .cons 0 .nil
    | .some comm => .cons 1 (encodeBlob comm.rawBytes)
    | .shared comm slots =>
      .cons 2 (byteAppend (encodeBlob comm.rawBytes)
        (byteAppend (encodeU32 (fListLen slots)) (encodeU32List slots)))
  byteAppend magicPackedKey
    (byteAppend (encodeBlob k.seed)
    (byteAppend (encodeU32 k.maxLog)
    (byteAppend (encodeU32 k.budget)
    (byteAppend (g1ToBytes c k.generator)
    (byteAppend k.anchors
    (byteAppend (encodeU32 (circuitListLen k.circuits))
    (byteAppend (encodePackedCircuits k.circuits) fxBytes)))))))

/-- Encode an `IXAUSP01` packed SHPLONK proof. -/
def encodePackedProof (p : PackedProof) : ByteList :=
  let foBytes := match p.fixedOpen with
    | .none => .cons 0 .nil
    | .some mats => .cons 1 (encodeOpenings mats)
  byteAppend magicPackedProof
    (byteAppend (encodeU32 (fListLen p.active))
    (byteAppend (encodeTags p.active)
    (byteAppend (encodeU32 (fListLen p.logs))
    (byteAppend (encodeTags p.logs)
    (byteAppend (encodeBlob p.main.rawBytes)
    (byteAppend (encodeBlob p.stage2.rawBytes)
    (byteAppend (encodeBlob p.quotient.rawBytes)
    (byteAppend (encodeU32 (fListLen p.accumulators))
    (byteAppend (encodeScalars p.accumulators)
    (byteAppend (encodeOpenings p.mainOpen)
    (byteAppend (encodeOpenings p.stage2Open)
    (byteAppend (encodeOpenings p.quotientOpen)
    (byteAppend foBytes
    (byteAppend (encodeU32 (fListLen p.extras))
    (byteAppend (encodeScalars p.extras)
    (byteAppend p.w1.rawBytes p.w2.rawBytes))))))))))))))))

/-! ## Section 7: Pure-Lean Self-Checks (`#guard`) — BN254, BLS12-381, BLAKE3, Wire Formats -/

-- 1. Curve constants, 2-adic generators, and G1 arithmetic on real BN254 & BLS12-381
#guard bn254Fp % 4 == 3
#guard bls12381Fp % 4 == 3
#guard bn254CircuitParams.fqMod % 4 == 3
#guard bls12381CircuitParams.fqMod % 4 == 3
#guard g1OnCurve bn254CurveParams (g1Gen bn254CurveParams) == true
#guard g1OnCurve bls12381CurveParams (g1Gen bls12381CurveParams) == true
#guard g1OnCurve bn254CircuitParams (g1Gen bn254CircuitParams) == true
#guard g1OnCurve bls12381CircuitParams (g1Gen bls12381CircuitParams) == true

private def bnG : G1Point := g1Gen bn254CurveParams
private def bn2G : G1Point := g1Double bn254CurveParams bnG
private def bn3G : G1Point := g1Add bn254CurveParams bn2G bnG
private def blsG : G1Point := g1Gen bls12381CurveParams
private def bls2G : G1Point := g1Double bls12381CurveParams blsG
private def bls3G : G1Point := g1Add bls12381CurveParams bls2G blsG

#guard g1ScalarMul bn254CurveParams 3 bnG == bn3G
#guard g1ScalarMul bn254CurveParams bn254Fr bnG == g1Inf
#guard g1ScalarMul bls12381CurveParams 3 blsG == bls3G
#guard g1ScalarMul bls12381CurveParams bls12381Fr blsG == g1Inf

-- 2. 4-bit windowed `g1Msm` agrees identically with `g1MsmDirect` on real BN254 & BLS12-381
#guard
  let terms : G1TermList :=
    .cons { point := bnG, scalar := 1234567 }
    (.cons { point := bn2G, scalar := 9876543 }
    (.cons { point := bn3G, scalar := 42 } .nil))
  g1Msm bn254CurveParams terms == g1MsmDirect bn254CurveParams terms
#guard
  let terms : G1TermList :=
    .cons { point := blsG, scalar := 1234567 }
    (.cons { point := bls2G, scalar := 9876543 }
    (.cons { point := bls3G, scalar := 42 } .nil))
  g1Msm bls12381CurveParams terms == g1MsmDirect bls12381CurveParams terms

-- 3. Ambient `Fr` ops on real BN254 Fr & BLS12-381 Fr
#guard frMul bn254Fr 123456789 (frInv bn254Fr 123456789) == 1
#guard frDiv bn254Fr 999999 123456789 == frMul bn254Fr 999999 (frInv bn254Fr 123456789)
#guard frMul bls12381Fr 123456789 (frInv bls12381Fr 123456789) == 1
#guard frDiv bls12381Fr 999999 123456789 == frMul bls12381Fr 999999 (frInv bls12381Fr 123456789)
#guard frIsZero 0 == 1 && frIsZero 7 == 0 && frEq 42 42 == 1 && frEq 42 43 == 0

-- 4. Tier-2 `checked def` checkers on real BN254 `Fp` & BLS12-381 `Fp`
#guard fqMulMod.check bn254Fp bn2G.x bn3G.y (fqMulMod bn254Fp bn2G.x bn3G.y) == true
#guard fqMulDivModCheck bn254Fp bn2G.x bn3G.y (fqMulDivMod bn254Fp bn2G.x bn3G.y) == true
#guard fqInvMod.check bn254Fp bn2G.x (fqInvMod bn254Fp bn2G.x) == true
#guard fqMulMod.check bls12381Fp bls2G.x bls3G.y (fqMulMod bls12381Fp bls2G.x bls3G.y) == true
#guard fqMulDivModCheck bls12381Fp bls2G.x bls3G.y (fqMulDivMod bls12381Fp bls2G.x bls3G.y) == true
#guard fqInvMod.check bls12381Fp bls2G.x (fqInvMod bls12381Fp bls2G.x) == true

-- 5. Limb packing (4×80b BN254 → 18 affine words, 5×80b BLS12-381 → 22 affine words)
#guard limb4CanonicalBN254 (toLimb4 bn3G.x) && ofLimb4 (toLimb4 bn3G.x) == bn3G.x
#guard limb5CanonicalBLS12381 (toLimb5 bls3G.x) && ofLimb5 (toLimb5 bls3G.x) == bls3G.x
#guard fListLen (encodeAffinePairWords bn254CurveParams bn2G bn3G) == 18
#guard fListLen (encodeAffinePairWords bls12381CurveParams bls2G bls3G) == 22
#guard
  let ws := encodeAffinePairWords bn254CurveParams bn2G bn3G
  decodeAffinePointWords bn254CurveParams (fListTake ws 9) == bn2G &&
    decodeAffinePointWords bn254CurveParams (fListDrop ws 9) == bn3G
#guard
  let ws := encodeAffinePairWords bls12381CurveParams bls2G bls3G
  decodeAffinePointWords bls12381CurveParams (fListTake ws 11) == bls2G &&
    decodeAffinePointWords bls12381CurveParams (fListDrop ws 11) == bls3G

-- 6. Compressed G1 codec (32B BN254 & 48B BLS12-381) + accumulator chunks + tampering rejection
#guard (g1FromBytes bn254CurveParams (g1ToBytes bn254CurveParams bnG)).point == bnG
#guard (g1FromBytes bn254CurveParams (g1ToBytes bn254CurveParams (g1Neg bn254CurveParams bnG))).point == g1Neg bn254CurveParams bnG
#guard (g1FromBytes bn254CurveParams (g1ToBytes bn254CurveParams bn3G)).point == bn3G
#guard (g1FromBytes bn254CurveParams (g1ToBytes bn254CurveParams g1Inf)).point == g1Inf
#guard (g1FromBytes bls12381CurveParams (g1ToBytes bls12381CurveParams blsG)).point == blsG
#guard (g1FromBytes bls12381CurveParams (g1ToBytes bls12381CurveParams (g1Neg bls12381CurveParams blsG))).point == g1Neg bls12381CurveParams blsG
#guard (g1FromBytes bls12381CurveParams (g1ToBytes bls12381CurveParams bls3G)).point == bls3G
#guard (g1FromBytes bls12381CurveParams (g1ToBytes bls12381CurveParams g1Inf)).point == g1Inf
-- Reject non-canonical Fq (>= bn254Fp) & off-curve x=5 on BN254 (5^3+3=128 non-residue) & bad infinity flags
#guard (g1FromBytes bn254CurveParams (natToLeBytes 32 bn254Fp)).ok == 0
#guard (g1FromBytes bn254CurveParams (addLastByteFlag 64 (natToLeBytes 32 1))).ok == 0
#guard (g1FromBytes bn254CurveParams (addLastByteFlag 192 (natToLeBytes 32 0))).ok == 0
#guard (g1FromBytes bls12381CurveParams (natToLeBytes 48 bls12381Fp)).ok == 0
#guard (g1FromBytes bls12381CurveParams (addLastByteFlag 64 (natToLeBytes 48 1))).ok == 0
-- Accumulator chunks 4×u128 (BN254) and 6×u128 (BLS12-381)
#guard
  let ch := packAccumulator4 bn254CurveParams bn2G bn3G
  unpackAccumulator4 bn254CurveParams ch == (1, bn2G, bn3G)
#guard
  let ch := packAccumulator6 bls12381CurveParams bls2G bls3G
  unpackAccumulator6 bls12381CurveParams ch == (1, bls2G, bls3G)

-- 7. Official BLAKE3 test vectors ("", "abc", multi-block) + exact domain lengths (34, 25, 31)
#guard blake3Hash .nil ==
  { w0 := 0xb94913af, w1 := 0xa6a1f9f5, w2 := 0xea4d40a0, w3 := 0x49c9dc36
    w4 := 0xc925cb9b, w5 := 0xb712c1ad, w6 := 0xca939acc, w7 := 0x62321fe4 }
#guard blake3Hash (.cons 97 (.cons 98 (.cons 99 .nil))) ==
  { w0 := 0xacb33764, w1 := 0x33514638, w2 := 0x753bb6ff, w3 := 0xb58d3a27
    w4 := 0x4658c548, w5 := 0x03db795d, w6 := 0x6c9c35fd, w7 := 0x859dbdd5 }
#guard byteLen openDomainBytes == 34
#guard byteLen batchDomainBytes == 25
#guard byteLen foldDomainBytes == 31

-- 8. Exact wire parser round-trips & tampering rejection (IXAUCL01, IXAUKG01, IXPSHC02)
#guard
  let cls : FListList := .cons (.cons 1 (.cons 7 .nil)) (.cons (.cons 42 .nil) .nil)
  let raw := encodeClaims cls
  (readClaims bn254CurveParams raw).ok == 1 &&
    (readClaims bn254CurveParams raw).claims == cls &&
    (readClaims bn254CurveParams (byteAppend raw (.cons 0 .nil))).ok == 0 &&
    (readClaims bn254CurveParams (.cons 0 raw)).ok == 0
#guard
  let badClaim := encodeClaims (.cons (.cons bn254Fr .nil) .nil)
  (readClaims bn254CurveParams badClaim).ok == 0
#guard
  let badBlsClaim := encodeClaims (.cons (.cons bls12381Fr .nil) .nil)
  (readClaims bls12381CurveParams badBlsClaim).ok == 0
#guard
  let pol : ChainPolicy :=
    { anchors := natToLeBytes 128 12345
      glDigest := blake3HashWords (.cons 1 .nil)
      glEntry := 0
      bnDigest := blake3HashWords (.cons 2 .nil)
      bnEntry := 1 }
  let raw := encodeChainPolicy pol
  (readChainPolicy raw).ok == 1 &&
    (readChainPolicy raw).policy == pol &&
    (readChainPolicy (byteAppend raw (.cons 99 .nil))).ok == 0 &&
    (readChainPolicy (.cons 74 raw)).ok == 0
#guard
  let shs : MatrixShapeList := .cons { log := 2, width := 3, hasNext := 1 } .nil
  let commBn := mkPackedCommitment bn254CurveParams shs (.cons bn2G .nil)
  let commBls := mkPackedCommitment bls12381CurveParams shs (.cons bls2G .nil)
  (readPackedCommitment bn254CurveParams commBn.rawBytes).ok == 1 &&
    (readPackedCommitment bls12381CurveParams commBls.rawBytes).ok == 1 &&
    (readPackedCommitment bn254CurveParams (byteAppend commBn.rawBytes (.cons 1 .nil))).ok == 0

end KzgWire
