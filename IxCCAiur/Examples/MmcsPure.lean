import Ix.Compile.CircuitContract

/-! # Pure Annotated Lean 4 `MultiStark/Mmcs` Vertical Slice (`MmcsPure`)

Faithful, idiomatic pure Lean 4 port of `MultiStark/MultiStark/Modules/Mmcs.lean`
(together with the helpers it invokes from `StarkHash.lean` and `Pcs.lean`),
annotated with `open scoped Ix.Circuit` directives (`@[circuit_inline]`,
`@[circuit_noinline]`, `@[circuit_budget ...]`).

## Design Notes

* **Zero forbidden constructs**: pure total Lean 4 only — every recursive function
  uses structural recursion (`termination_by structural`), with zero `sorry`,
  `admit`, `axiom`, `partial`, `unsafe`, `native_decide`, `bv_decide`,
  `@[extern]`, or `@[implemented_by]`.
* **Monomorphic recursive ADTs**: `IxCC.Fir.ShapeInfer` currently assigns one
  monovariant `DataDecl` per Lean inductive type (`Config.indOf`). Using
  domain-specific monomorphic lists (`BitList`, `HeightList`, `DigestList`,
  `FrontierList`, `Digest32List`, `FrontierList32`) mirrors Formal Aiur's
  monomorphized `Lists::List<T>` enums and keeps every struct and list node
  strictly unboxed (zero fallback to universal `Obj`).
* **Two `Nat`-argument benchmark entrypoints**:
  1. `MmcsPure.entryStructural (leaf0 sib0 sib1 idx : Nat) : Nat` — full batched
     MMCS verification (`frontierSplit`, `frontierMerge`, `frontierSort`,
     `frontierLevel`, `frontierFold`, `bitsToNum`, `hasHeight`, `injectMaybe`,
     `compressOrdered`, `digestEq`) with lightweight unboxed mixing compression
     (`TableTier.byte256`, 256-row byte check table) to measure the exact
     non-hash MMCS skeleton cost.
  2. `MmcsPure.entryBlake3 (leaf0 sib0 idx : Nat) : Nat` — full MMCS Merkle path
     verification with real 7-round pure-Lean keyed BLAKE3 compression
     (`blake3CompressInit` over flat `UInt32` state structs, matching
     `MultiStark.Source.starkHash`'s exact `v6_merkle_compress_cv` and
     `flags = 75`).
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace MmcsPure

/-! ## Shared Index-Bit and Matrix-Height Lists (`Pcs::bits_to_num`, `Pcs::has_height`) -/

/-- LSB-first query index bits, matching `Lists::List<Field>` in `Mmcs.lean`. -/
inductive BitList where
  | nil
  | cons (bit : Nat) (rest : BitList)
  deriving BEq, DecidableEq, Repr

/-- Matrix log-heights committed in an MMCS batch (`lhs : Lists::List<Field>`). -/
inductive HeightList where
  | nil
  | cons (height : Nat) (rest : HeightList)
  deriving BEq, DecidableEq, Repr

/-- Decode an LSB-first bit list to its natural index (`Pcs::bits_to_num`).
Uses `b + r + r` rather than `b + 2 * r` so widened loop bounds avoid `mul_56`. -/
def bitsToNum : BitList → Nat
  | .nil => 0
  | .cons b rest =>
    let r := bitsToNum rest
    b + r + r
termination_by structural bits => bits

/-- Return `1` iff `target` appears in `lhs`, else `0` (`Pcs::has_height`). -/
def hasHeight (lhs : HeightList) (target : Nat) : Nat :=
  match lhs with
  | .nil => 0
  | .cons h rest =>
    if h == target then 1 else hasHeight rest target
termination_by structural lhs

/-- Encode a 2-bit leaf index `idx ∈ {0, 1, 2, 3}` as LSB-first `BitList`. -/
@[circuit_inline]
def bitsOf2 (idx : Nat) : BitList :=
  match idx with
  | 0 => .cons 0 (.cons 0 .nil)
  | 1 => .cons 1 (.cons 0 .nil)
  | 2 => .cons 0 (.cons 1 .nil)
  | _ => .cons 1 (.cons 1 .nil)

/-! ## Part 1: Structural MMCS Skeleton (`entryStructural`)

Faithful port of `Mmcs.lean` using 4-limb unboxed digests (`Digest4`) and
lightweight order-sensitive mixing compression so `TableTier` stays at
`byte256` (256 fixed rows), isolating exact MMCS control-flow & ADT overhead. -/

/-- 4-limb unboxed digest mirroring MultiStark's `[UInt64; 4]` digest shape. -/
structure Digest4 where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  deriving BEq, DecidableEq, Repr

/-- Merkle proof sibling list (`Lists::List<ProofDeserialize::DigestP>`). -/
inductive DigestList where
  | nil
  | cons (head : Digest4) (tail : DigestList)
  deriving BEq, DecidableEq, Repr

/-- One active node in the batched MMCS frontier (`Pcs::FrontierNode::Mk`). -/
structure FrontierNode where
  idx : Nat
  bits : BitList
  rowTag : Nat
  digest : Digest4
  deriving BEq, DecidableEq, Repr

/-- Active MMCS frontier list (`Lists::List<Pcs::FrontierNode>`). -/
inductive FrontierList where
  | nil
  | cons (head : FrontierNode) (tail : FrontierList)
  deriving BEq, DecidableEq, Repr

/-- Result of `frontierSplit` (monomorphic pair to stay unboxed in `ShapeInfer`). -/
structure FrontierPair where
  left : FrontierList
  right : FrontierList
  deriving BEq, DecidableEq, Repr

/-- Result of `frontierLevel` / `frontierFold` (monomorphic pair). -/
structure LevelResult where
  nodes : FrontierList
  proof : DigestList
  deriving BEq, DecidableEq, Repr

@[circuit_inline]
def mkDigest4 (seed : Nat) : Digest4 :=
  { d0 := seed, d1 := seed + 1, d2 := seed + 2, d3 := seed + 3 }

/-- Digest equality returning `1` iff all 4 limbs match, else `0` (`StarkHash::digest_eq`). -/
@[circuit_inline]
def digestEq (a b : Digest4) : Nat :=
  if a.d0 == b.d0 then
    if a.d1 == b.d1 then
      if a.d2 == b.d2 then
        if a.d3 == b.d3 then 1 else 0
      else 0
    else 0
  else 0

/-- Order-sensitive unboxed 4-limb compression for measuring the MMCS skeleton
without hash-table noise (`mixCompress a b ≠ mixCompress b a`). -/
@[circuit_inline]
def mixCompress (a b : Digest4) : Digest4 :=
  { d0 := a.d0 + b.d0 + b.d1 + 1
    d1 := a.d1 + b.d1 + b.d2 + 3
    d2 := a.d2 + b.d2 + b.d3 + 5
    d3 := a.d3 + b.d3 + b.d0 + 7 }

/-- Child-order-aware 2-to-1 compression (`Pcs::compress_ordered`). -/
@[circuit_inline]
def compressOrdered (bit : Nat) (d s : Digest4) : Digest4 :=
  match bit with
  | 0 => mixCompress d s
  | _ => mixCompress s d

/-- Height-indexed row injection (`Pcs::inject_maybe`). -/
@[circuit_inline]
def injectMaybe (rowTag : Nat) (lhs : HeightList) (lh : Nat) (d : Digest4) : Digest4 :=
  match hasHeight lhs lh with
  | 0 => d
  | _ => mixCompress d (mkDigest4 (rowTag + lh + 100))

/-- Consistency check of opened claims at heights `≤ nextLh` (`Pcs::select_rows_le` +
`StarkVerifier::assert_same_claims`). -/
@[circuit_inline]
def sameClaimsLe (rowA rowB : Nat) (lhs : HeightList) (nextLh : Nat) : Bool :=
  match hasHeight lhs nextLh with
  | 0 => true
  | _ => rowA == rowB

/-- Length of a frontier list (`Lists::length`). -/
def frontierLength : FrontierList → Nat
  | .nil => 0
  | .cons _ rest => frontierLength rest + 1
termination_by structural xs => xs

/-- Alternating split for merge sort (`Mmcs::frontier_split`). -/
def frontierSplit : FrontierList → FrontierPair
  | .nil => { left := .nil, right := .nil }
  | .cons x .nil => { left := .cons x .nil, right := .nil }
  | .cons x (.cons y tail) =>
    let split := frontierSplit tail
    { left := .cons x split.left, right := .cons y split.right }
termination_by structural xs => xs

/-- Countdown-fuelled sorted deduplicating merge of two frontier lists (`Mmcs::frontier_merge`).
On equal indices, requires matching digests and row claims (rejecting mismatches
by collapsing the frontier so verification fails closed). -/
def frontierMergeFuel : Nat → FrontierList → FrontierList → FrontierList
  | 0, xs, _ => xs
  | _ + 1, .nil, ys => ys
  | _ + 1, xs, .nil => xs
  | fuel + 1, .cons x xrest, .cons y yrest =>
    if x.idx < y.idx then
      .cons x (frontierMergeFuel fuel xrest (.cons y yrest))
    else if x.idx == y.idx then
      if digestEq x.digest y.digest == 1 then
        if x.rowTag == y.rowTag then
          .cons x (frontierMergeFuel fuel xrest yrest)
        else .nil
      else .nil
    else
      .cons y (frontierMergeFuel fuel (.cons x xrest) yrest)
termination_by structural fuel => fuel

@[circuit_inline]
def frontierMerge (xs ys : FrontierList) : FrontierList :=
  frontierMergeFuel (frontierLength xs + frontierLength ys) xs ys

/-- Countdown-fuelled merge sort over the active frontier (`Mmcs::frontier_sort`). -/
def frontierSortFuel : Nat → FrontierList → FrontierList
  | 0, xs => xs
  | fuel + 1, xs =>
    match xs with
    | .nil => .nil
    | .cons _ .nil => xs
    | .cons _ (.cons _ _) =>
      let sp := frontierSplit xs
      frontierMerge (frontierSortFuel fuel sp.left) (frontierSortFuel fuel sp.right)
termination_by structural fuel => fuel

/-- Structural worker for `frontierLevel` (`Mmcs::frontier_level`), processing a
non-empty frontier `a :: rest` by pairing adjacent siblings that share a parent
index or consuming a proof sibling via `compressOrdered`, followed by `injectMaybe`. -/
@[circuit_noinline]
def frontierLevelCons (a : FrontierNode) (rest : FrontierList) (proof : DigestList)
    (lhs : HeightList) (nextLh : Nat) : LevelResult :=
  match a.bits with
  | .nil => { nodes := .nil, proof := proof }
  | .cons abit aparentBits =>
    let aparent := bitsToNum aparentBits
    match rest with
    | .nil =>
      match proof with
      | .nil => { nodes := .nil, proof := .nil }
      | .cons sib prest =>
        let parent := injectMaybe a.rowTag lhs nextLh (compressOrdered abit a.digest sib)
        { nodes := .cons { idx := aparent, bits := aparentBits, rowTag := a.rowTag, digest := parent } .nil
          proof := prest }
    | .cons b brest =>
      match b.bits with
      | .nil => { nodes := .nil, proof := proof }
      | .cons _bbit bparentBits =>
        if aparent == bitsToNum bparentBits then
          if sameClaimsLe a.rowTag b.rowTag lhs nextLh then
            let parent := injectMaybe a.rowTag lhs nextLh (mixCompress a.digest b.digest)
            let r : LevelResult := match brest with
              | .nil => { nodes := .nil, proof := proof }
              | .cons c crest => frontierLevelCons c crest proof lhs nextLh
            { nodes := .cons { idx := aparent, bits := aparentBits, rowTag := a.rowTag, digest := parent } r.nodes
              proof := r.proof }
          else
            { nodes := .nil, proof := proof }
        else
          match proof with
          | .nil => { nodes := .nil, proof := .nil }
          | .cons sib prest =>
            let parent := injectMaybe a.rowTag lhs nextLh (compressOrdered abit a.digest sib)
            let r := frontierLevelCons b brest prest lhs nextLh
            { nodes := .cons { idx := aparent, bits := aparentBits, rowTag := a.rowTag, digest := parent } r.nodes
              proof := r.proof }
termination_by structural rest

/-- Advance the sorted MMCS frontier by one Merkle level (`Mmcs::frontier_level`). -/
@[circuit_inline]
def frontierLevel (nodes : FrontierList) (proof : DigestList)
    (lhs : HeightList) (nextLh : Nat) : LevelResult :=
  match nodes with
  | .nil => { nodes := .nil, proof := proof }
  | .cons a rest => frontierLevelCons a rest proof lhs nextLh

/-- Countdown structural fold across all `levels` of the Merkle tree (`Mmcs::frontier_fold`). -/
@[circuit_noinline]
def frontierFold (nodes : FrontierList) (proof : DigestList)
    (lhs : HeightList) : Nat → LevelResult
  | 0 => { nodes := nodes, proof := proof }
  | levels + 1 =>
    let step := frontierLevel nodes proof lhs levels
    frontierFold step.nodes step.proof lhs levels
termination_by structural levels => levels

/-- Batched MMCS verifier (`Mmcs::mmcs_verify_multi`): sorts the query frontier,
folds `logMax` levels, checks that the proof is fully consumed and collapses to a
single cap root at index `0`, and returns `digestEq expected root.digest`. -/
@[circuit_noinline]
def verifyMulti (expected : Digest4) (leaves : FrontierList)
    (lhs : HeightList) (proof : DigestList) (logMax : Nat) : Nat :=
  let sorted := frontierSortFuel (frontierLength leaves) leaves
  let res := frontierFold sorted proof lhs logMax
  match res.proof with
  | .cons _ _ => 0
  | .nil =>
    match res.nodes with
    | .cons root .nil =>
      if root.idx == 0 then digestEq expected root.digest else 0
    | _ => 0

/-- Committed Merkle cap for the canonical 3-query, 2-height structural batch
(`leaf0 = 20, sib0 = 30, sib1 = 40, idx = 2`, `lhs = [2, 1]`). -/
@[circuit_inline]
def expectedStructuralRoot : Digest4 :=
  { d0 := 908, d1 := 937, d2 := 958, d3 := 943 }

/-- **Entrypoint 1 (`entryStructural`)**: exercises the full batched `Mmcs`
skeleton (unsorted 3-node frontier → `frontierSort` → `frontierFold` across 2
levels with both sibling-merge and proof-consume branches, plus height-1
`injectMaybe` and `digestEq`). Returns `1` on valid opening `(20, 30, 40, 2)`
and `0` on any tampered leaf, sibling, or index. -/
@[circuit_budget 20 160 96 24 800]
def entryStructural (leaf0 sib0 sib1 idx : Nat) : Nat :=
  let bitsQ := bitsOf2 idx
  let bits1 := bitsOf2 1
  let bits0 := bitsOf2 0
  let nQ : FrontierNode :=
    { idx := bitsToNum bitsQ, bits := bitsQ, rowTag := 2, digest := mkDigest4 sib0 }
  let n1 : FrontierNode :=
    { idx := bitsToNum bits1, bits := bits1, rowTag := 1, digest := mkDigest4 leaf0 }
  let n0 : FrontierNode :=
    { idx := bitsToNum bits0, bits := bits0, rowTag := 1, digest := mkDigest4 10 }
  -- Deliberately unsorted frontier `[nQ, n1, n0]` to exercise `frontierSort`.
  let leaves : FrontierList := .cons nQ (.cons n1 (.cons n0 .nil))
  let lhs : HeightList := .cons 2 (.cons 1 .nil)
  let proof : DigestList := .cons (mkDigest4 sib1) .nil
  verifyMulti expectedStructuralRoot leaves lhs proof 2

/-! ## Part 2: Real 7-Round Keyed BLAKE3 MMCS Verification (`entryBlake3`)

Matches `MultiStark/MultiStark/Modules/StarkHash.lean` (`v6_merkle_compress_cv`,
`flags = 75`, `block_len = 64`, `counter = 0`) and `Aiur/Aiur/Library/Blake3.lean`
using strictly flat `UInt32` structs so `TypedLower` keeps every word unboxed as
`UInt32::U32` (`TableTier.u32`) and `Peephole` fuses `add3`, `rotr16`, `rotr8`,
`xor_rotr12`, and `xor_rotr7`. -/

/-- 8-word (32-byte) unboxed `UInt32` BLAKE3 digest / chaining value. -/
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

/-- Output of one BLAKE3 quarter-round `G` call. -/
structure QuarterOut where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving BEq, DecidableEq, Repr

/-- 16-word BLAKE3 internal compression state. -/
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

/-- Standard BLAKE3 IV (`Aiur.Library.Blake3.iv`). -/
@[circuit_inline]
def blake3IV : Digest32 :=
  { w0 := 0x6A09E667, w1 := 0xBB67AE85, w2 := 0x3C6EF372, w3 := 0xA54FF53A
    w4 := 0x510E527F, w5 := 0x9B05688C, w6 := 0x1F83D9AB, w7 := 0x5BE0CD19 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key` context CV for
`"multi-stark/v6/merkle/compress"` (`StarkHash::v6_merkle_compress_cv`). -/
@[circuit_inline]
def v6MerkleCompressCv : Digest32 :=
  { w0 := 0xCC4D7633, w1 := 0xF8492FEC, w2 := 0x5704B1FD, w3 := 0x2D69A6B5
    w4 := 0xA871EBB5, w5 := 0x6439610D, w6 := 0x89E86BE6, w7 := 0x02E22A34 }

/-- BLAKE3 quarter-round `G` written directly in Peephole-fusible form
(`add3`, `rotr16`, `xor_rotr12`, `rotr8`, `xor_rotr7`). Uses direct `UInt32.*`
operations so `IxCC`'s inliner does not residualize 2-level `HAdd`/`HXor`/
`HOr`/`HShiftRight`/`HShiftLeft` typeclass dictionaries into closures. -/
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

/-- One full BLAKE3 round (4 column quarter-rounds + 4 diagonal quarter-rounds),
matching `Blake3::compress_inner_j`. -/
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

/-- Countdown-recursive 7-round BLAKE3 loop (`rem = 6` executes rounds `0..6`
and XORs the two halves of the final state to produce the 8-word chaining value). -/
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

/-- Pure-Lean `Blake3::compress_init` (with `counter = 0`) over flat `UInt32` structs. -/
@[circuit_noinline]
def blake3CompressInit (cv : Digest32) (m : Block16)
    (blockLen flags : UInt32) : Digest32 :=
  let iv := blake3IV
  let st : State16 :=
    { v0 := cv.w0, v1 := cv.w1, v2 := cv.w2, v3 := cv.w3
      v4 := cv.w4, v5 := cv.w5, v6 := cv.w6, v7 := cv.w7
      v8 := iv.w0, v9 := iv.w1, v10 := iv.w2, v11 := iv.w3
      v12 := 0, v13 := 0, v14 := blockLen, v15 := flags }
  blake3CompressLoop 6 st m

/-- Protocol `v6` MMCS 2-to-1 Merkle compression (`Mmcs::mmcs_compress`):
`Blake3::compress_init(StarkHash::v6_merkle_compress_cv(), [a || b], 0, 64, 75)`. -/
@[circuit_noinline]
def mmcsCompress32 (a b : Digest32) : Digest32 :=
  let block : Block16 :=
    { m0 := a.w0, m1 := a.w1, m2 := a.w2, m3 := a.w3
      m4 := a.w4, m5 := a.w5, m6 := a.w6, m7 := a.w7
      m8 := b.w0, m9 := b.w1, m10 := b.w2, m11 := b.w3
      m12 := b.w4, m13 := b.w5, m14 := b.w6, m15 := b.w7 }
  blake3CompressInit v6MerkleCompressCv block 64 75

/-- Child-order-aware BLAKE3 compression (`Pcs::compress_ordered`). -/
@[circuit_inline]
def compressOrdered32 (bit : Nat) (d s : Digest32) : Digest32 :=
  match bit with
  | 0 => mmcsCompress32 d s
  | _ => mmcsCompress32 s d

/-- Word equality via `UInt32.toNat` (lowers directly to linear byte recomposition
plus single-column field equality in `TypedLower`). -/
@[circuit_inline]
def u32Eq (a b : UInt32) : Bool :=
  a.toNat == b.toNat

/-- 32-byte digest equality returning `1` iff all 8 `UInt32` words match (`StarkHash::digest_eq`). -/
@[circuit_inline]
def digest32Eq (a b : Digest32) : Nat :=
  if u32Eq a.w0 b.w0 then
    if u32Eq a.w1 b.w1 then
      if u32Eq a.w2 b.w2 then
        if u32Eq a.w3 b.w3 then
          if u32Eq a.w4 b.w4 then
            if u32Eq a.w5 b.w5 then
              if u32Eq a.w6 b.w6 then
                if u32Eq a.w7 b.w7 then 1 else 0
              else 0
            else 0
          else 0
        else 0
      else 0
    else 0
  else 0

/-- Construct a deterministic 32-byte digest from a `Nat` seed. -/
@[circuit_inline]
def mkDigest32 (seed : Nat) : Digest32 :=
  let w := seed.toUInt32
  { w0 := w, w1 := w + 1, w2 := w + 2, w3 := w + 3
    w4 := w + 4, w5 := w + 5, w6 := w + 6, w7 := w + 7 }

/-- Proof sibling list of 32-byte BLAKE3 digests (`Lists::List<DigestP>`). -/
inductive Digest32List where
  | nil
  | cons (head : Digest32) (tail : Digest32List)
  deriving BEq, DecidableEq, Repr

/-- Frontier node carrying a 32-byte BLAKE3 digest (`Pcs::FrontierNode`). -/
structure FrontierNode32 where
  idx : Nat
  bits : BitList
  digest : Digest32
  deriving BEq, DecidableEq, Repr

/-- Active frontier list for BLAKE3 MMCS (`Lists::List<Pcs::FrontierNode>`). -/
inductive FrontierList32 where
  | nil
  | cons (head : FrontierNode32) (tail : FrontierList32)
  deriving BEq, DecidableEq, Repr

/-- Output of `frontierLevel32` / `frontierFold32`. -/
structure LevelResult32 where
  nodes : FrontierList32
  proof : Digest32List
  deriving BEq, DecidableEq, Repr

/-- Height-aware injection hook (`Pcs::inject_maybe` for `Digest32`). -/
@[circuit_inline]
def injectMaybe32 (lhs : HeightList) (lh : Nat) (d : Digest32) : Digest32 :=
  match hasHeight lhs lh with
  | 0 => d
  | _ => mmcsCompress32 d (mkDigest32 (lh + 100))

/-- Structural worker for `frontierLevel32` (`Mmcs::frontier_level` over BLAKE3 digests). -/
@[circuit_noinline]
def frontierLevelCons32 (a : FrontierNode32) (rest : FrontierList32) (proof : Digest32List)
    (lhs : HeightList) (nextLh : Nat) : LevelResult32 :=
  match a.bits with
  | .nil => { nodes := .nil, proof := proof }
  | .cons abit aparentBits =>
    let aparent := bitsToNum aparentBits
    match rest with
    | .nil =>
      match proof with
      | .nil => { nodes := .nil, proof := .nil }
      | .cons sib prest =>
        let parent := injectMaybe32 lhs nextLh (compressOrdered32 abit a.digest sib)
        { nodes := .cons { idx := aparent, bits := aparentBits, digest := parent } .nil
          proof := prest }
    | .cons b brest =>
      match b.bits with
      | .nil => { nodes := .nil, proof := proof }
      | .cons _bbit bparentBits =>
        if aparent == bitsToNum bparentBits then
          let parent := injectMaybe32 lhs nextLh (mmcsCompress32 a.digest b.digest)
          let r : LevelResult32 := match brest with
            | .nil => { nodes := .nil, proof := proof }
            | .cons c crest => frontierLevelCons32 c crest proof lhs nextLh
          { nodes := .cons { idx := aparent, bits := aparentBits, digest := parent } r.nodes
            proof := r.proof }
        else
          match proof with
          | .nil => { nodes := .nil, proof := .nil }
          | .cons sib prest =>
            let parent := injectMaybe32 lhs nextLh (compressOrdered32 abit a.digest sib)
            let r := frontierLevelCons32 b brest prest lhs nextLh
            { nodes := .cons { idx := aparent, bits := aparentBits, digest := parent } r.nodes
              proof := r.proof }
termination_by structural rest

/-- Single-level BLAKE3 MMCS frontier transition (`Mmcs::frontier_level`). -/
@[circuit_inline]
def frontierLevel32 (nodes : FrontierList32) (proof : Digest32List)
    (lhs : HeightList) (nextLh : Nat) : LevelResult32 :=
  match nodes with
  | .nil => { nodes := .nil, proof := proof }
  | .cons a rest => frontierLevelCons32 a rest proof lhs nextLh

/-- Countdown structural fold across `levels` of a BLAKE3 MMCS tree (`Mmcs::frontier_fold`). -/
@[circuit_noinline]
def frontierFold32 (nodes : FrontierList32) (proof : Digest32List)
    (lhs : HeightList) : Nat → LevelResult32
  | 0 => { nodes := nodes, proof := proof }
  | levels + 1 =>
    let step := frontierLevel32 nodes proof lhs levels
    frontierFold32 step.nodes step.proof lhs levels
termination_by structural levels => levels

/-- Full BLAKE3 MMCS Merkle path verifier (`Mmcs::mmcs_verify_multi`). -/
@[circuit_noinline]
def verifyPath32 (expected : Digest32) (leaf : Digest32)
    (bits : BitList) (lhs : HeightList) (proof : Digest32List) (logMax : Nat) : Nat :=
  let start : FrontierList32 :=
    .cons { idx := bitsToNum bits, bits := bits, digest := leaf } .nil
  let res := frontierFold32 start proof lhs logMax
  match res.proof with
  | .cons _ _ => 0
  | .nil =>
    match res.nodes with
    | .cons root .nil =>
      if root.idx == 0 then digest32Eq expected root.digest else 0
    | _ => 0

/-- Committed BLAKE3 root for canonical depth-2 opening `(leaf0 = 7, sib0 = 13, idx = 1)`
with `proof = [mkDigest32 13, mkDigest32 113]` and `lhs = [2]`.
Stored as literal constants so the verifier circuit does not recompute the cap. -/
@[circuit_inline]
def expectedBlake3Root : Digest32 :=
  { w0 := 0x1F193719, w1 := 0xC0669864, w2 := 0xDDD78849, w3 := 0xF6F627F1
    w4 := 0x3973ABED, w5 := 0x0A06B22F, w6 := 0xBDFFD745, w7 := 0x6EC3DD3D }

/-- **Entrypoint 2 (`entryBlake3`)**: exercises full `Mmcs` Merkle path
verification (depth 2, `frontierFold32` countdown recursion, `bitsToNum`,
`hasHeight`, `compressOrdered32`, `digest32Eq`) with real 7-round keyed
Protocol-`v6` BLAKE3 compression (`v6MerkleCompressCv`, `blockLen = 64`,
`flags = 75`). Returns `1` on valid witness `(7, 13, 1)` and `0` on any
tampered leaf, sibling, or index. -/
@[circuit_budget 16 640 384 24 3000]
def entryBlake3 (leaf0 sib0 idx : Nat) : Nat :=
  let bits := bitsOf2 idx
  let lhs : HeightList := .cons 2 .nil
  let proof : Digest32List := .cons (mkDigest32 sib0) (.cons (mkDigest32 (sib0 + 100)) .nil)
  verifyPath32 expectedBlake3Root (mkDigest32 leaf0) bits lhs proof 2

/-! ## Pure Lean Self-Checks (`#guard`) -/

-- 1. Official BLAKE3("") test vector:
--    af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
private def zeroBlock16 : Block16 :=
  { m0 := 0, m1 := 0, m2 := 0, m3 := 0, m4 := 0, m5 := 0, m6 := 0, m7 := 0
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def officialEmptyBlake3 : Digest32 :=
  { w0 := 0xb94913af, w1 := 0xa6a1f9f5, w2 := 0xea4d40a0, w3 := 0x49c9dc36
    w4 := 0xc925cb9b, w5 := 0xb712c1ad, w6 := 0xca939acc, w7 := 0x62321fe4 }

#guard blake3CompressInit blake3IV zeroBlock16 0 11 == officialEmptyBlake3

-- 2. Verify `v6MerkleCompressCv` matches `BLAKE3 derive_key_context("multi-stark/v6/merkle/compress")`:
--    30 bytes, flags = CHUNK_START | CHUNK_END | ROOT | DERIVE_KEY_CONTEXT = 1 + 2 + 8 + 32 = 43.
private def v6ContextBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x6d2f3676
    m4 := 0x6c6b7265, m5 := 0x6f632f65, m6 := 0x6572706d, m7 := 0x00007373
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

#guard blake3CompressInit blake3IV v6ContextBlock 30 43 == v6MerkleCompressCv

-- 3. `entryStructural`: valid opening returns 1; any tampering returns 0.
#guard entryStructural 20 30 40 2 == 1
#guard entryStructural 21 30 40 2 == 0
#guard entryStructural 20 31 40 2 == 0
#guard entryStructural 20 30 41 2 == 0
#guard entryStructural 20 30 40 3 == 0
#guard entryStructural 20 30 40 1 == 0

-- 4. `entryBlake3`: committed root matches direct compression, valid opening returns 1,
--    and any tampering returns 0.
#guard expectedBlake3Root ==
  mmcsCompress32 (mmcsCompress32 (mkDigest32 13) (mkDigest32 7)) (mkDigest32 113)
#guard entryBlake3 7 13 1 == 1
#guard entryBlake3 8 13 1 == 0
#guard entryBlake3 7 14 1 == 0
#guard entryBlake3 7 13 0 == 0
#guard entryBlake3 7 13 2 == 0
#guard entryBlake3 7 13 3 == 0

end MmcsPure
