import Ix.Compile.CircuitContract
import IxCCAiur.Compression.StarkWire
import IxCCAiur.Compression.CompressWrapPure

/-! # Production Pure Annotated Lean 4 Aggregation Verifier (`AggregatePure`)

Complete, single-source pure total Lean 4 port of the 19-shape Multi-STARK
aggregation verifier (`MultiStark/MultiStark/Modules/{Aggregate,Aggregation}.lean`)
over full Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$ and cubic extension
$\mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$, composing directly with
`StarkWire` and `CompressWrapPure`:

1. **Allowed-Blob Identity Pin (`parseAllowedBlob`):**
   Verifies the exact 80-byte identity blob
   `ixvm_vk_digest (32 B) ‖ verify_idx (8 B LE) ‖ self_vk_digest (32 B) ‖ aggr_idx (8 B LE)`
   against the public `allowedDigest` (`packDigest (blake3HashBytes allowedBytes)`),
   rejecting wrong length, non-canonical indices `≥ p_GL`, or digest mismatch.
2. **Inner Multi-STARK Batch Verification (`verifyChildProof`, `verifyChildDigest`):**
   Delegates child proof verification directly to `CompressWrapPure.verifyRootBytesWithFloor`
   (enforcing `verifyBatch` with production security floor, canonical wire decoding,
   zero-PoW canonicalization, MMCS, multi-arity FRI, AIR, LogUp, and MEMSEG checks),
   pins the child verifying key digest to `ixvmVkDigest` (`kind = 0`) or `selfVkDigest`
   (`kind = 1`), and enforces exact claim channel (`1`), entrypoint (`verifyIdx` / `aggrIdx`),
   length (`10` / `18` words), and recursive `allowedDigest` propagation.
3. **Canonical Merkle Assumption Trees & Set Operations:**
   Exact big-endian 32-byte address ordering (`aggrAddressOrder`), Ixon `0xE2` tree body
   parsing, strict-sortedness enforcement, canonical Merkle root reconstruction
   (`aggrLeafHash` with prefix `0x00`, `aggrNodeHash` with prefix `0x01`, odd-node zero
   padding), set union (`aggrAssertUnion`), disjoint union (`aggrAssertDisjointUnion`),
   disjointness (`aggrAssertDisjoint`), flat assumption difference (`aggrAssertDifference`),
   and structural Merkle-path discharge (`aggrAssertStructuralDifference`).
4. **All 19 Aggregation Shapes (`0..18`):**
   - Shapes `0–1`: `aggrWrap` (IxVM leaf `Check`/`CheckEnv`/`Binding`/`Eval`/`Reveal`/`Contains`/`Catalog` or recursive `ix_aggr` wrap),
   - Shapes `2–5`: `aggrPair` (flat canonical pair fold with cross-discharge and user-axiom union),
   - Shapes `6–9`: `aggrPairStructural` (structural `nodeHash(left, right)` Merkle pair fold),
   - Shape `10`: `aggrRangeLeaf` (direct verification of shards `[lo, hi)` via `CompressWrapPure.verifyShardWithFloor` with `ExtGl` residual summation),
   - Shape `11`: `aggrRangeJoin` (adjacent range residual addition in `ExtGl`),
   - Shape `12`: `aggrRangeRoot` (full `[0, k)` closure with batch row bounds, MEMSEG closure pairs & widths, global LogUp balance vanishing, and 10-word `verify_claim` extraction),
   - Shapes `13–14`: `aggrDischargeBinding` (role-binding discharge `validator 4 → 3`),
   - Shape `15`: `aggrCrossBinding` (108-role binding walk extracting the exact 13 class roles into validator `5`),
   - Shape `16`: `aggrCatalogJoin` (sorted union of unconditional binding-discharged `CheckEnv` / `Catalog` children),
   - Shape `17`: `aggrDynamicLink` (`0xE8 0x0D`, uniform security envelope, external batch proof verification, codec arity enforcement, and optional unconditional validator-`3` bridge certificate verification),
   - Shape `18`: `aggrDischargeEval` (`0xE8 0x0E`, strictly disabling Mode 1 `tag = 227`; Mode 2 `@Eq` `Claim.check` transitions `10 → 14` / `11 → 15` ONLY when `evalAssumptions` becomes empty and `linkedCircuits = none`, NEVER producing standard validators `3`/`4`/`5`; Mode 3a `DynamicLinkStatement` ALWAYS commits a canonical `LinkedCircuitEntry` `0xE8 0x0F` under linked validators `12`/`13`, NEVER producing `3`/`4`/`5`/`14`/`15`).
5. **Step & Recursive Tree Verification (`verifyAggregateStep`, `verifyAggregateRoot`):**
   Total, strictly structural pure verification of both individual aggregation steps
   and full recursive aggregation proof trees.

## Proof & Compilation Hygiene
* ONLY `import Ix.Compile.CircuitContract`, `import IxCCAiur.Compression.StarkWire`,
  and `import IxCCAiur.Compression.CompressWrapPure`.
* Zero `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `partial`, `unsafe`,
  `@[extern]`, or `@[implemented_by]`; strictly structural recursion throughout.
* 100% Ixon content-address invariant under `open scoped Ix.Circuit`.
-/

set_option autoImplicit false

open scoped Ix.Circuit
open StarkWire CompressWrapPure

namespace AggregatePure

/-! ## Section 1: Monomorphic Unboxed Aggregation ADTs & 32-Byte Address Utilities -/

/-- Optional 32-byte Ixon content address (`Options::Option<Bytes::AddressRef>`). -/
inductive OptAddr where
  | none
  | some (addr : DigestBytes)
  deriving BEq, DecidableEq, Repr

/-- Merge-cursor step for two sorted assumption lists (`Aggregation::AggrNextAssumption`). -/
inductive NextAssumption where
  | done
  | more (candidate : DigestBytes) (source : Nat) (leftRest rightRest : DigestBytesList)
  deriving BEq, DecidableEq, Repr

/-- Optional bridge binding inside a Shape 17 `DynamicLinkStatement` (`Aggregation::AggrOptBridge`). -/
inductive OptBridge where
  | noBridge
  | someBridge (spec binding targetConst : DigestBytes) (codec : U64Bytes) (certConst : DigestBytes)
  deriving BEq, DecidableEq, Repr

/-- Optional external circuit reference inside a Shape 18 `EvalAssumption` (`Aggregation::AggrOptCircuitRef`). -/
inductive OptCircuitRef where
  | noCircuitRef
  | someCircuitRef (vk : DigestBytes) (entryIdx : U64Bytes)
  deriving BEq, DecidableEq, Repr

/-- Context tuple `(spec, binding, axioms, validator)` of a `Check` / `CheckEnv` claim. -/
structure CheckEnvCtx where
  spec : DigestBytes
  binding : DigestBytes
  axioms : OptAddr
  validator : Nat
  deriving BEq, DecidableEq, Repr

/-- Decoded 80-byte allowed-identity parameters `(ixvmVkDigest, verifyIdx, selfVkDigest, aggrIdx)`. -/
structure AllowedParams where
  ixvmVkDigest : Digest32Words
  verifyIdx : Nat
  selfVkDigest : Digest32Words
  aggrIdx : Nat
  deriving BEq, DecidableEq, Repr

/-- Lookup table entry mapping a candidate assumption address to its structural discharge choice bytes. -/
structure PathEntry where
  candidate : DigestBytes
  bytes : ByteList
  deriving BEq, DecidableEq, Repr

/-- Monomorphic association list for structural Merkle-path discharge choices (IO channel 6). -/
inductive PathTable where
  | nil
  | cons (head : PathEntry) (tail : PathTable)
  deriving BEq, DecidableEq, Repr

/-- Explicit pure witness for one child Multi-STARK batch proof (`vkBytes`, `claimsBytes`, `proofBytes`). -/
structure ChildProofWitness where
  vkBytes : ByteList
  claimsBytes : ByteList
  proofBytes : ByteList
  deriving BEq, DecidableEq, Repr

/-- Dummy `Digest32Words` (all zeros) for fail-closed error paths. -/
@[circuit_inline]
def zeroDigest32Words : Digest32Words :=
  { w0 := 0, w1 := 0, w2 := 0, w3 := 0, w4 := 0, w5 := 0, w6 := 0, w7 := 0 }

/-- Dummy `CheckEnvCtx` for fail-closed error paths. -/
@[circuit_inline]
def dummyCheckEnvCtx : CheckEnvCtx :=
  { spec := dummyDigestBytes, binding := dummyDigestBytes, axioms := .none, validator := 0 }

/-- Dummy `AllowedParams` for fail-closed error paths. -/
@[circuit_inline]
def dummyAllowedParams : AllowedParams :=
  { ixvmVkDigest := zeroDigest32Words, verifyIdx := 0
    selfVkDigest := zeroDigest32Words, aggrIdx := 0 }

/-- Dummy `ChildProofWitness` for unused slots. -/
@[circuit_inline]
def emptyChildProofWitness : ChildProofWitness :=
  { vkBytes := .nil, claimsBytes := .nil, proofBytes := .nil }

/-! ### Monomorphic Parse-Result Structs -/

structure ParseOptAddr where
  ok : Nat
  val : OptAddr
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure ParseAllowedOut where
  ok : Nat
  val : AllowedParams
  deriving BEq, DecidableEq, Repr

structure ParseCheckEnvOut where
  ok : Nat
  ctx : CheckEnvCtx
  root : DigestBytes
  assumptions : OptAddr
  deriving BEq, DecidableEq, Repr

structure ParseBindingOut where
  ok : Nat
  spec : DigestBytes
  binding : DigestBytes
  deriving BEq, DecidableEq, Repr

structure ParseCatalogOut where
  ok : Nat
  members : DigestBytes
  deriving BEq, DecidableEq, Repr

structure ParseEvalOut where
  ok : Nat
  ctx : CheckEnvCtx
  lhs : DigestBytes
  rhs : DigestBytes
  typ : DigestBytes
  deriving BEq, DecidableEq, Repr

structure ParseRangeOut where
  ok : Nat
  batchDigest : DigestBytes
  lo : U64Bytes
  hi : U64Bytes
  residual : ExtGl
  deriving BEq, DecidableEq, Repr

structure ParseDynamicLinkOut where
  ok : Nat
  vkDigest : DigestBytes
  entryIdx : U64Bytes
  pubInputs : U64List
  pubOutputs : U64List
  bridge : OptBridge
  deriving BEq, DecidableEq, Repr

structure ParseEvalAssumptionOut where
  ok : Nat
  lhs : DigestBytes
  rhs : DigestBytes
  typ : DigestBytes
  circuit : OptCircuitRef
  deriving BEq, DecidableEq, Repr

structure ParseEvalAssumedOut where
  ok : Nat
  tag : Nat
  ctx : CheckEnvCtx
  target : DigestBytes
  assumptions : OptAddr
  evalRoot : DigestBytes
  linked : OptAddr
  deriving BEq, DecidableEq, Repr

structure ParseEvalDischargeOut where
  ok : Nat
  ctx : CheckEnvCtx
  target : DigestBytes
  assumptions : OptAddr
  evalOpt : OptAddr
  linkedOpt : OptAddr
  deriving BEq, DecidableEq, Repr

structure ParsePreambleOut where
  ok : Nat
  headers : ShardHeaderList
  messages : BatchMessageList
  deriving BEq, DecidableEq, Repr

structure VerifyRangeOut where
  ok : Nat
  residual : ExtGl
  deriving BEq, DecidableEq, Repr

structure ExtractRemovedOut where
  ok : Nat
  removed : DigestBytes
  deriving BEq, DecidableEq, Repr

structure VerifyChildDigestOut where
  ok : Nat
  digest : Digest32Words
  deriving BEq, DecidableEq, Repr

structure ParseOnlyClaimOut where
  ok : Nat
  claim : U64List
  deriving BEq, DecidableEq, Repr

structure ParseTagN4Out where
  ok : Nat
  flag : Nat
  val : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure SkipExprOut where
  ok : Nat
  rest : ByteList
  deriving BEq, DecidableEq, Repr

structure BindingClassOut where
  ok : Nat
  cls : DigestBytes
  deriving BEq, DecidableEq, Repr

structure SeekSubjectOut where
  found : Nat
  rest : DigestBytesList
  deriving BEq, DecidableEq, Repr

/-! ### Core 32-Byte Address & Digest Helpers -/

/-- Exact equality on packed 8-word digests (`Aggregation::aggr_assert_digest`). -/
@[circuit_inline]
def digest32WordsEq (a b : Digest32Words) : Nat :=
  if a.w0 == b.w0 && a.w1 == b.w1 && a.w2 == b.w2 && a.w3 == b.w3 &&
     a.w4 == b.w4 && a.w5 == b.w5 && a.w6 == b.w6 && a.w7 == b.w7 then 1 else 0

/-- Pack 4 LE bytes into a `< 2^32` natural number. -/
@[circuit_inline]
def packLe4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3

/-- Pack a 32-byte address (`DigestBytes`) into 8 LE `u32` words (`Aggregation::aggr_pack_address`). -/
@[circuit_inline]
def packAddress (a : DigestBytes) : Digest32Words :=
  { w0 := packLe4 a.d0.b0 a.d0.b1 a.d0.b2 a.d0.b3
    w1 := packLe4 a.d0.b4 a.d0.b5 a.d0.b6 a.d0.b7
    w2 := packLe4 a.d1.b0 a.d1.b1 a.d1.b2 a.d1.b3
    w3 := packLe4 a.d1.b4 a.d1.b5 a.d1.b6 a.d1.b7
    w4 := packLe4 a.d2.b0 a.d2.b1 a.d2.b2 a.d2.b3
    w5 := packLe4 a.d2.b4 a.d2.b5 a.d2.b6 a.d2.b7
    w6 := packLe4 a.d3.b0 a.d3.b1 a.d3.b2 a.d3.b3
    w7 := packLe4 a.d3.b4 a.d3.b5 a.d3.b6 a.d3.b7 }

/-- Standard BLAKE3 content address of a byte stream (`Blake3::bytes_to_addr`). -/
@[circuit_inline]
def bytesToAddr (bs : ByteList) : DigestBytes :=
  digest32ToDigestBytes (blake3HashBytes bs)

/-- Canonical Ixon Merkle node hash `BLAKE3(0x01 ‖ left ‖ right)` (`Aggregation::aggr_node_hash`). -/
@[circuit_noinline]
def aggrNodeHash (left right : DigestBytes) : DigestBytes :=
  bytesToAddr (.cons 1 (digestBytesOnto left (digestBytesOnto right .nil)))

/-- Canonical Ixon Merkle leaf hash `BLAKE3(0x00 ‖ addr)` (`Aggregation::aggr_leaf_hash`). -/
@[circuit_noinline]
def aggrLeafHash (addr : DigestBytes) : DigestBytes :=
  bytesToAddr (.cons 0 (digestBytesOnto addr .nil))

/-- Pack 4 big-endian bytes into a `< 2^32` natural number (`Aggregation::aggr_pack_be4`). -/
@[circuit_inline]
def packBe4 (a b c d : Nat) : Nat :=
  ((a * 256 + b) * 256 + c) * 256 + d

/-- Compare two 32-bit big-endian chunks: returns `0` (`<`), `1` (`=`), or `2` (`>`). -/
@[circuit_inline]
def cmpU32 (a b : Nat) : Nat :=
  if a == b then 1 else if a < b then 0 else 2

/-- Lexicographic big-endian ordering on 32-byte addresses (`Aggregation::aggr_address_order`):
returns `0` if `a < b`, `1` if `a == b`, `2` if `a > b`. -/
@[circuit_noinline]
def aggrAddressOrder (a b : DigestBytes) : Nat :=
  let c0 := cmpU32 (packBe4 a.d0.b0 a.d0.b1 a.d0.b2 a.d0.b3) (packBe4 b.d0.b0 b.d0.b1 b.d0.b2 b.d0.b3)
  if c0 != 1 then c0 else
  let c1 := cmpU32 (packBe4 a.d0.b4 a.d0.b5 a.d0.b6 a.d0.b7) (packBe4 b.d0.b4 b.d0.b5 b.d0.b6 b.d0.b7)
  if c1 != 1 then c1 else
  let c2 := cmpU32 (packBe4 a.d1.b0 a.d1.b1 a.d1.b2 a.d1.b3) (packBe4 b.d1.b0 b.d1.b1 b.d1.b2 b.d1.b3)
  if c2 != 1 then c2 else
  let c3 := cmpU32 (packBe4 a.d1.b4 a.d1.b5 a.d1.b6 a.d1.b7) (packBe4 b.d1.b4 b.d1.b5 b.d1.b6 b.d1.b7)
  if c3 != 1 then c3 else
  let c4 := cmpU32 (packBe4 a.d2.b0 a.d2.b1 a.d2.b2 a.d2.b3) (packBe4 b.d2.b0 b.d2.b1 b.d2.b2 b.d2.b3)
  if c4 != 1 then c4 else
  let c5 := cmpU32 (packBe4 a.d2.b4 a.d2.b5 a.d2.b6 a.d2.b7) (packBe4 b.d2.b4 b.d2.b5 b.d2.b6 b.d2.b7)
  if c5 != 1 then c5 else
  let c6 := cmpU32 (packBe4 a.d3.b0 a.d3.b1 a.d3.b2 a.d3.b3) (packBe4 b.d3.b0 b.d3.b1 b.d3.b2 b.d3.b3)
  if c6 != 1 then c6 else
  cmpU32 (packBe4 a.d3.b4 a.d3.b5 a.d3.b6 a.d3.b7) (packBe4 b.d3.b4 b.d3.b5 b.d3.b6 b.d3.b7)

/-- Append two `DigestBytesList`s (structural on `xs`). -/
@[circuit_noinline]
def digestBytesListAppend (xs ys : DigestBytesList) : DigestBytesList :=
  match xs with
  | .nil => ys
  | .cons x rest => .cons x (digestBytesListAppend rest ys)
termination_by structural xs

/-- Prepend every 32-byte address in `addrs` onto `tail` (`Aggregation::aggr_put_addresses`). -/
@[circuit_noinline]
def putAddresses (addrs : DigestBytesList) (tail : ByteList) : ByteList :=
  match addrs with
  | .nil => tail
  | .cons a rest => digestBytesOnto a (putAddresses rest tail)
termination_by structural addrs

/-- Check strict ascending order on a list of 32-byte addresses (`Aggregation::aggr_assert_strict_sorted`). -/
@[circuit_noinline]
def aggrAssertStrictSorted : DigestBytesList → Nat
  | .nil => 1
  | .cons a rest =>
    match rest with
    | .nil => 1
    | .cons b _ =>
      if aggrAddressOrder a b == 0 then aggrAssertStrictSorted rest else 0
termination_by structural xs => xs

/-! ## Section 2: Canonical Assumption Trees & Set Operations (`Aggregation.lean` lines 235–506) -/

/-- Structural-fuel parser for an Ixon `AssumptionTree` body (`Aggregation::aggr_parse_tree_body`).
Tags: `0` = leaf (`32` bytes), `1` = padding (empty), `2` = binary node. -/
@[circuit_noinline]
def aggrParseTreeBodyFuel (fuel : Nat) (s : ByteList) : ParseDigestList :=
  match fuel with
  | 0 => { ok := 0, val := .nil, rest := .nil }
  | fuel' + 1 =>
    let rt := readU8 s
    if rt.ok == 0 then { ok := 0, val := .nil, rest := .nil }
    else if rt.val == 0 then
      let ra := readDigest rt.rest
      if ra.ok == 0 then { ok := 0, val := .nil, rest := .nil }
      else { ok := 1, val := .cons ra.val .nil, rest := ra.rest }
    else if rt.val == 1 then
      { ok := 1, val := .nil, rest := rt.rest }
    else if rt.val == 2 then
      let rl := aggrParseTreeBodyFuel fuel' rt.rest
      if rl.ok == 0 then { ok := 0, val := .nil, rest := .nil }
      else
        let rr := aggrParseTreeBodyFuel fuel' rl.rest
        if rr.ok == 0 then { ok := 0, val := .nil, rest := .nil }
        else { ok := 1, val := digestBytesListAppend rl.val rr.val, rest := rr.rest }
    else
      { ok := 0, val := .nil, rest := .nil }
termination_by structural fuel

/-- Hash every leaf address with prefix `0x00` (`Aggregation::aggr_leaf_hashes`). -/
@[circuit_noinline]
def aggrLeafHashes : DigestBytesList → DigestBytesList
  | .nil => .nil
  | .cons addr rest => .cons (aggrLeafHash addr) (aggrLeafHashes rest)
termination_by structural xs => xs

/-- Pair adjacent Merkle hashes, padding a trailing odd node with `dummyDigestBytes` (32 zero bytes)
(`Aggregation::aggr_pair_hashes`). -/
@[circuit_noinline]
def aggrPairHashes : DigestBytesList → DigestBytesList
  | .nil => .nil
  | .cons left rest =>
    match rest with
    | .nil => .cons (aggrNodeHash left dummyDigestBytes) .nil
    | .cons right tail => .cons (aggrNodeHash left right) (aggrPairHashes tail)
termination_by structural xs => xs

/-- Reduce a non-empty list of Merkle node hashes to its single root (`Aggregation::aggr_reduce_hashes`). -/
@[circuit_noinline]
def aggrReduceHashesFuel (fuel : Nat) (nodes : DigestBytesList) : DigestBytes :=
  match fuel with
  | 0 =>
    match nodes with
    | .nil => dummyDigestBytes
    | .cons root _ => root
  | fuel' + 1 =>
    match nodes with
    | .nil => dummyDigestBytes
    | .cons root rest =>
      match rest with
      | .nil => root
      | .cons _ _ => aggrReduceHashesFuel fuel' (aggrPairHashes nodes)
termination_by structural fuel

/-- Canonical Merkle root of a non-empty strictly sorted leaf list (`Aggregation::aggr_canonical_root`). -/
@[circuit_inline]
def aggrCanonicalRoot (leaves : DigestBytesList) : DigestBytes :=
  aggrReduceHashesFuel (digestBytesListLen leaves + 1) (aggrLeafHashes leaves)

/-- Verify a serialized Ixon `0xE2` canonical tree against `root` (`Aggregation::aggr_load_canonical_tree`):
checks tag `226`, parses tree body with zero trailing bytes, checks non-empty leaves, checks
strict ascending order, and checks that `aggrCanonicalRoot leaves == root`. -/
@[circuit_noinline]
def aggrCheckCanonicalTree (root : DigestBytes) (treeBytes : ByteList) : ParseDigestList :=
  let bad : ParseDigestList := { ok := 0, val := .nil, rest := .nil }
  let rt := readU8 treeBytes
  if rt.ok == 0 || rt.val != 226 then bad
  else
    let rb := aggrParseTreeBodyFuel (byteListLen rt.rest + 1) rt.rest
    if rb.ok == 0 then bad
    else
      match rb.rest with
      | .cons _ _ => bad
      | .nil =>
        match rb.val with
        | .nil => bad
        | .cons _ _ =>
          if aggrAssertStrictSorted rb.val == 0 then bad
          else if digestBytesEq (aggrCanonicalRoot rb.val) root == 0 then bad
          else { ok := 1, val := rb.val, rest := .nil }

/-- Verify an optional canonical tree (`Aggregation::aggr_load_optional_tree`). -/
@[circuit_inline]
def aggrCheckOptionalTree (optRoot : OptAddr) (treeBytes : ByteList) : ParseDigestList :=
  match optRoot with
  | .none => { ok := 1, val := .nil, rest := .nil }
  | .some root => aggrCheckCanonicalTree root treeBytes

/-- Exact list equality on `DigestBytesList` (`Aggregation::aggr_assert_same_list`). -/
@[circuit_noinline]
def aggrAssertSameList (left right : DigestBytesList) : Nat :=
  match left with
  | .nil => match right with | .nil => 1 | .cons _ _ => 0
  | .cons a ar =>
    match right with
    | .nil => 0
    | .cons b br =>
      if digestBytesEq a b == 1 then aggrAssertSameList ar br else 0
termination_by structural left

/-- Verify `output = left ∪ right` on strictly sorted lists (`Aggregation::aggr_assert_union`). -/
@[circuit_noinline]
def aggrAssertUnionFuel (fuel : Nat) (left right output : DigestBytesList) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match left with
    | .nil => aggrAssertSameList right output
    | .cons a ar =>
      match right with
      | .nil => aggrAssertSameList left output
      | .cons b br =>
        match output with
        | .nil => 0
        | .cons o or_ =>
          let ord := aggrAddressOrder a b
          if ord == 0 then
            if digestBytesEq a o == 1 then aggrAssertUnionFuel fuel' ar right or_ else 0
          else if ord == 1 then
            if digestBytesEq a o == 1 then aggrAssertUnionFuel fuel' ar br or_ else 0
          else
            if digestBytesEq b o == 1 then aggrAssertUnionFuel fuel' left br or_ else 0
termination_by structural fuel

@[circuit_inline]
def aggrAssertUnion (left right output : DigestBytesList) : Nat :=
  aggrAssertUnionFuel (digestBytesListLen left + digestBytesListLen right + 1) left right output

/-- Verify `left ∩ right = ∅` and `output = left ∪ right` (`Aggregation::aggr_assert_disjoint_union`). -/
@[circuit_noinline]
def aggrAssertDisjointUnionFuel (fuel : Nat) (left right output : DigestBytesList) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match left with
    | .nil => aggrAssertSameList right output
    | .cons a ar =>
      match right with
      | .nil => aggrAssertSameList left output
      | .cons b br =>
        match output with
        | .nil => 0
        | .cons o or_ =>
          let ord := aggrAddressOrder a b
          if ord == 0 then
            if digestBytesEq a o == 1 then aggrAssertDisjointUnionFuel fuel' ar right or_ else 0
          else if ord == 1 then 0
          else
            if digestBytesEq b o == 1 then aggrAssertDisjointUnionFuel fuel' left br or_ else 0
termination_by structural fuel

@[circuit_inline]
def aggrAssertDisjointUnion (left right output : DigestBytesList) : Nat :=
  aggrAssertDisjointUnionFuel (digestBytesListLen left + digestBytesListLen right + 1) left right output

/-- Verify `left ∩ right = ∅` on strictly sorted lists (`Aggregation::aggr_assert_disjoint`). -/
@[circuit_noinline]
def aggrAssertDisjointFuel (fuel : Nat) (left right : DigestBytesList) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match left with
    | .nil => 1
    | .cons a ar =>
      match right with
      | .nil => 1
      | .cons b br =>
        let ord := aggrAddressOrder a b
        if ord == 0 then aggrAssertDisjointFuel fuel' ar right
        else if ord == 1 then 0
        else aggrAssertDisjointFuel fuel' left br
termination_by structural fuel

@[circuit_inline]
def aggrAssertDisjoint (left right : DigestBytesList) : Nat :=
  aggrAssertDisjointFuel (digestBytesListLen left + digestBytesListLen right + 1) left right

/-- Pop the minimum next assumption from two sorted assumption lists (`Aggregation::aggr_next_assumption`).
`source = 0` (left only), `1` (both), `2` (right only). -/
@[circuit_noinline]
def aggrNextAssumption (left right : DigestBytesList) : NextAssumption :=
  match left with
  | .nil =>
    match right with
    | .nil => .done
    | .cons b br => .more b 2 .nil br
  | .cons a ar =>
    match right with
    | .nil => .more a 0 ar .nil
    | .cons b br =>
      let ord := aggrAddressOrder a b
      if ord == 0 then .more a 0 ar right
      else if ord == 1 then .more a 1 ar br
      else .more b 2 left br

/-- Seek `target` inside a sorted subject list (`Aggregation::aggr_seek_subject`). -/
@[circuit_noinline]
def aggrSeekSubject (target : DigestBytes) (subjects : DigestBytesList) : SeekSubjectOut :=
  match subjects with
  | .nil => { found := 0, rest := .nil }
  | .cons subj rest =>
    let ord := aggrAddressOrder subj target
    if ord == 0 then aggrSeekSubject target rest
    else if ord == 1 then { found := 1, rest := rest }
    else { found := 0, rest := subjects }
termination_by structural subjects

/-- Verify `output = (left ∪ right) \ subjects` on sorted lists (`Aggregation::aggr_assert_difference`). -/
@[circuit_noinline]
def aggrAssertDifferenceFuel (fuel : Nat) (left right subjects output : DigestBytesList) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match aggrNextAssumption left right with
    | .done =>
      match output with
      | .nil => 1
      | .cons _ _ => 0
    | .more cand _ leftRest rightRest =>
      let seek := aggrSeekSubject cand subjects
      if seek.found == 1 then
        aggrAssertDifferenceFuel fuel' leftRest rightRest seek.rest output
      else
        match output with
        | .nil => 0
        | .cons actual outRest =>
          if digestBytesEq cand actual == 1 then
            aggrAssertDifferenceFuel fuel' leftRest rightRest seek.rest outRest
          else 0
termination_by structural fuel

@[circuit_inline]
def aggrAssertDifference (left right subjects output : DigestBytesList) : Nat :=
  aggrAssertDifferenceFuel (digestBytesListLen left + digestBytesListLen right + 1) left right subjects output

/-- Lookup a candidate assumption's structural discharge choice bytes in `PathTable`. -/
@[circuit_noinline]
def pathTableLookup (tbl : PathTable) (cand : DigestBytes) : ByteList :=
  match tbl with
  | .nil => .nil
  | .cons entry rest =>
    if digestBytesEq entry.candidate cand == 1 then entry.bytes
    else pathTableLookup rest cand
termination_by structural tbl

/-- Fold `remaining` Merkle path steps upward from `hash` (`Aggregation::aggr_fold_path`). -/
@[circuit_noinline]
def aggrFoldPath (hash : DigestBytes) (remaining : Nat) (s : ByteList) : ParseDigest :=
  match remaining with
  | 0 => { ok := 1, val := hash, rest := s }
  | rem' + 1 =>
    let rside := readU8 s
    if rside.ok == 0 || rside.val ≥ 2 then { ok := 0, val := dummyDigestBytes, rest := .nil }
    else
      let rsib := readDigest rside.rest
      if rsib.ok == 0 then { ok := 0, val := dummyDigestBytes, rest := .nil }
      else
        let parent :=
          if rside.val == 0 then aggrNodeHash rsib.val hash
          else aggrNodeHash hash rsib.val
        aggrFoldPath parent rem' rsib.rest
termination_by structural remaining

/-- Verify one structural discharge choice (`Aggregation::aggr_discharge_choice`):
returns `ok = 1, val = 0` for carried, `ok = 1, val = 1` for discharged by a verified Merkle
path into the opposite child's subject root (`source = 0 → rightRoot`, `source = 2 → leftRoot`,
rejecting shared `source = 1`), or `ok = 0` on any failure. -/
@[circuit_noinline]
def aggrVerifyDischargeChoice (candidate : DigestBytes) (source : Nat)
    (leftRoot rightRoot : DigestBytes) (choiceBytes : ByteList) : ParseNat :=
  let bad : ParseNat := { ok := 0, val := 0, rest := .nil }
  let rc := readU8 choiceBytes
  if rc.ok == 0 || rc.val ≥ 2 then bad
  else if rc.val == 0 then
    match rc.rest with
    | .nil => { ok := 1, val := 0, rest := .nil }
    | .cons _ _ => bad
  else
    let rcnt := readU8 rc.rest
    if rcnt.ok == 0 || rcnt.val == 0 || rcnt.val ≥ 65 then bad
    else
      let rf := aggrFoldPath (aggrLeafHash candidate) (rcnt.val - 1) rcnt.rest
      if rf.ok == 0 then bad
      else
        let rls := readU8 rf.rest
        if rls.ok == 0 then bad
        else
          let rlsib := readDigest rls.rest
          if rlsib.ok == 0 then bad
          else
            match rlsib.rest with
            | .cons _ _ => bad
            | .nil =>
              if source == 0 then
                if rls.val == 0 && digestBytesEq rlsib.val leftRoot == 1 &&
                   digestBytesEq rf.val rightRoot == 1 then
                  { ok := 1, val := 1, rest := .nil }
                else bad
              else if source == 2 then
                if rls.val == 1 && digestBytesEq rlsib.val rightRoot == 1 &&
                   digestBytesEq rf.val leftRoot == 1 then
                  { ok := 1, val := 1, rest := .nil }
                else bad
              else bad

/-- Verify structural assumption discharge across two sorted assumption lists
(`Aggregation::aggr_assert_structural_difference`). -/
@[circuit_noinline]
def aggrAssertStructuralDifferenceFuel (fuel : Nat) (left right : DigestBytesList)
    (leftRoot rightRoot : DigestBytes) (output : DigestBytesList) (paths : PathTable) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match aggrNextAssumption left right with
    | .done =>
      match output with
      | .nil => 1
      | .cons _ _ => 0
    | .more cand source leftRest rightRest =>
      let dc := aggrVerifyDischargeChoice cand source leftRoot rightRoot (pathTableLookup paths cand)
      if dc.ok == 0 then 0
      else if dc.val == 1 then
        aggrAssertStructuralDifferenceFuel fuel' leftRest rightRest leftRoot rightRoot output paths
      else
        match output with
        | .nil => 0
        | .cons actual outRest =>
          if digestBytesEq cand actual == 1 then
            aggrAssertStructuralDifferenceFuel fuel' leftRest rightRest leftRoot rightRoot outRest paths
          else 0
termination_by structural fuel

@[circuit_inline]
def aggrAssertStructuralDifference (left right : DigestBytesList)
    (leftRoot rightRoot : DigestBytes) (output : DigestBytesList) (paths : PathTable) : Nat :=
  aggrAssertStructuralDifferenceFuel
    (digestBytesListLen left + digestBytesListLen right + 1)
    left right leftRoot rightRoot output paths

/-! ## Section 3: Allowed-Blob Binding & All Claim / Statement Binary Parsers -/

/-- Parse and verify the exact 80-byte allowed-identity blob (`MultiStark::ix_aggr` lines 17–31):
`ixvm_vk (32 B) ‖ verify_idx (8 B LE) ‖ self_vk (32 B) ‖ aggr_idx (8 B LE)` hashing to `allowedDigest`. -/
@[circuit_noinline]
def parseAllowedBlob (allowedDigest : Digest32Words) (allowedBytes : ByteList) : ParseAllowedOut :=
  let bad : ParseAllowedOut := { ok := 0, val := dummyAllowedParams }
  if byteListLen allowedBytes != 80 then bad
  else if digest32WordsEq (packDigest (blake3HashBytes allowedBytes)) allowedDigest == 0 then bad
  else
    let rIxvm := readDigest allowedBytes
    if rIxvm.ok == 0 then bad
    else
      let rVidx := readU64LE rIxvm.rest
      if rVidx.ok == 0 || glLtPBytes rVidx.val == 0 then bad
      else
        let rSelf := readDigest rVidx.rest
        if rSelf.ok == 0 then bad
        else
          let rAidx := readU64LE rSelf.rest
          if rAidx.ok == 0 || glLtPBytes rAidx.val == 0 then bad
          else
            match rAidx.rest with
            | .cons _ _ => bad
            | .nil =>
              { ok := 1
                val :=
                  { ixvmVkDigest := packAddress rIxvm.val
                    verifyIdx := glValBytes rVidx.val
                    selfVkDigest := packAddress rSelf.val
                    aggrIdx := glValBytes rAidx.val } }

/-- Read an `OptAddr` (`0 => none`, `1 => some addr`) (`Aggregation::aggr_get_opt_address`). -/
@[circuit_noinline]
def readOptAddr (s : ByteList) : ParseOptAddr :=
  let bad : ParseOptAddr := { ok := 0, val := .none, rest := .nil }
  let rt := readU8 s
  if rt.ok == 0 then bad
  else if rt.val == 0 then { ok := 1, val := .none, rest := rt.rest }
  else if rt.val == 1 then
    let ra := readDigest rt.rest
    if ra.ok == 0 then bad
    else { ok := 1, val := .some ra.val, rest := ra.rest }
  else bad

/-- Exact equality on `OptAddr` (`Aggregation::aggr_opt_address_eq`). -/
@[circuit_inline]
def optAddrEq (a b : OptAddr) : Nat :=
  match a, b with
  | .none, .none => 1
  | .some x, .some y => digestBytesEq x y
  | _, _ => 0

/-- Parse a standard `CheckEnv` claim (`Aggregation::aggr_parse_check_env`):
tag `229` (`0xE5`), format `4`, validator `∈ {3, 4, 5}`, zero trailing bytes. -/
@[circuit_noinline]
def aggrParseCheckEnv (bytes : ByteList) : ParseCheckEnvOut :=
  let bad : ParseCheckEnvOut :=
    { ok := 0, ctx := dummyCheckEnvCtx, root := dummyDigestBytes, assumptions := .none }
  let rTag := readU8 bytes
  if rTag.ok == 0 || rTag.val != 229 then bad else
  let rFmt := readU8 rTag.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 || (rVal.val != 3 && rVal.val != 4 && rVal.val != 5) then bad else
  let rSpec := readDigest rVal.rest
  if rSpec.ok == 0 then bad else
  let rBind := readDigest rSpec.rest
  if rBind.ok == 0 then bad else
  let rAx := readOptAddr rBind.rest
  if rAx.ok == 0 then bad else
  let rRoot := readDigest rAx.rest
  if rRoot.ok == 0 then bad else
  let rAsm := readOptAddr rRoot.rest
  if rAsm.ok == 0 then bad else
  match rAsm.rest with
  | .cons _ _ => bad
  | .nil =>
    { ok := 1
      ctx := { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := rVal.val }
      root := rRoot.val
      assumptions := rAsm.val }

/-- Parse a standard `Check` claim (`Aggregation::aggr_parse_check`):
tag `228` (`0xE4`), format `4`, validator `∈ {3, 4}`, zero trailing bytes. -/
@[circuit_noinline]
def aggrParseCheck (bytes : ByteList) : ParseCheckEnvOut :=
  let bad : ParseCheckEnvOut :=
    { ok := 0, ctx := dummyCheckEnvCtx, root := dummyDigestBytes, assumptions := .none }
  let rTag := readU8 bytes
  if rTag.ok == 0 || rTag.val != 228 then bad else
  let rFmt := readU8 rTag.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 || (rVal.val != 3 && rVal.val != 4) then bad else
  let rSpec := readDigest rVal.rest
  if rSpec.ok == 0 then bad else
  let rBind := readDigest rSpec.rest
  if rBind.ok == 0 then bad else
  let rAx := readOptAddr rBind.rest
  if rAx.ok == 0 then bad else
  let rConst := readDigest rAx.rest
  if rConst.ok == 0 then bad else
  let rAsm := readOptAddr rConst.rest
  if rAsm.ok == 0 then bad else
  match rAsm.rest with
  | .cons _ _ => bad
  | .nil =>
    { ok := 1
      ctx := { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := rVal.val }
      root := rConst.val
      assumptions := rAsm.val }

/-- Parse a `Binding` claim (`Aggregation::aggr_parse_binding`):
tags `232, 2` (`0xE8 0x02`), format `4`, validator `3`, zero trailing bytes. -/
@[circuit_noinline]
def aggrParseBinding (bytes : ByteList) : ParseBindingOut :=
  let bad : ParseBindingOut := { ok := 0, spec := dummyDigestBytes, binding := dummyDigestBytes }
  let r0 := readU8 bytes
  if r0.ok == 0 || r0.val != 232 then bad else
  let r1 := readU8 r0.rest
  if r1.ok == 0 || r1.val != 2 then bad else
  let rFmt := readU8 r1.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 || rVal.val != 3 then bad else
  let rSpec := readDigest rVal.rest
  if rSpec.ok == 0 then bad else
  let rBind := readDigest rSpec.rest
  if rBind.ok == 0 then bad else
  match rBind.rest with
  | .cons _ _ => bad
  | .nil => { ok := 1, spec := rSpec.val, binding := rBind.val }

/-- Parse a `Catalog` claim (`Aggregation::aggr_parse_catalog`):
tags `232, 0` (`0xE8 0x00`), format `4`, validator `3`, zero trailing bytes. -/
@[circuit_noinline]
def aggrParseCatalog (bytes : ByteList) : ParseCatalogOut :=
  let bad : ParseCatalogOut := { ok := 0, members := dummyDigestBytes }
  let r0 := readU8 bytes
  if r0.ok == 0 || r0.val != 232 then bad else
  let r1 := readU8 r0.rest
  if r1.ok == 0 || r1.val != 0 then bad else
  let rFmt := readU8 r1.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 || rVal.val != 3 then bad else
  let rMem := readDigest rVal.rest
  if rMem.ok == 0 then bad else
  match rMem.rest with
  | .cons _ _ => bad
  | .nil => { ok := 1, members := rMem.val }

/-- Parse a leaf `Eval` claim (`tag = 227`, format `4`, validator `∈ {3, 4}`) for leaf
classification only (explicitly NEVER invoked by Shape 18 `verifyShapeDischargeEval`). -/
@[circuit_noinline]
def aggrParseLeafEval (bytes : ByteList) : ParseEvalOut :=
  let bad : ParseEvalOut :=
    { ok := 0, ctx := dummyCheckEnvCtx
      lhs := dummyDigestBytes, rhs := dummyDigestBytes, typ := dummyDigestBytes }
  let rTag := readU8 bytes
  if rTag.ok == 0 || rTag.val != 227 then bad else
  let rFmt := readU8 rTag.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 || (rVal.val != 3 && rVal.val != 4) then bad else
  let rSpec := readDigest rVal.rest
  if rSpec.ok == 0 then bad else
  let rBind := readDigest rSpec.rest
  if rBind.ok == 0 then bad else
  let rAx := readOptAddr rBind.rest
  if rAx.ok == 0 then bad else
  let rLhs := readDigest rAx.rest
  if rLhs.ok == 0 then bad else
  let rRhs := readDigest rLhs.rest
  if rRhs.ok == 0 then bad else
  let rTyp := readDigest rRhs.rest
  if rTyp.ok == 0 then bad else
  match rTyp.rest with
  | .cons _ _ => bad
  | .nil =>
    { ok := 1
      ctx := { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := rVal.val }
      lhs := rLhs.val, rhs := rRhs.val, typ := rTyp.val }

/-- Recognize a leaf `Reveal` (`tag = 230`) or `Contains` (`tag = 231`) structural claim header
(format `4`, validator `0`, followed by its 32-byte subject address). -/
@[circuit_noinline]
def aggrParseStructuralLeafHeader (expectedTag : Nat) (bytes : ByteList) : ParseDigest :=
  let bad : ParseDigest := { ok := 0, val := dummyDigestBytes, rest := .nil }
  let rTag := readU8 bytes
  if rTag.ok == 0 || rTag.val != expectedTag then bad else
  let rFmt := readU8 rTag.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 || rVal.val != 0 then bad else
  readDigest rVal.rest

/-- Parse a Shape `10–12` range statement (`Aggregation::aggr_parse_range`):
tag `82` (`0x52`), batch digest `32 B`, canonical `< p_GL` `lo`, `hi`, and residual `(r0, r1, r2)`. -/
@[circuit_noinline]
def aggrParseRange (bytes : ByteList) : ParseRangeOut :=
  let bad : ParseRangeOut :=
    { ok := 0, batchDigest := dummyDigestBytes, lo := u64Zero, hi := u64Zero, residual := extZero }
  let rTag := readU8 bytes
  if rTag.ok == 0 || rTag.val != 82 then bad else
  let rd := readDigest rTag.rest
  if rd.ok == 0 then bad else
  let rLo := readU64LE rd.rest
  if rLo.ok == 0 || glLtPBytes rLo.val == 0 then bad else
  let rHi := readU64LE rLo.rest
  if rHi.ok == 0 || glLtPBytes rHi.val == 0 then bad else
  let r0 := readU64LE rHi.rest
  if r0.ok == 0 || glLtPBytes r0.val == 0 then bad else
  let r1 := readU64LE r0.rest
  if r1.ok == 0 || glLtPBytes r1.val == 0 then bad else
  let r2 := readU64LE r1.rest
  if r2.ok == 0 || glLtPBytes r2.val == 0 then bad else
  match r2.rest with
  | .cons _ _ => bad
  | .nil =>
    { ok := 1
      batchDigest := rd.val
      lo := rLo.val
      hi := rHi.val
      residual := { c0 := glValBytes r0.val, c1 := glValBytes r1.val, c2 := glValBytes r2.val } }

/-- Parse a Shape `17` `DynamicLinkStatement` (`Aggregation::aggr_parse_dynamic_link`, `0xE8 0x0D`). -/
@[circuit_noinline]
def aggrParseDynamicLink (bytes : ByteList) : ParseDynamicLinkOut :=
  let bad : ParseDynamicLinkOut :=
    { ok := 0, vkDigest := dummyDigestBytes, entryIdx := u64Zero
      pubInputs := .nil, pubOutputs := .nil, bridge := .noBridge }
  let r0 := readU8 bytes
  if r0.ok == 0 || r0.val != 232 then bad else
  let r1 := readU8 r0.rest
  if r1.ok == 0 || r1.val != 13 then bad else
  let rVk := readDigest r1.rest
  if rVk.ok == 0 then bad else
  let rEntry := readU64LE rVk.rest
  if rEntry.ok == 0 then bad else
  let rNin := readU32LE rEntry.rest
  if rNin.ok == 0 then bad else
  let rIn := readU64VecN rNin.rest rNin.val
  if rIn.ok == 0 then bad else
  let rNout := readU32LE rIn.rest
  if rNout.ok == 0 then bad else
  let rOut := readU64VecN rNout.rest rNout.val
  if rOut.ok == 0 then bad else
  let rBtag := readU8 rOut.rest
  if rBtag.ok == 0 then bad else
  if rBtag.val == 0 then
    match rBtag.rest with
    | .cons _ _ => bad
    | .nil =>
      { ok := 1, vkDigest := rVk.val, entryIdx := rEntry.val
        pubInputs := rIn.val, pubOutputs := rOut.val, bridge := .noBridge }
  else if rBtag.val == 1 then
    let rSpec := readDigest rBtag.rest
    if rSpec.ok == 0 then bad else
    let rBind := readDigest rSpec.rest
    if rBind.ok == 0 then bad else
    let rTgt := readDigest rBind.rest
    if rTgt.ok == 0 then bad else
    let rCodec := readU64LE rTgt.rest
    if rCodec.ok == 0 then bad else
    let rCert := readDigest rCodec.rest
    if rCert.ok == 0 then bad else
    match rCert.rest with
    | .cons _ _ => bad
    | .nil =>
      { ok := 1, vkDigest := rVk.val, entryIdx := rEntry.val
        pubInputs := rIn.val, pubOutputs := rOut.val
        bridge := .someBridge rSpec.val rBind.val rTgt.val rCodec.val rCert.val }
  else bad

/-- Parse a Shape `18` `EvalAssumption` leaf (`Aggregation::aggr_parse_eval_assumption`, `0xE8 0x0E`). -/
@[circuit_noinline]
def aggrParseEvalAssumption (bytes : ByteList) : ParseEvalAssumptionOut :=
  let bad : ParseEvalAssumptionOut :=
    { ok := 0, lhs := dummyDigestBytes, rhs := dummyDigestBytes, typ := dummyDigestBytes
      circuit := .noCircuitRef }
  let r0 := readU8 bytes
  if r0.ok == 0 || r0.val != 232 then bad else
  let r1 := readU8 r0.rest
  if r1.ok == 0 || r1.val != 14 then bad else
  let rLhs := readDigest r1.rest
  if rLhs.ok == 0 then bad else
  let rRhs := readDigest rLhs.rest
  if rRhs.ok == 0 then bad else
  let rTyp := readDigest rRhs.rest
  if rTyp.ok == 0 then bad else
  let rCtag := readU8 rTyp.rest
  if rCtag.ok == 0 then bad else
  if rCtag.val == 0 then
    match rCtag.rest with
    | .cons _ _ => bad
    | .nil => { ok := 1, lhs := rLhs.val, rhs := rRhs.val, typ := rTyp.val, circuit := .noCircuitRef }
  else if rCtag.val == 1 then
    let rVk := readDigest rCtag.rest
    if rVk.ok == 0 then bad else
    let rEntry := readU64LE rVk.rest
    if rEntry.ok == 0 then bad else
    match rEntry.rest with
    | .cons _ _ => bad
    | .nil =>
      { ok := 1, lhs := rLhs.val, rhs := rRhs.val, typ := rTyp.val
        circuit := .someCircuitRef rVk.val rEntry.val }
  else bad

/-- Parse child 0 of Shape `18` (`Aggregation::aggr_parse_eval_assumed`):
admits ONLY tags `228`/`229`, format `4`, and validators `∈ {10, 11, 12, 13}` (never `3`/`4`/`5`/`14`/`15`). -/
@[circuit_noinline]
def aggrParseEvalAssumed (bytes : ByteList) : ParseEvalAssumedOut :=
  let bad : ParseEvalAssumedOut :=
    { ok := 0, tag := 0, ctx := dummyCheckEnvCtx, target := dummyDigestBytes
      assumptions := .none, evalRoot := dummyDigestBytes, linked := .none }
  let rTag := readU8 bytes
  if rTag.ok == 0 || (rTag.val != 228 && rTag.val != 229) then bad else
  let rFmt := readU8 rTag.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 then bad else
  let rSpec := readDigest rVal.rest
  if rSpec.ok == 0 then bad else
  let rBind := readDigest rSpec.rest
  if rBind.ok == 0 then bad else
  let rAx := readOptAddr rBind.rest
  if rAx.ok == 0 then bad else
  let rTgt := readDigest rAx.rest
  if rTgt.ok == 0 then bad else
  let rAsm := readOptAddr rTgt.rest
  if rAsm.ok == 0 then bad else
  let ctx : CheckEnvCtx :=
    { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := rVal.val }
  if rVal.val == 10 || rVal.val == 11 then
    let rEval := readDigest rAsm.rest
    if rEval.ok == 0 then bad else
    match rEval.rest with
    | .cons _ _ => bad
    | .nil =>
      { ok := 1, tag := rTag.val, ctx := ctx, target := rTgt.val
        assumptions := rAsm.val, evalRoot := rEval.val, linked := .none }
  else if rVal.val == 12 || rVal.val == 13 then
    let rEvalOpt := readOptAddr rAsm.rest
    if rEvalOpt.ok == 0 then bad else
    match rEvalOpt.val with
    | .none => bad
    | .some evalRoot =>
      let rLnk := readDigest rEvalOpt.rest
      if rLnk.ok == 0 then bad else
      match rLnk.rest with
      | .cons _ _ => bad
      | .nil =>
        { ok := 1, tag := rTag.val, ctx := ctx, target := rTgt.val
          assumptions := rAsm.val, evalRoot := evalRoot, linked := .some rLnk.val }
  else bad

/-- Parse the output claim of Shape `18` (`Aggregation::aggr_parse_eval_discharge_out`):
- Linked output (`outValidator == linkedVal`, where `10/12 → 12`, `11/13 → 13`): carries `evalOpt` and mandatory `linkedRoot`.
- Unlinked output requires `c0Validator ∈ {10, 11}` (validators `12`/`13` can NEVER transition to unlinked!):
  - Partial step (`outValidator == c0Validator`): carries mandatory `evalRoot`, `linked = none`.
  - Full Mode 2 discharge (`outValidator == c0Validator + 4`, i.e., `10 → 14` or `11 → 15`, NEVER `3`/`4`/`5`): `eval = none`, `linked = none`. -/
@[circuit_noinline]
def aggrParseEvalDischargeOut (bytes : ByteList) (expectedTag c0Validator : Nat) :
    ParseEvalDischargeOut :=
  let bad : ParseEvalDischargeOut :=
    { ok := 0, ctx := dummyCheckEnvCtx, target := dummyDigestBytes
      assumptions := .none, evalOpt := .none, linkedOpt := .none }
  if c0Validator != 10 && c0Validator != 11 && c0Validator != 12 && c0Validator != 13 then bad else
  let rTag := readU8 bytes
  if rTag.ok == 0 || rTag.val != expectedTag then bad else
  let rFmt := readU8 rTag.rest
  if rFmt.ok == 0 || rFmt.val != 4 then bad else
  let rVal := readU8 rFmt.rest
  if rVal.ok == 0 then bad else
  let rSpec := readDigest rVal.rest
  if rSpec.ok == 0 then bad else
  let rBind := readDigest rSpec.rest
  if rBind.ok == 0 then bad else
  let rAx := readOptAddr rBind.rest
  if rAx.ok == 0 then bad else
  let rTgt := readDigest rAx.rest
  if rTgt.ok == 0 then bad else
  let rAsm := readOptAddr rTgt.rest
  if rAsm.ok == 0 then bad else
  let outVal := rVal.val
  let ctx : CheckEnvCtx :=
    { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := outVal }
  let linkedVal := if c0Validator == 10 || c0Validator == 12 then 12 else 13
  if outVal == linkedVal then
    let rEvalOpt := readOptAddr rAsm.rest
    if rEvalOpt.ok == 0 then bad else
    let rLnk := readDigest rEvalOpt.rest
    if rLnk.ok == 0 then bad else
    match rLnk.rest with
    | .cons _ _ => bad
    | .nil =>
      { ok := 1, ctx := ctx, target := rTgt.val, assumptions := rAsm.val
        evalOpt := rEvalOpt.val, linkedOpt := .some rLnk.val }
  else if c0Validator == 10 || c0Validator == 11 then
    if outVal == c0Validator then
      let rEval := readDigest rAsm.rest
      if rEval.ok == 0 then bad else
      match rEval.rest with
      | .cons _ _ => bad
      | .nil =>
        { ok := 1, ctx := ctx, target := rTgt.val, assumptions := rAsm.val
          evalOpt := .some rEval.val, linkedOpt := .none }
    else if outVal == c0Validator + 4 then
      match rAsm.rest with
      | .cons _ _ => bad
      | .nil =>
        { ok := 1, ctx := ctx, target := rTgt.val, assumptions := rAsm.val
          evalOpt := .none, linkedOpt := .none }
    else bad
  else bad

/-! ### Context, Axiom Merge, Role-Binding Class, Security Envelope, Linked Merge, & `@Eq` Checks -/

/-- Check `(spec, binding, validator)` equality (`Aggregation::aggr_assert_same_context_base`). -/
@[circuit_inline]
def aggrAssertSameContextBase (a b : CheckEnvCtx) : Nat :=
  if digestBytesEq a.spec b.spec == 1 &&
     digestBytesEq a.binding b.binding == 1 &&
     a.validator == b.validator then 1 else 0

/-- Check full `(spec, binding, axioms, validator)` equality (`Aggregation::aggr_assert_same_context`). -/
@[circuit_inline]
def aggrAssertSameContext (a b : CheckEnvCtx) : Nat :=
  if aggrAssertSameContextBase a b == 1 && optAddrEq a.axioms b.axioms == 1 then 1 else 0

/-- Verify user-axiom set union (`Aggregation::aggr_assert_axioms_merge`). -/
@[circuit_noinline]
def aggrAssertAxiomsMerge (left right output : OptAddr)
    (leftTreeBytes rightTreeBytes outTreeBytes : ByteList) : Nat :=
  match left with
  | .none => optAddrEq right output
  | .some la =>
    match right with
    | .none => optAddrEq left output
    | .some ra =>
      if digestBytesEq la ra == 1 then optAddrEq left output
      else
        match output with
        | .none => 0
        | .some oa =>
          let lt := aggrCheckCanonicalTree la leftTreeBytes
          let rt := aggrCheckCanonicalTree ra rightTreeBytes
          let ot := aggrCheckCanonicalTree oa outTreeBytes
          if lt.ok == 1 && rt.ok == 1 && ot.ok == 1 then
            aggrAssertUnion lt.val rt.val ot.val
          else 0

/-- Exact 13 literal-class roles (`Aggregation::aggr_is_class_role`). -/
@[circuit_inline]
def aggrIsClassRole (i : Nat) : Nat :=
  if i == 0 || i == 1 || i == 2 ||
     i == 29 || i == 30 || i == 31 ||
     i == 36 || i == 37 || i == 38 || i == 39 || i == 40 ||
     i == 56 || i == 57 then 1 else 0

/-- Walk `remaining` role entries starting at index `i`, asserting strict role order `0..107`
and collecting the 13 class-role addresses (`Aggregation::aggr_class_walk`). -/
@[circuit_noinline]
def aggrClassWalk (s : ByteList) (i : Nat) : Nat → ParseDigestList
  | 0 => { ok := 1, val := .nil, rest := s }
  | rem + 1 =>
    let rr := readU8 s
    if rr.ok == 0 || rr.val != i then { ok := 0, val := .nil, rest := .nil }
    else
      let ra := readDigest rr.rest
      if ra.ok == 0 then { ok := 0, val := .nil, rest := .nil }
      else
        let tail := aggrClassWalk ra.rest (i + 1) rem
        if tail.ok == 0 then { ok := 0, val := .nil, rest := .nil }
        else if aggrIsClassRole i == 1 then
          { ok := 1, val := .cons ra.val tail.val, rest := tail.rest }
        else tail
termination_by structural rem => rem

/-- Compute the 13-role literal class address of a complete 108-role binding section
(`Aggregation::aggr_binding_class`). -/
@[circuit_noinline]
def aggrBindingClass (binding : DigestBytes) (bindingBytes : ByteList) : BindingClassOut :=
  let bad : BindingClassOut := { ok := 0, cls := dummyDigestBytes }
  if digest32WordsEq (packDigest (blake3HashBytes bindingBytes)) (packAddress binding) == 0 then bad
  else
    let r0 := readU8 bindingBytes
    if r0.ok == 0 || r0.val != 232 then bad else
    let r1 := readU8 r0.rest
    if r1.ok == 0 || r1.val != 3 then bad else
    let rVer := readU8 r1.rest
    if rVer.ok == 0 then bad else
    let rCnt := readU8 rVer.rest
    if rCnt.ok == 0 || rCnt.val != 108 then bad else
    let rw := aggrClassWalk rCnt.rest 0 108
    if rw.ok == 0 then bad else
    let body := putAddresses rw.val .nil
    { ok := 1, cls := bytesToAddr (.cons 232 (.cons 4 body)) }

/-- Extract the literal class of a validator `3`/`5` context (`Aggregation::aggr_context_class`). -/
@[circuit_noinline]
def aggrContextClass (ctx : CheckEnvCtx) (bindingBytes : ByteList) : BindingClassOut :=
  if ctx.validator == 5 then { ok := 1, cls := ctx.binding }
  else if ctx.validator == 3 then aggrBindingClass ctx.binding bindingBytes
  else { ok := 0, cls := dummyDigestBytes }

/-- Exact Shape `17` uniform Multi-STARK security envelope (`Aggregation::aggr_assert_security_envelope`):
`capHeight = 0`, `logFinalPolyLen = 0`, `maxLogArity = 1`, `1 ≤ logBlowup ≤ 4`, `1 ≤ numQueries`,
`commitPowBits ≤ 32`, `queryPowBits ≤ 32`, conjectured `≥ 220` bits, provable UD `≥ 80` bits,
and finite-`m` (`m = 16`) Johnson `≥ 128` bits. -/
@[circuit_noinline]
def aggrAssertSecurityEnvelope (p : SysParams) : Nat :=
  if p.capHeight != 0 then 0
  else if p.logFinalPolyLen != 0 then 0
  else if p.maxLogArity != 1 then 0
  else checkSecurityFloor p

/-- Enforce Shape `17` codec-specific `pubInputs`/`pubOutputs` arities (`Aggregation::aggr_assert_codec_arity`):
codec `1` (`ixonAddrPair`) requires `8 + 8` words; codec `2` (`ixonAddrSingle`) requires `8 + 0` words. -/
@[circuit_noinline]
def aggrAssertCodecArity (codec : U64Bytes) (pubInputs pubOutputs : U64List) : Nat :=
  let one := u64BytesOfU32 1
  let two := u64BytesOfU32 2
  if u64BytesEq codec one == 1 then
    if u64ListLen pubInputs == 8 && u64ListLen pubOutputs == 8 then 1 else 0
  else if u64BytesEq codec two == 1 then
    if u64ListLen pubInputs == 8 && u64ListLen pubOutputs == 0 then 1 else 0
  else 1

/-- Extract the unique removed leaf `a` such that strictly sorted `before = after ∪ {a}` (`a ∉ after`)
(`Aggregation::aggr_extract_removed_leaf`). -/
@[circuit_noinline]
def aggrExtractRemovedLeaf (before after : DigestBytesList) : ExtractRemovedOut :=
  let bad : ExtractRemovedOut := { ok := 0, removed := dummyDigestBytes }
  match before with
  | .nil => bad
  | .cons a ar =>
    match after with
    | .nil =>
      match ar with
      | .nil => { ok := 1, removed := a }
      | .cons _ _ => bad
    | .cons b br =>
      if digestBytesEq a b == 1 then aggrExtractRemovedLeaf ar br
      else if aggrAssertSameList ar after == 1 then { ok := 1, removed := a }
      else bad
termination_by structural before

/-- Check that `words` is the exact 8-word `u32`-in-`u64` LE packing of `addr`
(`Aggregation::aggr_assert_packed_addr_u64s`). -/
@[circuit_noinline]
def aggrAssertPackedAddrU64s (words : U64List) (addr : DigestBytes) : Nat :=
  let mkWord (b0 b1 b2 b3 : Nat) : U64Bytes :=
    { b0 := b0, b1 := b1, b2 := b2, b3 := b3, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
  match words with
  | .cons w0 (.cons w1 (.cons w2 (.cons w3 (.cons w4 (.cons w5 (.cons w6 (.cons w7 .nil))))))) =>
    if u64BytesEq w0 (mkWord addr.d0.b0 addr.d0.b1 addr.d0.b2 addr.d0.b3) == 1 &&
       u64BytesEq w1 (mkWord addr.d0.b4 addr.d0.b5 addr.d0.b6 addr.d0.b7) == 1 &&
       u64BytesEq w2 (mkWord addr.d1.b0 addr.d1.b1 addr.d1.b2 addr.d1.b3) == 1 &&
       u64BytesEq w3 (mkWord addr.d1.b4 addr.d1.b5 addr.d1.b6 addr.d1.b7) == 1 &&
       u64BytesEq w4 (mkWord addr.d2.b0 addr.d2.b1 addr.d2.b2 addr.d2.b3) == 1 &&
       u64BytesEq w5 (mkWord addr.d2.b4 addr.d2.b5 addr.d2.b6 addr.d2.b7) == 1 &&
       u64BytesEq w6 (mkWord addr.d3.b0 addr.d3.b1 addr.d3.b2 addr.d3.b3) == 1 &&
       u64BytesEq w7 (mkWord addr.d3.b4 addr.d3.b5 addr.d3.b6 addr.d3.b7) == 1 then 1 else 0
  | _ => 0

/-- Content address of a canonical `LinkedCircuitEntry` (`0xE8 0x0F`, `Aggregation::aggr_linked_entry_addr`). -/
@[circuit_noinline]
def aggrLinkedEntryAddr (vkDigest : DigestBytes) (entryIdx codec : U64Bytes)
    (targetConst certConst evalType spec binding : DigestBytes) : DigestBytes :=
  let s7 := digestBytesOnto binding .nil
  let s6 := digestBytesOnto spec s7
  let s5 := digestBytesOnto evalType s6
  let s4 := digestBytesOnto certConst s5
  let s3 := digestBytesOnto targetConst s4
  let s2 := u64BytesOnto codec s3
  let s1 := u64BytesOnto entryIdx s2
  let s0 := digestBytesOnto vkDigest s1
  bytesToAddr (.cons 232 (.cons 15 s0))

/-- Merge an optional prior sorted Merkle tree of `LinkedCircuitEntry` leaves with an optional
newly recorded entry address (`Aggregation::aggr_assert_linked_merge`). -/
@[circuit_noinline]
def aggrAssertLinkedMerge (prevLinked addedEntry outLinked : OptAddr)
    (prevTreeBytes outTreeBytes : ByteList) : Nat :=
  match addedEntry with
  | .none => optAddrEq prevLinked outLinked
  | .some entryAddr =>
    match outLinked with
    | .none => 0
    | .some outRoot =>
      let singleRoot := aggrLeafHash entryAddr
      match prevLinked with
      | .none => digestBytesEq singleRoot outRoot
      | .some prevRoot =>
        if digestBytesEq prevRoot singleRoot == 1 then
          digestBytesEq prevRoot outRoot
        else
          let pt := aggrCheckCanonicalTree prevRoot prevTreeBytes
          let ot := aggrCheckCanonicalTree outRoot outTreeBytes
          if pt.ok == 1 && ot.ok == 1 then
            aggrAssertUnion pt.val (.cons entryAddr .nil) ot.val
          else 0

/-! ### Ixon TagN0 / TagN4 / Expression Skipper & `@Eq` Witness Verification (Shape 18 Mode 2) -/

@[circuit_noinline]
def aggrReadU24LE (s : ByteList) : ParseNat :=
  readLeNatAux 3 s 1 0

/-- Read an Ixon `TagN0` unsigned integer (`Aggregation::aggr_read_tagn0`). -/
@[circuit_noinline]
def aggrReadTagN0 (s : ByteList) : ParseNat :=
  let bad : ParseNat := { ok := 0, val := 0, rest := .nil }
  let rb := readU8 s
  if rb.ok == 0 then bad else
  let bv := rb.val
  if bv < 128 then { ok := 1, val := bv, rest := rb.rest }
  else if bv < 192 then
    let rb1 := readU8 rb.rest
    if rb1.ok == 0 then bad
    else { ok := 1, val := 128 + (bv - 128) * 256 + rb1.val, rest := rb1.rest }
  else if bv == 192 then
    let rv := readU16LE rb.rest
    if rv.ok == 0 then bad else { ok := 1, val := 16512 + rv.val, rest := rv.rest }
  else if bv == 193 then
    let rv := aggrReadU24LE rb.rest
    if rv.ok == 0 then bad else { ok := 1, val := 82048 + rv.val, rest := rv.rest }
  else if bv == 194 then
    let rv := readU32LE rb.rest
    if rv.ok == 0 then bad else { ok := 1, val := 16859264 + rv.val, rest := rv.rest }
  else if bv == 195 then
    let ru := readU64LE rb.rest
    if ru.ok == 0 then bad else { ok := 1, val := 4311826560 + glValBytes ru.val, rest := ru.rest }
  else bad

@[circuit_noinline]
def aggrSkipTagN0N (s : ByteList) : Nat → SkipExprOut
  | 0 => { ok := 1, rest := s }
  | n + 1 =>
    let r := aggrReadTagN0 s
    if r.ok == 0 then { ok := 0, rest := .nil }
    else aggrSkipTagN0N r.rest n
termination_by structural n => n

/-- Read an Ixon `TagN4` `(flag, payload)` header (`Aggregation::aggr_read_tagn4`). -/
@[circuit_noinline]
def aggrReadTagN4 (s : ByteList) : ParseTagN4Out :=
  let bad : ParseTagN4Out := { ok := 0, flag := 0, val := 0, rest := .nil }
  let rb := readU8 s
  if rb.ok == 0 then bad else
  let flag := rb.val / 16
  let payload := rb.val % 16
  if payload < 8 then { ok := 1, flag := flag, val := payload, rest := rb.rest }
  else if payload < 12 then
    let rb1 := readU8 rb.rest
    if rb1.ok == 0 then bad
    else { ok := 1, flag := flag, val := 8 + (payload - 8) * 256 + rb1.val, rest := rb1.rest }
  else if payload == 12 then
    let rv := readU16LE rb.rest
    if rv.ok == 0 then bad else { ok := 1, flag := flag, val := 1032 + rv.val, rest := rv.rest }
  else if payload == 13 then
    let rv := aggrReadU24LE rb.rest
    if rv.ok == 0 then bad else { ok := 1, flag := flag, val := 66568 + rv.val, rest := rv.rest }
  else if payload == 14 then
    let rv := readU32LE rb.rest
    if rv.ok == 0 then bad else { ok := 1, flag := flag, val := 16843784 + rv.val, rest := rv.rest }
  else
    let ru := readU64LE rb.rest
    if ru.ok == 0 then bad else { ok := 1, flag := flag, val := 4311811080 + glValBytes ru.val, rest := ru.rest }

/-- Structural-fuel skipper for `count` consecutive Ixon expressions (`Aggregation::aggr_skip_expr{,s_n}`). -/
@[circuit_noinline]
def aggrSkipExprsFuel (fuel count : Nat) (s : ByteList) : SkipExprOut :=
  match fuel with
  | 0 => if count == 0 then { ok := 1, rest := s } else { ok := 0, rest := .nil }
  | fuel' + 1 =>
    match count with
    | 0 => { ok := 1, rest := s }
    | rem + 1 =>
      let rh := aggrReadTagN4 s
      if rh.ok == 0 then { ok := 0, rest := .nil }
      else if rh.flag == 0 || rh.flag == 1 || rh.flag == 5 || rh.flag == 6 || rh.flag == 11 then
        aggrSkipExprsFuel fuel' rem rh.rest
      else if rh.flag == 2 || rh.flag == 3 then
        let rsk := aggrSkipTagN0N rh.rest (1 + rh.val)
        if rsk.ok == 0 then { ok := 0, rest := .nil }
        else aggrSkipExprsFuel fuel' rem rsk.rest
      else if rh.flag == 4 then
        let rt := aggrReadTagN0 rh.rest
        if rt.ok == 0 then { ok := 0, rest := .nil }
        else aggrSkipExprsFuel fuel' (1 + rem) rt.rest
      else if rh.flag == 7 || rh.flag == 8 || rh.flag == 9 then
        if rh.val == 0 then { ok := 0, rest := .nil }
        else aggrSkipExprsFuel fuel' (1 + rh.val + rem) rh.rest
      else if rh.flag == 10 then
        aggrSkipExprsFuel fuel' (3 + rem) rh.rest
      else
        { ok := 0, rest := .nil }
termination_by structural fuel

@[circuit_noinline]
def aggrFindRoleAddr (s : ByteList) (targetRole : Nat) : Nat → ParseDigest
  | 0 => { ok := 0, val := dummyDigestBytes, rest := .nil }
  | rem + 1 =>
    let rr := readU8 s
    if rr.ok == 0 then { ok := 0, val := dummyDigestBytes, rest := .nil }
    else
      let ra := readDigest rr.rest
      if ra.ok == 0 then { ok := 0, val := dummyDigestBytes, rest := .nil }
      else if rr.val == targetRole then { ok := 1, val := ra.val, rest := ra.rest }
      else aggrFindRoleAddr ra.rest targetRole rem
termination_by structural rem => rem

/-- Lookup `Role.eq` (`role = 8`) in a role-binding section preimage (`Aggregation::aggr_binding_eq_addr`). -/
@[circuit_noinline]
def aggrBindingEqAddr (binding : DigestBytes) (bindingBytes : ByteList) : ParseDigest :=
  let bad : ParseDigest := { ok := 0, val := dummyDigestBytes, rest := .nil }
  if digest32WordsEq (packDigest (blake3HashBytes bindingBytes)) (packAddress binding) == 0 then bad else
  let r0 := readU8 bindingBytes
  if r0.ok == 0 || r0.val != 232 then bad else
  let r1 := readU8 r0.rest
  if r1.ok == 0 || r1.val != 3 then bad else
  let rVer := readU8 r1.rest
  if rVer.ok == 0 then bad else
  let rCnt := readU8 rVer.rest
  if rCnt.ok == 0 then bad else
  aggrFindRoleAddr rCnt.rest 8 rCnt.val

/-- Verify that a `Claim.check` constant record at `constAddr` is a safe, closed `defn`/`thm`
whose type is `@Eq.{u} leafTyp leafLhs leafRhs` with `refs[0..3] = [binding[Role.eq], leafTyp, leafLhs, leafRhs]`
(`Aggregation::aggr_verify_eq_check_record`). -/
@[circuit_noinline]
def aggrVerifyEqCheckRecord (constAddr binding leafLhs leafRhs leafTyp : DigestBytes)
    (bindingBytes recBytes : ByteList) : Nat :=
  let rEq := aggrBindingEqAddr binding bindingBytes
  if rEq.ok == 0 then 0 else
  if digest32WordsEq (packDigest (blake3HashBytes recBytes)) (packAddress constAddr) == 0 then 0 else
  let rCtag := readU8 recBytes
  if rCtag.ok == 0 || rCtag.val != 208 then 0 else
  let rFlags := readU8 rCtag.rest
  if rFlags.ok == 0 then 0 else
  let safety := rFlags.val % 4
  let kind := (rFlags.val / 4) % 4
  if safety != 1 || (kind != 0 && kind != 2) then 0 else
  let rLvls := aggrReadTagN0 rFlags.rest
  if rLvls.ok == 0 || rLvls.val != 0 then 0 else
  -- Type must be `App(3, Ref(0, [u]), Ref(1, []), Ref(2, []), Ref(3, []))`
  let t0 := readU8 rLvls.rest
  let t1 := readU8 t0.rest
  let t2 := readU8 t1.rest
  if t0.ok * t1.ok * t2.ok == 0 || t0.val != 115 || t1.val != 33 || t2.val != 0 then 0 else
  let ru := aggrReadTagN0 t2.rest
  if ru.ok == 0 then 0 else
  let t3 := readU8 ru.rest
  let t4 := readU8 t3.rest
  let t5 := readU8 t4.rest
  let t6 := readU8 t5.rest
  let t7 := readU8 t6.rest
  let t8 := readU8 t7.rest
  if t3.ok * t4.ok * t5.ok * t6.ok * t7.ok * t8.ok == 0 ||
     t3.val != 32 || t4.val != 1 || t5.val != 32 || t6.val != 2 || t7.val != 32 || t8.val != 3 then 0 else
  let fuel := byteListLen t8.rest + 1
  let rVal := aggrSkipExprsFuel fuel 1 t8.rest
  if rVal.ok == 0 then 0 else
  let rNshare := aggrReadTagN0 rVal.rest
  if rNshare.ok == 0 then 0 else
  let rSh := aggrSkipExprsFuel (byteListLen rNshare.rest + 1) rNshare.val rNshare.rest
  if rSh.ok == 0 then 0 else
  let rNrefs := aggrReadTagN0 rSh.rest
  if rNrefs.ok == 0 || rNrefs.val ≤ 3 then 0 else
  let rr0 := readDigest rNrefs.rest
  let rr1 := readDigest rr0.rest
  let rr2 := readDigest rr1.rest
  let rr3 := readDigest rr2.rest
  if rr0.ok * rr1.ok * rr2.ok * rr3.ok == 0 then 0 else
  if digestBytesEq rr0.val rEq.val == 1 &&
     digestBytesEq rr1.val leafTyp == 1 &&
     digestBytesEq rr2.val leafLhs == 1 &&
     digestBytesEq rr3.val leafRhs == 1 then 1 else 0

/-! ## Section 4: Inner Multi-STARK Child Proof Verification (`CompressWrapPure` Bridge) -/

/-- Extract the unique claim from a length-1 `U64ListList` (`Aggregation::aggr_only_claim`). -/
@[circuit_inline]
def aggrOnlyClaim (claims : U64ListList) : ParseOnlyClaimOut :=
  match claims with
  | .cons c .nil => { ok := 1, claim := c }
  | _ => { ok := 0, claim := .nil }

/-- Total `U64List` index lookup (`Lists::lookup`). -/
@[circuit_noinline]
def u64ListLookup (xs : U64List) : Nat → U64Bytes
  | 0 => match xs with | .nil => u64Zero | .cons x _ => x
  | idx + 1 => match xs with | .nil => u64Zero | .cons _ rest => u64ListLookup rest idx
termination_by structural idx => idx

/-- Decode claim word `index` as a Goldilocks field element (`Aggregation::aggr_claim_field`). -/
@[circuit_inline]
def aggrClaimField (claim : U64List) (index : Nat) : Nat :=
  glValBytes (u64ListLookup claim index)

/-- Extract an 8-word digest slice `claim[start .. start + 7]` (`Aggregation::aggr_claim_digest`). -/
@[circuit_inline]
def aggrClaimDigest (claim : U64List) (start : Nat) : Digest32Words :=
  { w0 := aggrClaimField claim start
    w1 := aggrClaimField claim (start + 1)
    w2 := aggrClaimField claim (start + 2)
    w3 := aggrClaimField claim (start + 3)
    w4 := aggrClaimField claim (start + 4)
    w5 := aggrClaimField claim (start + 5)
    w6 := aggrClaimField claim (start + 6)
    w7 := aggrClaimField claim (start + 7) }

/-- Verify a child Multi-STARK batch proof via `CompressWrapPure.verifyRootBytesWithFloor`!
Returns `ok = 1` iff the child's `(vkBytes, claimsBytes, proofBytes)` passes full Multi-STARK
batch verification with canonical wire decoding, security floor (when `enforceFloor ≠ 0`),
and exact claims equality. -/
@[circuit_noinline]
def verifyChildBatchWithFloor (enforceFloor : Nat) (w : ChildProofWitness) : ParseU64ListList :=
  let stmt := computeStatementDigest w.vkBytes w.claimsBytes
  let ok := verifyRootBytesWithFloor enforceFloor 0 0 0 0 0 0 0 0
    stmt.w0 stmt.w1 stmt.w2 stmt.w3 stmt.w4 stmt.w5 stmt.w6 stmt.w7
    w.vkBytes w.claimsBytes w.proofBytes
  if ok == 0 then { ok := 0, val := .nil, rest := .nil }
  else
    let pClaims := readClaims w.claimsBytes
    { ok := pClaims.ok, val := pClaims.val, rest := .nil }

/-- Verify a child IxVM (`kind = 0`) or recursive `ix_aggr` (`kind = 1`) proof against the pinned
allowed-identity parameters and extract its claim digest (`Aggregation::aggr_child_check_env_digest`). -/
@[circuit_noinline]
def verifyChildDigestWithFloor (enforceFloor kind : Nat) (ap : AllowedParams)
    (allowedDigest : Digest32Words) (w : ChildProofWitness) : VerifyChildDigestOut :=
  let bad : VerifyChildDigestOut := { ok := 0, digest := zeroDigest32Words }
  let vkDig := packDigest (blake3HashBytes w.vkBytes)
  let expectedVk := if kind == 0 then ap.ixvmVkDigest else ap.selfVkDigest
  if digest32WordsEq vkDig expectedVk == 0 then bad
  else
    let vc := verifyChildBatchWithFloor enforceFloor w
    if vc.ok == 0 then bad
    else
      let oc := aggrOnlyClaim vc.val
      if oc.ok == 0 then bad
      else if aggrClaimField oc.claim 0 != 1 then bad
      else if kind == 0 then
        if u64ListLen oc.claim != 10 then bad
        else if aggrClaimField oc.claim 1 != ap.verifyIdx then bad
        else { ok := 1, digest := aggrClaimDigest oc.claim 2 }
      else
        if u64ListLen oc.claim != 18 then bad
        else if aggrClaimField oc.claim 1 != ap.aggrIdx then bad
        else if digest32WordsEq (aggrClaimDigest oc.claim 2) allowedDigest == 0 then bad
        else { ok := 1, digest := aggrClaimDigest oc.claim 10 }

/-- Verify that `preimageBytes` hashes to `expectedDigest` (`Aggregation::aggr_load_preimage`). -/
@[circuit_inline]
def checkPreimageDigest (expectedDigest : Digest32Words) (preimageBytes : ByteList) : Nat :=
  digest32WordsEq (packDigest (blake3HashBytes preimageBytes)) expectedDigest

/-! ## Section 5: All 19 Aggregation Shapes (`0..18`), `verifyAggregateStep`, & `verifyAggregateRoot` -/

/-- Drop `n` headers from a `ShardHeaderList` (`Lists::drop`). -/
@[circuit_noinline]
def shardHeaderListDrop (n : Nat) (hs : ShardHeaderList) : ShardHeaderList :=
  match n with
  | 0 => hs
  | n' + 1 =>
    match hs with
    | .nil => .nil
    | .cons _ rest => shardHeaderListDrop n' rest
termination_by structural n

/-- Parse a Shape `10`/`12` batch preamble `(headers, messages)` and check it hashes to `d`
(`Aggregation::aggr_load_preamble`). -/
@[circuit_noinline]
def aggrCheckPreamble (d : DigestBytes) (preambleBytes : ByteList) : ParsePreambleOut :=
  let bad : ParsePreambleOut := { ok := 0, headers := .nil, messages := .nil }
  if digestBytesEq (bytesToAddr preambleBytes) d == 0 then bad else
  let rh := readShardHeaderVec preambleBytes
  if rh.ok == 0 then bad else
  let rm := readBatchMessageVec rh.rest
  if rm.ok == 0 then bad else
  match rm.rest with
  | .cons _ _ => bad
  | .nil => { ok := 1, headers := rh.val, messages := rm.val }

/-- Verify `n` consecutive shard proofs `[shard .. shard + n - 1]` and accumulate their `ExtGl`
LogUp residuals (`Aggregation::aggr_verify_range`). -/
@[circuit_noinline]
def aggrVerifyRangeWithFloor (enforceFloor : Nat) (sys : SysKey)
    (headers : ShardHeaderList) (proofs : ShardProofList) (shard : Nat) :
    Nat → ByteList → ExtGl → ExtGl → ExtGl → VerifyRangeOut
  | 0, _, _, _, acc =>
    match proofs with
    | .nil => { ok := 1, residual := acc }
    | .cons _ _ => { ok := 0, residual := extZero }
  | n + 1, input, lch, fch, acc =>
    match headers, proofs with
    | .cons h hrest, .cons p prest =>
      let r := verifyShardWithFloor enforceFloor sys h shard p input lch fch
      if r.ok == 0 then { ok := 0, residual := extZero }
      else aggrVerifyRangeWithFloor enforceFloor sys hrest prest (shard + 1) n input lch fch
        (extAdd acc r.lastAcc)
    | _, _ => { ok := 0, residual := extZero }
termination_by structural n => n

/-- Explicit pure advice bundle for one `verifyAggregateStep` invocation across all 19 shapes `0..18`. -/
structure AggrStepWitness where
  /-- Exact 80-byte allowed-identity blob. -/
  allowedBytes : ByteList
  /-- Shape selector byte (`0..18`). -/
  shape : Nat
  /-- Auxiliary selector byte 0 (Shape 17 bridge cert kind, or Shape 18 child 0 kind). -/
  auxKind0 : Nat
  /-- Auxiliary selector byte 1 (Shape 18 child 1 kind). -/
  auxKind1 : Nat
  /-- Primary child proof (slot 0: wrap/pair-left/range-root-child/discharge-child/dynamic-link-ext/eval-child0). -/
  child0 : ChildProofWitness
  /-- Secondary child proof (slot 1: pair-right/binding-child/bridge-cert/eval-discharger-child1). -/
  child1 : ChildProofWitness
  /-- Output claim/statement preimage bytes (channel 2 key 2). -/
  outputBytes : ByteList
  /-- Child 0 claim preimage bytes (channel 4). -/
  child0Preimage : ByteList
  /-- Child 1 claim preimage bytes (channel 4). -/
  child1Preimage : ByteList
  /-- Extra preimage 0 (Shape 15 left binding section, or Shape 18 removed `EvalAssumption` leaf). -/
  extraPreimage0 : ByteList
  /-- Extra preimage 1 (Shape 15 right binding section, or Shape 18 Mode 2 binding section for `Role.eq`). -/
  extraPreimage1 : ByteList
  /-- Extra preimage 2 (Shape 18 Mode 2 `@Eq` constant record bytes). -/
  extraPreimage2 : ByteList
  /-- Tree bytes for left/child0 subjects (or Shape 16 left catalog tree, or Shape 18 `c0_eval_root`). -/
  leftSubjTreeBytes : ByteList
  /-- Tree bytes for right/child1 subjects (or Shape 16 right catalog tree, or Shape 18 `out_eval_opt`). -/
  rightSubjTreeBytes : ByteList
  /-- Tree bytes for output subjects (or Shape 16 output catalog tree). -/
  outSubjTreeBytes : ByteList
  /-- Tree bytes for left assumptions (or Shape 18 `prev_linked` tree). -/
  leftAsmTreeBytes : ByteList
  /-- Tree bytes for right assumptions (or Shape 18 `out_linked` tree). -/
  rightAsmTreeBytes : ByteList
  /-- Tree bytes for output assumptions. -/
  outAsmTreeBytes : ByteList
  /-- Tree bytes for user-axiom set merge (left, right, output). -/
  leftAxTreeBytes : ByteList
  rightAxTreeBytes : ByteList
  outAxTreeBytes : ByteList
  /-- Structural discharge choice lookup table (Shapes `6–9` & `15`). -/
  structuralPaths : PathTable
  /-- Range VK bytes (`ixvmVkBytes` for Shapes `10` & `12`). -/
  rangeVkBytes : ByteList
  /-- Range preamble bytes (Shapes `10` & `12`). -/
  rangePreambleBytes : ByteList
  /-- Range shard proofs bytes (Shape `10`: `count (u64 LE)` followed by `count` `ShardProof`s). -/
  rangeShardProofsBytes : ByteList
  deriving BEq, DecidableEq, Repr

/-- Default empty `AggrStepWitness` for building targeted test witnesses cleanly. -/
def emptyStepWitness : AggrStepWitness :=
  { allowedBytes := .nil, shape := 0, auxKind0 := 0, auxKind1 := 0
    child0 := emptyChildProofWitness, child1 := emptyChildProofWitness
    outputBytes := .nil, child0Preimage := .nil, child1Preimage := .nil
    extraPreimage0 := .nil, extraPreimage1 := .nil, extraPreimage2 := .nil
    leftSubjTreeBytes := .nil, rightSubjTreeBytes := .nil, outSubjTreeBytes := .nil
    leftAsmTreeBytes := .nil, rightAsmTreeBytes := .nil, outAsmTreeBytes := .nil
    leftAxTreeBytes := .nil, rightAxTreeBytes := .nil, outAxTreeBytes := .nil
    structuralPaths := .nil, rangeVkBytes := .nil, rangePreambleBytes := .nil
    rangeShardProofsBytes := .nil }

/-! ### Individual Shape Verifiers (`0..18`) -/

/-- Shapes `0–1` (`Aggregation::aggr_wrap`). -/
@[circuit_noinline]
def verifyShapeWrap (enforceFloor kind : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let c := verifyChildDigestWithFloor enforceFloor kind ap allowedDigest w.child0
  if c.ok == 0 then 0 else digest32WordsEq c.digest outClaimDigest

/-- Shapes `2–5` (`Aggregation::aggr_pair`): flat canonical pair fold with cross-discharge & axiom merge. -/
@[circuit_noinline]
def verifyShapePairFlat (enforceFloor leftKind rightKind : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let cL := verifyChildDigestWithFloor enforceFloor leftKind ap allowedDigest w.child0
  if cL.ok == 0 then 0 else
  let cR := verifyChildDigestWithFloor enforceFloor rightKind ap allowedDigest w.child1
  if cR.ok == 0 then 0 else
  if checkPreimageDigest cL.digest w.child0Preimage == 0 then 0 else
  if checkPreimageDigest cR.digest w.child1Preimage == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pL := aggrParseCheckEnv w.child0Preimage
  let pR := aggrParseCheckEnv w.child1Preimage
  let pO := aggrParseCheckEnv w.outputBytes
  if pL.ok * pR.ok * pO.ok == 0 then 0 else
  if aggrAssertSameContextBase pL.ctx pR.ctx == 0 then 0 else
  if aggrAssertSameContextBase pL.ctx pO.ctx == 0 then 0 else
  if aggrAssertAxiomsMerge pL.ctx.axioms pR.ctx.axioms pO.ctx.axioms
      w.leftAxTreeBytes w.rightAxTreeBytes w.outAxTreeBytes == 0 then 0 else
  let tLS := aggrCheckCanonicalTree pL.root w.leftSubjTreeBytes
  let tRS := aggrCheckCanonicalTree pR.root w.rightSubjTreeBytes
  let tLA := aggrCheckOptionalTree pL.assumptions w.leftAsmTreeBytes
  let tRA := aggrCheckOptionalTree pR.assumptions w.rightAsmTreeBytes
  let tOS := aggrCheckCanonicalTree pO.root w.outSubjTreeBytes
  let tOA := aggrCheckOptionalTree pO.assumptions w.outAsmTreeBytes
  if tLS.ok * tRS.ok * tLA.ok * tRA.ok * tOS.ok * tOA.ok == 0 then 0 else
  if aggrAssertDisjoint tLS.val tLA.val == 0 then 0 else
  if aggrAssertDisjoint tRS.val tRA.val == 0 then 0 else
  if aggrAssertDisjointUnion tLS.val tRS.val tOS.val == 0 then 0 else
  aggrAssertDifference tLA.val tRA.val tOS.val tOA.val

/-- Shapes `6–9` (`Aggregation::aggr_pair_structural`): structural Merkle pair fold & axiom merge. -/
@[circuit_noinline]
def verifyShapePairStructural (enforceFloor leftKind rightKind : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let cL := verifyChildDigestWithFloor enforceFloor leftKind ap allowedDigest w.child0
  if cL.ok == 0 then 0 else
  let cR := verifyChildDigestWithFloor enforceFloor rightKind ap allowedDigest w.child1
  if cR.ok == 0 then 0 else
  if checkPreimageDigest cL.digest w.child0Preimage == 0 then 0 else
  if checkPreimageDigest cR.digest w.child1Preimage == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pL := aggrParseCheckEnv w.child0Preimage
  let pR := aggrParseCheckEnv w.child1Preimage
  let pO := aggrParseCheckEnv w.outputBytes
  if pL.ok * pR.ok * pO.ok == 0 then 0 else
  if aggrAssertSameContextBase pL.ctx pR.ctx == 0 then 0 else
  if aggrAssertSameContextBase pL.ctx pO.ctx == 0 then 0 else
  if aggrAssertAxiomsMerge pL.ctx.axioms pR.ctx.axioms pO.ctx.axioms
      w.leftAxTreeBytes w.rightAxTreeBytes w.outAxTreeBytes == 0 then 0 else
  if digestBytesEq pL.root pR.root == 1 then 0 else
  if digestBytesEq pO.root (aggrNodeHash pL.root pR.root) == 0 then 0 else
  let tLA := aggrCheckOptionalTree pL.assumptions w.leftAsmTreeBytes
  let tRA := aggrCheckOptionalTree pR.assumptions w.rightAsmTreeBytes
  let tOA := aggrCheckOptionalTree pO.assumptions w.outAsmTreeBytes
  if tLA.ok * tRA.ok * tOA.ok == 0 then 0 else
  aggrAssertStructuralDifference tLA.val tRA.val pL.root pR.root tOA.val w.structuralPaths

/-- Shape `10` (`Aggregation::aggr_range_leaf`): verifies shards `[lo, hi)` directly under `ixvmVkDigest`. -/
@[circuit_noinline]
def verifyShapeRangeLeaf (enforceFloor : Nat) (ap : AllowedParams)
    (outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  if digest32WordsEq (packDigest (blake3HashBytes w.rangeVkBytes)) ap.ixvmVkDigest == 0 then 0 else
  let pSys := readSystem w.rangeVkBytes
  if pSys.ok == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pRng := aggrParseRange w.outputBytes
  if pRng.ok == 0 then 0 else
  let pPre := aggrCheckPreamble pRng.batchDigest w.rangePreambleBytes
  if pPre.ok == 0 then 0 else
  let bfs := batchFiatShamir pSys.val.transcriptLimbs (optCommitCap pSys.val.prepCommit)
    pPre.headers pPre.messages
  if bfs.ok == 0 then 0 else
  if u64BytesLe pRng.lo pRng.hi == 0 then 0 else
  let lo := glValBytes pRng.lo
  let hi := glValBytes pRng.hi
  let n := hi - lo
  let rCnt := readCount w.rangeShardProofsBytes
  if rCnt.ok == 0 || rCnt.val != n then 0 else
  let rPrfs := readShardProofVecN rCnt.rest n
  if rPrfs.ok == 0 then 0 else
  match rPrfs.rest with
  | .cons _ _ => 0
  | .nil =>
    let vr := aggrVerifyRangeWithFloor enforceFloor pSys.val
      (shardHeaderListDrop lo pPre.headers) rPrfs.val lo n bfs.input bfs.lch bfs.fch extZero
    if vr.ok == 0 then 0 else extEq vr.residual pRng.residual

/-- Shape `11` (`Aggregation::aggr_range_join`): adds residuals of adjacent ranges `[lo, mid)` and `[mid, hi)`. -/
@[circuit_noinline]
def verifyShapeRangeJoin (enforceFloor : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let cL := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child0
  if cL.ok == 0 then 0 else
  let cR := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child1
  if cR.ok == 0 then 0 else
  if checkPreimageDigest cL.digest w.child0Preimage == 0 then 0 else
  if checkPreimageDigest cR.digest w.child1Preimage == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pL := aggrParseRange w.child0Preimage
  let pR := aggrParseRange w.child1Preimage
  let pO := aggrParseRange w.outputBytes
  if pL.ok * pR.ok * pO.ok == 0 then 0 else
  if digestBytesEq pL.batchDigest pR.batchDigest == 0 then 0 else
  if digestBytesEq pO.batchDigest pL.batchDigest == 0 then 0 else
  if glValBytes pL.hi != glValBytes pR.lo then 0 else
  if glValBytes pO.lo != glValBytes pL.lo then 0 else
  if glValBytes pO.hi != glValBytes pR.hi then 0 else
  extEq (extAdd pL.residual pR.residual) pO.residual

/-- Shape `12` (`Aggregation::aggr_range_root`): closes `[0, k)` with full batch bounds, MEMSEG closure,
LogUp vanishing, and 10-word `verify_claim` extraction. -/
@[circuit_noinline]
def verifyShapeRangeRoot (enforceFloor : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let c0 := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child0
  if c0.ok == 0 then 0 else
  if checkPreimageDigest c0.digest w.child0Preimage == 0 then 0 else
  let pRng := aggrParseRange w.child0Preimage
  if pRng.ok == 0 then 0 else
  if digest32WordsEq (packDigest (blake3HashBytes w.rangeVkBytes)) ap.ixvmVkDigest == 0 then 0 else
  let pSys := readSystem w.rangeVkBytes
  if pSys.ok == 0 then 0 else
  let pPre := aggrCheckPreamble pRng.batchDigest w.rangePreambleBytes
  if pPre.ok == 0 then 0 else
  let k := shardHeaderListLen pPre.headers
  if k == 0 || k > 65536 then 0 else
  if lookupsCountOk pSys.val.circuits == 0 then 0 else
  if batchRowsOk (circuitRowWeights pSys.val.circuits) pPre.headers 0 == 0 then 0 else
  if glValBytes pRng.lo != 0 || glValBytes pRng.hi != k then 0 else
  if assertClosurePairs pPre.messages u64Zero u64Zero 0 == 0 then 0 else
  let romWidths := systemRomWidths pSys.val.circuits
  let cw := assertClosureWidthsLoop pPre.messages romWidths 0
  if cw.fst == 0 || cw.snd > k * natListLen romWidths then 0 else
  let bfs := batchFiatShamir pSys.val.transcriptLimbs (optCommitCap pSys.val.prepCommit)
    pPre.headers pPre.messages
  if bfs.ok == 0 then 0 else
  let total := messagesAcc pRng.residual pPre.messages bfs.lch bfs.fch
  if total.ok == 0 || extIsZero total.lastAcc == 0 then 0 else
  let oc := aggrOnlyClaim (batchClaims pPre.headers)
  if oc.ok == 0 then 0 else
  if u64ListLen oc.claim != 10 then 0 else
  if aggrClaimField oc.claim 0 != 1 then 0 else
  if aggrClaimField oc.claim 1 != ap.verifyIdx then 0 else
  digest32WordsEq (aggrClaimDigest oc.claim 2) outClaimDigest

/-- Shapes `13–14` (`Aggregation::aggr_discharge_binding`): discharges assumed binding (`validator 4 → 3`). -/
@[circuit_noinline]
def verifyShapeDischargeBinding (enforceFloor kind : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let c0 := verifyChildDigestWithFloor enforceFloor kind ap allowedDigest w.child0
  if c0.ok == 0 then 0 else
  let cB := verifyChildDigestWithFloor enforceFloor 0 ap allowedDigest w.child1
  if cB.ok == 0 then 0 else
  if checkPreimageDigest c0.digest w.child0Preimage == 0 then 0 else
  if checkPreimageDigest cB.digest w.child1Preimage == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pC := aggrParseCheckEnv w.child0Preimage
  if pC.ok == 0 || pC.ctx.validator != 4 then 0 else
  let pB := aggrParseBinding w.child1Preimage
  if pB.ok == 0 then 0 else
  if digestBytesEq pC.ctx.spec pB.spec == 0 || digestBytesEq pC.ctx.binding pB.binding == 0 then 0 else
  let pO := aggrParseCheckEnv w.outputBytes
  if pO.ok == 0 then 0 else
  let expectedCtx : CheckEnvCtx := { pC.ctx with validator := 3 }
  if aggrAssertSameContext expectedCtx pO.ctx == 0 then 0 else
  if digestBytesEq pC.root pO.root == 0 then 0 else
  optAddrEq pC.assumptions pO.assumptions

/-- Shape `15` (`Aggregation::aggr_cross_binding`): cross-binding structural join under 13-role
literal class `k` (`validator ∈ {3, 5} → 5`) with axiom merge. -/
@[circuit_noinline]
def verifyShapeCrossBinding (enforceFloor : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let cL := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child0
  if cL.ok == 0 then 0 else
  let cR := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child1
  if cR.ok == 0 then 0 else
  if checkPreimageDigest cL.digest w.child0Preimage == 0 then 0 else
  if checkPreimageDigest cR.digest w.child1Preimage == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pL := aggrParseCheckEnv w.child0Preimage
  let pR := aggrParseCheckEnv w.child1Preimage
  let pO := aggrParseCheckEnv w.outputBytes
  if pL.ok * pR.ok * pO.ok == 0 then 0 else
  let clsL := aggrContextClass pL.ctx w.extraPreimage0
  let clsR := aggrContextClass pR.ctx w.extraPreimage1
  if clsL.ok * clsR.ok == 0 then 0 else
  if digestBytesEq clsL.cls clsR.cls == 0 then 0 else
  let expL : CheckEnvCtx := { spec := pL.ctx.spec, binding := clsL.cls, axioms := pL.ctx.axioms, validator := 5 }
  let expR : CheckEnvCtx := { spec := pR.ctx.spec, binding := clsR.cls, axioms := pR.ctx.axioms, validator := 5 }
  if aggrAssertSameContextBase expL pO.ctx == 0 then 0 else
  if aggrAssertSameContextBase expR pO.ctx == 0 then 0 else
  if aggrAssertAxiomsMerge pL.ctx.axioms pR.ctx.axioms pO.ctx.axioms
      w.leftAxTreeBytes w.rightAxTreeBytes w.outAxTreeBytes == 0 then 0 else
  if digestBytesEq pL.root pR.root == 1 then 0 else
  if digestBytesEq pO.root (aggrNodeHash pL.root pR.root) == 0 then 0 else
  let tLA := aggrCheckOptionalTree pL.assumptions w.leftAsmTreeBytes
  let tRA := aggrCheckOptionalTree pR.assumptions w.rightAsmTreeBytes
  let tOA := aggrCheckOptionalTree pO.assumptions w.outAsmTreeBytes
  if tLA.ok * tRA.ok * tOA.ok == 0 then 0 else
  aggrAssertStructuralDifference tLA.val tRA.val pL.root pR.root tOA.val w.structuralPaths

/-- Helper for Shape `16`: extract sorted catalog member list from an unconditional `CheckEnv`
(`validator ∈ {3, 5}`) or an existing `Catalog` (`Aggregation::aggr_catalog_part`). -/
@[circuit_noinline]
def aggrCatalogPart (expectedDigest : Digest32Words) (preimageBytes treeBytes : ByteList) :
    ParseDigestList :=
  let bad : ParseDigestList := { ok := 0, val := .nil, rest := .nil }
  if checkPreimageDigest expectedDigest preimageBytes == 0 then bad else
  let rTag := readU8 preimageBytes
  if rTag.ok == 0 then bad else
  if rTag.val == 229 then
    let pC := aggrParseCheckEnv preimageBytes
    if pC.ok == 0 then bad else
    if pC.ctx.validator != 3 && pC.ctx.validator != 5 then bad else
    if optAddrEq pC.assumptions .none == 0 then bad else
    { ok := 1, val := .cons (bytesToAddr preimageBytes) .nil, rest := .nil }
  else
    let pCat := aggrParseCatalog preimageBytes
    if pCat.ok == 0 then bad else
    aggrCheckCanonicalTree pCat.members treeBytes

/-- Shape `16` (`Aggregation::aggr_catalog_join`): sorted union of unconditional `CheckEnv`/`Catalog` children. -/
@[circuit_noinline]
def verifyShapeCatalogJoin (enforceFloor : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let cL := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child0
  if cL.ok == 0 then 0 else
  let cR := verifyChildDigestWithFloor enforceFloor 1 ap allowedDigest w.child1
  if cR.ok == 0 then 0 else
  let left := aggrCatalogPart cL.digest w.child0Preimage w.leftSubjTreeBytes
  let right := aggrCatalogPart cR.digest w.child1Preimage w.rightSubjTreeBytes
  if left.ok * right.ok == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pOut := aggrParseCatalog w.outputBytes
  if pOut.ok == 0 then 0 else
  let outTree := aggrCheckCanonicalTree pOut.members w.outSubjTreeBytes
  if outTree.ok == 0 then 0 else
  aggrAssertUnion left.val right.val outTree.val

/-- Helper for Shape `17`: verify an unconditional validator-`3` `Check`/`CheckEnv` bridge certificate
binding `(expectedSpec, expectedBinding)` to `certConst` (`Aggregation::aggr_verify_bridge_cert`). -/
@[circuit_noinline]
def aggrVerifyBridgeCert (enforceFloor : Nat) (expectedSpec expectedBinding certConst : DigestBytes)
    (ap : AllowedParams) (allowedDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  if w.auxKind0 != 0 && w.auxKind0 != 1 then 0 else
  let cCert := verifyChildDigestWithFloor enforceFloor w.auxKind0 ap allowedDigest w.child1
  if cCert.ok == 0 then 0 else
  if checkPreimageDigest cCert.digest w.child1Preimage == 0 then 0 else
  let certClaimAddr := bytesToAddr w.child1Preimage
  let rTag := readU8 w.child1Preimage
  if rTag.ok == 0 then 0 else
  if rTag.val == 228 then
    let pC := aggrParseCheck w.child1Preimage
    if pC.ok == 0 then 0 else
    if pC.ctx.validator != 3 then 0 else
    if digestBytesEq pC.ctx.spec expectedSpec == 0 then 0 else
    if digestBytesEq pC.ctx.binding expectedBinding == 0 then 0 else
    if optAddrEq pC.ctx.axioms .none == 0 then 0 else
    if optAddrEq pC.assumptions .none == 0 then 0 else
    if digestBytesEq certClaimAddr certConst == 1 || digestBytesEq pC.root certConst == 1 then 1 else 0
  else if rTag.val == 229 then
    let pC := aggrParseCheckEnv w.child1Preimage
    if pC.ok == 0 then 0 else
    if pC.ctx.validator != 3 then 0 else
    if digestBytesEq pC.ctx.spec expectedSpec == 0 then 0 else
    if digestBytesEq pC.ctx.binding expectedBinding == 0 then 0 else
    if optAddrEq pC.ctx.axioms .none == 0 then 0 else
    if optAddrEq pC.assumptions .none == 0 then 0 else
    digestBytesEq certClaimAddr certConst
  else 0

/-- Shape `17` (`Aggregation::aggr_dynamic_link`, `0xE8 0x0D`): verifies an external Multi-STARK
batch proof under the uniform security envelope, with optional unconditional bridge certificate. -/
@[circuit_noinline]
def verifyShapeDynamicLink (enforceFloor : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let extVkAddr := bytesToAddr w.child0.vkBytes
  let pSys := readSystem w.child0.vkBytes
  if pSys.ok == 0 then 0 else
  if enforceFloor != 0 && aggrAssertSecurityEnvelope pSys.val.params == 0 then 0 else
  let vc := verifyChildBatchWithFloor enforceFloor w.child0
  if vc.ok == 0 then 0 else
  let oc := aggrOnlyClaim vc.val
  if oc.ok == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let pDL := aggrParseDynamicLink w.outputBytes
  if pDL.ok == 0 then 0 else
  if digestBytesEq pDL.vkDigest extVkAddr == 0 then 0 else
  let expectedClaim : U64List :=
    .cons (u64BytesOfU32 1) (.cons pDL.entryIdx (u64ListAppend pDL.pubInputs pDL.pubOutputs))
  if assertSameLimbs oc.claim expectedClaim == 0 then 0 else
  match pDL.bridge with
  | .noBridge => 1
  | .someBridge bSpec bBind _ codec certConst =>
    if aggrAssertCodecArity codec pDL.pubInputs pDL.pubOutputs == 0 then 0 else
    aggrVerifyBridgeCert enforceFloor bSpec bBind certConst ap allowedDigest w

/-- Shape `18` (`Aggregation::aggr_discharge_eval`, `0xE8 0x0E`):
- Strictly disables Mode 1 (`tag = 227`, `Claim.eval`).
- Mode 2 (`tag = 228`, `@Eq` `Claim.check`): transitions `10 → 14` / `11 → 15` ONLY when
  `evalAssumptions` becomes empty and `linkedCircuits = none` (NEVER producing `3`/`4`/`5`).
- Mode 3a (`tag = 232`, Shape 17 `DynamicLinkStatement`): ALWAYS commits `LinkedCircuitEntry`
  (`0xE8 0x0F`) into `outLinkedOpt` under linked validators `12`/`13` (NEVER `3`/`4`/`5`/`14`/`15`). -/
@[circuit_noinline]
def verifyShapeDischargeEval (enforceFloor : Nat) (ap : AllowedParams)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  if (w.auxKind0 != 0 && w.auxKind0 != 1) || (w.auxKind1 != 0 && w.auxKind1 != 1) then 0 else
  let c0 := verifyChildDigestWithFloor enforceFloor w.auxKind0 ap allowedDigest w.child0
  if c0.ok == 0 then 0 else
  let c1 := verifyChildDigestWithFloor enforceFloor w.auxKind1 ap allowedDigest w.child1
  if c1.ok == 0 then 0 else
  if checkPreimageDigest c0.digest w.child0Preimage == 0 then 0 else
  if checkPreimageDigest c1.digest w.child1Preimage == 0 then 0 else
  if checkPreimageDigest outClaimDigest w.outputBytes == 0 then 0 else
  let p0 := aggrParseEvalAssumed w.child0Preimage
  if p0.ok == 0 then 0 else
  let pOut := aggrParseEvalDischargeOut w.outputBytes p0.tag p0.ctx.validator
  if pOut.ok == 0 then 0 else
  if digestBytesEq p0.ctx.spec pOut.ctx.spec == 0 then 0 else
  if digestBytesEq p0.ctx.binding pOut.ctx.binding == 0 then 0 else
  if digestBytesEq p0.target pOut.target == 0 then 0 else
  if optAddrEq p0.assumptions pOut.assumptions == 0 then 0 else
  let tEval0 := aggrCheckCanonicalTree p0.evalRoot w.leftSubjTreeBytes
  let tEvalOut := aggrCheckOptionalTree pOut.evalOpt w.rightSubjTreeBytes
  if tEval0.ok * tEvalOut.ok == 0 then 0 else
  let rem := aggrExtractRemovedLeaf tEval0.val tEvalOut.val
  if rem.ok == 0 then 0 else
  if checkPreimageDigest (packAddress rem.removed) w.extraPreimage0 == 0 then 0 else
  let pLeaf := aggrParseEvalAssumption w.extraPreimage0
  if pLeaf.ok == 0 then 0 else
  let rC1Tag := readU8 w.child1Preimage
  if rC1Tag.ok == 0 then 0 else
  if rC1Tag.val == 228 then
    -- Mode 2 (`@Eq` `Claim.check`)
    let pC1 := aggrParseCheck w.child1Preimage
    if pC1.ok == 0 then 0 else
    if pC1.ctx.validator != 3 then 0 else
    if digestBytesEq p0.ctx.spec pC1.ctx.spec == 0 then 0 else
    if digestBytesEq p0.ctx.binding pC1.ctx.binding == 0 then 0 else
    if optAddrEq pC1.assumptions .none == 0 then 0 else
    if aggrVerifyEqCheckRecord pC1.root p0.ctx.binding pLeaf.lhs pLeaf.rhs pLeaf.typ
        w.extraPreimage1 w.extraPreimage2 == 0 then 0 else
    if aggrAssertLinkedMerge p0.linked .none pOut.linkedOpt
        w.leftAsmTreeBytes w.rightAsmTreeBytes == 0 then 0 else
    aggrAssertAxiomsMerge p0.ctx.axioms pC1.ctx.axioms pOut.ctx.axioms
      w.leftAxTreeBytes w.rightAxTreeBytes w.outAxTreeBytes
  else if rC1Tag.val == 232 then
    -- Mode 3a (Shape 17 `DynamicLinkStatement`)
    if w.auxKind1 != 1 then 0 else
    let pDL := aggrParseDynamicLink w.child1Preimage
    if pDL.ok == 0 then 0 else
    match pLeaf.circuit, pDL.bridge with
    | .someCircuitRef leafVk leafEntry, .someBridge dlSpec dlBind tgtConst codec certConst =>
      if digestBytesEq pDL.vkDigest leafVk == 0 then 0 else
      if u64BytesEq pDL.entryIdx leafEntry == 0 then 0 else
      if digestBytesEq dlSpec p0.ctx.spec == 0 then 0 else
      if digestBytesEq dlBind p0.ctx.binding == 0 then 0 else
      if u64BytesEq codec (u64BytesOfU32 1) == 0 then 0 else
      if aggrAssertPackedAddrU64s pDL.pubInputs pLeaf.lhs == 0 then 0 else
      if aggrAssertPackedAddrU64s pDL.pubOutputs pLeaf.rhs == 0 then 0 else
      let entryAddr := aggrLinkedEntryAddr pDL.vkDigest pDL.entryIdx codec tgtConst certConst
        pLeaf.typ dlSpec dlBind
      if aggrAssertLinkedMerge p0.linked (.some entryAddr) pOut.linkedOpt
          w.leftAsmTreeBytes w.rightAsmTreeBytes == 0 then 0 else
      aggrAssertAxiomsMerge p0.ctx.axioms .none pOut.ctx.axioms
        w.leftAxTreeBytes w.rightAxTreeBytes w.outAxTreeBytes
    | _, _ => 0
  else 0

/-! ### Top-Level Aggregation Step Verifier (`MultiStark::ix_aggr`) -/

/-- Exact 19-shape pure aggregation step verifier with configurable security-floor toggle
(`enforceFloor = 1` for production; `enforceFloor = 0` strictly for tiny synthetic test harnesses). -/
@[circuit_noinline]
def verifyAggregateStepWithFloor (enforceFloor : Nat)
    (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  let pa := parseAllowedBlob allowedDigest w.allowedBytes
  if pa.ok == 0 then 0
  else
    let ap := pa.val
    if w.shape == 0 then verifyShapeWrap enforceFloor 0 ap allowedDigest outClaimDigest w
    else if w.shape == 1 then verifyShapeWrap enforceFloor 1 ap allowedDigest outClaimDigest w
    else if w.shape == 2 then verifyShapePairFlat enforceFloor 0 0 ap allowedDigest outClaimDigest w
    else if w.shape == 3 then verifyShapePairFlat enforceFloor 0 1 ap allowedDigest outClaimDigest w
    else if w.shape == 4 then verifyShapePairFlat enforceFloor 1 0 ap allowedDigest outClaimDigest w
    else if w.shape == 5 then verifyShapePairFlat enforceFloor 1 1 ap allowedDigest outClaimDigest w
    else if w.shape == 6 then verifyShapePairStructural enforceFloor 0 0 ap allowedDigest outClaimDigest w
    else if w.shape == 7 then verifyShapePairStructural enforceFloor 0 1 ap allowedDigest outClaimDigest w
    else if w.shape == 8 then verifyShapePairStructural enforceFloor 1 0 ap allowedDigest outClaimDigest w
    else if w.shape == 9 then verifyShapePairStructural enforceFloor 1 1 ap allowedDigest outClaimDigest w
    else if w.shape == 10 then verifyShapeRangeLeaf enforceFloor ap outClaimDigest w
    else if w.shape == 11 then verifyShapeRangeJoin enforceFloor ap allowedDigest outClaimDigest w
    else if w.shape == 12 then verifyShapeRangeRoot enforceFloor ap allowedDigest outClaimDigest w
    else if w.shape == 13 then verifyShapeDischargeBinding enforceFloor 0 ap allowedDigest outClaimDigest w
    else if w.shape == 14 then verifyShapeDischargeBinding enforceFloor 1 ap allowedDigest outClaimDigest w
    else if w.shape == 15 then verifyShapeCrossBinding enforceFloor ap allowedDigest outClaimDigest w
    else if w.shape == 16 then verifyShapeCatalogJoin enforceFloor ap allowedDigest outClaimDigest w
    else if w.shape == 17 then verifyShapeDynamicLink enforceFloor ap allowedDigest outClaimDigest w
    else if w.shape == 18 then verifyShapeDischargeEval enforceFloor ap allowedDigest outClaimDigest w
    else 0

/-- **Full Production Pure Aggregation Step Verifier (`MultiStark::ix_aggr`)**:
always enforces `enforceFloor = 1` (production Aiur security floor + Shape 17 envelope). -/
@[circuit_inline]
def verifyAggregateStep (allowedDigest outClaimDigest : Digest32Words) (w : AggrStepWitness) : Nat :=
  verifyAggregateStepWithFloor 1 allowedDigest outClaimDigest w

/-! ### Full Recursive Aggregation Tree Verifier (`verifyAggregateRoot`) -/

/-- Recursive monomorphic witness tree for a complete 19-shape aggregation derivation:
- `step0`: a step with 0 recursive `ix_aggr` children (e.g., `wrapIxvm`, `pair*(0,0)`, `rangeLeaf`,
  `dischargeBinding(0)`, `dynamicLink` without recursive bridge cert, `dischargeEval(0,0)`).
- `step1`: a step with 1 recursive `ix_aggr` child (`wrapAggr`, `pair*(0,1)`/`(1,0)`, `rangeRoot`,
  `dischargeBinding(1)`, `dynamicLink` with recursive bridge cert, `dischargeEval(0,1)`/`(1,0)`).
- `step2`: a step with 2 recursive `ix_aggr` children (`pair*(1,1)`, `rangeJoin`, `crossBinding`,
  `catalogJoin`, `dischargeEval(1,1)`). -/
inductive AggrTreeWitness where
  | step0 (step : AggrStepWitness)
  | step1 (step : AggrStepWitness) (sub : AggrTreeWitness)
  | step2 (step : AggrStepWitness) (sub0 sub1 : AggrTreeWitness)
  deriving BEq, DecidableEq, Repr

/-- Extract the root step witness of an `AggrTreeWitness`. -/
@[circuit_inline]
def AggrTreeWitness.rootStep : AggrTreeWitness → AggrStepWitness
  | .step0 s => s
  | .step1 s _ => s
  | .step2 s _ _ => s

/-- Extract the recursive child's inner claim digest (`words 10..17`) from a verified `ix_aggr`
child's canonical `claimsBytes`. -/
@[circuit_noinline]
def extractRecursiveChildDigest (claimsBytes : ByteList) : Digest32Words :=
  let pc := readClaims claimsBytes
  if pc.ok == 0 then zeroDigest32Words
  else
    let oc := aggrOnlyClaim pc.val
    if oc.ok == 0 then zeroDigest32Words
    else aggrClaimDigest oc.claim 10

/-- Whether slot 0 of `step` is a recursive (`kind = 1`) `ix_aggr` child. -/
@[circuit_inline]
def stepHasRecChild0 (w : AggrStepWitness) : Nat :=
  if w.shape == 1 || w.shape == 4 || w.shape == 5 ||
     w.shape == 8 || w.shape == 9 ||
     w.shape == 11 || w.shape == 12 || w.shape == 14 ||
     w.shape == 15 || w.shape == 16 then 1
  else if w.shape == 18 && w.auxKind0 == 1 then 1
  else 0

/-- Whether slot 1 of `step` is a recursive (`kind = 1`) `ix_aggr` child. -/
@[circuit_inline]
def stepHasRecChild1 (w : AggrStepWitness) : Nat :=
  if w.shape == 3 || w.shape == 5 || w.shape == 7 || w.shape == 9 ||
     w.shape == 11 || w.shape == 15 || w.shape == 16 then 1
  else if w.shape == 17 then
    let pDL := aggrParseDynamicLink w.outputBytes
    match pDL.bridge with
    | .someBridge _ _ _ _ _ => if w.auxKind0 == 1 then 1 else 0
    | .noBridge => 0
  else if w.shape == 18 && w.auxKind1 == 1 then 1
  else 0

/-- Full recursive aggregation tree verifier with configurable security-floor toggle:
verifies `verifyAggregateStepWithFloor` at the current node AND recursively verifies every
`kind = 1` (`ix_aggr`) child subtree against the EXACT same `allowedDigest` and the EXACT
inner claim digest extracted from the parent's verified child claim! -/
@[circuit_noinline]
def verifyAggregateRootWithFloor (enforceFloor : Nat)
    (allowedDigest outClaimDigest : Digest32Words) (t : AggrTreeWitness) : Nat :=
  match t with
  | .step0 s =>
    if stepHasRecChild0 s != 0 || stepHasRecChild1 s != 0 then 0
    else verifyAggregateStepWithFloor enforceFloor allowedDigest outClaimDigest s
  | .step1 s sub =>
    let r0 := stepHasRecChild0 s
    let r1 := stepHasRecChild1 s
    if r0 == 1 && r1 == 0 then
      if verifyAggregateStepWithFloor enforceFloor allowedDigest outClaimDigest s == 0 then 0
      else
        let d0 := extractRecursiveChildDigest s.child0.claimsBytes
        verifyAggregateRootWithFloor enforceFloor allowedDigest d0 sub
    else if r0 == 0 && r1 == 1 then
      if verifyAggregateStepWithFloor enforceFloor allowedDigest outClaimDigest s == 0 then 0
      else
        let d1 := extractRecursiveChildDigest s.child1.claimsBytes
        verifyAggregateRootWithFloor enforceFloor allowedDigest d1 sub
    else 0
  | .step2 s sub0 sub1 =>
    if stepHasRecChild0 s != 1 || stepHasRecChild1 s != 1 then 0
    else if verifyAggregateStepWithFloor enforceFloor allowedDigest outClaimDigest s == 0 then 0
    else
      let d0 := extractRecursiveChildDigest s.child0.claimsBytes
      let d1 := extractRecursiveChildDigest s.child1.claimsBytes
      if verifyAggregateRootWithFloor enforceFloor allowedDigest d0 sub0 == 0 then 0
      else verifyAggregateRootWithFloor enforceFloor allowedDigest d1 sub1
termination_by structural t

/-- **Full Production Pure Aggregation Root Verifier**:
verifies an entire recursive aggregation tree under production security floor (`enforceFloor = 1`),
pinning `allowedDigest` uniformly across every node and matching every recursive child claim digest. -/
@[circuit_inline]
def verifyAggregateRoot (allowedDigest outClaimDigest : Digest32Words) (t : AggrTreeWitness) : Nat :=
  verifyAggregateRootWithFloor 1 allowedDigest outClaimDigest t

/-! ## Section 6: Self-Contained Pure `#guard` Regression Suite -/

private def mkTestAddr (b0 : Nat) : DigestBytes :=
  { d0 := { b0 := b0 % 256, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
    d1 := u64Zero, d2 := u64Zero, d3 := u64Zero }

private def testAddrA : DigestBytes := mkTestAddr 1
private def testAddrB : DigestBytes := mkTestAddr 2
private def testAddrC : DigestBytes := mkTestAddr 3
private def testAddrD : DigestBytes := mkTestAddr 4

-- 1. Big-endian 32-byte address ordering & strict sorting
#guard aggrAddressOrder testAddrA testAddrB == 0
#guard aggrAddressOrder testAddrA testAddrA == 1
#guard aggrAddressOrder testAddrB testAddrA == 2
#guard aggrAssertStrictSorted (.cons testAddrA (.cons testAddrB (.cons testAddrC .nil))) == 1
#guard aggrAssertStrictSorted (.cons testAddrB (.cons testAddrA .nil)) == 0
#guard aggrAssertStrictSorted (.cons testAddrA (.cons testAddrA .nil)) == 0

-- 2. Canonical Merkle assumption tree (`0xE2`) verification & tamper rejection
private def testTreeABBytes : ByteList :=
  .cons 226 (.cons 2 (.cons 0 (digestBytesOnto testAddrA (.cons 0 (digestBytesOnto testAddrB .nil)))))
private def testTreeABRoot : DigestBytes :=
  aggrNodeHash (aggrLeafHash testAddrA) (aggrLeafHash testAddrB)

#guard (aggrCheckCanonicalTree testTreeABRoot testTreeABBytes).ok == 1
#guard (aggrCheckCanonicalTree (aggrLeafHash testAddrA) testTreeABBytes).ok == 0
#guard (aggrCheckCanonicalTree testTreeABRoot (byteListAppend testTreeABBytes (.cons 0 .nil))).ok == 0

-- 3. Set union, disjoint union, difference & structural Merkle-path discharge
private def listAB : DigestBytesList := .cons testAddrA (.cons testAddrB .nil)
private def listBC : DigestBytesList := .cons testAddrB (.cons testAddrC .nil)
private def listCD : DigestBytesList := .cons testAddrC (.cons testAddrD .nil)
private def listABC : DigestBytesList := .cons testAddrA (.cons testAddrB (.cons testAddrC .nil))
private def listABCD : DigestBytesList :=
  .cons testAddrA (.cons testAddrB (.cons testAddrC (.cons testAddrD .nil)))

#guard aggrAssertUnion listAB listBC listABC == 1
#guard aggrAssertUnion listAB listBC listAB == 0
#guard aggrAssertDisjointUnion listAB listCD listABCD == 1
#guard aggrAssertDisjointUnion listAB listBC listABC == 0
#guard aggrAssertDisjoint listAB listCD == 1
#guard aggrAssertDisjoint listAB listBC == 0
#guard aggrAssertDifference (.cons testAddrC .nil) (.cons testAddrA .nil) listABCD .nil == 1
#guard aggrAssertDifference (.cons testAddrC .nil) (.cons testAddrD .nil) listAB (.cons testAddrC (.cons testAddrD .nil)) == 1

-- Structural discharge: candidate C from left (source = 0) discharged by rightRoot = leaf(C)
private def rootA : DigestBytes := aggrLeafHash testAddrA
private def rootC : DigestBytes := aggrLeafHash testAddrC
private def validPathLeftToRight : ByteList :=
  .cons 1 (.cons 1 (.cons 0 (digestBytesOnto rootA .nil)))
#guard (aggrVerifyDischargeChoice testAddrC 0 rootA rootC validPathLeftToRight).ok == 1
#guard (aggrVerifyDischargeChoice testAddrC 0 rootA rootC validPathLeftToRight).val == 1
-- Shared assumption (source = 1) can NEVER be discharged!
#guard (aggrVerifyDischargeChoice testAddrC 1 rootA rootC validPathLeftToRight).ok == 0

-- 4. Allowed-blob binding (exact 80 bytes) & tamper rejection
private def testAllowedBytes : ByteList :=
  digestBytesOnto testAddrA
    (u64BytesOnto (u64BytesOfU32 7)
      (digestBytesOnto testAddrB
        (u64BytesOnto (u64BytesOfU32 9) .nil)))
private def testAllowedDigest : Digest32Words := packDigest (blake3HashBytes testAllowedBytes)

#guard (parseAllowedBlob testAllowedDigest testAllowedBytes).ok == 1
#guard (parseAllowedBlob testAllowedDigest testAllowedBytes).val.verifyIdx == 7
#guard (parseAllowedBlob testAllowedDigest testAllowedBytes).val.aggrIdx == 9
#guard (parseAllowedBlob { testAllowedDigest with w0 := testAllowedDigest.w0 + 1 } testAllowedBytes).ok == 0
#guard (parseAllowedBlob testAllowedDigest (byteListAppend testAllowedBytes (.cons 0 .nil))).ok == 0

-- 5. Shape 17 security envelope acceptance & deceptive high-blowup rejection
#guard aggrAssertSecurityEnvelope
  { logBlowup := 3, capHeight := 0, logFinalPolyLen := 0, maxLogArity := 1
    numQueries := 78, commitPowBits := 16, queryPowBits := 16 } == 1
#guard aggrAssertSecurityEnvelope
  { logBlowup := 4, capHeight := 0, logFinalPolyLen := 0, maxLogArity := 1
    numQueries := 55, commitPowBits := 0, queryPowBits := 0 } == 0  -- 220 conj, 50.2 UD rejected!
#guard aggrAssertSecurityEnvelope
  { logBlowup := 3, capHeight := 0, logFinalPolyLen := 0, maxLogArity := 2
    numQueries := 78, commitPowBits := 16, queryPowBits := 16 } == 0  -- maxLogArity ≠ 1 rejected!

-- 6. Shape 18 Mode 2 (`10 → 14`, `11 → 15`) & Mode 3a (`10/12 → 12`, `11/13 → 13`) validator isolation
private def mkEvalDischargeClaimBytes (tag val : Nat) (extra : ByteList) : ByteList :=
  .cons tag (.cons 4 (.cons val
    (digestBytesOnto testAddrA
      (digestBytesOnto testAddrB
        (.cons 0 (digestBytesOnto testAddrC (.cons 0 extra)))))))

-- Mode 2 full unlinked discharge: 10 → 14 and 11 → 15 ACCEPTED
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 14 .nil) 229 10).ok == 1
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 15 .nil) 229 11).ok == 1
-- Standard validators 3, 4, 5 REJECTED from ANY Shape 18 discharge!
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 3 .nil) 229 10).ok == 0
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 4 .nil) 229 11).ok == 0
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 5 .nil) 229 10).ok == 0
-- Linked claims (12/13) can NEVER transition to unlinked 14/15/3/4!
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 14 .nil) 229 12).ok == 0
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 15 .nil) 229 13).ok == 0
#guard (aggrParseEvalDischargeOut (mkEvalDischargeClaimBytes 229 3 .nil) 229 12).ok == 0
-- Mode 3a linked output (10 → 12, 12 → 12) ACCEPTED when linked root is present
#guard (aggrParseEvalDischargeOut
  (mkEvalDischargeClaimBytes 229 12 (.cons 0 (digestBytesOnto testAddrD .nil))) 229 10).ok == 1
#guard (aggrParseEvalDischargeOut
  (mkEvalDischargeClaimBytes 229 12 (.cons 0 (digestBytesOnto testAddrD .nil))) 229 12).ok == 1

-- 7. Shape 10/11/12 range statement canonical `< p_GL` enforcement
private def mkRangeStmtBytes (lo hi r0 : U64Bytes) : ByteList :=
  .cons 82 (digestBytesOnto testAddrA
    (u64BytesOnto lo (u64BytesOnto hi
      (u64BytesOnto r0 (u64BytesOnto u64Zero (u64BytesOnto u64Zero .nil))))))

#guard (aggrParseRange (mkRangeStmtBytes (u64BytesOfU32 0) (u64BytesOfU32 4) (u64BytesOfU32 7))).ok == 1
#guard (aggrParseRange (mkRangeStmtBytes (u64BytesOfNat glPrime) (u64BytesOfU32 4) u64Zero)).ok == 0

end AggregatePure
