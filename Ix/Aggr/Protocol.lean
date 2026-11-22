module
public import Ix.Aggr.Parameters
public import Ix.AssumptionTree
public import Ix.Claim
public import Ix.DynamicLink.Codec

/-! Aggregation identity, shape codes, and advice encoding. -/

public section
namespace Aggr

/-! ## Identity and public input -/

/-- The 80-byte identity blob of the verifying-key digests `ixvmDigest`
and `selfDigest`:

`ixvmDigest ‖ verify_claim index as u64-LE ‖ selfDigest ‖ ix_aggr index as
u64-LE`. -/
def allowedOfDigests (ixvmDigest : ByteArray) (verifyClaimIdx : Nat)
    (selfDigest : ByteArray) (aggrIdx : Nat) : ByteArray :=
  ⟨ixvmDigest.data ++ MultiStark.u64le verifyClaimIdx ++
    selfDigest.data ++ MultiStark.u64le aggrIdx⟩

/-- The digest-bound identity blob of the verifying keys themselves:
`allowedOfDigests (blake3 ixvm vk) … (blake3 self vk) …`. -/
def allowedBlob (ixvmVkBytes : ByteArray) (verifyClaimIdx : Nat)
    (selfVkBytes : ByteArray) (aggrIdx : Nat) : ByteArray :=
  allowedOfDigests (Address.blake3 ixvmVkBytes).hash verifyClaimIdx
    (Address.blake3 selfVkBytes).hash aggrIdx

/-- Public input of `ix_aggr`: the packed Blake3 digest of the identity blob
followed by the packed digest of the output `CheckEnv` claim bytes. -/
def pubInput (allowed outClaimBytes : ByteArray) : Array Aiur.G :=
  MultiStark.digestGs allowed ++ MultiStark.digestGs outClaimBytes

/-! ## Shapes -/

/-- Which system a child proof verifies against. -/
inductive ChildKind where
  | ixvm
  | aggr
  deriving BEq, Repr

def ChildKind.code : ChildKind → Nat
  | .ixvm => 0
  | .aggr => 1

/-- The advice byte selecting a wrap or flat pair: `0`/`1` wrap one IxVM /
`ix_aggr` child; `2`–`5` fold a flat pair, `2 + 2·left + right` with IxVM = 0
and `ix_aggr` = 1. -/
def shapeCode : (children : ChildKind × Option ChildKind) → Nat
  | (kind, none) => kind.code
  | (left, some right) => 2 + 2 * left.code + right.code

/-- Structural pair shapes `6`–`9`: `6 + 2·left + right`. Wraps have no
structural form. -/
def structuralShapeCode (left right : ChildKind) : Nat :=
  6 + 2 * left.code + right.code

/-! ## Range-sum recursion -/

@[expose] def rangeLeafShape : Nat := 10
@[expose] def rangeJoinShape : Nat := 11
@[expose] def rangeRootShape : Nat := 12

/-! ## Binding discharge -/

/-- The binding-discharge shape for a child of kind `kind`. -/
@[expose] def dischargeShapeCode (kind : ChildKind) : Nat := 13 + kind.code

/-- The cross-binding structural pair: two `ix_aggr` children whose role
bindings have one literal class, joined into a claim under that class. -/
@[expose] def crossBindingShapeCode : Nat := 15

/-- The catalog join: two `ix_aggr` children, each an unconditional `CheckEnv`
claim or a `Catalog` claim, joined into the `Catalog` of all their member
statements. -/
@[expose] def catalogShapeCode : Nat := 16

/-- Dynamic circuit linking (`aggr_dynamic_link`, Tier 1 Workstream 5A):
verifies an external Multi-STARK proof against an advice-supplied VK on IO
channel 1 key 2 under the uniform security envelope, optionally paired with an
unconditional IxVM/`ix_aggr` bridge theorem proof on slot 1, and emits a
canonical `DynamicLinkStatement` (`0xE8 0x0D`). -/
@[expose] def dynamicLinkShapeCode : Nat := 17

/-- Tier 2 eval-assumption discharge (`aggr_discharge_eval`, Workstream 5B):
discharges one `EvalAssumption` leaf (`0xE8 0x0E`) from an `EvalAssumedClaim`
(validator `10`/`11`) via a `Claim.eval`, `Claim.check`, or Shape 17
`DynamicLinkStatement` child, transitioning validator `10 → 3` (or `11 → 4`)
when the final eval assumption is discharged. -/
@[expose] def dischargeEvalShapeCode : Nat := 18

/-- The byte that opens every range statement; no `Ix.Claim` starts with it,
so a range statement never parses as a `CheckEnv` claim. -/
def rangeStatementTag : UInt8 := 0x52

/-- A range node's output statement:

`0x52 ‖ blake3(preamble)(32) ‖ lo(u64 LE) ‖ hi(u64 LE) ‖ residual(16)`. -/
def rangeStatement (preamble : ByteArray) (lo hi : Nat)
    (residual : ByteArray) : ByteArray :=
  ⟨#[rangeStatementTag] ++ (Address.blake3 preamble).hash.data ++
    MultiStark.u64le lo ++ MultiStark.u64le hi ++ residual.data⟩

/-! ## Advice framing -/

private def u32le (n : Nat) : Array UInt8 :=
  (Array.range 4).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

private def keyedBlobs
    (entries : Array (ByteArray × ByteArray)) : ByteArray := Id.run do
  assert! entries.size < 4294967296
  let mut out := u32le entries.size
  for (key, payload) in entries do
    assert! key.size == 32
    assert! payload.size < 4294967296
    out := out ++ key.data ++ u32le payload.size ++ payload.data
  return ⟨out⟩

/-- Pack `CheckEnv` claim preimages. Each key is computed as Blake3(payload),
matching IO channel 4's packed-digest lookup. -/
def preimagesBlob (preimages : Array ByteArray) : ByteArray :=
  keyedBlobs <| preimages.map fun bytes =>
    ((Address.blake3 bytes).hash, bytes)

/-- Pack serialized canonical trees. Channel 5 keys use the raw 32-byte tree root. -/
def treesBlob (trees : Array Ix.AssumptionTree) : ByteArray :=
  keyedBlobs <| trees.map fun tree =>
    (tree.root.hash, Ix.AssumptionTree.ser tree)

/-- Encode one structural-discharge choice. -/
def pathPayload (path? : Option Ix.Merkle.MerklePath) : ByteArray := Id.run do
  match path? with
  | none => return ⟨#[0]⟩
  | some path =>
    assert! path.size ≤ 64
    let mut out : Array UInt8 := #[1, UInt8.ofNat path.size]
    for (sibling, isLeft) in path do
      out := out.push (if isLeft then 0 else 1)
      out := out ++ sibling.hash.data
    return ⟨out⟩

/-- Pack one structural-discharge choice per unique input-assumption candidate
for IO channel 6. -/
def pathsBlob
    (paths : Array (Address × Option Ix.Merkle.MerklePath)) : ByteArray :=
  keyedBlobs <| paths.map fun (candidate, path?) =>
    (candidate.hash, pathPayload path?)

/-! ## Advice assembly -/

/-- One byte per Goldilocks element, the layout `read_checked_byte_stream` expects. -/
def byteGs (bytes : ByteArray) : Array Aiur.G :=
  bytes.data.map .ofUInt8

/-- Channel 4: a `CheckEnv` claim preimage, keyed by its packed digest. -/
def extendPreimage (io : Aiur.IOBuffer) (bytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 4 (MultiStark.digestGs bytes) (byteGs bytes)

/-- Channel 5: one serialized canonical tree, keyed by its raw 32-byte root. -/
def extendTree (io : Aiur.IOBuffer) (tree : Ix.AssumptionTree) : Aiur.IOBuffer :=
  io.extend 5 (byteGs tree.root.hash) (byteGs (Ix.AssumptionTree.ser tree))

/-- Channel 6: one structural carried/discharged choice keyed by the raw
candidate address. -/
def extendPath (io : Aiur.IOBuffer) (candidate : Address)
    (path? : Option Ix.Merkle.MerklePath) : Aiur.IOBuffer :=
  io.extend 6 (byteGs candidate.hash) (byteGs (pathPayload path?))

/-- Channels 0/2 for one child slot: verified serialized proof transport and
serialized claims. -/
def extendChild (io : Aiur.IOBuffer) (key : Nat)
    (proofAdviceBytes claimsBytes : ByteArray) : Aiur.IOBuffer :=
  let io := io.extend 0 #[.ofNat key] (byteGs proofAdviceBytes)
  io.extend 2 #[.ofNat key] (byteGs claimsBytes)

/-- Channels 3 and 6: the identity blob and the shape byte. -/
def extendIdentity (io : Aiur.IOBuffer) (allowed : ByteArray)
    (shape : Nat) : Aiur.IOBuffer :=
  let io := io.extend 3 #[.ofNat 0] (byteGs allowed)
  io.extend 6 #[.ofNat 0] #[.ofNat shape]

/-- Channel 1: vk bytes for one child kind (key 0 = IxVM, key 1 = self). -/
def extendVk (io : Aiur.IOBuffer) (kind : ChildKind)
    (vkBytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 1 #[.ofNat kind.code] (byteGs vkBytes)

/-- Channel 2 key 2: the output claim bytes of a pair fold. -/
def extendOutputClaim (io : Aiur.IOBuffer) (bytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 2 #[.ofNat 2] (byteGs bytes)

/-- Channel 1 key 2: external accelerator verifying-key bytes for Shape 17
(`aggr_dynamic_link`). -/
def extendExternalVk (io : Aiur.IOBuffer) (vkBytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 1 #[.ofNat 2] (byteGs vkBytes)

/-- Channel 6 key 1: auxiliary shape-selector bytes (1-byte bridge-cert child
kind for Shape 17 when `bridge?.isSome`, or 2-byte `(child0Kind, child1Kind)`
for Shape 18). -/
def extendShapeAux (io : Aiur.IOBuffer) (bytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 6 #[.ofNat 1] (byteGs bytes)

/-- Channel 5 trees needed for `A7` axiom-set merging when two children carry
distinct non-empty user-axiom trees. No advice is added on the fast path
(identical or single-sided axiom sets). -/
def extendAxiomMergeTrees (io : Aiur.IOBuffer)
    (left right output : Option Ix.AssumptionTree) : Aiur.IOBuffer :=
  match left, right, output with
  | some lt, some rt, some ot =>
    if lt.root == rt.root then io
    else extendTree (extendTree (extendTree io lt) rt) ot
  | _, _, _ => io

/-- Pack a 32-byte Ixon `Address` into 8 little-endian `u32` values stored as
`UInt64` words (matching `Ix.DynamicLink.CodecTag.ixonAddrPair` and
`Aggregation::aggr_assert_packed_addr_u64s`). -/
def packAddressU64s (addr : Address) : Array UInt64 :=
  (Array.range 8).map fun i =>
    let b0 := (addr.hash.data.getD (4 * i) 0).toNat
    let b1 := (addr.hash.data.getD (4 * i + 1) 0).toNat
    let b2 := (addr.hash.data.getD (4 * i + 2) 0).toNat
    let b3 := (addr.hash.data.getD (4 * i + 3) 0).toNat
    UInt64.ofNat (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)

/-- Build IO advice for Shape 17 (`aggr_dynamic_link`).
- `extVkBytes`: serialized external Multi-STARK verifying key (placed on channel 1 key 2).
- `extProofBytes`: serialized external Multi-STARK batch proof (placed on channel 0 key 0).
- `stmt`: canonical `DynamicLinkStatement` whose bytes are placed on channel 2 key 2.
- `bridgeCert?`: when `stmt.bridge?.isSome`, supplies
  `(certKind, certVkBytes, certProofBytes, certClaimsBytes, certClaimBytes)` for slot 1. -/
def dynamicLinkAdvice (allowed extVkBytes extProofBytes : ByteArray)
    (stmt : Ix.DynamicLink.DynamicLinkStatement)
    (bridgeCert? : Option (ChildKind × ByteArray × ByteArray × ByteArray × ByteArray) := none) :
    Aiur.IOBuffer :=
  let extClaimGs : Array Aiur.G := stmt.expectedMultiStarkClaim.map fun w => .ofNat w.toNat
  let extClaimsBytes := MultiStark.serializeClaims #[extClaimGs]
  let stmtBytes := Ix.DynamicLink.serDynamicLink stmt
  let io := extendIdentity default allowed dynamicLinkShapeCode
  let io := extendExternalVk io extVkBytes
  let io := extendChild io 0 extProofBytes extClaimsBytes
  let io := extendOutputClaim io stmtBytes
  match bridgeCert? with
  | none => io
  | some (certKind, certVkBytes, certProofBytes, certClaimsBytes, certClaimBytes) =>
    let io := extendShapeAux io ⟨#[UInt8.ofNat certKind.code]⟩
    let io := extendVk io certKind certVkBytes
    let io := extendChild io 1 certProofBytes certClaimsBytes
    extendPreimage io certClaimBytes

/-- Build IO advice for Shape 18 (`aggr_discharge_eval`).
- Slot 0 carries the `EvalAssumedClaim` child (`validator = 10` or `11`).
- Slot 1 carries the discharging child (`Claim.eval`, `Claim.check`, or Shape 17 `DynamicLinkStatement`).
- `evalBeforeTree` / `evalAfterTree?` are the canonical `evalAssumptions` trees before and after
  removing `dischargedLeaf`.
- `extraPreimages` / `extraTrees` carry any constant/binding preimages (for `Claim.check` discharge)
  and A7 axiom-merge trees (when both children carry distinct non-empty axiom trees). -/
def dischargeEvalAdvice (allowed : ByteArray)
    (child0Kind : ChildKind) (child0VkBytes child0ProofBytes child0ClaimsBytes child0ClaimBytes : ByteArray)
    (child1Kind : ChildKind) (child1VkBytes child1ProofBytes child1ClaimsBytes child1ClaimBytes : ByteArray)
    (outputClaimBytes : ByteArray)
    (evalBeforeTree : Ix.AssumptionTree)
    (evalAfterTree? : Option Ix.AssumptionTree)
    (dischargedLeaf : Ix.DynamicLink.EvalAssumption)
    (extraPreimages : Array ByteArray := #[])
    (extraTrees : Array Ix.AssumptionTree := #[]) : Aiur.IOBuffer :=
  let io := extendIdentity default allowed dischargeEvalShapeCode
  let io := extendShapeAux io ⟨#[UInt8.ofNat child0Kind.code, UInt8.ofNat child1Kind.code]⟩
  let io := extendVk io child0Kind child0VkBytes
  let io := extendVk io child1Kind child1VkBytes
  let io := extendChild io 0 child0ProofBytes child0ClaimsBytes
  let io := extendChild io 1 child1ProofBytes child1ClaimsBytes
  let io := extendOutputClaim io outputClaimBytes
  let io := extendPreimage io child0ClaimBytes
  let io := extendPreimage io child1ClaimBytes
  let io := extendPreimage io (Ix.DynamicLink.serEvalAssumption dischargedLeaf)
  let io := extraPreimages.foldl extendPreimage io
  let io := extendTree io evalBeforeTree
  let io := match evalAfterTree? with
    | some afterTree => extendTree io afterTree
    | none => io
  extraTrees.foldl extendTree io

/-- Outer `ix_aggr` public claim for a Tier 1 `DynamicLinkStatement`. -/
def dynamicLinkOuterClaim (allowed : ByteArray) (aggrIdx : Nat)
    (stmt : Ix.DynamicLink.DynamicLinkStatement) : Array Aiur.G :=
  Aiur.buildClaim aggrIdx (Aggr.pubInput allowed (Ix.DynamicLink.serDynamicLink stmt)) #[]

/-- Outer `ix_aggr` public claim for a Tier 2 `EvalAssumedClaim`. -/
def evalAssumedOuterClaim (allowed : ByteArray) (aggrIdx : Nat)
    (claim : Ix.DynamicLink.EvalAssumedClaim) : Array Aiur.G :=
  Aiur.buildClaim aggrIdx (Aggr.pubInput allowed (Ix.DynamicLink.serEvalAssumedClaim claim)) #[]

/-- Bump when aggregate cache identity changes beyond the recursion verifying
key. Version 2 uses uniform `ix_aggr` outer claims. -/
def aggregateCacheVersion : Nat := 2

/--
`blake3(version ‖ recursion_vk_digest ‖ fri_params_ser ‖ outer_claim_bytes)`.
-/
def aggregateCacheKey (recursionVk : ByteArray)
    (recursionParameters : Aggr.RecursionParameters)
    (outerClaim : Array Aiur.G) (version : Nat := aggregateCacheVersion) : Address :=
  let recursionVkDigest := (Address.blake3 recursionVk).hash
  let outerClaimBytes := MultiStark.serializeClaims #[outerClaim]
  Address.blake3 ⟨MultiStark.u64le version ++ recursionVkDigest.data ++
    recursionParameters.cacheFriBytes.data ++ outerClaimBytes.data⟩

/-- The public claim is uniform across wrap, flat, and structural witnesses. -/
def aggregateOuterClaim (allowed : ByteArray) (aggrIdx : Nat)
    (claim : Ix.Claim) : Array Aiur.G :=
  Aiur.buildClaim aggrIdx (Aggr.pubInput allowed (Ix.Claim.ser claim)) #[]

end Aggr
end
