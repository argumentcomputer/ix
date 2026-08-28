module
public import Blake3.Rust
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.AssumptionTree
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.MultiStark.Goldilocks
public import Ix.MultiStark.Aggregate
public import Ix.MultiStark.Host
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak
public import Ix.MultiStark.Pcs
public import Ix.MultiStark.SystemDeserialize
public import Ix.MultiStark.Verifier
public import Ix.MultiStark.Tests

/-!
# Multi-STARK proof verifier and binary join (Aiur)

The lift entrypoint's public statement is purely existential: *"there
exists a valid multi-stark proof for the constraint system with this Blake3
digest and these public claims."* The FRI parameters (blowup, query count,
PoW bits, …) are NOT separate public inputs: they live in the verifying key,
which the statement already binds through `system_digest` — repeating them
publicly would be redundant. The proof itself is
**non-deterministic advice** (fed on IO channel 0,
never hashed or otherwise bound as a public input): the Fiat-Shamir transcript
replay plus the Merkle/OOD/FRI checks are exactly what make any accepted advice
a valid proof — a hash binding of the proof bytes would add nothing to the
statement, while costing an extra in-circuit hash over those bytes.

The verifying key and claims, by contrast, ARE digest-bound (`system_digest`,
`claims_digest`): they determine *what was proven*.

The two production join entrypoints verify lift/join proofs under one pinned
recursion vk and fold their `CheckEnv` statements. `join_two` uses canonical
subject union; `join_two_structural` commits to a root-of-roots and discharges
assumptions with Merkle paths. Their implementation lives in
`Ix/MultiStark/Aggregate.lean`.

Fixed protocol assumptions (our system): `capHeight = 0`, `maxLogArity = 1`,
`logFinalPolyLen = 0`. The variable FRI parameters (`num_queries`,
`commit_pow_bits`, `query_pow_bits`, `log_blowup`) are read from the
digest-bound verifying key.
-/

public section

namespace MultiStark

def entrypoints := ⟦
  -- Public inputs: the Blake3 digests of the verifying key and the claims,
  -- each as 8 field elements of 4 packed LE bytes (32 bytes; 4-byte packing
  -- is injective in Goldilocks where 8-byte limbs are not, and costs 16
  -- input columns instead of 64). The proof is pure
  -- non-deterministic advice on IO channel 0 — see the module docstring. One
  -- stream per channel (0 = proof, 1 = vk, 2 = claims), each registered under
  -- key `[0]` on its channel.
  pub fn verify_multi_stark_proof(system_digest: [G; 8], claims_digest: [G; 8]) {
    -- Proof advice from IO channel 0: deserialize directly from the IO arena
    -- by byte offset (no materialized byte stream), assert fully consumed.
    -- The byte FETCHES inside the readers are unconstrained (the proof is
    -- advice — same trust model as the former `#read_byte_stream`); the
    -- parse structure itself stays constrained.
    let (idx, len) = io_get_info(0, [0]);
    let (proof, stop) = @read_proof(idx);
    assert_eq!(stop, idx + len);
    -- Verifying key (`System<AiurCircuit>`) from IO channel 1: fetch the raw
    -- bytes once as advice, then constrain both the hash and deserialization
    -- against that exact byte stream (the same binding pattern as IxVM).
    let (sidx, slen) = io_get_info(1, [0]);
    let sbytes = #read_byte_stream(1, sidx, slen);
    assert_eq!(@b3_pack(@blake3(sbytes)), system_digest);
    let (sys, srest) = @read_system(sbytes);
    assert_eq!(load(srest), ListNode.Nil);
    -- Public claims (`&[&[Val]]`) from IO channel 2: bind the bytes to the
    -- public Blake3 `claims_digest`, then deserialize. Binding them as a
    -- public input is what makes the lookup argument sound (a prover cannot
    -- choose claims adaptively).
    let (cidx, clen) = io_get_info(2, [0]);
    let cbytes = #read_byte_stream(2, cidx, clen);
    assert_eq!(@b3_pack(@blake3(cbytes)), claims_digest);
    let (claims, crest) = @read_claims(cbytes);
    assert_eq!(load(crest), ListNode.Nil);
    -- Structural + accumulator + PCS checks.
    let vres = @verify(proof);
    assert_eq!(vres, 1);
    -- Step 3 + 5: prover-faithful Fiat-Shamir replay and the out-of-domain
    -- composition/quotient check, `composition(ζ)·inv_vanishing(ζ) == quotient(ζ)`.
    let oodres = @ood_verify(sys, proof, claims, cbytes);
    assert_eq!(oodres, 1);
    ()
  }
⟧

/-- The FULL Multi-STARK verifier toplevel: `core` (lists/options) +
`byteStream` (`U64`, `flatten_u64`, `read_byte_stream`, …) + the deserializer,
the Blake3 hash, and both production entrypoints — unpruned, including entries inherited
from the shared modules (`blake3_test`/`blake3_bench`). Only `multiStarkTests`
builds on this; production uses `multiStark` (pruned). -/
def multiStarkFull : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  let t ← t.merge MultiStark.goldilocks
  let t ← t.merge deserialize
  let t ← t.merge IxVM.blake3
  let t ← t.merge systemDeserialize
  let t ← t.merge pcs
  let t ← t.merge verifier
  let t ← t.merge aggregate
  t.merge entrypoints

/-- The production recursion toplevel: `multiStarkFull` pruned to the combined
call closures of `verify_multi_stark_proof` (lift), `join_two` (flat join), and
`join_two_structural`. Every
compiled function is a committed circuit whose openings pad every proof of the
system's execution, so functions only reachable from unrelated entries
(kernel-oriented helpers of the shared modules, test/bench entries) cost real
proof bytes if kept. -/
def multiStark : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← multiStarkFull
  pure (t.prune [`verify_multi_stark_proof, `join_two, `join_two_structural])

/-! ## Lean-side input assembly

Callers of `verify_multi_stark_proof` (tests, benchmarks) must reproduce the
verifier's wire formats byte-for-byte — the vk and claims are Blake3
digest-bound. These helpers are that recipe's single home. -/

/-- The 8 little-endian bytes of `n` as a `u64`. -/
def u64le (n : Nat) : Array UInt8 :=
  (Array.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Serialize public claims to `read_claims`'s wire format (which is also what
the prover's Fiat-Shamir transcript observes): a length-prefixed list of
length-prefixed claims, every word a little-endian `u64`. -/
def serializeClaims (claims : Array (Array Aiur.G)) : ByteArray := Id.run do
  let mut out : Array UInt8 := u64le claims.size
  for c in claims do
    out := out ++ u64le c.size
    for g in c do
      out := out ++ u64le g.val.toNat
  return ⟨out⟩

/-- Assemble `verify_multi_stark_proof`'s public input from the serialized vk
(`AiurSystem.vkBytes`) and claims (`serializeClaims`): vk digest ++ claims
digest, each as 8 packed-4-byte field elements (the entrypoint's format). The FRI parameters are read in-circuit from the digest-bound vk, not
passed publicly. The proof/vk/claims advice itself goes through the
natively-built IO buffer (`executeMultiStark` / `proveMultiStark`, which take
the raw byte blobs directly: channel 0 = proof, 1 = vk, 2 = claims, each
under key `[0]`). -/
def digestGs (bytes : ByteArray) : Array Aiur.G :=
  let h := (Blake3.Rust.hash bytes).val.data
  (Array.range 8).map fun i =>
    .ofNat (h[4*i]!.toNat + 256 * h[4*i+1]!.toNat
      + 65536 * h[4*i+2]!.toNat + 16777216 * h[4*i+3]!.toNat)

def verifierPubInput (vkBytes claimBytes : ByteArray) : Array Aiur.G :=
  digestGs vkBytes ++ digestGs claimBytes

/-! ## Aggregate-first input assembly

These helpers define the host half of the recursive join wire contracts from
`plans/aggregate-first-pipeline.md` §10.  Keeping the byte layout and digest
packing next to `verifierPubInput` prevents the CLI, tests, and FFI callers from
growing subtly different encodings while the join entrypoint is brought up.
-/

/-- The digest-bound 96-byte allowlist preimage for a recursive join:

`blake3(ixvm vk) ‖ verify_claim index as u64-LE ‖ blake3(recursion vk) ‖
lift index as u64-LE ‖ flat join index as u64-LE ‖ structural join index as
u64-LE`.

The verifying keys stay outside the public input. Their digests and all four
entrypoint indices form the stable identity that every join in an aggregation
tree pins transitively. The indices must be explicit because the Source DSL
cannot materialize its compiler-assigned function index inside a circuit. -/
def allowedBlob (ixvmVkBytes : ByteArray) (verifyClaimIdx : Nat)
    (recursionVkBytes : ByteArray) (liftIdx joinIdx structuralJoinIdx : Nat) : ByteArray :=
  let ixvmDigest := (Blake3.Rust.hash ixvmVkBytes).val.data
  let recursionDigest := (Blake3.Rust.hash recursionVkBytes).val.data
  ⟨ixvmDigest ++ u64le verifyClaimIdx ++ recursionDigest ++
    u64le liftIdx ++ u64le joinIdx ++ u64le structuralJoinIdx⟩

/-- Public input for either join entrypoint: the packed Blake3 digest of the
allowlist blob followed by the packed digest of the output `CheckEnv` claim
bytes. -/
def joinPubInput (allowed outClaimBytes : ByteArray) : Array Aiur.G :=
  digestGs allowed ++ digestGs outClaimBytes

/-- Four little-endian bytes of `n`, used only by the compact native-FFI
framing below. Join advice blobs are bounded by the `ByteArray`/Rust address
space in practice and therefore never approach the `u32` limit. -/
private def u32le (n : Nat) : Array UInt8 :=
  (Array.range 4).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Encode content-addressed byte blobs for the native join FFI as

`count:u32-LE ‖ (key:32 ‖ length:u32-LE ‖ payload)*`.

The circuit still re-hashes/re-roots every payload. These host-side keys only
make the advice addressable; they are not trusted bindings. -/
private def joinKeyedBlobs
    (entries : Array (ByteArray × ByteArray)) : ByteArray := Id.run do
  assert! entries.size < 4294967296
  let mut out := u32le entries.size
  for (key, payload) in entries do
    assert! key.size == 32
    assert! payload.size < 4294967296
    out := out ++ key.data ++ u32le payload.size ++ payload.data
  return ⟨out⟩

/-- Pack nested claim preimages for `executeMultiStarkJoin` /
`proveMultiStarkJoin`. Each key is computed as Blake3(payload), matching IO
channel 4's packed-digest lookup. -/
def joinPreimagesBlob (preimages : Array ByteArray) : ByteArray :=
  joinKeyedBlobs <| preimages.map fun bytes =>
    ((Blake3.Rust.hash bytes).val, bytes)

/-- Pack serialized canonical subject/assumption trees for the native join
FFI. Channel 5 keys use the raw 32-byte tree root. The in-circuit loader
independently checks strict leaf order and recomputes the canonical root. -/
def joinTreesBlob (trees : Array Ix.AssumptionTree) : ByteArray :=
  joinKeyedBlobs <| trees.map fun tree =>
    (tree.root.hash, Ix.AssumptionTree.ser tree)

/-- Encode one structural-discharge choice. A `none` path means "carry" and
encodes as one zero byte. A present path means "discharge" and encodes as

`1 ‖ count:u8 ‖ (side:u8 ‖ sibling:32)*`,

where side `0` places the sibling on the left and side `1` places it on the
right. Paths are bounded to 64 steps in both the host encoder and circuit. -/
def joinPathPayload (path? : Option Ix.Merkle.MerklePath) : ByteArray := Id.run do
  match path? with
  | none => return ⟨#[0]⟩
  | some path =>
    assert! path.size ≤ 64
    let mut out : Array UInt8 := #[1, UInt8.ofNat path.size]
    for (sibling, isLeft) in path do
      -- MerklePath's Bool says whether the sibling is on the left.
      out := out.push (if isLeft then 0 else 1)
      out := out ++ sibling.hash.data
    return ⟨out⟩

/-- Pack one structural-discharge choice per unique input-assumption candidate
for IO channel 6. -/
def joinPathsBlob
    (paths : Array (Address × Option Ix.Merkle.MerklePath)) : ByteArray :=
  joinKeyedBlobs <| paths.map fun (candidate, path?) =>
    (candidate.hash, joinPathPayload path?)

/-- The verifier toplevel PLUS its self-test entrypoints
(`Ix/MultiStark/Tests.lean`), unpruned. Kept separate from `multiStark`
because every `pub fn` adds a circuit to the compiled system — the production
verifier should not carry test-only width. Use this toplevel only to run the
`*_test` entrypoints. -/
def multiStarkTests : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← multiStarkFull
  t.merge tests

end MultiStark

end
