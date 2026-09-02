module
public import Ix.Aiur.Semantics.BytecodeFfi

/-!
AiurSystem, Proof, FRI params, and `buildClaim` — the "prove & verify" FFI surface.

The bytecode-execution FFI that used to live here has moved to
`Ix/Aiur/Bytecode/ExecuteFfi.lean` so that `Bytecode/Eval.lean` can be built
without pulling in the proving backend.
-/

public section

namespace Aiur

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

namespace Proof

@[extern "rs_aiur_proof_to_bytes"]
opaque toBytes : @& Proof → ByteArray

@[extern "rs_aiur_proof_of_bytes"]
opaque ofBytes : @& ByteArray → Proof

/-- Decode an untrusted serialized proof without aborting the process. Store
and network boundaries must use this variant; `ofBytes` remains for callers
whose bytes were produced in-process or already validated. -/
@[extern "rs_aiur_proof_of_bytes_checked"]
opaque ofBytesChecked : @& ByteArray → Except String Proof
end Proof

structure CommitmentParameters where
  logBlowup : Nat
  capHeight : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat

/-- Canonical Aiur parameters, shared by `ix prove`, `ix verify`, and the
`ix check` statistics. Until these become flags / commit to the proof
header, every flow MUST use the same values or proofs won't verify. -/
def defaultCommitmentParameters : CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }

def defaultFriParameters : FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

/-- Shape of one compiled circuit, built directly by Rust
(`LeanAiurCircuitShape` in `crates/ffi/src/lean.rs`; field order must
match). Heights of function and memory circuits are execution-dependent
and are not part of the shape; `preprocessedHeight` doubles as the fixed
trace height of the byte-gadget circuits (256 and 65536), whose witness
builders always emit the full table. -/
structure CircuitShape where
  mainWidth : Nat
  stage2Width : Nat
  quotientDegree : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  deriving Inhabited

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

/-- Result of a prove FFI call, built directly by Rust
(`LeanAiurProveResult` in `crates/ffi/src/lean.rs`). `ioData`/`ioMap`
are the flattened `IOBuffer`; see `IOBuffer.ofArrays`. -/
structure ProveResult where
  claim : Array G
  proof : Proof
  ioData : Array (G × Array G)
  ioMap : Array ((G × Array G) × IOKeyInfo)
  deriving Nonempty

/-- Result of a with-env prove FFI call, built directly by Rust
(`LeanAiurProveEnvResult` in `crates/ffi/src/lean.rs`). `claimBytes`
is the claim's wire serialization (`ixon::Claim::put`). -/
structure ProveEnvResult where
  claimBytes : ByteArray
  proof : Proof
  ioData : Array (G × Array G)
  ioMap : Array ((G × Array G) × IOKeyInfo)
  deriving Nonempty

namespace AiurSystem

@[extern "rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → @&FriParameters → AiurSystem

/-- Serialize the verifying key (`System<AiurCircuit>`) to bytes. -/
@[extern "rs_aiur_system_vk_bytes"]
opaque vkBytes : @& AiurSystem → ByteArray

/-- Per-circuit shapes in canonical system order: constrained functions
(ascending index), memories, `Bytes1`, `Bytes2`. -/
@[extern "rs_aiur_system_circuit_shapes"]
opaque circuitShapes : @& AiurSystem → Array CircuitShape

@[extern "rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String ProveResult

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Except String (Array G × Proof × IOBuffer) :=
  (prove' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray).map
    fun r => (r.claim, r.proof, .ofArrays r.ioData r.ioMap)

@[extern "rs_aiur_system_prove_ixvm"]
private opaque proveIxVM' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String ProveResult

/-- IxVM-native prove: same shape as `prove`, but routes execution
    through the codegen'd Rust kernel (`execute_generated`) instead
    of the bytecode interpreter. The resulting `Proof` is
    verification-compatible with one from `prove`. Only valid when
    `system.toplevel` is the IxVM kernel's bytecode. -/
def proveIxVM (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Except String (Array G × Proof × IOBuffer) :=
  (proveIxVM' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray).map
    fun r => (r.claim, r.proof, .ofArrays r.ioData r.ioMap)

/-- Prove the MultiStark recursive verifier over proof-advice/vk/claims
byte blobs. `proofAdviceBytes` must come from
`AiurSystem.proofToAdviceBytes`; compact `Proof.toBytes` wire bytes are not
an in-circuit input. The IO advice buffer is built natively in Rust (see
    `Bytecode.Toplevel.executeMultiStark`); the execute step inside
    the prove routes through the codegen'd verifier
    (`crates/ixvm-codegen/src/aiur_multi_stark.rs`) unless
    `useBytecode` is set. Only valid when `system` was built from the
    production `MultiStark.multiStark` bytecode. Returns the claim
    (`#[functionChannel, funIdx] ++ pubInput ++ output`) and the
    `Proof`; the final buffer is not returned. -/
@[extern "rs_aiur_multi_stark_prove"]
opaque proveMultiStark (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G)
  (proofAdviceBytes vkBytes claimBytes : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Proof)

/-- Prove one flat or structural aggregate-first binary join over child
proof/claim advice. Both proof blobs must come from
`AiurSystem.proofToAdviceBytes`; compact child `Proof.toBytes` values remain
the persisted/cache representation. The compact preimage/tree/path blobs are produced by
`MultiStark.joinPreimagesBlob`, `MultiStark.joinTreesBlob`, and
`MultiStark.joinPathsBlob`. Malformed
framing is returned as an error; as with `prove`/`proveMultiStark`, callers
must supply an accepting execution witness. The final native IO buffer is
intentionally not marshalled back to Lean. -/
@[extern "rs_aiur_multi_stark_join_prove"]
opaque proveMultiStarkJoin (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G)
  (leftProofAdviceBytes rightProofAdviceBytes recursionVkBytes : @& ByteArray)
  (leftClaimsBytes rightClaimsBytes outputClaimBytes allowedBytes : @& ByteArray)
  (preimagesBlob treesBlob pathsBlob : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Proof)

/-- Prove one `ix_aggr` execution — any shape — over raw child proof/claim
advice. Both proof blobs must come from `AiurSystem.proofToAdviceBytes`;
compact `Proof.toBytes` values remain the persisted representation. The
compact preimage/tree/path blobs are produced by `Aggr.preimagesBlob`,
`Aggr.treesBlob`, and `Aggr.pathsBlob`; wrap and flat shapes pass empty
right-child blobs. Malformed framing is returned as an error; as with
`prove`/`proveMultiStark`, callers must supply an accepting execution
witness. Only valid when `system` was built from the production
`Aggr.ixAggr` bytecode (unless `useBytecode` is set). The final native IO
buffer is intentionally not marshalled back to Lean. -/
@[extern "rs_aiur_ix_aggr_prove"]
opaque proveIxAggr (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G) (shape : @& Nat)
  (leftProofAdviceBytes rightProofAdviceBytes ixvmVkBytes selfVkBytes : @& ByteArray)
  (leftClaimsBytes rightClaimsBytes outputClaimBytes allowedBytes : @& ByteArray)
  (preimagesBlob treesBlob pathsBlob : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Proof)

@[extern "rs_aiur_system_prove_addr_with_env"]
private opaque proveAddrWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool →
    Except String ProveEnvResult

/-- Per-claim prove against a Rust-owned `EnvHandle`. Returns
    `(claimBytes, proof, ioBuffer)` — Rust serializes the
    reconstructed `Ix.Claim` via `ixon::Claim::put` so Lean can
    deserialize directly without re-running the closure walk.
    `useBytecode` routes the witness-generating execution through the
    generic Aiur bytecode interpreter instead of the codegen'd IxVM
    kernel (same toggle as `checkAddrWithEnv`). -/
def proveAddrWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (addrBytes : ByteArray)
  (useBytecode : Bool := false) :
    Except String (ByteArray × Proof × IOBuffer) :=
  (proveAddrWithEnv' system funIdx envHandle addrBytes useBytecode).map
    fun r => (r.claimBytes, r.proof, .ofArrays r.ioData r.ioMap)

/-- Result of a per-shard prove: the claim's wire bytes, the proof, the
    projected prover RAM peak of the record that produced it
    (`AiurSystem::peak_prove_bytes`), and the part count the peak model
    projects will fit the budget
    (`AiurSystem::suggested_split_parts`).

    `proof` is `none` exactly when the peak exceeded the budget — a
    RESULT rather than an error, since the caller's answer is to cut
    the shard into `suggestedParts` parts and prove those. The count is
    computed Rust-side because only there does the executed record
    still exist to read per-circuit heights from; it is optimistic
    (parts re-execute dependencies shared across the cut), so each part
    must still be gated on its own record. `suggestedParts` is 1
    whenever the prove ran. The claim bytes are filled either way (the
    claim is known before proving starts).

    The final IO buffer is not returned — it is the shard's whole
    ingested byte scope and no caller reads it. -/
structure ShardProveResult where
  claimBytes : ByteArray
  proof : Option Proof
  peakBytes : Nat
  suggestedParts : Nat

@[extern "rs_aiur_system_shard_prove_with_env"]
private opaque shardProveWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → @& Nat → Bool →
    Except String ShardProveResult

/-- Per-shard prove against a Rust-owned `EnvHandle`: ONE execution,
    whose record is proven from directly.

    `maxRamBytes` is a per-shard prover-RAM budget checked against that
    record's projected peak before the witness phase begins; `0` means
    detect (85% of `MemAvailable`, the policy the check batch's RAM gate
    uses), and an unreadable `/proc/meminfo` disables the check rather
    than guessing. Over budget, the record is dropped and `proof` is
    `none` — learning that here costs one execution instead of an OOM
    part-way through an FFT. The peak comes back either way, so a prove
    run yields the same split/merge signal a check run does.

    `execOnly` stops after execution + measurement (`proof` is `none`
    either way; `suggestedParts` is 1 exactly when the peak fits): the
    split loop runs on executions alone, never starting a STARK. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (ownedBlob : ByteArray) (maxRamBytes : Nat := 0)
  (execOnly : Bool := false) :
    Except String ShardProveResult :=
  shardProveWithEnv' system funIdx envHandle ownedBlob maxRamBytes execOnly

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem →
  @& Array G → @& Proof → Except String Unit

/-- The proof re-encoded in the per-query advice transport the in-circuit
verifier consumes (pruned FRI multiproofs expanded to one authentication
path per query); errors if the proof does not verify natively. -/
@[extern "rs_aiur_proof_to_advice_bytes"]
opaque proofToAdviceBytes : @& AiurSystem →
  @& Array G → @& Proof → Except String ByteArray

end AiurSystem

/-- Write a `.ixes` manifest for an EXPLICIT partition — the block lists
    a run actually produced (splits included) rather than a planner's
    output. `shardsBlob`: per shard, a 4-byte LE block count followed by
    that many 32-byte block addresses; every env block must appear in
    exactly one shard. `peaksBlob`: one 8-byte LE measured prover peak
    per shard in order, recorded on the manifest for schedulers. Own
    sizes, foreign blocks, cross-ingress and assumption roots are
    recomputed from the env's static profile; prints the manifest
    summary to stderr. -/
@[extern "rs_shard_manifest_from_partition"]
opaque shardManifestFromPartition : @& EnvHandle →
  @& ByteArray → @& ByteArray → @& String → IO Unit

/-- Refine an existing `.ixes` manifest (`sourcePath`) by cutting some of
    its leaves into parts and write the result to `outPath`
    (`ShardManifest::refine`, `crates/kernel/src/shard.rs`). Every other
    leaf keeps its block list, record, id and place in the aggregation
    tree; a refined leaf's place becomes a balanced subtree over its
    parts, part 0 keeps the leaf's id and later parts take fresh ids after
    the last existing one.

    `refinementsBlob`: `count(u32)`, then per refined leaf `id(u32) ‖
    nparts(u32)` and per part `nblocks(u32) ‖ 32·nblocks ‖ peak(u64)`.
    `measuredBlob`: empty, or one `u64` analytic prover peak per SOURCE
    shard in id order; a nonzero value overrides the peak carried forward
    for an unsplit leaf. The new partition is validated as an exact,
    disjoint cover of the env's blocks. Returns the parts' new ids:
    `count(u32)`, then per refinement `n(u32) ‖ n × id(u32)`. -/
@[extern "rs_shard_manifest_refine"]
opaque shardManifestRefine : @& EnvHandle → @& String →
  @& ByteArray → @& ByteArray → @& String → IO ByteArray

@[extern "rs_aiur_detected_ram_budget"]
private opaque detectedRamBudgetFFI : IO UInt64

/-- The prover/execution RAM budget the Rust side detects on this machine:
    85 % of `MemAvailable` (`ix_kernel::shard::RAM_USABLE_FRAC`) — the policy
    the check batch's RAM gate and `ix prove --max-ram 0` use. `0` when
    `/proc/meminfo` is unreadable; callers that need a budget fail closed
    on it instead of running ungated. -/
def detectedRamBudgetBytes : IO Nat := do
  pure (← detectedRamBudgetFFI).toNat

namespace Bytecode.Toplevel

/-- One shard's result from `shardCheckBatchWithEnv`. `weights` is the
    shard's per-constant virtual-gas table, packed as 48-byte rows —
    32-byte address, then `vspan` and `mult` as little-endian `UInt64`s
    (see `ShardResult.foldWeights`). Empty unless the batch ran with
    `profile := true`; the record it is read from is reduced to these
    rows and dropped inside the shard's own task, so a whole partition's
    weights fit in RAM when its records could not. -/
structure ShardResult where
  error : String
  peakBytes : Nat
  weights : ByteArray
  /-- 1 when `peakBytes` fits the batch's `maxRamBytes` (or no budget
      was given); otherwise the part count the peak model projects will
      fit (`AiurSystem::suggested_split_parts`, measured on the record
      in-task). -/
  suggestedParts : Nat
  deriving Inhabited

/-- Bytes per packed `weights` row: 32 address + 8 vspan + 8 mult. -/
def shardWeightRow : Nat := 48

/-- Fold `f` over the packed `(addrBytes, vspan, mult)` rows of `weights`.
    Trailing bytes that do not complete a row are ignored. -/
@[inline] def ShardResult.foldWeights {α : Type} (r : ShardResult) (init : α)
    (f : α → ByteArray → UInt64 → UInt64 → α) : α :=
  go (r.weights.size / shardWeightRow) 0 init
where
  go : Nat → Nat → α → α
    | 0, _, acc => acc
    | rows + 1, off, acc =>
      go rows (off + shardWeightRow) <| f acc
        (r.weights.extract off (off + 32))
        (r.weights.extract (off + 32) (off + 40)).toUInt64LE!
        (r.weights.extract (off + 40) (off + 48)).toUInt64LE!

@[extern "rs_aiur_toplevel_shard_check_batch"]
private opaque shardCheckBatchWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool → @& Nat →
  @& CommitmentParameters → @& FriParameters → Bool → @& Nat → @& Nat →
    Except String (Array ShardResult)

/-- Check EVERY shard of a partition in one call: rayon over the shard
    list with true work-stealing (no chunk barriers), each shard
    through the exact single-shard machinery over its own private
    record and witness io. `shardsBlob` encodes, per shard, a 4-byte LE
    owned-constant count followed by that many 32-byte addresses.
    Returns one `ShardResult` per shard in shard order: empty error =
    clean, and `peakBytes` is the analytic prover RAM peak
    ([`AiurSystem::peak_prove_bytes`] Rust-side) of the shard's executed
    record — the split/merge input (0 on failure). `profile` turns on the
    virtual-gas meter and fills each result's `weights` with the shard's
    per-constant cost rows, read off the record inside the shard's own
    task; `checkConstIdx` names the `check_const` function whose queries
    those rows come from (ignored when not profiling).
    `jobs = 0` uses rayon's default pool width (all cores): peak RSS
    is bounded by the Rust-side RAM gate (a byte-weighted admission
    semaphore over estimated per-shard execution RSS vs available
    system RAM), not by thread count — pass `jobs` only to narrow
    CPU use.

    `maxRamBytes > 0` is a per-shard prover-RAM budget: each result's
    `suggestedParts` is 1 when its peak fits and the model's projected
    part count otherwise, so a caller can cut over-budget shards and
    re-batch the parts — the wave loop that audits a partition's split
    behavior on executions alone. -/
def shardCheckBatchWithEnv (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (shardsBlob : ByteArray) (useBytecode : Bool := false) (jobs : Nat := 0)
  (commitmentParameters : CommitmentParameters := defaultCommitmentParameters)
  (friParameters : FriParameters := defaultFriParameters)
  (profile : Bool := false) (checkConstIdx : Nat := 0)
  (maxRamBytes : Nat := 0)
  : Except String (Array ShardResult) :=
  shardCheckBatchWithEnv' toplevel funIdx envHandle shardsBlob useBytecode
    jobs commitmentParameters friParameters profile checkConstIdx maxRamBytes

end Bytecode.Toplevel

/-- One-shot variant of `AiurSystem.circuitShapes` for flows that never
build an `AiurSystem` (the `ix check` statistics): Rust builds the system,
extracts the shapes, and drops it. -/
@[extern "rs_aiur_circuit_shapes"]
opaque circuitShapes :
  @& Bytecode.Toplevel → @& CommitmentParameters → @& FriParameters →
    Array CircuitShape

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur

end
