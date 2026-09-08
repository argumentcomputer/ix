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

/-- Manifest-bound aggregate root reconstructed and audited by the native
Stage 2 controller. `claimBytes` is the exact root `Ix.Claim` wire encoding;
`constantCount` is the number of environment constants proven to occur once. -/
structure AggregateExpected where
  claimBytes : ByteArray
  constantCount : Nat
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
`AiurSystem.proofToAdviceBytes`, which verifies and serializes the native
proof transport. The IO advice buffer is built natively in Rust (see
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
`AiurSystem.proofToAdviceBytes`. The compact preimage/tree/path blobs are produced by
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
the compact preimage/tree/path blobs are produced by `Aggr.preimagesBlob`,
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

/-- Run the production aggregate-first Stage 2 pipeline natively after Lean
has compiled the IxVM and `ix_aggr` systems. Rust owns all data-dependent
orchestration: manifest/environment binding, shard-claim reconstruction,
statement folding, cache validation, dependency scheduling, recursive advice,
proving, and persistence. `proofHexes` is one store address per line;
`cacheFriBytes` is the stable 40-byte recursion-FRI cache identity.
`reproveSlotCode` is zero for a full run and `slot + 1` for a targeted replay;
the latter loads and verifies only the target's immediate cached children.
When `writeOutputs` is false, proofs are hashed but neither the store nor cache
is changed. Returns the root or replayed proof address. -/
@[extern "rs_aiur_stage2_aggregate"]
opaque aggregateStage2 (ixvmSystem aggrSystem : @& AiurSystem)
  (envHandle : @& EnvHandle) (manifestPath proofHexes : @& String)
  (verifyIdx aggrIdx jobs ramBudgetBytes structuralAbove reproveSlotCode : @& Nat)
  (directJoins planOnly : Bool) (cacheFriBytes : @& ByteArray)
  (useCache writeOutputs : Bool) :
    Except String String

/-- Reconstruct and audit the manifest-relative aggregate root entirely in
Rust, using the same ownership, frontier, pruning, and statement-fold code as
`aggregateStage2`. This is the native orchestration path for `ix verify` and
does not construct shard statements or schedule Lean tasks. -/
@[extern "rs_aiur_aggregate_expected"]
opaque aggregateExpected (envHandle : @& EnvHandle)
  (manifestPath : @& String) (structuralAbove : @& Nat) :
    Except String AggregateExpected

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

    `proof` is `none` for measurement-only execution, an oversized prover
    peak, or an early execution-memory interruption. Oversize is a
    RESULT rather than an error, since the caller's answer is to cut
    the shard into `suggestedParts` parts and prove those. The count is
    computed Rust-side because only there does the executed record
    still exist to read per-circuit heights from; it is optimistic
    (parts re-execute dependencies shared across the cut), so each part
    must still be gated on its own record. `suggestedParts` is 1
    whenever the prove ran. The claim bytes are filled either way (the
    claim is known before proving starts).

    Early execution-memory interruption returns `peakBytes = 0` (unknown,
    NOT a measured zero-byte peak) and `suggestedParts = 2`, so neither
    prove nor exec-only callers can accept the interrupted parent.

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
    IO (Except String ShardProveResult)

/-- Per-shard prove against a Rust-owned `EnvHandle`: ONE execution,
    whose record is proven from directly.

    `maxRamBytes` is a per-shard prover-RAM budget checked against that
    record's projected peak before the witness phase begins; `0` means
    detect (85% of cgroup-aware available memory). A separate cooperative
    execution-storage limit can abort before the record completes. Over
    the prover budget, the record is dropped and `proof` is
    `none` — learning that here costs one execution instead of an OOM
    part-way through an FFT. The peak comes back either way, so a prove
    run yields the same split/merge signal a check run does. Early execution
    interruption instead returns an unknown peak (0) and a split request.

    `execOnly` stops after execution + measurement (`proof` is `none`
    either way; `suggestedParts` is 1 exactly when the peak fits): the
    split loop runs on executions alone, never starting a STARK. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (ownedBlob : ByteArray) (maxRamBytes : Nat := 0)
  (execOnly : Bool := false) :
    IO (Except String ShardProveResult) :=
  shardProveWithEnv' system funIdx envHandle ownedBlob maxRamBytes execOnly

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem →
  @& Array G → @& Proof → Except String Unit

/-- Verify and serialize a proof in the transport consumed by the in-circuit
recursive verifier. -/
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

/-- The one-shot prover RAM budget: 85 % of the minimum of host available
    RAM and visible cgroup headroom (including existing charges).
    Returns `0` when telemetry is unavailable. Shard-batch execution uses
    a separate live admission controller with additional growth headroom. -/
def detectedRamBudgetBytes : IO Nat := do
  pure (← detectedRamBudgetFFI).toNat

namespace Bytecode.Toplevel

/-- Small result of native partition orchestration. Counts describe only the
selected source shards and their owned constants (all shards without a
selection). The environment, ownership, witness data and audit stay in Rust. -/
structure PartitionCheckResult where
  constants : Nat
  shards : Nat
  failures : Nat
  elapsedMs : Nat
  deriving Inhabited

/-- Partition execution without a destination prover budget or proof-cache
reuse. Rust memory-maps the input, validates and assigns EVERY constant in one
pass, then executes only the selected shards with the existing wave executor.
`none` selects all shards; `some #[]` is an error, never an all-shards fallback.
Ids are bounds-checked, sorted and deduplicated. Coverage/tree validation is
never restricted by the selection, and skipped leaves are not reported checked.
An empty `report` string omits the audit file. File reads and report writes
are sequenced through `IO`; this is not a pure function of the path strings. -/
@[extern "rs_aiur_check_partition"]
opaque checkPartition (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (ixe manifest : @& String)
  (jobs : @& Nat) (useBytecode : Bool)
  (commitment : @& CommitmentParameters) (fri : @& FriParameters)
  (report revision command budgetSource : @& String)
  (selection : @& Option (Array Nat) := none) :
    IO (Except String PartitionCheckResult)

/-- One shard's result from `shardCheckBatchWithEnv`. -/
structure ShardResult where
  error : String
  peakBytes : Nat
  /-- 1 when `peakBytes` fits the batch's `maxRamBytes` (or no budget
      was given); otherwise the part count the peak model projects will
      fit (`AiurSystem::suggested_split_parts`, measured on the record
      in-task). -/
  suggestedParts : Nat
  /-- 0 = execution finished (success or semantic error); 1 = interrupted at
      the per-record memory limit (split and retry); 2 = interrupted at the
      shared batch record limit (retry after this wave drains). An interrupted
      execution always has a nonempty error and no measured prover peak. -/
  resourceStatus : Nat := 0
  deriving Inhabited

@[extern "rs_aiur_toplevel_shard_check_batch"]
private opaque shardCheckBatchWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool → @& Nat →
  @& CommitmentParameters → @& FriParameters → @& Nat →
    IO (Except String (Array ShardResult))

/-- Check EVERY shard of a partition in one call: rayon over the shard
    list with true work-stealing (no chunk barriers), each shard
    through the exact single-shard machinery over its own private
    record and witness io. `shardsBlob` encodes, per shard, a 4-byte LE
    owned-constant count followed by that many 32-byte addresses.
    Returns one `ShardResult` per shard in shard order: empty error =
    clean, and `peakBytes` is the analytic prover RAM peak
    ([`AiurSystem::peak_prove_bytes`] Rust-side) of the shard's executed
    record — the split/merge input (0 when no completed record is available).
    `jobs = 0` uses rayon's default pool width (all cores). Live memory
    admission controls concurrency, and cooperative allocation accounting
    bounds per-record and aggregate query storage. Neither replaces the OS
    memory cap: input/witness construction, stacks and allocator overhead
    also consume memory. `IX_AIUR_EXEC_MAX_BYTES` overrides the per-record
    accounted-storage limit (positive bytes; default at most 32 GiB).

    `maxRamBytes > 0` is a per-shard prover-RAM budget: each result's
    `suggestedParts` is 1 when its peak fits and the model's projected
    part count otherwise, so a caller can cut over-budget shards and
    re-batch the parts — the wave loop that audits a partition's split
    behavior on executions alone. Early execution limits instead return a
    nonzero `resourceStatus`, a nonempty error and no measured peak. Callers
    split/retry these outcomes even without a destination prover budget. -/
def shardCheckBatchWithEnv (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (shardsBlob : ByteArray) (useBytecode : Bool := false) (jobs : Nat := 0)
  (commitmentParameters : CommitmentParameters := defaultCommitmentParameters)
  (friParameters : FriParameters := defaultFriParameters)
  (maxRamBytes : Nat := 0)
  : IO (Except String (Array ShardResult)) :=
  shardCheckBatchWithEnv' toplevel funIdx envHandle shardsBlob useBytecode
    jobs commitmentParameters friParameters maxRamBytes

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
