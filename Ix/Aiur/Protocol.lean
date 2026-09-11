module
public import Ix.Address
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

/-- The advice of a range-sum recursion node over shards `[lo, hi)` of this
batch: the serialized preamble (headers and messages, the prefix of the
batch's own encoding), the range's proofs as one length-prefixed vector, and
the range's residual sum as two little-endian `u64` limbs. -/
@[extern "rs_aiur_proof_range_advice"]
opaque rangeAdvice : @& Proof → @& Nat → @& Nat →
  Except String (ByteArray × ByteArray × ByteArray)
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
  (useCache writeOutputs traceShards : Bool) (rangeWidth : @& Nat)
  (wrapRoot : Bool) :
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
  /-- `proveEnvDistributed` with `execOnly`: each worker's measured record
      bytes, 8-byte LE per worker in manifest order; empty otherwise. -/
  workerBytes : ByteArray

@[extern "rs_aiur_system_shard_prove_with_env"]
private opaque shardProveWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → @& Nat → Bool → Bool →
  @& Nat → Except String ShardProveResult

/-- What a trace-shard batch keeps of each shard between its two rounds.
    `auto` lets the prover's RAM model choose: retain when the whole
    retained batch fits the budget, regenerate otherwise. -/
inductive ShardRetention where
  | auto
  | retain
  | regenerate
  deriving Repr, DecidableEq

def ShardRetention.parse : String → Option ShardRetention
  | "auto" => some .auto
  | "retain" => some .retain
  | "regenerate" => some .regenerate
  | _ => none

def ShardRetention.code : ShardRetention → Nat
  | .auto => 0
  | .retain => 1
  | .regenerate => 2

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
    split loop runs on executions alone, never starting a STARK.

    `traceShards` proves an over-budget record as a batch of trace
    shards, each within the budget, instead of splitting it into parts;
    `peakBytes` is then the heaviest shard's projection. Only when no
    shard count fits does the result fall back to `suggestedParts`.
    `retention` fixes what the batch keeps between its rounds, or lets
    the RAM model choose. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (ownedBlob : ByteArray) (maxRamBytes : Nat := 0)
  (execOnly : Bool := false) (traceShards : Bool := false)
  (retention : ShardRetention := .auto) :
    Except String ShardProveResult :=
  shardProveWithEnv' system funIdx envHandle ownedBlob maxRamBytes execOnly
    traceShards retention.code

@[extern "rs_aiur_system_prove_env_distributed"]
private opaque proveEnvDistributed' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray →
  @& Nat → Bool → Bool → @& Nat → @& Nat → @& ByteArray →
  Except String ShardProveResult

/-- The whole environment as ONE claim, `CheckEnv(root, none)`, proven from
    one worker record per element of `owners` (trace-sharding design
    §13.3). Worker 0 runs `verify_claim` (`verifyIdx`) and defers every
    `check_owned` (`checkOwnedIdx`) call for a constant it does not own;
    every other worker runs `check_owned` over its chunk (the constants it
    owns), in its own pointer namespace. The workers execute in parallel;
    the records
    are proven as one batch, each planned to `maxCells` committed cells
    (`0`: one shard per record). `planOnly` stops after the static caller
    graph and the commit order, reporting every worker's owned constants,
    byte scope and callers and the largest group of mutually calling
    workers (how many records the first round holds at once), without
    executing; `execOnly` stops after execution and the absorption of the
    deferred calls, reporting every record's size. Both leave `proof`
    `none`. `peakBytes` is not measured (`0`).

    Records are proven in an order that lets a worker commit as soon as
    every worker that calls into it has executed, at most `execJobs`
    workers executing at once (`0`: all). Executions run ahead of the
    prover as far as `maxRamBytes` (`0`: detect) leaves room for their
    records beside the prover's working set, and a record stays resident
    for its second round while that room lasts, so a worker executes twice
    only when memory forces it. `measured` gives each worker's record
    bytes as an earlier `execOnly` run measured them (the manifest's
    measured-peaks section); without them nothing runs ahead until this
    run has measured a record. -/
def proveEnvDistributed (system : @& AiurSystem)
  (verifyIdx checkOwnedIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (owners : Array (Array Address)) (maxCells : Nat := 0)
  (planOnly : Bool := false) (execOnly : Bool := false) (execJobs : Nat := 0)
  (maxRamBytes : Nat := 0) (measured : Array Nat := #[]) :
    Except String ShardProveResult :=
  let u32le (n : Nat) : ByteArray :=
    ⟨#[(n &&& 0xFF).toUInt8, ((n >>> 8) &&& 0xFF).toUInt8,
      ((n >>> 16) &&& 0xFF).toUInt8, ((n >>> 24) &&& 0xFF).toUInt8]⟩
  let header : ByteArray :=
    owners.foldl (fun (acc : ByteArray) (o : Array Address) => acc ++ u32le o.size)
      (u32le owners.size)
  let blob : ByteArray :=
    owners.foldl (fun (acc : ByteArray) (o : Array Address) =>
      o.foldl (fun (acc : ByteArray) (a : Address) => acc ++ a.hash) acc) header
  let u64le (n : Nat) : ByteArray :=
    ⟨(Array.range 8).map fun i => ((n >>> (8 * i)) &&& 0xFF).toUInt8⟩
  let measuredBlob : ByteArray := measured.foldl
    (fun (acc : ByteArray) (n : Nat) => acc ++ u64le n) ByteArray.empty
  proveEnvDistributed' system verifyIdx checkOwnedIdx envHandle blob maxCells
    planOnly execOnly execJobs maxRamBytes measuredBlob

/-- One shard claim proven by `shardProveAheadWithEnv`: the claim's wire
    bytes, the persisted proof wrapper's store address (hex) and the
    heaviest trace shard's projected peak. -/
structure ShardProvenAhead where
  claimBytes : ByteArray
  proofAddr : String
  peakBytes : Nat

@[extern "rs_aiur_system_shard_prove_ahead_with_env"]
private opaque shardProveAheadWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → @& ByteArray → @& Nat →
  @& Nat → @& Nat → @& String → @& String →
  Except String (Array ShardProvenAhead)

/-- Several shard claims proven in order, each from one execution planned
    as trace shards within `maxRamBytes`, with the executions running
    ahead of the prover on threads — `execJobs` at once (`0`: one per
    core), so peak host memory is the prover's budget plus the records in
    flight. Every proof and its claim are written to the store under
    `storeDir` and, unless `indexDir` is empty, recorded in the shard-proof
    index as soon as they exist, so a killed run keeps what it finished.
    `labels` are the shards' manifest indices, for the lines printed. -/
def shardProveAheadWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (owners : Array (Array Address)) (labels : Array Nat) (maxRamBytes : Nat)
  (retention : ShardRetention) (execJobs : Nat) (storeDir indexDir : String) :
    Except String (Array ShardProvenAhead) :=
  let u32le (n : Nat) : ByteArray :=
    ⟨#[(n &&& 0xFF).toUInt8, ((n >>> 8) &&& 0xFF).toUInt8,
      ((n >>> 16) &&& 0xFF).toUInt8, ((n >>> 24) &&& 0xFF).toUInt8]⟩
  let header : ByteArray :=
    owners.foldl (fun (acc : ByteArray) (o : Array Address) => acc ++ u32le o.size)
      (u32le owners.size)
  let blob : ByteArray :=
    owners.foldl (fun (acc : ByteArray) (o : Array Address) =>
      o.foldl (fun (acc : ByteArray) (a : Address) => acc ++ a.hash) acc) header
  let labelsBlob : ByteArray :=
    labels.foldl (fun (acc : ByteArray) (n : Nat) => acc ++ u32le n) ByteArray.empty
  shardProveAheadWithEnv' system funIdx envHandle blob labelsBlob maxRamBytes
    retention.code execJobs storeDir indexDir

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

/-- The prover/execution RAM budget the Rust side detects on this machine:
    85 % of `MemAvailable` (`ix_kernel::shard::RAM_USABLE_FRAC`) — the policy
    the check batch's RAM gate and `ix prove --max-ram 0` use. `0` when
    `/proc/meminfo` is unreadable; callers that need a budget fail closed
    on it instead of running ungated. -/
def detectedRamBudgetBytes : IO Nat := do
  pure (← detectedRamBudgetFFI).toNat

namespace Bytecode.Toplevel

/-- One shard's result from `shardCheckBatchWithEnv`. -/
structure ShardResult where
  error : String
  peakBytes : Nat
  /-- 1 when `peakBytes` fits the batch's `maxRamBytes` (or no budget
      was given); otherwise the part count the peak model projects will
      fit (`AiurSystem::suggested_split_parts`, measured on the record
      in-task). -/
  suggestedParts : Nat
  deriving Inhabited

@[extern "rs_aiur_toplevel_shard_check_batch"]
private opaque shardCheckBatchWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool → @& Nat →
  @& CommitmentParameters → @& FriParameters → @& Nat →
    Except String (Array ShardResult)

/-- Check EVERY shard of a partition in one call: rayon over the shard
    list with true work-stealing (no chunk barriers), each shard
    through the exact single-shard machinery over its own private
    record and witness io. `shardsBlob` encodes, per shard, a 4-byte LE
    owned-constant count followed by that many 32-byte addresses.
    Returns one `ShardResult` per shard in shard order: empty error =
    clean, and `peakBytes` is the analytic prover RAM peak
    ([`AiurSystem::peak_prove_bytes`] Rust-side) of the shard's executed
    record — the split/merge input (0 on failure).
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
  (maxRamBytes : Nat := 0)
  : Except String (Array ShardResult) :=
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
