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

/-- Decode an untrusted serialized proof without aborting the process. Cache
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
    ProveResult

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let r := prove' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray
  (r.claim, r.proof, .ofArrays r.ioData r.ioMap)

@[extern "rs_aiur_system_prove_ixvm"]
private opaque proveIxVM' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    ProveResult

/-- IxVM-native prove: same shape as `prove`, but routes execution
    through the codegen'd Rust kernel (`execute_generated`) instead
    of the bytecode interpreter. The resulting `Proof` is
    verification-compatible with one from `prove`. Only valid when
    `system.toplevel` is the IxVM kernel's bytecode. -/
def proveIxVM (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let r := proveIxVM' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray
  (r.claim, r.proof, .ofArrays r.ioData r.ioMap)

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
    Array G × Proof

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

@[extern "rs_aiur_system_shard_prove_with_env"]
private opaque shardProveWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray →
    Except String ProveEnvResult

/-- Per-shard prove against a Rust-owned `EnvHandle`. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (ownedBlob : ByteArray) :
    Except String (ByteArray × Proof × IOBuffer) :=
  (shardProveWithEnv' system funIdx envHandle ownedBlob).map
    fun r => (r.claimBytes, r.proof, .ofArrays r.ioData r.ioMap)

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

namespace Bytecode.Toplevel

@[extern "rs_aiur_toplevel_shard_check_batch"]
private opaque shardCheckBatchWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool → @& Nat →
  @& CommitmentParameters → @& FriParameters →
    Except String (Array (String × Nat))

/-- Check EVERY shard of a partition in one call: rayon over the shard
    list with true work-stealing (no chunk barriers), each shard
    through the exact single-shard machinery over its own private
    record and witness io. `shardsBlob` encodes, per shard, a 4-byte LE
    owned-constant count followed by that many 32-byte addresses.
    Returns one `(error, peakBytes)` pair per shard in shard order:
    empty error = clean, and `peakBytes` is the analytic prover RAM
    peak ([`AiurSystem::peak_prove_bytes`] Rust-side) of the shard's
    executed record — the split/merge input (0 on failure).
    `jobs = 0` uses rayon's default pool width (all cores): peak RSS
    is bounded by the Rust-side RAM gate (a byte-weighted admission
    semaphore over estimated per-shard execution RSS vs available
    system RAM), not by thread count — pass `jobs` only to narrow
    CPU use. -/
def shardCheckBatchWithEnv (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (shardsBlob : ByteArray) (useBytecode : Bool := false) (jobs : Nat := 0)
  (commitmentParameters : CommitmentParameters := defaultCommitmentParameters)
  (friParameters : FriParameters := defaultFriParameters)
  : Except String (Array (String × Nat)) :=
  shardCheckBatchWithEnv' toplevel funIdx envHandle shardsBlob useBytecode
    jobs commitmentParameters friParameters

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
